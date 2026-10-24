import os, sys, gzip, io, re, time, datetime, boto3, duckdb, pandas as pd
# usage: week_build.py FIRST_DAY DAYS [HOURS_PER_DAY]
# stores, per day: pair counts per role, node activity, undo pair counts, and the path inventory (see README)
first, ndays = datetime.date.fromisoformat(sys.argv[1]), int(sys.argv[2])
hours = int(sys.argv[3]) if len(sys.argv) > 3 else 24
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('BSKY_DATA', os.path.join(HERE, 'data'))
os.makedirs(f'{DATA}/tmp', exist_ok=True)
s3 = boto3.client('s3', endpoint_url=os.environ['R2_ENDPOINT'], aws_access_key_id=os.environ['R2_ACCESS_KEY_ID'],
                  aws_secret_access_key=os.environ['R2_SECRET_ACCESS_KEY'], region_name='auto')
B = os.environ['R2_BUCKET']
rules = []
for line in open(f'{HERE}/roles.plain'):
    p = line.rstrip('\n').split(', ')
    if len(p) == 5 and p[1] == 'at' and p[3] == 'means': rules.append({'collection': p[0], 'path': '$.' + p[2], 'role': p[4]})
LIKE_RULES = [r for r in rules if r['collection'] == 'app.bsky.feed.like']
db = duckdb.connect(f'{DATA}/week.duckdb'); db.execute("set threads=3"); db.execute("set memory_limit='9GB'")
db.execute("set preserve_insertion_order=false"); db.execute("set enable_progress_bar=false"); db.execute(f"set temp_directory='{DATA}/tmp'")
db.register('rules_df', pd.DataFrame(rules)); db.execute("create or replace table rules as select * from rules_df")
db.execute("create table if not exists accounts(id integer, did varchar)")
db.execute("create table if not exists pairs(day date, actor integer, target integer, role varchar, n integer)")
db.execute("create table if not exists activity(day date, actor integer, kind varchar, collection varchar, op varchar, n integer)")
db.execute("create table if not exists undos(day date, actor integer, target integer, role varchar, n integer)")
db.execute("create table if not exists inventory(day date, sampled boolean, collection varchar, path varchar, type varchar, n bigint, did_values bigint, uri_values bigint)")
db.execute("create table if not exists days_done(day date)")
TIME = re.compile(rb'"time_us":\s*(\d+)')
def stage_tables():
    db.execute("create or replace table s_roles(actor_did varchar, role varchar, tdid varchar, collection varchar, rkey varchar, op varchar)")
    db.execute("create or replace table s_act(did varchar, kind varchar, collection varchar, op varchar, n integer)")
    db.execute("create or replace table s_del(did varchar, collection varchar, rkey varchar)")
nb = 0
def batch(lines, day, kind):
    global nb; nb += 1
    f = f'{DATA}/tmp/batch.jsonl'
    with open(f, 'wb') as fh: fh.write(b''.join(lines))
    db.execute(f"create or replace temp table j as select row_number() over () eid, json from read_json_objects('{f}', format='newline_delimited')")
    db.execute("""create or replace temp table h as select eid, json->>'$.did' did, json->>'$.kind' kind, json->>'$.commit.collection' collection,
                  json->>'$.commit.operation' op, json->>'$.commit.rkey' rkey from j""")
    db.execute("insert into s_act select did, kind, collection, op, count(*) from h group by all")
    db.execute("insert into s_del select did, collection, rkey from h where op = 'delete'")
    full = kind != 'likes' or nb % 10 == 0
    if full:   # the batch's facts, transient: one row per JSON leaf
        db.execute("""create or replace temp table leaf as select j.eid, regexp_replace(t.fullkey, '\\[\\d+\\]', '.*', 'g') path, t.type,
                      case when t.type in ('OBJECT','ARRAY') then null else t.atom::varchar end val
                      from j, json_tree(j.json) t where t.type not in ('OBJECT','ARRAY') or t.value::varchar in ('{}','[]')""")
        db.execute(f"""insert into inventory select '{day}', {'true' if kind == 'likes' else 'false'}, coalesce(h.collection, '(' || h.kind || ' event)'),
                       l.path, l.type, count(*), count(*) filter (where l.val like '"did:%'), count(*) filter (where l.val like '"at://%')
                       from leaf l join h using (eid) group by all""")
    if kind == 'likes':  # read the like rules' paths directly
        for r in LIKE_RULES:
            db.execute(f"""insert into s_roles select h.did, '{r['role']}', v, h.collection, h.rkey, h.op from (
                           select eid, j.json ->> '{r['path']}' v from j) x join h using (eid)
                           where h.collection = '{r['collection']}' and v is not null""")
    else:
        db.execute("""insert into s_roles select h.did, ru.role, l.val ->> '$', h.collection, h.rkey, h.op
                      from leaf l join h using (eid) join rules ru on ru.collection = h.collection and ru.path = l.path""")
    os.remove(f)
t0 = time.time()
for i in range(ndays):
    day = (first + datetime.timedelta(days=i)).isoformat()
    if db.execute("select count(*) from days_done where day=?", [day]).fetchone()[0]: print(day, 'already done', flush=True); continue
    cutoff = int(datetime.datetime.fromisoformat(day + 'T00:00:00+00:00').timestamp() * 1e6) + hours * 3600 * 1_000_000
    td = time.time(); stage_tables()
    for kind in ['follows', 'blocks', 'reposts', 'posts', 'other', 'likes']:
        key = s3.list_objects_v2(Bucket=B, Prefix=f'{kind}/{day}/')['Contents'][0]['Key']
        body = s3.get_object(Bucket=B, Key=key)['Body']; lines = []
        for line in io.BufferedReader(gzip.GzipFile(fileobj=body), buffer_size=1 << 20):
            if not line.strip(): continue
            m = TIME.search(line)
            if m and int(m.group(1)) >= cutoff: break
            lines.append(line)
            if len(lines) >= 250_000: batch(lines, day, kind); lines = []
        if lines: batch(lines, day, kind)
        body.close()
    # targets: an account, or the author named in a record address; pointers with no account are dropped
    db.execute("""create or replace temp table sr as select actor_did, role, op, collection, rkey,
                  case when tdid like 'at://%' then split_part(tdid,'/',3) else tdid end t from s_roles""")
    db.execute("delete from sr where t is null or t not like 'did:%'")
    db.execute("""insert into accounts select (select coalesce(max(id),0) from accounts) + row_number() over (), did from (
                  select distinct did from (select actor_did did from sr union select t from sr union select did from s_act)
                  where did is not null and did not in (select did from accounts))""")
    db.execute(f"""insert into pairs select '{day}', a.id, b.id, sr.role, count(*) from sr join accounts a on a.did = sr.actor_did
                   join accounts b on b.did = sr.t group by all""")
    db.execute(f"""insert into activity select '{day}', a.id, s.kind, s.collection, s.op, sum(s.n) from s_act s join accounts a on a.did = s.did group by all""")
    db.execute(f"""insert into undos select '{day}', a.id, b.id, 'undid: ' || sr.role, count(*) from s_del d
                   join sr on sr.actor_did = d.did and sr.collection = d.collection and sr.rkey = d.rkey and sr.op = 'create'
                   join accounts a on a.did = sr.actor_did join accounts b on b.did = sr.t group by all""")
    for t in ['s_roles', 's_act', 's_del']: db.execute(f"drop table {t}")
    db.execute("insert into days_done values (?)", [day]); db.execute("checkpoint")
    print(f'{day}: {time.time()-td:.0f}s; pairs {db.execute("select count(*) from pairs").fetchone()[0]:,}; accounts {db.execute("select count(*) from accounts").fetchone()[0]:,}; '
          f'db {os.path.getsize(DATA + "/week.duckdb")/1e9:.2f} GB', flush=True)
print(f'done in {time.time()-t0:.0f}s', flush=True)
