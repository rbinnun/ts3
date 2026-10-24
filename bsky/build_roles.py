import duckdb, os, time, pandas as pd
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('BSKY_DATA', os.path.join(HERE, 'data'))
P = HERE
G = DATA
rules = []
for line in open(f'{P}/roles.plain'):
    parts = line.rstrip('\n').split(', ')
    if len(parts) == 5 and parts[1] == 'at' and parts[3] == 'means':
        rules.append({'collection': parts[0], 'path': '$.' + parts[2], 'role': parts[4]})
con = duckdb.connect(f'{G}/roles.duckdb'); con.execute("set threads=4"); con.execute("set memory_limit='10GB'")
con.execute("set enable_progress_bar=false"); con.execute(f"set temp_directory='{G}/tmp'")
con.register('rules_df', pd.DataFrame(rules)); con.execute("create or replace table rules as select * from rules_df")
F = f"read_parquet('{G}/facts/*.parquet')"
t = time.time()
# one header row per event: who, when, what kind of record, which operation, which record
con.execute(f"""create or replace table events as select event_id,
    max(value) filter (where path='$.did') ->> '$' actor,
    max(value) filter (where path='$.time_us')::bigint time_us,
    max(value) filter (where path='$.commit.collection') ->> '$' collection,
    max(value) filter (where path='$.commit.operation') ->> '$' op,
    max(value) filter (where path='$.commit.rkey') ->> '$' rkey
  from {F} where path in ('$.did','$.time_us','$.commit.collection','$.commit.operation','$.commit.rkey') group by event_id""")
print(f'events {con.execute("select count(*) from events").fetchone()[0]:,} ({time.time()-t:.0f}s)', flush=True)
# every fact whose path one of the rules names becomes a role row
con.execute(f"""create or replace table roles as
  select f.event_id, e.time_us, e.actor, e.collection, e.op, r.role,
         f.value ->> '$' target,
         case when (f.value ->> '$') like 'at://%' then split_part(f.value ->> '$','/',3) else f.value ->> '$' end target_account,
         case when (f.value ->> '$') like 'at://%' then split_part(f.value ->> '$','/',4) else 'account' end target_kind
  from {F} f join events e using (event_id)
  join rules r on r.collection = e.collection and r.path = regexp_replace(f.path, '\\[\\d+\\]', '.*', 'g')""")
con.execute("alter table roles add column self boolean"); con.execute("update roles set self = (actor = target_account)")
print(f'role rows {con.execute("select count(*) from roles").fetchone()[0]:,} ({time.time()-t:.0f}s)', flush=True)
# undo: a delete matched to the create it removes (when that create is inside the captured window)
con.execute("""create or replace table undos as
  select d.event_id, d.time_us, d.actor, d.collection, 'delete' op, 'undid: ' || r.role role, r.target, r.target_account, r.target_kind, r.self
  from events d join events c on c.actor=d.actor and c.collection=d.collection and c.rkey=d.rkey and c.op='create' and d.op='delete'
  join roles r on r.event_id = c.event_id""")
print(f'undo rows {con.execute("select count(*) from undos").fetchone()[0]:,} ({time.time()-t:.0f}s)', flush=True)
