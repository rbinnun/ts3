import os, sys, gzip, io, re, time, boto3, duckdb
day, hours = sys.argv[1], int(sys.argv[2])
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('BSKY_DATA', os.path.join(HERE, 'data'))
S = DATA
os.makedirs(f'{S}/facts', exist_ok=True); os.makedirs(f'{S}/tmp', exist_ok=True)
s3 = boto3.client('s3', endpoint_url=os.environ['R2_ENDPOINT'], aws_access_key_id=os.environ['R2_ACCESS_KEY_ID'],
                  aws_secret_access_key=os.environ['R2_SECRET_ACCESS_KEY'], region_name='auto')
B = os.environ['R2_BUCKET']
import datetime
start_us = int(datetime.datetime.fromisoformat(day + 'T00:00:00+00:00').timestamp() * 1e6)
cutoff = start_us + hours * 3600 * 1_000_000
con = duckdb.connect(); con.execute("set threads=3"); con.execute("set memory_limit='9GB'"); con.execute("set preserve_insertion_order=false")
con.execute(f"set temp_directory='{S}/tmp'")
TIME = re.compile(rb'"time_us":\s*(\d+)')
event_id = 0; part = 0; t0 = time.time()
def flush(lines, kind):
    global part
    if not lines: return
    f = f'{S}/tmp/batch.jsonl'
    with open(f, 'wb') as fh: fh.write(b''.join(lines))
    # one row per JSON leaf (and per empty object/array, so shapes survive); event_id ties facts to their event
    con.execute(f"""copy (
        select r.event_id, '{kind}' as file, j.fullkey as path, j.type as type,
               case when j.type in ('OBJECT','ARRAY') then null else j.atom::varchar end as value
        from (select (json->>'$._eid')::bigint event_id, json from read_json_objects('{f}', format='newline_delimited')) r,
             json_tree(r.json) j
        where (j.type not in ('OBJECT','ARRAY') or j.value::varchar in ('{{}}','[]')) and j.key is distinct from '_eid'
      ) to '{S}/facts/part-{part:05d}.parquet' (format parquet, compression zstd)""")
    part += 1; os.remove(f)
for kind in ['follows', 'blocks', 'reposts', 'posts', 'other', 'likes']:
    key = s3.list_objects_v2(Bucket=B, Prefix=f'{kind}/{day}/')['Contents'][0]['Key']
    body = s3.get_object(Bucket=B, Key=key)['Body']
    gz = gzip.GzipFile(fileobj=body); batch = []; n = 0; t = time.time()
    for line in io.BufferedReader(gz, buffer_size=1 << 20):
        m = TIME.search(line)
        if m and int(m.group(1)) >= cutoff: break
        event_id += 1; n += 1
        # stamp each event with its id, as the first key of the object
        batch.append(b'{"_eid":' + str(event_id).encode() + b',' + line.lstrip()[1:])
        if len(batch) >= 300_000: flush(batch, kind); batch = []
    flush(batch, kind); body.close()
    print(f'{kind:8} {n:>11,} events in {time.time()-t:6.0f}s  (total {time.time()-t0:.0f}s)', flush=True)
print(f'done: {event_id:,} events, {part} parts, {sum(os.path.getsize(S+"/facts/"+p) for p in os.listdir(S+"/facts"))/1e9:.2f} GB, {time.time()-t0:.0f}s', flush=True)
