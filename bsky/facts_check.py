import os, re, json, gzip, io, boto3, duckdb, random
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('BSKY_DATA', os.path.join(HERE, 'data'))
S = DATA
con = duckdb.connect(); con.execute("set threads=4"); con.execute("set enable_progress_bar=false")
F = f"read_parquet('{S}/facts/*.parquet')"
# ---- losslessness: rebuild the first N events of each file from facts, compare with the originals in R2
s3 = boto3.client('s3', endpoint_url=os.environ['R2_ENDPOINT'], aws_access_key_id=os.environ['R2_ACCESS_KEY_ID'],
                  aws_secret_access_key=os.environ['R2_SECRET_ACCESS_KEY'], region_name='auto')
B = os.environ['R2_BUCKET']
TOK = re.compile(r'\.("(?:[^"\\]|\\.)*"|[^.\[]+)|\[(\d+)\]')
def steps(fullkey):
    out = []
    for m in TOK.finditer(fullkey[1:]):
        if m.group(2) is not None: out.append(int(m.group(2)))
        else:
            k = m.group(1); out.append(json.loads(k) if k.startswith('"') else k)
    return out
def rebuild(rows):
    root = {}
    for path, typ, val in rows:
        st = steps(path); cur = root
        for i, s in enumerate(st):
            last = i == len(st) - 1
            nxt = None if last else st[i+1]
            if isinstance(s, int):
                while len(cur) <= s: cur.append(None)
                if last: cur[s] = leaf(typ, val)
                else:
                    if cur[s] is None: cur[s] = [] if isinstance(nxt, int) else {}
                    cur = cur[s]
            else:
                if last: cur[s] = leaf(typ, val)
                else:
                    if s not in cur: cur[s] = [] if isinstance(nxt, int) else {}
                    cur = cur[s]
    return root
def leaf(typ, val):
    if typ == 'OBJECT': return {}
    if typ == 'ARRAY': return []
    if typ == 'NULL': return None
    return json.loads(val)
total_ok = total = 0
for kind in ['follows', 'posts', 'other']:
    first, = con.execute(f"select min(event_id) from {F} where file='{kind}'").fetchone()
    N = 2000
    rows = con.execute(f"select event_id, path, type, value from {F} where file='{kind}' and event_id < {first+N} order by event_id").fetchall()
    by = {}
    for e, p, t, v in rows: by.setdefault(e, []).append((p, t, v))
    key = s3.list_objects_v2(Bucket=B, Prefix=f'{kind}/{os.environ.get("BSKY_DAY", "2026-10-22")}/')['Contents'][0]['Key']
    body = s3.get_object(Bucket=B, Key=key)['Body']; gz = io.BufferedReader(gzip.GzipFile(fileobj=body))
    ok = 0
    for i in range(N):
        orig = json.loads(gz.readline())
        if rebuild(by.get(first + i, [])) == orig: ok += 1
    body.close()
    print(f'lossless check {kind:8}: {ok}/{N} events rebuilt exactly from facts')
