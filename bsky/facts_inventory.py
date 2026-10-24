import duckdb, os
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get('BSKY_DATA', os.path.join(HERE, 'data'))
S = DATA
con = duckdb.connect(f'{S}/inventory.duckdb'); con.execute("set threads=4"); con.execute("set memory_limit='10GB'"); con.execute("set enable_progress_bar=false")
con.execute(f"set temp_directory='{S}/tmp'")
F = f"read_parquet('{S}/facts/*.parquet')"
con.execute(f"""create or replace table ev as select event_id, file,
    max(value) filter (where path='$.kind') kind,
    max(value) filter (where path='$.commit.collection') collection,
    max(value) filter (where path='$.commit.operation') op
  from {F} where path in ('$.kind','$.commit.collection','$.commit.operation') group by event_id, file""")
con.execute(f"""create or replace table inv as
  select coalesce(json_extract_string(e.collection, '$'), '(' || json_extract_string(e.kind,'$') || ' event)') collection,
         regexp_replace(f.path, '\\[\\d+\\]', '[*]', 'g') path, f.type, count(*) n, count(distinct f.event_id) events,
         any_value(f.value) example,
         count(*) filter (where f.value like '"did:%') as did_values,
         count(*) filter (where f.value like '"at://%') as uri_values
  from {F} f join ev e using (event_id, file) group by all""")
print('events by file:', con.execute("select file, count(*) from ev group by 1 order by 2 desc").fetchall())
print('events by kind:', con.execute("select json_extract_string(kind,'$'), count(*) from ev group by 1 order by 2 desc").fetchall())
print('total facts:', f"{con.execute('select sum(n) from inv').fetchone()[0]:,}",
      '| storage:', round(sum(os.path.getsize(f'{S}/facts/'+p) for p in os.listdir(f'{S}/facts'))/1e9, 2), 'GB')
print('record types:', con.execute("select count(distinct collection) from inv").fetchone()[0],
      '| distinct paths (indices collapsed):', con.execute("select count(distinct (collection, path)) from inv").fetchone()[0])
