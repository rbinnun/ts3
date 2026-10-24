# bsky: a lossless view of the Bluesky firehose

Reads the Jetstream capture in R2 (read-only; never touches the collector) and turns it into facts, then roles.

1. `facts_build.py DAY HOURS`: every event from DAY 00:00 UTC for HOURS hours, flattened into one row per JSON leaf (`event_id, file, path, type, value`), as zstd Parquet in `$BSKY_DATA/facts/`.
2. `facts_check.py`: rebuilds sample events from the facts and compares them with the originals in R2 (the losslessness check).
3. `facts_inventory.py`: every path that exists, per record type, with counts and which paths point at accounts or records.
4. `roles.plain`: the role rules. Each line names where a pointer sits and what it means (`app.bsky.feed.like, at, commit.record.subject.uri, means, liked`). Paths not named here are consciously not yet used.
5. `build_roles.py`: applies the rules to the facts: one row per pointer per event (actor, role, target, time), plus undo rows for deletes matched to their creates.

Needs `R2_ENDPOINT`, `R2_ACCESS_KEY_ID`, `R2_SECRET_ACCESS_KEY`, `R2_BUCKET`, and optionally `BSKY_DATA` (default `bsky/data/`, not committed). Python packages: `requirements.txt`.
