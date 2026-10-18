cd "$(dirname "$0")" || exit 2
place="$(mktemp -d)" || exit 2
if ! go build -buildvcs=false -o "$place/engine" . ; then
    rm -rf "$place"
    exit 2
fi
"$place/engine"
answer=$?
rm -rf "$place"
exit "$answer"
