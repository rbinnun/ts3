cd "$(dirname "$0")" || exit
dir=$(mktemp -d) || exit
go build -trimpath -buildvcs=false -o "$dir/engine" . && "$dir/engine" spec.plain
code=$?
rm -rf "$dir"
exit "$code"
