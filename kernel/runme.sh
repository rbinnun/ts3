dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
go build -o "$dir/engine" . || exit 2
"$dir/engine" "$@"
