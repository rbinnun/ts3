cd "$(dirname "$0")" || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
go build -o "$dir/machine" . || exit 2
"$dir/machine" spec.plain "$@"
