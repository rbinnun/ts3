cd "$(dirname "$0")" || exit 2
dir=$(mktemp -d) || exit 2
if ! go build -o "$dir/engine" .; then
	rm -rf "$dir"
	exit 2
fi
"$dir/engine" "$@"
code=$?
rm -rf "$dir"
exit "$code"
