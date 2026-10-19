cd "$(dirname "$0")" || exit 2
place=$(mktemp -d) || exit 2
if ! go build -trimpath -o "$place/machine" .; then
	rm -rf "$place"
	exit 2
fi
"$place/machine" "$@"
code=$?
rm -rf "$place"
exit "$code"
