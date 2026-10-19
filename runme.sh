cd "$(dirname "$0")" || exit 2
bin="$(mktemp -d)" || exit 2
if ! go build -o "$bin/engine" engine.go tools.go; then
	rm -rf "$bin"
	exit 2
fi
"$bin/engine"
code=$?
rm -rf "$bin"
exit "$code"
