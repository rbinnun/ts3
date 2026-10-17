cd "$(dirname "$0")" || exit 2
bin="$(mktemp -d)" || exit 2
trap 'rm -rf "$bin"' EXIT
go build -o "$bin/engine" . || exit 2
"$bin/engine"
