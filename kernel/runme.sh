k=$(cd "$(dirname "$0")" && pwd)
b=$(mktemp -d)
trap 'rm -rf "$b"' EXIT
(cd "$k" && go build -o "$b/engine" .) || exit 2
"$b/engine" "$k"
