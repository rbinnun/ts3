cd "$(dirname "$0")" || exit 2
work="$(mktemp -d)" || exit 2
trap 'rm -rf "$work"' EXIT
go build -o "$work/machine" . || exit 2
"$work/machine"
