cd "$(dirname "$0")" || exit 2
work=$(mktemp -d) || exit 2
if go build -trimpath -o "$work/engine" . >&2
then
	"$work/engine" spec.plain
	code=$?
else
	code=2
fi
rm -rf "$work"
exit $code
