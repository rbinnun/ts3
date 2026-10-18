cd "$(dirname "$0")" || exit 2
place="$(mktemp -d)" || exit 2
if go build -o "$place/engine" .
then
	"$place/engine" spec.plain
	answer=$?
else
	answer=2
fi
rm -rf "$place"
exit "$answer"
