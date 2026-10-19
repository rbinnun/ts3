import re
import sys

BUILTINS = {"ends with": ":string:ends_with", "starts with": ":string:starts_with"}
FROM_BUILTIN = {v: k for k, v in BUILTINS.items()}


def split_top(text, sep):
    parts, depth, cur, quote, i = [], 0, "", None, 0
    while i < len(text):
        ch = text[i]
        if quote:
            cur += ch
            if ch == "\\" and i + 1 < len(text):
                cur += text[i + 1]
                i += 2
                continue
            if ch == quote:
                quote = None
            i += 1
            continue
        if ch in "\"'":
            quote = ch
        elif ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return parts


def mangle_string(text):
    return "'" + text + "'" if '"' in text else '"' + text + '"'


def to_words(camel):
    return re.sub(r"(?<!^)([A-Z])", r" \1", camel).lower()


def to_camel(words):
    return "".join(w[:1].upper() + w[1:] for w in words.split(" "))


def plain_value(term):
    term = term.strip()
    if re.fullmatch(r"[A-Z][A-Za-z]*", term):
        return "[" + to_words(term) + "]"
    if re.fullmatch(r"-?[0-9]+", term):
        return term
    if len(term) >= 2 and term[0] in "\"'" and term[-1] == term[0]:
        text = term[1:-1]
        if (", " in text or re.fullmatch(r"\[[a-z ]+\]", text) or re.fullmatch(r"-?[0-9]+", text)
                or text == "is" or text.startswith(("declared: ", "if ", "and ")) or text != text.strip()):
            return term
        return text
    raise ValueError("cannot say in plain: " + term)


def mangle_value(text):
    if re.fullmatch(r"\[[a-z ]+\]", text):
        return to_camel(text[1:-1])
    if re.fullmatch(r"-?[0-9]+", text):
        return text
    if len(text) >= 2 and text[0] in "\"'" and text[-1] == text[0]:
        return text
    return mangle_string(text)


def plain_atom(atom):
    atom = atom.strip()
    m = re.fullmatch(r"(\S+) != (\S+)", atom)
    if m:
        return ", ".join([plain_value(m.group(1)), "differs from", plain_value(m.group(2))])
    m = re.fullmatch(r"([A-Z][A-Za-z]*) = fn:string:concat\((.*)\)", atom, re.S)
    if m:
        return ", ".join([plain_value(m.group(1)), "is the join of"] + [plain_value(a) for a in split_top(m.group(2), ", ")])
    negated = atom.startswith("!")
    if negated:
        atom = atom[1:]
    m = re.fullmatch(r"(:?[a-z_:]+)\((.*)\)", atom, re.S)
    if not m:
        raise ValueError("cannot say in plain: " + atom)
    name, inside = m.group(1), m.group(2)
    args = [a for a in split_top(inside, ", ")] if inside.strip() else []
    if name.startswith(":"):
        words = FROM_BUILTIN[name]
    else:
        words = name.replace("_", " ")
        if words in BUILTINS or words in ("differs from", "is", "is the join of"):
            raise ValueError("reserved word used as a name: " + name)
    values = [plain_value(a) for a in args]
    if not values:
        said = words
    elif len(values) == 1:
        said = ", ".join([values[0], "is", words])
    else:
        said = ", ".join([values[0], words] + values[1:])
    return ("not " if negated else "") + said


def to_plain(line):
    line = line.strip()
    if not line:
        return [""]
    if line.startswith("Decl "):
        return ["declared: " + plain_atom(line[5:].rstrip("."))]
    clause = line[:-1] if line.endswith(".") else line
    halves = split_top(clause, " :- ")
    head = plain_atom(halves[0])
    if len(halves) == 1:
        return [head]
    body = split_top(halves[1], ", ")
    out = [head]
    for i, literal in enumerate(body):
        out.append("    " + ("if " if i == 0 else "and ") + plain_atom(literal))
    return out


def mangle_atom(said):
    negated = said.startswith("not ")
    if negated:
        said = said[4:]
    parts = split_top(said, ", ")
    if len(parts) == 1:
        if negated:
            return "!" + parts[0].replace(" ", "_") + "()"
        return parts[0].replace(" ", "_") + "()"
    if len(parts) == 2:
        raise ValueError("a plain sentence has one part or three or more: " + said)
    if len(parts) == 3 and parts[1] == "is":
        name, values = parts[2], [parts[0]]
    else:
        name, values = parts[1], [parts[0]] + parts[2:]
    if name == "differs from":
        return mangle_value(values[0]) + " != " + mangle_value(values[1])
    if name == "is the join of":
        return mangle_value(values[0]) + " = fn:string:concat(" + ", ".join(mangle_value(v) for v in values[1:]) + ")"
    symbol = BUILTINS.get(name, name.replace(" ", "_"))
    return ("!" if negated else "") + symbol + "(" + ", ".join(mangle_value(v) for v in values) + ")"


def to_mangle(lines):
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            out.append("")
            i += 1
            continue
        if line.startswith("declared: "):
            out.append("Decl " + mangle_atom(line[len("declared: "):]) + ".")
            i += 1
            continue
        head = mangle_atom(line)
        body = []
        i += 1
        while i < len(lines) and lines[i].startswith("    "):
            cond = lines[i][4:]
            if body == [] and not cond.startswith("if "):
                raise ValueError("a rule's first condition starts with if: " + cond)
            if body != [] and not cond.startswith("and "):
                raise ValueError("a rule's later conditions start with and: " + cond)
            body.append(mangle_atom(cond[3:] if cond.startswith("if ") else cond[4:]))
            i += 1
        out.append(head + (" :- " + ", ".join(body) if body else "") + ".")
    return out


if __name__ == "__main__":
    mode, path = sys.argv[1], sys.argv[2]
    text = open(path).read().split("\n")
    if text and text[-1] == "":
        text = text[:-1]
    if mode == "to-plain":
        out = [p for line in text for p in to_plain(line)]
    else:
        out = to_mangle(text)
    print("\n".join(out))
