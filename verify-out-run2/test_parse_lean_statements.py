import re

def parse_lean_statements(filepath):
    with open(filepath) as f:
        text = f.read()

    # Pattern for axioms:
    # 'Name' does not depend on any axioms
    # 'Name' depends on axioms: [a, b, c]
    pat = re.compile(r"^'(.+?)'\s+(does not depend on any axioms|depends on axioms:\s*\[(.*?)\])$", re.MULTILINE)
    
    matches = list(pat.finditer(text))
    results = {}
    last_end = 0
    for m in matches:
        name = m.group(1)
        dep_kind = m.group(2)
        ax_str = m.group(3)
        if ax_str is not None:
            axioms = [a.strip() for a in ax_str.split(',') if a.strip()]
        else:
            axioms = []
            
        chunk = text[last_end:m.start()].strip()
        # Filter out lines that are lean warnings or errors
        lines = [l for l in chunk.splitlines() if not l.startswith('error(') and not l.startswith('warning(') and 'error(lean.' not in l and not l.startswith('verify-out/Stmts.lean:')]
        check_text = "\n".join(lines).strip()
        results[name] = {
            'check': check_text,
            'axioms': sorted(axioms)
        }
        last_end = m.end()
    return results

data = parse_lean_statements('verify-out/lean-statements.txt')
print(f"Parsed {len(data)} entries")
