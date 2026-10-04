import re

with open('verify-out/Stmts.lean') as f:
    decls = [l.strip()[len('-- DECL: '):] for l in f if l.startswith('-- DECL: ')]

with open('verify-out/lean-statements.txt') as f:
    text = f.read()

# Let's split text by lines that look like:
# 'XYZ' depends on axioms: [...]
# or
# 'XYZ' does not depend on any axioms
axiom_pat = re.compile(r"^'([^']+)'\s+(does not depend on any axioms|depends on axioms:\s*\[(.*?)\])$", re.MULTILINE)

decl_data = {}
last_end = 0

for m in axiom_pat.finditer(text):
    decl_name = m.group(1)
    dep_type = m.group(2)
    axioms_raw = m.group(3)
    if axioms_raw is not None:
        axioms = [a.strip() for a in axioms_raw.split(',') if a.strip()]
    else:
        axioms = []
    
    # Text between last_end and m.start() contains the #check output
    chunk = text[last_end:m.start()].strip()
    # The chunk might have error messages if previous had error, or just the check statement
    # Filter out any lean error lines
    lines = [l for l in chunk.splitlines() if not l.startswith('verify-out/Stmts.lean:') and not l.startswith('error(')]
    check_stmt = "\n".join(lines).strip()
    
    decl_data[decl_name] = {
        'check': check_stmt,
        'axioms': axioms
    }
    last_end = m.end()

print(f"Parsed {len(decl_data)} declarations successfully!")
for d in list(decl_data.keys())[:10]:
    print(f"Decl: {d}")
    print(f"  Check: {decl_data[d]['check'][:80]}...")
    print(f"  Axioms: {decl_data[d]['axioms']}")
