import re

with open('verify-out/Stmts.lean') as f:
    stmts_lines = [l.strip() for l in f if l.startswith('-- DECL: ')]
all_decls = [l[len('-- DECL: '):] for l in stmts_lines]

with open('verify-out/lean-statements.txt') as f:
    text = f.read()

axiom_decls = set(re.findall(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:)", text))

missing = [d for d in all_decls if d not in axiom_decls]
print(f"Missing from axiom reports ({len(missing)}):")
for m in missing:
    print(m)
