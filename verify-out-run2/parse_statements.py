import re

with open('verify-out/Stmts.lean') as f:
    stmts_lines = [l.strip() for l in f if l.startswith('-- DECL: ')]
all_decls = [l[len('-- DECL: '):] for l in stmts_lines]

with open('verify-out/lean-statements.txt') as f:
    text = f.read()

print(f"Total decls in Stmts.lean: {len(all_decls)}")

# Find all blocks in lean-statements.txt
# Notice pattern:
# (Name or @Name) : ...
# 'Name' depends on axioms: [...]  OR  'Name' does not depend on any axioms
# OR error(lean.unknownIdentifier): ...

# Let's count how many decls have '#print axioms' output
axiom_lines = re.findall(r"'([^']+)'\s+(does not depend on any axioms|depends on axioms:.*?)$", text, re.MULTILINE)
print(f"Total axiom reports found: {len(axiom_lines)}")
