import re

# Read test_resolution.out and lean-statements.txt to see which exist
with open('verify-out/lean-statements.txt') as f:
    text = f.read()

# Let's inspect all valid Molt, MoltPetit.Model, Rust declarations that succeeded
# In lean-statements.txt:
# Molt.XYZ : ... or @Molt.XYZ : ...
# 'Molt.XYZ' depends on axioms: ... or 'Molt.XYZ' does not depend on any axioms

checks = {}
# Find all lines like:
# (optional @)Decl : ...
# and following axioms

# Let's check which symbols were in Stmts.lean
with open('verify-out/Stmts.lean') as f:
    stmts_lines = [l.strip()[len('-- DECL: '):] for l in f if l.startswith('-- DECL: ')]

print(f"Stmts.lean has {len(stmts_lines)} declarations")

# Let's check which of these have errors in lean-statements.txt
errors = set()
for m in re.finditer(r'error\(lean\.unknownIdentifier\): Unknown (?:identifier|constant) `([^`]+)`', text):
    errors.add(m.group(1))

print("Unknown identifiers:", errors)
