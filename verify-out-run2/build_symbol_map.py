import re

with open('verify-out/lean-statements.txt') as f:
    lean_out = f.read()

# Let's inspect how checks and axioms are formatted in lean-statements.txt
# When `#check @Name` runs, it outputs:
# Name ... : ...
# or @Name : ...
# Followed by:
# 'Name' depends on axioms: [...]
# or 'Name' does not depend on any axioms

# Let's build a map from declaration name -> (check_stmt, axioms)
entries = {}
current_decl = None
current_check_lines = []

# Let's parse Stmts.lean to know the exact order of declarations
with open('verify-out/Stmts.lean') as f:
    stmts_order = [l.strip()[len('-- DECL: '):] for l in f if l.startswith('-- DECL: ')]

print(f"Total decls in Stmts.lean: {len(stmts_order)}")
