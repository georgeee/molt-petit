import os
import re

# Read all 110 unique symbols from paper
with open('verify-out/claims-draft.json') as f:
    import json
    claims = json.load(f)

paper_syms = set()
for c in claims:
    for code in c.get('raw_codes', []):
        sym = code.replace(r'\_', '_').replace('$', '').strip()
        paper_syms.add(sym)

print(f"Paper symbols: {len(paper_syms)}")

# Check each symbol in Molt, MoltPetit, Rust
# We want to find:
# 1. Molt front-facing declaration (Molt.<sym> or Molt.Block.<sym>, etc.)
# 2. Underlying resolved declaration in MoltPetit.Model or Rust or Molt
# 3. Axioms

