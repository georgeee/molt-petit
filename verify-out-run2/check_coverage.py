import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

# Collect all symbols mentioned in raw_codes across all claims
all_symbols = set()
for c in claims:
    for code in c.get('raw_codes', []):
        sym = code.replace(r'\_', '_').replace('$', '').strip()
        all_symbols.add(sym)

print(f"Total symbols mentioned across all claims: {len(all_symbols)}")

# Let's check which symbols have a declaration in Stmts.lean
with open('verify-out/Stmts.lean') as f:
    stmts = f.read()

found = set()
missing = set()
for sym in sorted(all_symbols):
    # Check if sym appears in a -- DECL: line
    if f".{sym}\n" in stmts or f".{sym}'\n" in stmts:
        found.add(sym)
    else:
        missing.add(sym)

print(f"Found in Stmts.lean: {len(found)}")
print(f"Missing from Stmts.lean: {len(missing)}")
if missing:
    print("Missing:", sorted(missing))
