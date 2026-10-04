import re

with open('paper/molt.tex') as f:
    text = f.read()

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

raw_codes = re.findall(r'\\code\{([^}]+)\}', text)
lean_syms = set()
for c in raw_codes:
    if c in NON_LEAN:
        continue
    clean = c.replace(r'\_', '_').replace('$', '').replace("'", "'").strip()
    if clean in NON_LEAN:
        continue
    lean_syms.add(clean)

print(f"Total unique lean symbols: {len(lean_syms)}")
for s in sorted(lean_syms):
    print(s)
