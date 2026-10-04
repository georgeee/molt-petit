import re

with open('paper/molt.tex') as f:
    text = f.read()

lines = text.splitlines()

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Let's inspect all occurrences of \code{...} in paper/molt.tex
hits = []
for i, line in enumerate(lines, 1):
    codes = re.findall(r'\\code\{([^}]+)\}', line)
    valid_codes = [c for c in codes if c not in NON_LEAN and c.replace(r'\_', '_') not in NON_LEAN]
    if valid_codes:
        hits.append((i, line, valid_codes))

print(f"Total lines with valid codes: {len(hits)}")
