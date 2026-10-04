import re

with open('paper/molt.tex') as f:
    text = f.read()

lines = text.splitlines()

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Find all lines that have \code{...} or machine-check or formaliz or proved
matches = []
for i, line in enumerate(lines, 1):
    codes = re.findall(r'\\code\{([^}]+)\}', line)
    lean_codes = [c for c in codes if c not in NON_LEAN and c.replace(r'\_', '_') not in NON_LEAN]
    has_kw = bool(re.search(r'machine-check|formaliz|proved|proven', line, re.I))
    if lean_codes or has_kw:
        matches.append((i, line, lean_codes, has_kw))

print(f"Total matching lines: {len(matches)}")
