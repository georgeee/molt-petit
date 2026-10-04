import re

with open('paper/molt.tex') as f:
    text = f.read()

lines = text.splitlines()

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Let's inspect where theorems are
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    start_pos = m.start()
    end_pos = m.end()
    start_line = text.count('\n', 0, start_pos) + 1
    end_line = text.count('\n', 0, end_pos) + 1
    theorems.append((m.group(1), start_line, end_line, m.group(0)))

print("=== THEOREMS ===")
for t in theorems:
    print(f"{t[0]} L{t[1]}-{t[2]}: {t[3][:60]}...")

