import re

with open('paper/molt.tex') as f:
    text = f.read()

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Theorem spans
theorems_spans = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    theorems_spans.append((m.start(), m.end()))

def in_thm(pos):
    return any(s <= pos < e for s, e in theorems_spans)

# Split text into paragraphs
paragraphs = []
for m in re.finditer(r'([^\n]+(?:\n[^\n]+)*)', text):
    p_text = m.group(0).strip()
    if not p_text:
        continue
    # skip comments only paragraphs
    lines = [l for l in p_text.splitlines() if not l.strip().startswith('%')]
    if not lines:
        continue
    start_pos = m.start()
    end_pos = m.end()
    paragraphs.append((start_pos, end_pos, p_text))

# For each paragraph outside theorems:
# Let's inspect paragraphs that contain \code{...} or machine-check / proved / formaliz
print(f"Total paragraphs: {len(paragraphs)}")

interesting = []
for s_pos, e_pos, p_text in paragraphs:
    if in_thm(s_pos):
        continue
    codes = [c for c in re.findall(r'\\code\{([^}]+)\}', p_text) if c not in NON_LEAN and c.replace(r'\_', '_') not in NON_LEAN]
    has_kw = bool(re.search(r'machine-check|formaliz|proved|proven', p_text, re.I))
    if codes or has_kw:
        s_line = text.count('\n', 0, s_pos) + 1
        e_line = text.count('\n', 0, e_pos) + 1
        interesting.append((s_line, e_line, p_text, codes, has_kw))

print(f"Interesting paragraphs: {len(interesting)}")
for s_line, e_line, p_text, codes, has_kw in interesting:
    print(f"P L{s_line}-{e_line}: codes={codes}, kw={has_kw}")
