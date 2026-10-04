import re

with open('paper/molt.tex') as f:
    text = f.read()

# Non-lean codes that are code formatting in latex
NON_LEAN_CODES = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Let's map each char in text to line number
line_starts = [0]
for idx, c in enumerate(text):
    if c == '\n':
        line_starts.append(idx + 1)

def char_to_line(pos):
    import bisect
    return bisect.bisect_right(line_starts, pos)

# Find all theorem env spans
env_spans = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}', text, re.DOTALL):
    env_spans.append((m.start(), m.end()))

def in_env(pos):
    for s, e in env_spans:
        if s <= pos < e:
            return True
    return False

# Let's search for paragraphs or sentences outside envs
# First, let's find all occurrences of \code{...}
code_matches = list(re.finditer(r'\\code\{([^}]+)\}', text))
print(f"Total \\code matches: {len(code_matches)}")

# Filter out non-lean codes and env matches
lean_code_matches = []
for m in code_matches:
    raw_code = m.group(1).replace(r'\_', '_').replace('$', '').replace("'", "'")
    if m.group(1) in NON_LEAN_CODES or raw_code in NON_LEAN_CODES:
        continue
    if in_env(m.start()):
        continue
    lean_code_matches.append((m, raw_code))

print(f"Lean code matches outside envs: {len(lean_code_matches)}")

# Also look for phrases like machine-checked, proved, formalised/formalized outside envs
keywords = [r'machine-check\w*', r'formaliz\w*', r'proved', r'proven']
kw_matches = []
for kw in keywords:
    for m in re.finditer(kw, text, re.IGNORECASE):
        if not in_env(m.start()):
            kw_matches.append(m)

print(f"Keyword matches outside envs: {len(kw_matches)}")

