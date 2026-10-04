import re
import json

with open('paper/molt.tex') as f:
    text = f.read()

lines = text.splitlines()

line_offsets = []
offset = 0
for line in lines:
    line_offsets.append(offset)
    offset += len(line) + 1

def get_line_range(start_idx, end_idx):
    import bisect
    start_line = bisect.bisect_right(line_offsets, start_idx)
    end_line = bisect.bisect_right(line_offsets, end_idx)
    return [start_line, end_line]

NON_LEAN = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# 1. Find all theorem environments
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    rng = get_line_range(m.start(), m.end() - 1)
    theorems.append({
        'kind': m.group(1),
        'span': (m.start(), m.end()),
        'tex_lines': rng,
        'tex_statement': m.group(0).strip()
    })

# 2. Prose sentences outside theorem environments
# Let's split text outside theorem environments into paragraphs
# Then split paragraphs into sentences
# A sentence is candidate if:
#   - it cites a Lean name (via \code{...} not in NON_LEAN)
#   - OR it asserts something is proved, machine-checked, or formalised

