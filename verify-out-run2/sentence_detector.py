import re

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

# We want to identify sentences. In LaTeX, paragraphs are separated by \n\s*\n or section headings.
# Inside a paragraph, sentences end at '.' followed by whitespace or newline or closing parenthesis, but not abbreviations like e.g., i.e., vs., Fig., etc.

# Let's find all theorem environments first
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    rng = get_line_range(m.start(), m.end() - 1)
    theorems.append({
        'kind': 'theorem',
        'lines': rng,
        'span': (m.start(), m.end()),
        'text': m.group(0).strip()
    })

NON_LEAN_CODES = {
    '128s', 'typewriter', 'lake build', 'moltPetit.ts', 'rust/src/lib.rs',
    'nix flake check', 'tools/thales-reemission/', 'Molt', 'Molt/', 'Molt/Axioms.lean',
    '\\#print axioms'
}

# Let's inspect where \code{...} appears outside theorem spans
# Also inspect where machine-check, formaliz, proved appear
