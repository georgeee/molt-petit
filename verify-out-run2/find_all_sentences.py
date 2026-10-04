import re

with open('paper/molt.tex') as f:
    text = f.read()

lines = text.splitlines()

# Precompute line offsets
line_offsets = []
offset = 0
for line in lines:
    line_offsets.append(offset)
    offset += len(line) + 1 # + '\n'

def get_line_range(start_idx, end_idx):
    import bisect
    start_line = bisect.bisect_right(line_offsets, start_idx)
    end_line = bisect.bisect_right(line_offsets, end_idx)
    return start_line, end_line

# Find all theorem environments
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    s_line, e_line = get_line_range(m.start(), m.end() - 1)
    theorems.append({
        'kind': m.group(1),
        'start_pos': m.start(),
        'end_pos': m.end(),
        'lines': [s_line, e_line],
        'text': m.group(0).strip()
    })

print(f"Theorems count: {len(theorems)}")

