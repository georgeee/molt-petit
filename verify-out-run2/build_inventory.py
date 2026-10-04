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

# Collect theorem environments
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    rng = get_line_range(m.start(), m.end() - 1)
    theorems.append({
        'kind': m.group(1),
        'span': (m.start(), m.end()),
        'tex_lines': rng,
        'tex_statement': m.group(0).strip()
    })

def in_thm(pos):
    return any(s <= pos < e for th in theorems for s, e in [th['span']])

# Sentence splitting function within a text block
def split_into_sentences(text_block, base_offset):
    # Regex for sentence boundaries:
    # A sentence ends with . or ? or ! followed by space or newline or end of block,
    # but not abbreviations like e.g., i.e., cf., vs., \etal.
    # Also ignore '.' inside math $...$
    
    # We can walk through text_block
    sentences = []
    curr_start = 0
    in_math = False
    in_code = False
    i = 0
    n = len(text_block)
    while i < n:
        c = text_block[i]
        if c == '$':
            in_math = not in_math
        elif c == '\\' and i + 1 < n and text_block[i:i+6] == r'\code{':
            pass
        elif not in_math and c in '.?!':
            # Check if this is truly end of sentence
            # Look ahead: followed by whitespace/newline or closing parenthesis/quote then whitespace/end
            j = i + 1
            while j < n and text_block[j] in ')"\' \t\n':
                if text_block[j] in '\n' or (j > i + 1 and text_block[j-1] in ')"\''):
                    break
                j += 1
            # Check abbreviation: e.g., i.e., vs., Fig., etc.
            pre = text_block[curr_start:i+1].strip()
            # If not end of block and looks like abbreviation, don't split
            if re.search(r'\b(e\.g|i\.e|cf|vs|Fig|Tab|al)\.$', pre):
                i += 1
                continue
            # Also check if followed by lowercase letter
            k = j
            while k < n and text_block[k] in ' \t\n':
                k += 1
            if k < n and text_block[k].islower() and not text_block[curr_start:i+1].strip().endswith('...'):
                i += 1
                continue
            # Valid sentence end
            s_text = text_block[curr_start:j].strip()
            if s_text:
                sentences.append((base_offset + curr_start, base_offset + j, s_text))
            curr_start = j
            i = j - 1
        i += 1
    if curr_start < n:
        s_text = text_block[curr_start:].strip()
        if s_text:
            sentences.append((base_offset + curr_start, base_offset + n, s_text))
    return sentences

# Now parse all paragraphs
para_iter = re.finditer(r'([^\n]+(?:\n[^\n]+)*)', text)
all_candidates = []

for th in theorems:
    all_candidates.append(th)

for pm in para_iter:
    p_start = pm.start()
    p_end = pm.end()
    p_text = pm.group(0)
    
    # Check if inside theorem
    if in_thm(p_start):
        continue
    
    # Split paragraph into sentences
    sents = split_into_sentences(p_text, p_start)
    for s_start, s_end, s_text in sents:
        # Check if sentence cites a lean code or asserts machine-checked / proved / formalised
        codes = [c for c in re.findall(r'\\code\{([^}]+)\}', s_text) if c not in NON_LEAN and c.replace(r'\_', '_') not in NON_LEAN]
        # Ignore comments
        clean_lines = [l for l in s_text.splitlines() if not l.strip().startswith('%')]
        if not clean_lines:
            continue
        clean_s_text = "\n".join(clean_lines).strip()
        has_kw = bool(re.search(r'\b(machine-check\w*|formaliz\w*|proved|proven)\b', clean_s_text, re.I))
        if codes or has_kw:
            rng = get_line_range(s_start, s_end - 1)
            all_candidates.append({
                'kind': 'prose',
                'span': (s_start, s_end),
                'tex_lines': rng,
                'tex_statement': clean_s_text,
                'codes': codes,
                'has_kw': has_kw
            })

# Sort all by start pos
all_candidates.sort(key=lambda c: c['span'][0])

print(f"Total candidate claims found: {len(all_candidates)}")
for idx, c in enumerate(all_candidates[:15], 1):
    print(f"C{idx} [{c['kind']}] L{c['tex_lines']}: {c['tex_statement'][:80]}...")
