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

# 1. Theorems
theorems = []
for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}', text, re.DOTALL):
    rng = get_line_range(m.start(), m.end() - 1)
    theorems.append({
        'kind': 'theorem',
        'span': (m.start(), m.end()),
        'tex_lines': rng,
        'tex_statement': m.group(0).strip()
    })

def in_thm(pos):
    return any(s <= pos < e for th in theorems for s, e in [th['span']])

# Sentence splitting inside paragraphs
def split_sentences(text_block, base_offset):
    sentences = []
    curr_start = 0
    in_math = False
    i = 0
    n = len(text_block)
    while i < n:
        c = text_block[i]
        if c == '$':
            in_math = not in_math
        elif not in_math and c in '.?!':
            j = i + 1
            while j < n and text_block[j] in ')"\' \t\n':
                if text_block[j] in '\n' or (j > i + 1 and text_block[j-1] in ')"\''):
                    break
                j += 1
            pre = text_block[curr_start:i+1].strip()
            if re.search(r'\b(e\.g|i\.e|cf|vs|Fig|Tab|al)\.$', pre):
                i += 1
                continue
            k = j
            while k < n and text_block[k] in ' \t\n':
                k += 1
            if k < n and text_block[k].islower() and not text_block[curr_start:i+1].strip().endswith('...'):
                i += 1
                continue
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

# Find all candidate sentences
para_iter = re.finditer(r'([^\n]+(?:\n[^\n]+)*)', text)
claims = []

# First collect all theorems
for th in theorems:
    claims.append(th)

# Now collect prose claims
for pm in para_iter:
    p_start = pm.start()
    p_end = pm.end()
    p_text = pm.group(0)
    
    if in_thm(p_start):
        continue
    
    sents = split_sentences(p_text, p_start)
    for s_start, s_end, s_text in sents:
        # Ignore comments
        clean_lines = [l for l in s_text.splitlines() if not l.strip().startswith('%')]
        if not clean_lines:
            continue
        clean_s_text = "\n".join(clean_lines).strip()
        # Find lean codes
        codes = [c for c in re.findall(r'\\code\{([^}]+)\}', clean_s_text) if c not in NON_LEAN and c.replace(r'\_', '_') not in NON_LEAN]
        # Ignore table fragments or pure punctuation
        if clean_s_text.startswith(r'\begin{table}') or clean_s_text.startswith(r'\begin{figure}'):
            continue
        if clean_s_text.startswith(r'\title') or clean_s_text.startswith(r'\noindent{\LARGE'):
            continue
        if 'Names in \\code{typewriter}' in clean_s_text or 'Machine-checked claims cite their Lean names' in clean_s_text:
            continue
        has_kw = bool(re.search(r'\b(machine-check\w*|formaliz\w*|proved|proven)\b', clean_s_text, re.I))
        if codes or has_kw:
            rng = get_line_range(s_start, s_end - 1)
            claims.append({
                'kind': 'prose',
                'span': (s_start, s_end),
                'tex_lines': rng,
                'tex_statement': clean_s_text,
                'raw_codes': codes,
                'has_kw': has_kw
            })

# Sort claims by appearance in text
claims.sort(key=lambda c: c['span'][0])

print(f"Total claims identified: {len(claims)}")
