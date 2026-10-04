import re
import json

with open('paper/molt.tex') as f:
    tex = f.read()

pat = r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}'
envs = list(re.finditer(pat, tex, re.DOTALL))
print(f'Total envs: {len(envs)}')
for e in envs:
    kind = e.group(1)
    lbl = re.search(r'\\label\{([^}]+)\}', e.group(0))
    lbl_text = lbl.group(1) if lbl else 'no-label'
    print(f'{kind}: {lbl_text}')
