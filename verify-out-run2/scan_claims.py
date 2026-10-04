import re

with open('paper/molt.tex') as f:
    text = f.read()
lines = text.splitlines()

code_hits = []
for i, line in enumerate(lines, 1):
    for m in re.finditer(r'\\code\{([^}]+)\}', line):
        code_hits.append((i, m.group(1), line))

print(f'Total code hits: {len(code_hits)}')
unique_codes = sorted(list(set(c[1] for c in code_hits)))
print(f'Unique codes: {len(unique_codes)}')
for c in unique_codes:
    print('  ', repr(c))
