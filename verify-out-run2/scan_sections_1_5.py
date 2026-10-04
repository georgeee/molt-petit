import re

with open('paper/molt.tex') as f:
    lines = f.readlines()

for idx, line in enumerate(lines[:644], 1):
    if any(k in line for k in ['\\code{', 'machine-check', 'proved', 'formal']):
        print(f"L{idx}: {line.rstrip()}")
