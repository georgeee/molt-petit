import re

with open('paper/molt.tex') as f:
    lines = f.readlines()

# Let's inspect the entire text line by line.
# 1. Theorem environments
envs = []
env_pattern = re.compile(r'\\begin\{(theorem|lemma|proposition|corollary)\}')
end_env_pattern = re.compile(r'\\end\{(theorem|lemma|proposition|corollary)\}')

i = 0
while i < len(lines):
    line = lines[i]
    m = env_pattern.search(line)
    if m:
        start_line = i + 1
        kind = m.group(1)
        # find matching end
        j = i
        while j < len(lines) and not end_env_pattern.search(lines[j]):
            j += 1
        end_line = j + 1
        content = "".join(lines[i:j+1])
        envs.append({
            'kind': kind,
            'start_line': start_line,
            'end_line': end_line,
            'text': content.strip()
        })
        i = j
    i += 1

print(f"Found {len(envs)} theorem-like environments:")
for e in envs:
    print(f"L{e['start_line']}-{e['end_line']} ({e['kind']}): {e['text'][:60]}...")

