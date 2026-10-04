with open('verify-out/Stmts.lean') as f:
    text = f.read()

import re
m = re.search(r'validSignedChainK.*', text)
print(m.group(0) if m else "Not found")

with open('verify-out/lean-statements.txt') as f:
    out = f.read()

for line in out.splitlines():
    if 'validSignedChainK' in line:
        print(line)
