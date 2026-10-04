import re

with open('verify-out/lean-statements.txt') as f:
    text = f.read()

axiom_pat = re.compile(r"^'(.+?)'\s+(does not depend on any axioms|depends on axioms:\s*\[(.*?)\])$", re.MULTILINE)

matches = list(axiom_pat.finditer(text))
print(f"Matches with non-greedy quote: {len(matches)}")
for m in matches:
    if 'validSignedChainK' in m.group(1):
        print("Found:", m.group(1), m.group(2))
