import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

for c in claims:
    if c['kind'] != 'prose':
        print(f"=== {c['id']} {c['kind']} L{c['tex_lines']} ===")
        print(c['tex_statement'][:150])
        print("...")
