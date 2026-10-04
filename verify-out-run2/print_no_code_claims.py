import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

for c in claims:
    if not c.get('raw_codes'):
        print(f"=== {c['id']} L{c['tex_lines']} ===")
        print(c['tex_statement'])
