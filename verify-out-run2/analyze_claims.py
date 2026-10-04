import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

for i, c in enumerate(claims):
    raw_codes = [x.replace(r'\_', '_').replace('$', '').strip() for x in c.get('raw_codes', [])]
    print(f"{c['id']}: kind={c['kind']} lines={c['tex_lines']} raw_codes={raw_codes}")
