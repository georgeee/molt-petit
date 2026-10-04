import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

print(f"Total claims: {len(claims)}")
for c in claims:
    cid = c['id']
    kind = c['kind']
    lines = c['tex_lines']
    codes = c.get('raw_codes', [])
    preview = c['tex_statement'].replace('\n', ' ')[:90]
    print(f"{cid:<5} | {kind:<8} | L{lines[0]:<4}-{lines[1]:<4} | codes={len(codes):<2} | {preview}...")
