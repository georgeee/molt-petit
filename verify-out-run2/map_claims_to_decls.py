import json
import re

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

# Let's inspect each claim and its symbols
for c in claims:
    cid = c['id']
    tex = c['tex_statement']
    codes = [x.replace(r'\_', '_').replace('$', '').strip() for x in c.get('raw_codes', [])]
    print(f"{cid}: codes={codes}")
