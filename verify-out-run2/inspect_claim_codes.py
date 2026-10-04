import json

with open('verify-out/claims-draft.json') as f:
    claims = json.load(f)

no_codes = []
all_codes = set()
for c in claims:
    codes = [x.replace(r'\_', '_').replace('$', '').strip() for x in c.get('raw_codes', [])]
    if not codes:
        no_codes.append(c)
    else:
        for x in codes:
            all_codes.add(x)

print(f"Total claims without raw_codes: {len(no_codes)}")
for c in no_codes:
    print(c['id'], c['tex_lines'], c['tex_statement'][:100].replace('\n', ' '))

print(f"\nTotal unique codes across all claims: {len(all_codes)}")
print(sorted(all_codes))
