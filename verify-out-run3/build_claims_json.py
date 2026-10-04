import re
import json

with open('verify-out/Stmts.lean') as f:
    decls = [l.strip()[len('-- DECL: '):] for l in f if l.startswith('-- DECL: ')]

with open('verify-out/lean-statements.txt') as f:
    text = f.read()

decl_data = {}
for i, d in enumerate(decls):
    pat = re.compile(rf"^{re.escape(d)} :|^@{re.escape(d)} :", re.MULTILINE)
    m_check = pat.search(text)
    if not m_check:
        raise ValueError(f"Failed to find check for {d}")
    
    pat_ax = re.compile(rf"^'{re.escape(d)}'\s+(does not depend on any axioms|depends on axioms:\s*\[(.*?)\])$", re.MULTILINE)
    m_ax = pat_ax.search(text, m_check.start())
    if not m_ax:
        raise ValueError(f"Failed to find axioms for {d}")
    
    check_str = text[m_check.start():m_ax.start()].strip()
    dep_type = m_ax.group(1)
    axioms_raw = m_ax.group(2)
    if axioms_raw:
        axioms = sorted(list(set(a.strip() for a in axioms_raw.split(',') if a.strip())))
    else:
        axioms = []
    
    decl_data[d] = {
        'check': check_str,
        'axioms': axioms
    }

with open('verify-out/claims-draft.json') as f:
    draft_claims = json.load(f)

final_claims = []
for c in draft_claims:
    cid = c['id']
    kind = c['kind']
    tex_lines = c['tex_lines']
    tex_statement = c['tex_statement']
    lean_decls = c.get('lean_decls', [])
    lean_resolved = c.get('lean_resolved', [])
    notes = c.get('notes', '')

    stmts = []
    all_axioms = set()
    for d in lean_decls:
        if d in decl_data:
            stmts.append(decl_data[d]['check'])
            for a in decl_data[d]['axioms']:
                all_axioms.add(a)
        else:
            print(f"Warning: decl {d} not in decl_data")
    
    lean_statement = "\n\n".join(stmts)
    axioms = sorted(list(all_axioms))

    final_claims.append({
        'id': cid,
        'kind': kind,
        'tex_lines': tex_lines,
        'tex_statement': tex_statement,
        'lean_decls': lean_decls,
        'lean_resolved': lean_resolved,
        'lean_statement': lean_statement,
        'axioms': axioms,
        'notes': notes
    })

with open('verify-out/claims.json', 'w') as f:
    json.dump(final_claims, f, indent=2)

print(f"Successfully generated verify-out/claims.json with {len(final_claims)} claims.")
