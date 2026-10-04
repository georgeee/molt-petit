import os
import re

molt_dir = "Molt"
lean_files = [os.path.join(molt_dir, f) for f in os.listdir(molt_dir) if f.endswith(".lean")]

aliases = {}
for path in sorted(lean_files):
    with open(path) as f:
        content = f.read()
    
    # find abbrev X := Y
    for m in re.finditer(r'abbrev\s+([A-Za-z0-9_\'\.]+)\s*:=\s*([A-Za-z0-9_\'\.]+)', content):
        aliases[m.group(1)] = m.group(2)
        aliases[f"Molt.{m.group(1)}"] = m.group(2)
    
    # find alias X := Y
    for m in re.finditer(r'alias\s+([A-Za-z0-9_\'\.]+)\s*:=\s*([A-Za-z0-9_\'\.]+)', content):
        aliases[m.group(1)] = m.group(2)
        aliases[f"Molt.{m.group(1)}"] = m.group(2)
        
    # find def/theorem comments like: Transported from `MoltPetit.Model.XYZ`
    for m in re.finditer(r'(?:Transported from|←)\s*`?([A-Za-z0-9_\'\.]+)`?.*?(?:theorem|def)\s+([A-Za-z0-9_\'\.]+)', content, re.DOTALL):
        underlying = m.group(1)
        name = m.group(2)
        aliases[name] = underlying
        aliases[f"Molt.{name}"] = underlying

    # also def X = Y := rfl or similar
    for m in re.finditer(r'theorem\s+([A-Za-z0-9_\'\.]+)_eq_core\s*:\s*([A-Za-z0-9_\'\.]+)\s*=\s*([A-Za-z0-9_\'\.]+)\s*:=\s*rfl', content):
        aliases[m.group(2)] = m.group(3)
        aliases[f"Molt.{m.group(2)}"] = m.group(3)

print(f"Total resolved mappings: {len(aliases)}")
for k, v in sorted(aliases.items())[:30]:
    print(f"{k} -> {v}")
