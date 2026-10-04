with open('verify-out/Stmts.lean') as f:
    text = f.read()

# 1. MoltPetit.Model.FaultBounded -> MoltPetit.Model.ByzantineBounded
text = text.replace(
"""-- DECL: MoltPetit.Model.FaultBounded
#check @MoltPetit.Model.FaultBounded
#print axioms MoltPetit.Model.FaultBounded""",
"""-- DECL: MoltPetit.Model.ByzantineBounded
#check @MoltPetit.Model.ByzantineBounded
#print axioms MoltPetit.Model.ByzantineBounded"""
)

# 2. MoltPetit.Model.deep_block_span
text = text.replace(
"""-- DECL: MoltPetit.Model.deep_block_span
#check @MoltPetit.Model.deep_block_span
#print axioms MoltPetit.Model.deep_block_span\n""",
""
)

# 3. MoltPetit.Model.recent_tip_ancestor_mem -> MoltPetit.Model.keyrot_recent_tip_ancestor_mem
text = text.replace(
"""-- DECL: MoltPetit.Model.recent_tip_ancestor_mem
#check @MoltPetit.Model.recent_tip_ancestor_mem
#print axioms MoltPetit.Model.recent_tip_ancestor_mem""",
"""-- DECL: MoltPetit.Model.keyrot_recent_tip_ancestor_mem
#check @MoltPetit.Model.keyrot_recent_tip_ancestor_mem
#print axioms MoltPetit.Model.keyrot_recent_tip_ancestor_mem"""
)

# 4. MoltPetit.Model.validSignedChainK -> MoltPetit.Model.validSignedChainK'
text = text.replace(
"""-- DECL: MoltPetit.Model.validSignedChainK
#check @MoltPetit.Model.validSignedChainK
#print axioms MoltPetit.Model.validSignedChainK""",
"""-- DECL: MoltPetit.Model.validSignedChainK'
#check @MoltPetit.Model.validSignedChainK'
#print axioms MoltPetit.Model.validSignedChainK'"""
)

# 5. Add MoltPetit.Model.groundedCert_history and MoltPetit.Model.ts_recent_tip_ancestor_mem
extra = """
-- DECL: MoltPetit.Model.groundedCert_history
#check @MoltPetit.Model.groundedCert_history
#print axioms MoltPetit.Model.groundedCert_history

-- DECL: MoltPetit.Model.ts_recent_tip_ancestor_mem
#check @MoltPetit.Model.ts_recent_tip_ancestor_mem
#print axioms MoltPetit.Model.ts_recent_tip_ancestor_mem
"""

if "MoltPetit.Model.groundedCert_history" not in text:
    text = text.strip() + "\n" + extra

with open('verify-out/Stmts.lean', 'w') as f:
    f.write(text)

print("Updated verify-out/Stmts.lean successfully!")
