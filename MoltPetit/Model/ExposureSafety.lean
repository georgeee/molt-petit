import MoltPetit.Model.Definitions

/-!
# Light-client safety under arbitrary-time key exposure

The core theorem of the timed model. Keys may be exposed (Byzantine seats,
stolen keys) at arbitrary real times and sign arbitrary stamps; honest
producers' clocks may run up to `σ` slots ahead. If at most `maxByzantine n`
seats are exposed in any window of `Λ` real slots, two quorum-dense chains
that are fresh (their tips within `ρ` slots of the real time `R` at which every
one of their blocks exists) agree at every height at least `n` below both tips.

The guard band: the budget window must cover `2n + ρ` slots, plus any producer
skew beyond `quorum n - maxByzantine n - 1`.

THE STATEMENT OF `exposure_agreement` IS FIXED. Its exact type is pinned by
`Molt/AxiomsExposureSafety.lean`. Prove it; do not change it.
See `docs/CORE_V2_SPEC.md` for the proof plan.
-/

namespace MoltPetit.Model

theorem exposure_agreement {n σ ρ Λ : Nat} (hn : 1 ≤ n)
    {exposed : Exposure} {log : TimedLog} {G : Block}
    (hexec : SigningExecution n σ exposed log G)
    (hBudget : ExposureBounded n Λ exposed)
    (hΛ : 2 * n + ρ + (maxByzantine n + σ + 1 - quorum n) ≤ Λ)
    {c c' : Chain} (hc : ValidChain n c) (hc' : ValidChain n c')
    (hHead : blockAt? c 0 = some G) (hHead' : blockAt? c' 0 = some G)
    {R : Nat}
    (hAvail : ∀ B ∈ c, AvailableAt log G B R)
    (hAvail' : ∀ B ∈ c', AvailableAt log G B R)
    {tip tip' : Block}
    (hTip : c.getLast? = some tip) (hTip' : c'.getLast? = some tip')
    (hRecent : R ≤ tip.slot + ρ) (hRecent' : R ≤ tip'.slot + ρ)
    {h : Nat} (hDeep : h + n < c.length) (hDeep' : h + n < c'.length) :
    blockAt? c h = blockAt? c' h := by
  sorry

end MoltPetit.Model
