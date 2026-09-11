# Proposed wording for `paper/molt.tex` — NOT applied

Companion to `docs/rollout/ROLLOUT_NOTES.md` §1 (the ledger of paper changes each landed Lean
item unlocks). The paper is untouched; this file is the proposal, one entry per
ledger row, in the order the text appears in the paper. Each entry gives the
location (a grep phrase — line numbers drift), the current text, the proposed
text, the Lean names it cites, and — where a sentence could be written that the
Lean does not support — what not to say. Every Lean name below is axiom-guarded
and built as of commit `14d2d11` plus this pass.

Conventions: `\code{}` for Lean names, `$\fmax$` for the fault budget, as in the
paper. Proposed text is written to drop in, but it is a proposal: wording is
yours to change; the hypothesis caveats are the part to keep.

---

## 0. Two corrections to the annotation-round edits themselves

These are not rollout items; they came out of reading the 2026-09-04 edits
against the Lean.

**0a. "then-live key" undercounts the census.** Two places, §6.3 mode 1:

- Theorem~\ref{thm:refresh}'s one-sentence form (grep `theft of a then-live key`):
  > … rented slots plus producers suffering a theft of a then-live key total at most $\fmax$ per window.
- The deployment walkthrough (grep `suffer a theft of a then-live`):
  > … at most $T$ of the seven seats suffer a theft of a then-live key …

The Lean predicate (`badKeyrot`, `badKeyrotOn`) charges a slot when *some
version at or above the one in force there* is stolen — `∃ j, inForce … ≤ j ∧
Stolen i j` — so a theft of a *later, not-yet-used* version counts too, not only
the version live at that slot. "Then-live" reads as exactly the in-force version.
Proposed, both places:

> … producers with a stolen key not yet retired there — their version in force, or any later one — …

The longer paragraph two pages on ("The model carries no theft times, so the census
at a window counts every producer whose version in force there is ever stolen and
not yet retired by then") has the same ambiguity in "whose version in force
there"; "any of whose versions not yet retired there is ever stolen" is exact.

**0b. AN/15 removed the paper's only disclosure that the representability lemmas
are production-side only.** Theorem~\ref{thm:lc}'s "exposes that height" paragraph
now ends at "so a holder can re-expose as many blocks as a comparison needs" with
no stated reason for the hypothesis staying in the statement. Already carried in
`docs/rollout/ROLLOUT_NOTES.md` §1 as your call; re-flagged because a reviewer will ask. One
clause restores it without the old sentence's weight:

> … as a comparison needs — argued, not proved (the representability lemmas are production-side), which is why the hypothesis stays in the statement.

**0c. "clients of the other two modes obey no rule at all"** (§1, grep `obey no
rule at all`). Mode 2/3 clients still pass the recency check at every sync
(`hRecent : now ≤ tip.slot + Δ` in every theorem). Precise: "obey no *cadence*
rule at all".

---

## 1. §2, mode-3 paragraph — W1 + W5 (AN/9a, AN/9b)

Grep: `currently proved for full chains`.

Current:
> (Mode 3's guarantees are currently proved for full chains, and erasure's per-generation credit against the budget is designed but not yet formalized --- today's theorems count thefts across all generations within one budget, with or without erasure; both are future work, Section~\ref{sec:rotation}.)

Proposed:
> (Mode 3's guarantees hold at the certificate presentation as well as for full chains (\code{lockstep\_recent\_certified\_suffix\_agreement}). Erasure's per-generation credit against the budget is machine-checked: under a per-generation census --- for each generation $j$ separately, at most $T$ seats whose generation-$j$ key is stolen --- the same agreement holds at confirmation depth $2n$ instead of $n$, and with no shared-genesis hypothesis (\code{lockstep\_client\_safety\_gen}); the cumulative, depth-$n$ form remains available. Section~\ref{sec:rotation}.)

Lean: `Molt.lockstep_recent_certified_suffix_agreement`, `Molt.lockstep_client_safety_gen`,
`MoltPetit.Model.lockstepGen_recent_genesis_agreement` (genesis-freedom).

Do not say: that erasure is "credited" in the cumulative (Theorem 5) form — it is
not; only the per-generation package consumes it (entry 8).

---

## 2. §4 "Validate", item 5 — W1

Grep: `future work for mode 3`.

Current:
> at certificate level they are proved for modes 1--2 (\code{keyrot\_recent\_certified\_suffix\_agreement}, \code{sched\_recent\_certified\_suffix\_agreement}) and future work for mode 3 (see the ``honest scope'' discussion in Section~\ref{sec:rotation}).

Proposed:
> at certificate level they are proved for all three modes (\code{keyrot\_recent\_certified\_suffix\_agreement}, \code{sched\_recent\_certified\_suffix\_agreement}, \code{lockstep\_recent\_certified\_suffix\_agreement}).

---

## 3. §6 intro — W1

Grep: `and its scheduled` (the parenthetical after "each mode's certified theorem").

Current: `(\code{keyrot\_recent\_certified\_suffix\_agreement} and its scheduled twin)`
Proposed: `(\code{keyrot\_recent\_certified\_suffix\_agreement} and its scheduled and lockstep twins)`

---

## 4. §6.3 mode 1, the certificate paragraph — W2 (AN/21)

Grep: `carrying the anchored, trailing`.

Current:
> (\code{keyrot\_recent\_certified\_suffix\_agreement}, over the strengthened grounding \code{GroundedCertK}) --- but under the global, all-window budget: carrying the anchored, trailing-$5n$ form to certificates is future work.

Proposed:
> (\code{keyrot\_recent\_certified\_suffix\_agreement}, over the strengthened grounding \code{GroundedCertK}) --- and under the anchored, trailing form as well: two certificate-plus-suffix presentations that both contain the client's anchor agree $n$ deep, with the corruption budget consulted only on windows ending after the anchor, over every history the certificate could be attesting (\code{keyrot\_certified\_suffix\_agreement\_anchored}; the client rules at this presentation are \code{cert\_sync\_rule} and \code{cert\_max\_sync\_period}). So the constant-size client, not only the full-chain one, gets the two-minute budget.

Lean: `MoltPetit.Model.keyrot_certified_suffix_agreement_anchored`, `Molt.cert_client_refresh_rule`,
`Molt.cert_stay_recent_client_safe`, `Molt.cert_sync_rule`, `Molt.cert_max_sync_period`.

Keep the phrase "over every history the certificate could be attesting": the
budget hypothesis is quantified over `AttestedHistoryK` (every full chain the
certificate-plus-suffix could be the presentation of). That quantification is the
statement's honest shape and the docstring names it; do not present the budget as
chain-independent here (it is chain-independent in modes 2--3, not in mode 1).

---

## 5. §6.3 mode 1, the budget in derived form — W3a (AN/20, AN/17)

Grep: `The operator's half of the rule reads the same way`. Add after that
sentence's paragraph:

> That budget need not be assumed outright. A deployment able to name a \emph{reaction delay} $d$ --- within $d$ slots of any theft, the victim's confirmed floor has moved past the stolen version (Lean \code{Reacts}) --- may instead assume a rent rate per window and a per-window census of producers hit by a theft within $d$ slots of the window; the trailing budget then follows (\code{budget\_of\_reaction}; composed into the client rules, \code{sync\_rule\_timed}, \code{max\_sync\_period\_timed}). The reaction delay is asserted, like \emph{not-before} in mode 2, not derived.

Lean: `MoltPetit.Model.Reacts`, `MoltPetit.Model.recentTheftProducersK`,
`MoltPetit.Model.budget_of_reaction`, `Molt.client_refresh_rule_timed`,
`Molt.sync_rule_timed`, `Molt.sync_rule_mem_timed`, `Molt.max_sync_period_timed`.

Do not say that this census is non-retroactive: `recentTheftProducersK` bounds a
theft's real time from above relative to the window (`u < r + d`) but not from
below, so an old window still counts a much later theft. Non-retroactivity is
entry 6.

---

## 6. §6.3 mode 1, "a larger $F$" — W3b (AN/24, AN/29)

Grep: `could in principle support a larger`.

Current:
> A deployment prepared to assume strictly more --- honest producers never extending adversarial branches, and theft \emph{times} inside the signature assumptions, so that a stolen key is charged from the moment it is stolen rather than to every window its version was in force --- could in principle support a larger $F$; that stronger model is outside the present development (future work; honest scope below).

Proposed:
> Theft times are now inside the development, as two named operational hypotheses: the reaction delay $d$ above (\code{Reacts}), and \emph{no stolen-key back-dating} --- a stolen version cannot be used to expose a slot that predates its theft (\code{NoTheftBackdating}). Together they confine what a theft at real slot $r$ can expose to the slots $[r, r{+}d)$ (\code{theft\_exposure\_window}): a stolen key is charged from the moment it is stolen until the reaction fires, and to no earlier window. The census a deployment attests is then per window and does not grow with the stretch: for the paced adversary above it is $1$ at every window, for every sync period (\code{paced\_tight\_census\_bound\_all\_F}; composed, \code{max\_sync\_period\_tight}). That is what ``a larger $F$'' means here --- the census no longer constrains $F$; rent still has to be bounded over the same stretch. Both hypotheses are asserted, like \emph{not-before}; deriving no-back-dating from a signature primitive aware of mint times is future work, and so is a model in which honest producers never extend adversarial branches.

Lean: `MoltPetit.Model.NoTheftBackdating`, `MoltPetit.Model.theft_exposure_window`,
`MoltPetit.Model.recentTheftProducersTight`, `MoltPetit.Model.budget_of_reaction_tight`,
`Molt.max_sync_period_tight`, `Molt.paced_tight_census_bound_all_F`,
`Molt.pacedStolenAt_safe_under_tight_unsafe_under_untimed`, `Molt.paced_separation_witnessed`.

**Do not say** "there are executions the untimed budget gets wrong and the timed
one gets right." There are none: `Molt.paced_budget_holds_under_timing` proves that
under `Reacts` + `NoTheftBackdating` the paced adversary *satisfies* the old
budget too. The separation that does exist (`paced_separation_witnessed`, no
hypotheses at all) is between what the two routes ask a deployment to attest —
a per-window census of $1$ versus a per-stretch total that exceeds $\fmax$ at
the first window — not between executions. The earlier draft of the separation
theorem that asserted both timing hypotheses alongside the untimed failure was
vacuous (its hypotheses contradict for $d < n$) and has been replaced; do not cite
that shape.

---

## 7. §6.3 mode 1 walkthrough, the induction over syncs — W4 (AN/26)

Grep: `argued on paper, not` (the sentence wraps).

Current:
> Agreement with the honest chain itself follows by an induction over syncs argued on paper, not itself machine-checked. Each sync's agreement keeps the next anchor on the honest chain while the honest tip is at least as tall as the accepted one (density keeps a recent taller fork's $n$-deep block below its divergence, hence on the honest chain --- an informal argument).

Proposed:
> Agreement with the honest chain itself follows by an induction over syncs, machine-checked (\code{sync\_induction\_full\_chain}): each sync's agreement keeps the next anchor on a reference chain that grows over time, provided that chain's tip is at least as tall as the accepted one at every sync, and recent. The height comparison is a stated hypothesis of the theorem, not a conclusion --- it is what the density remark argues for informally (a recent taller fork's $n$-deep block sits below its divergence), and that remark is not itself machine-checked.

Keep the existing next sentence ("And the honest tip staying recent is a
liveness-style side condition, outside the safety hypotheses") — it is still
exactly right (`hRRecent`).

Lean: `Molt.sync_induction_full_chain`, `Molt.SyncInductionData`,
`Molt.SyncInductionData.invariant` (axiom-free).

Do not say the density argument is machine-checked. The theorem assumes `hRLe`
(reference tip at least as tall), which is the conclusion of that argument; its
docstring says so in as many words. The ledger row for AN/26 originally named
tip-recency as the side condition to keep visible; the load-bearing one is the
height comparison.

---

## 8. §6.3 mode 3, Theorem 5 and its route — W5 (AN/9b), W1

Grep: `\code{lockstep\_client\_safety}]\label{thm:lock}` for the theorem;
`The route is a machine-checked \emph{pinning} theorem` for the paragraph after it.

Leave Theorem~\ref{thm:lock} as is (it is the cumulative, depth-$n$ form and its
package really does have the monotone-counter and genesis-declares fields). Add
after its route paragraph:

> \begin{theorem}[Lockstep safety, per-generation census; Lean \code{lockstep\_client\_safety\_gen}]\label{thm:lock-gen}
> Under the lockstep validator and the per-generation package --- honest signatures declare their grid window's counter; hash injectivity; the pin-free core signature surface; rent at most $\rho$ per window and, for every generation $j$ separately, at most $T$ seats whose generation-$j$ key is stolen; $\rho + T \le \fmax$ --- any two accepted chains with recent tips agree on the block $2n$ below each tip, and, through the parent-id chain, on their whole common prefix down to height $0$: no shared genesis is assumed (\code{lockstepGen\_recent\_genesis\_agreement}).
> \end{theorem}
>
> The route is a second pinning theorem that needs neither induction nor genesis (\code{lockstep\_window\_declares\_rosterGen}): the last grid window matured below the lower tip declares one generation on both chains, so the counting argument runs on a window whose corruption reading is at a single generation (\code{window\_shared\_prefix}). The unmatured tip window cannot be used, and that is what costs depth $2n$ --- exactly $n + ((t{+}1) \bmod n)$ positions for lower tip slot $t$ (\code{lockstepGen\_shared\_prefix\_sharp}). The two packages are incomparable in general; the cumulative one delivers the per-generation one when the counter skips no generation (\code{LockstepPackage.toGen}).

Lean: `Molt.lockstep_client_safety_gen`, `Molt.LockstepPackageGen`,
`MoltPetit.Model.lockstep_window_declares_rosterGen`, `MoltPetit.Model.window_shared_prefix`,
`MoltPetit.Model.lockstepGen_shared_prefix_sharp`, `MoltPetit.Model.LockstepPackage.toGen`,
`MoltPetit.Model.lockstepGen_recent_tip_ancestor_mem` (unequal heights).

Do not carry Theorem 5's package wording into Theorem 5′: "the roster tracks one
monotone counter" and "the genesis declares the counter's initial value" are
*not* fields of the per-generation package (neither is consumed by the
non-inductive route), and listing them would overstate what it assumes.

---

## 9. §6.3 mode 3, operator duties — W5 (AN/9b)

Grep: `its budget credit: honest scope below`.

Current:
> and \emph{real erasure} of retired key material at each switch (its budget credit: honest scope below).

Proposed:
> and \emph{real erasure} of retired key material at each switch. Its budget credit is now formal: with theft time-stamped, erasure is the hypothesis that no generation is stolen after the roster has moved past it (\code{ErasureTimedLock}), and it is \emph{consumed} --- it turns the census a deployment attests while a generation is live into the per-generation census Theorem~\ref{thm:lock-gen} needs (\code{genBound\_of\_preRetirementBound}; end to end, \code{lockstep\_client\_safety\_timed}). A deployment budgets $T$ seats lost \emph{per generation, while it is live}, not $T$ across all generations. In mode 2 the erasure field is documentary and \emph{not-before} carries the count; mode 3 is the mirror image.

Lean: `MoltPetit.Model.ErasureTimedLock`, `MoltPetit.Model.NoPrematureTheftLock`,
`MoltPetit.Model.preRetirementTheftProducers`, `MoltPetit.Model.genBound_of_preRetirementBound`,
`MoltPetit.Model.LockstepPackageTimed`, `Molt.lockstep_client_safety_timed`,
`MoltPetit.Model.theft_in_era_lock` (axiom-free), the two `_iff_flagship` lemmas
(mode 2 recovered at the identity counter).

---

## 10. §6.3 mode 3, the deployment walkthrough — W1 (AN/28), W5

Grep: `verifying the full signed chain on wake`.

Current:
> Clients hold genesis and a clock, nothing else, and sleep arbitrarily long --- verifying the full signed chain on wake, since the certificate presentation is future work.

Proposed:
> Clients hold genesis and a clock, nothing else, and sleep arbitrarily long; on wake they sync from a certificate plus an $O(n)$ suffix, as in modes 1--2. The certificate carries the claim and the tip generation; for $n \ge 2$ the generation is determined by the claim's own tail (\code{groundedCertLock\_gen\_of\_tail}, \code{groundedCertLock\_gen\_unique}), so the certificate attests nothing beyond the plain claim, and only $n = 1$ needs the extra counter --- which must then be attested with the claim: an unauthenticated counter readmits a stolen retired-generation key exactly as an unauthenticated floor does in mode 1.

Then, in the same paragraph's "What must then be true of the world" list, replace
the last item:

> and \emph{either} the same $\rho$/$T$ budget as mode 2's global form, assessed at the one-grid-window-lagged counter (Theorem~\ref{thm:lock}, depth $n$), \emph{or}, at confirmation depth $2n$, rent at most $\rho$ per window and, for every generation $j$, at most $T$ seats whose generation-$j$ key is stolen while $j$ is live (Theorem~\ref{thm:lock-gen}; end to end with time-stamped theft, \code{lockstep\_client\_safety\_timed}).

And extend "Conclusion, machine-checked (…)":

> … and at the certificate presentation \code{lockstep\_recent\_certified\_suffix\_agreement}, with the certificate's own counter pinned to the roster's once its grid window matures (\code{lockstep\_cert\_gen\_pinned}) …

Lean: `MoltPetit.Model.GroundedCertLock`, `MoltPetit.Model.lockstepFrom`,
`MoltPetit.Model.groundedCertLock_gen_of_tail`, `MoltPetit.Model.groundedCertLock_gen_unique`,
`MoltPetit.Model.lockstep_cert_gen_pinned`, `MoltPetit.Model.lockstep_cert_declares_rosterGen`.

Do not say the certificate client needs *less* than in mode 2: the certificate
carries the same claim plus, for $n = 1$ only, one counter; the "attests nothing
beyond the plain claim" reading is exact for $n \ge 2$ and only then.

---

## 11. §6.3 "The modes at a glance" table — W5

Grep: `3 lockstep & roster counter, no-mixing`.

Proposed row: `3 lockstep & roster counter, no-mixing & genesis + clock & yes (credited, Thm.~\ref{thm:lock-gen}) & no \\`

And the sentence after the table, grep `Modes 1--3 share`:
> Modes 1--3 share the $\rho + T \le \fmax$ budget --- in mode 3 the $T$ may be read per generation, at depth $2n$ --- and a recency-scoped signature surface;

If a depth column is wanted: mode 1 $n$, mode 2 $n$, mode 3 $n$ (cumulative) / $2n$ (per-generation).

---

## 12. §6.3 "Honest scope" — W3a/W3b (AN/24, AN/29), W5, W1

Grep: `Three bounds on what this subsection claims`.

Current: three bounds (retroactive counting; mode 3 counts across generations;
mode 3 is full-chains-only).

Proposed:
> \paragraph{Honest scope.} Two bounds on what this subsection claims. First, in the base theorems the budget counts a key as stolen in every window where its version was not yet retired, \emph{even if the theft only happens later}. The timed layer removes this for a deployment that names a reaction delay and rules out stolen-key back-dating (\code{Reacts}, \code{NoTheftBackdating}): a theft is then charged only to the $d$ slots that follow it (\code{theft\_exposure\_window}). Both are asserted, like \emph{not-before}; deriving no-back-dating from a signature primitive aware of mint times is future work. Second, mode 3's per-generation form costs confirmation depth $2n$ --- exactly $n + ((t{+}1) \bmod n)$ --- and its census, like every census here, is future-inclusive within a generation's live span.

The third bound (certificate-level form is future work) is deleted: W1.

---

## 13. Appendix, "What no-back-dating is", and Limitations — W6 (AN/34b)

Grep (appendix): `What no-back-dating is, and why it is not free`. Add after that
paragraph:

> \emph{Why the rotation modes assume their surfaces rather than derive them.} The theorems of Section~\ref{sec:rotation} take each mode's key-stealing signature surface as a named assumption, and the timed model above does not deliver it --- not because of the deliberate refusal of no-back-dating for stolen keys, but for a structural reason: a timed custody argument certifies facts about a real \emph{slot}, while each surface is premised on a single key \emph{version} being safe, and one slot can host one safe version and one stolen one. We machine-check the mismatch as two witnesses --- a slot at which a named version is unstolen yet the slot is corrupt, because another version eligible there is stolen (\code{badSched\_single\_key\_safe\_not\_enough} for modes 2--3, \code{badKeyrotOn\_single\_key\_safe\_not\_enough} for mode 1). Closing the gap means changing the surfaces' premise from per-version to per-slot; that is an edit to an assumed structure, not an addition, and is left as such.

Grep (Limitations): `assumed, not derived from the timed model`. Proposed:
> the key-stealing signature surface (assumed, not derived from the timed model --- the appendix machine-checks why the derivation does not go through);

Lean: `MoltPetit.Model.badSched_single_key_safe_not_enough`,
`MoltPetit.Model.badKeyrotOn_single_key_safe_not_enough` (both axiom-free).

Do not say the witnesses show the timed model is *inconsistent* with the surface,
or that no-back-dating for stolen keys is being reintroduced. They show only that
per-version safety does not imply slot safety, which is the direction a
derivation would need. (The module docstring's framing sentence is loose on this
direction; the theorem docstrings are exact.)

---

## 14. §6.4 liveness — W7 (AN/31)

Grep: `a fully multi-chain network model is future work`. **Unchanged.** W7 was not
attempted; every version of its design recommends against it (`docs/rollout/ROLLOUT_PLAN.md`
item 8).

---

## Not a paper change, recorded so it is not lost

- The mode-3 module doc's "exactly $n + ((t{+}1) \bmod n)$" is now a theorem
  (`lockstepGen_shared_prefix_sharp`), so entries 8 and 12 may cite it.
- `LockstepPackage.toGen` proves cumulative ⇒ per-generation *when* the counter is
  surjective; the converse is not proved and should not be implied.
- The Assumption~\ref{ass:hash} rewrite says "ids are shorter than blocks, so
  colliding values exist in the type". True of real hashes; in the model `id` is an
  unbounded `Nat` field independent of content, so colliding values exist for the
  simpler reason that nothing ties the field to the payload. Harmless as prose
  about hashes; mentioned only so the model's reason is not misattributed.
