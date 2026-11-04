module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Complete local rings as inverse limits of their adic truncations

Let `(R, 𝔪)` be a local ring. The Stacks project calls `R` a *complete local ring* when the
canonical map
`R ⟶ lim_n R / 𝔪ⁿ`
to the `𝔪`-adic completion of `R` is an isomorphism, where the limit is taken over the tower of
truncation maps `R / 𝔪ⁿ → R / 𝔪ᵏ` for `k ≤ n`. A footnote stresses that this is *more* than
being able to lift compatible families: it also demands `⋂ₙ 𝔪ⁿ = (0)`, i.e. that `R` be
separated, which some texts spell out by saying that `R` is "complete and separated".

This library expresses that notion as Mathlib's `IsAdicComplete (IsLocalRing.maximalIdeal R) R`,
which is how every downstream result in the Cohen structure theorem section states its
completeness hypothesis. `IsAdicComplete` is, by definition, the conjunction of `IsHausdorff`
(the footnote's separatedness) and `IsPrecomplete` (convergence of Cauchy sequences), so it is
not visibly the source's condition on a map into an inverse limit. This module supplies the
bridge in elementary terms.

## Main results

* `IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq`:
  for a local ring `R`, `IsAdicComplete (maximalIdeal R) R` holds if and only if every
  compatible family `f : (n : ℕ) → R ⧸ 𝔪ⁿ` — compatible meaning that
  `Ideal.Quotient.factor` carries `f n` to `f k` whenever `k ≤ n` — is induced by a *unique*
  element of `R`. Existence of such an element says the canonical map `R → lim_n R / 𝔪ⁿ` is
  surjective, uniqueness says it is injective, and the two together say it is bijective, hence
  (being a ring map) an isomorphism. This is the Stacks definition of a complete local ring,
  footnote included: the uniqueness clause applied to the zero family is exactly
  `⋂ₙ 𝔪ⁿ = (0)`.

## Implementation notes

The inverse limit is not named as an object. Spelling the conclusion as `∃!` says precisely that
the canonical ring map `R → lim_n R / 𝔪ⁿ` is a bijection onto the limit, while keeping the
statement in terms of `Ideal.Quotient.mk` and `Ideal.Quotient.factor` — the truncations and
transition maps the source writes down — rather than in terms of any particular construction of
the limit. In particular it is independent of Mathlib's `AdicCompletion`, whose underlying type
is a subtype of `∀ n, R ⧸ (𝔪ⁿ • ⊤)` with the submodule, not the ideal, spelling of the
truncations; `AdicCompletion.of_bijective_iff` is the corresponding statement for that model and
is not used here.

The proof passes through the definition of `IsAdicComplete` directly. Going right, a compatible
family is lifted to a Cauchy sequence of representatives, `IsPrecomplete.prec` produces a limit,
and `IsHausdorff.haus` makes it unique. Going left, separatedness is the uniqueness clause for
the zero family and precompleteness is existence for the family of truncations of a Cauchy
sequence. The one translation needed throughout is `(J • ⊤ : Submodule R R) = J` for an ideal
`J`, which turns `SModEq` modulo `𝔪ⁿ • ⊤` into equality of residues modulo `𝔪ⁿ`.

## No `@[stacks 0323]` of its own

Tag 0323 is the label of the `\section{The Cohen structure theorem}` heading, not of a
statement. It is carried here alongside 0324 with a clause recording that, and recording where
the section's twelve labelled items actually live; see the attribute below.
-/

@[expose] public section

universe u

open IsLocalRing

/-- **A local ring is complete exactly when it is the inverse limit of its adic truncations.**

Let `(R, 𝔪)` be a local ring. Then `R` is `𝔪`-adically complete if and only if for every
family `f` of residues `f n : R ⧸ 𝔪ⁿ` that is compatible with the truncation maps
`R ⧸ 𝔪ⁿ → R ⧸ 𝔪ᵏ` for `k ≤ n`, there is a *unique* `r : R` whose residue modulo `𝔪ⁿ` is
`f n` for every `n`.

This is the Stacks project's definition of a complete local ring: a compatible family is an
element of `lim_n R / 𝔪ⁿ`, existence of `r` says the canonical map `R → lim_n R / 𝔪ⁿ` is
surjective, and uniqueness says it is injective, so the two together say that this ring map is
an isomorphism. Uniqueness for the zero family is the separatedness `⋂ₙ 𝔪ⁿ = (0)` that the
source's footnote insists on; it corresponds to the `IsHausdorff` half of `IsAdicComplete`,
while existence corresponds to the `IsPrecomplete` half. -/
@[stacks 0324 "The source defines `(R, 𝔪)` to be a *complete local ring* when the canonical map \
`R ⟶ lim_n R / 𝔪ⁿ` is an isomorphism. This library has no definition of its own for that: \
completeness of a local ring is spelled `IsAdicComplete (IsLocalRing.maximalIdeal R) R` \
everywhere downstream (for instance in 032A, 032D and 0C0S), and introducing a second name for \
it would shadow canonical Mathlib API. So the definition is carried as the CHARACTERIZATION \
theorem that identifies the library's spelling with the source's: `IsAdicComplete` holds iff \
every compatible family of residues modulo `𝔪ⁿ` comes from a unique element of `R`, i.e. iff \
the canonical ring map into the inverse limit is bijective, hence an isomorphism. `lim_n R/𝔪ⁿ` \
is not named as an object; it is spelled by its universal property, with the source's own \
truncations `Ideal.Quotient.mk (𝔪ⁿ)` and transition maps `Ideal.Quotient.factor`, so the \
statement does not depend on a model of the limit. The source's footnote — that this includes \
`⋂ 𝔪ⁿ = (0)`, `R` complete AND separated — is the uniqueness half of the `∃!`, applied to the \
zero family; it matches the `IsHausdorff` component of `IsAdicComplete`, existence matching \
`IsPrecomplete`. The footnote's three cross-references (05JC, 05GG, 05GH) are remarks on when \
the completion is itself complete and Noetherian; they are separate tags and are not claimed \
here.",
  stacks 0323 "0323 is the label of the heading `\\section{The Cohen structure theorem}`, not of \
a mathematical statement: it has no hypotheses and no conclusion, so NO single theorem can be a \
faithful formalization of it, and this attribute is placed under the project's rule that a tag \
which is not a statement as written is carried in corrected form with the correction recorded. \
The correction: 0323 is carried here, on the section's OPENING NOTION — the section begins \
`Here is a fundamental notion in commutative algebra` and then states Definition 0324, the \
definition of a complete local ring, which is what this declaration characterizes — and the \
section's remaining eleven labelled items are carried at their own tags elsewhere in this \
library, not here. Namely: 032A, the Cohen structure theorem itself, on \
`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries` in \
`StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem`; 032D on \
`IsLocalRing.exists_injective_finite_mvPowerSeries` in the same module; 0C0S, the power series \
description of a regular complete local ring, on \
`IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries` in \
`StacksFrontier.RingTheory.CompleteLocalRing.Regular`; 0325 on \
`quotient_isNoetherianCompleteLocalRing` and `finite_isProduct_isNoetherianCompleteLocalRing`, \
and 032B on `complete_local_ring_noetherian`, all in \
`StacksFrontier.RingTheory.CompleteLocalRing.Noetherian`; 0326 on \
`LocalSubring.IsCoefficientRing` in \
`StacksFrontier.RingTheory.CompleteLocalRing.CoefficientRing`; 0327 on the class `IsCohenRing`, \
0328 on `IsCohenRing.exists_residueField_ringEquiv` and 0329 on \
`IsCohenRing.formallySmooth_quotient_span_pow`, all in `StacksFrontier.RingTheory.CohenRing`; and \
032C on `isUniversallyCatenary_of_isPrecomplete_maximalIdeal` in \
`StacksFrontier.RingTheory.Catenary.Formal`. With 0324 carried here, every labelled item of the \
section now has a carrier and only the heading itself had none."]
theorem IsLocalRing.isAdicComplete_maximalIdeal_iff_forall_compatible_existsUnique_mk_eq
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsAdicComplete (maximalIdeal R) R ↔
      ∀ f : (n : ℕ) → R ⧸ maximalIdeal R ^ n,
        (∀ (k n : ℕ) (h : k ≤ n),
            Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (f n) = f k) →
          ∃! r : R, ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) r = f n := by
  have key : ∀ (J : Ideal R) (x y : R),
      (x ≡ y [SMOD (J • ⊤ : Submodule R R)]) ↔
        Ideal.Quotient.mk J x = Ideal.Quotient.mk J y := by
    intro J x y
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.Quotient.eq]
  constructor
  · intro hc f hf
    choose x hx using fun n : ℕ =>
      Ideal.Quotient.mk_surjective (I := maximalIdeal R ^ n) (f n)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hc.toIsPrecomplete fun {k n} h => by
      rw [key, hx k, ← hf k n h, ← hx n, Ideal.Quotient.factor_mk]
    have hLmk : ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) L = f n := fun n => by
      rw [← hx n, ← (key _ _ _).mp (hL n)]
    refine ⟨L, hLmk, fun r hr => sub_eq_zero.mp <| hc.haus _ fun n => ?_⟩
    rw [key, map_sub, hr n, hLmk n, sub_self, map_zero]
  · intro H
    refine { toIsHausdorff := ⟨fun y hy => ?_⟩, toIsPrecomplete := ⟨fun g hg => ?_⟩ }
    · obtain ⟨r, -, huniq⟩ := H (fun _ => 0) (fun _ _ _ => by simp)
      exact (huniq y fun n => by simpa using (key _ _ _).mp (hy n)).trans
        (huniq 0 fun _ => by simp).symm
    · obtain ⟨L, hL, -⟩ := H (fun n => Ideal.Quotient.mk (maximalIdeal R ^ n) (g n))
        fun k n h => by
          rw [Ideal.Quotient.factor_mk]
          exact ((key _ _ _).mp (hg h)).symm
      exact ⟨L, fun n => (key _ _ _).mpr (hL n).symm⟩

end
