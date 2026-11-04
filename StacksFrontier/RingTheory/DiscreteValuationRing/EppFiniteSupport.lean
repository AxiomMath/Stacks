module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSeparableEmbedding

/-!
# Epp's condition has finite support, and that removes a finiteness hypothesis

Condition **(†)** of `EppConditionalDescent` is arranged by absorbing `separableClosure κ_A κ_B`
into the base, which has to assume that closure is **finite** over `κ_A`.  That hypothesis fails
in general: the separable closure of `κ_A` in `κ_B` can be infinite over `κ_A`.

This file removes the need for it, by observing that **Epp's condition has finite support**.  Any
construction that consumes the perfect core — a polynomial, a finite presentation, a base change
— touches only finitely many residue coefficients at a time.  So one never needs the whole
separable closure to be finite; one needs, for each finite set of perfect-core elements, a finite
separable intermediate field containing it.  That is always available, and it composes with the
Hensel-embedded base change of `EppSeparableEmbedding` to give a finite weakly unramified
extension absorbing any prescribed finite part of the perfect core.

This is the filtered-colimit argument done at the right granularity: instead of building an
infinite extension and then trying to descend weak solutions along it — which is precisely what
Tag 09ET got wrong, and what `Stacks.WeakSolution.Obstruction.conjugateFactor_injective`
certifies fails — one stays finite throughout.

What is deliberately *not* done is a reduction through the separably closed case.
Descending a weak solution along the separable closure is equivalent to Epp's theorem itself, so
a statement that assumes that descent assumes what it would have to prove.

## Main results

* `Stacks.EppTheorem.EppCondition.exists_finite_separable_subextension`: every finite subset of the
  perfect core of `κ_B` lies in a finite separable intermediate field of `κ_B / κ_A`, and in a
  smallest one.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_nonempty_algHom_of_finset`:
  consequently, for any finite subset of the perfect core there is a finite weakly unramified
  extension `A₁ / A` of discrete valuation rings equipped with an `A`-algebra map `A₁ → B` — with
  **no** finiteness hypothesis on the separable closure.  Note that this statement does *not*
  record which elements the extension absorbs, so it is satisfied by `A₁ = A`; for the absorbing
  form use the next result.
* `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_absorbing_finset`: the same extension,
  with the absorption **in the conclusion** — every element of the prescribed finite subset lies
  in the image of `κ_{A₁}` in `κ_B`, and that image is still inside the perfect core.  This is the
  form the degree-`p` argument needs, since its hypothesis is an assertion about that image.

## References

* [Epp, *Elimination of wild ramification*][epp1973]
* `StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionalDescent` — why staying finite matters
-/

@[expose] public section

open IsLocalRing

namespace Stacks.EppTheorem

universe u v

section FinitePerfectCore

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]

/-- **Epp's condition has finite support.**

Every finite subset of the perfect core of `κ_B` generates a finite separable extension of `κ_A`
inside `κ_B`.  Stated for a `Finset` on purpose: constructions of a polynomial, a finite
presentation, or a finite base change use only finitely many residue coefficients, so this is the
form in which Epp's condition is actually consumed. -/
theorem EppCondition.exists_finite_separable_subextension
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ E : IntermediateField (ResidueField A) (ResidueField B),
      FiniteDimensional (ResidueField A) E ∧
      Algebra.IsSeparable (ResidueField A) E ∧
      (∀ z ∈ s, z ∈ E) ∧
      ∀ F : IntermediateField (ResidueField A) (ResidueField B),
        (∀ z ∈ s, z ∈ F) → E ≤ F := by
  classical
  have hsep : ∀ z ∈ (s : Set (ResidueField B)), IsSeparable (ResidueField A) z :=
    fun z hz => h z (hs z hz)
  have hle : ∀ F : IntermediateField (ResidueField A) (ResidueField B),
      (∀ z ∈ s, z ∈ F) → IntermediateField.adjoin (ResidueField A) (s : Set (ResidueField B)) ≤ F :=
    fun F hF => IntermediateField.adjoin_le_iff.mpr hF
  refine ⟨IntermediateField.adjoin (ResidueField A) (s : Set (ResidueField B)),
    IntermediateField.finiteDimensional_adjoin fun z hz => (hsep z hz).isIntegral,
    (le_separableClosure_iff (ResidueField A) (ResidueField B) _).mp
      (hle _ fun z hz => mem_separableClosure_iff.mpr (hsep z hz)),
    fun z hz => IntermediateField.subset_adjoin (ResidueField A) _ hz, hle⟩

end FinitePerfectCore

/-- **The finite-support base change, with no finiteness hypothesis on the separable closure.**

For any finite subset `s` of the perfect core of `κ_B`, there is a finite weakly unramified
extension of discrete valuation rings `A₁ / A`, equipped with an `A`-algebra map `A₁ → B`, whose
residue field absorbs `s`.

This is the composition of `EppCondition.exists_finite_separable_subextension` with
`exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable`, and it is what makes the finiteness
hypothesis of `exists_isWeaklyUnramified_nonempty_algHom_separableClosure` avoidable: rather than
requiring `separableClosure κ_A κ_B` to be finite over `κ_A` — which fails in general and whose
repair would need an infinite extension of exactly the kind whose weak-solution descent Tag 09ET
gets wrong — one absorbs a prescribed finite part at a time and stays finite throughout.

`B` henselian is inherited from the embedding step, and holds for complete `B` by
`henselianLocalRing_of_isAdicComplete_maximalIdeal`. -/
theorem EppCondition.exists_isWeaklyUnramified_nonempty_algHom_of_finset {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧ Nonempty (A₁ →ₐ[A] B) := by
  obtain ⟨E, hfin, hsep, -, -⟩ := h.exists_finite_separable_subextension s hs
  have := hfin
  have := hsep
  exact exists_isWeaklyUnramified_nonempty_algHom_of_isSeparable E

/-- **Finite-support absorption, with the absorption recorded in the conclusion.**

Let `A → B` be a local homomorphism of discrete valuation rings with `B` henselian and `κ_A`
perfect, let Epp's condition hold, and let `s` be a finite subset of `perfectCore κ_B p`.  Then
there is a discrete valuation ring `A₁`, finite and weakly unramified over `A` and sitting inside
`B` over `A`, such that

* every element of `s` lies in the image of `κ_{A₁}` in `κ_B` — the absorption; and
* that image is still contained in `perfectCore κ_B p` — nothing has been over-absorbed.

**There is no finiteness hypothesis on the perfect core.**  The conclusion of
`exists_isWeaklyUnramified_nonempty_algHom_of_finset` above does not record the absorption, so it
is satisfied by any finite weakly unramified extension whatsoever — `A₁ = A` included — and
therefore cannot supply the `hresidue` hypothesis of
`IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP`, which is an
assertion about the *image* of `κ_A` in `κ_B`.  Here the absorption is part of the conclusion,
carried by the `fieldRange` equality of
`exists_isWeaklyUnramified_algebraMap_fieldRange_eq_of_isSeparable`.

The second clause is where `κ_A` perfect is used: the image of `κ_{A₁}` is `κ_A(s)`, and that lies
in the perfect core only because the image of `κ_A` does.

Relation to `exists_isWeaklyUnramified_algebraMap_fieldRange_eq_perfectCore`: that result absorbs
the perfect core *entirely*, giving `fieldRange = perfectCore` — exactly `hresidue` — but it needs
the perfect core to be finite over `κ_A`, which fails in general (take `κ_A = 𝔽_p` inside a `κ_B`
containing `𝔽_p`'s algebraic closure: Epp's condition holds and the perfect core is infinite over
`κ_A`).  This result trades that equality for absorption of a prescribed finite part, at no cost in
hypotheses.  Converting it into `hresidue` for a *particular* degree-`p` equation requires knowing
that the finitely many residue coefficients of that equation are the only part of the perfect core
the argument consumes, and then iterating absorption against Kuhlmann's decreasing wild-support
measure. -/
theorem EppCondition.exists_isWeaklyUnramified_absorbing_finset {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ}
    [ExpChar (ResidueField A) p] [PerfectRing (ResidueField A) p]
    [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        (∀ z ∈ s, z ∈ (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange) ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange ≤
          perfectCore (ResidueField B) p := by
  obtain ⟨E, hfin, hsep, habs, hmin⟩ := h.exists_finite_separable_subextension s hs
  have := hfin
  have := hsep
  obtain ⟨A₁, _, hdom, hdvr, _, hmf, hext, algψ, htower, hlhψ, hwu, -, hfr⟩ :=
    exists_isWeaklyUnramified_algebraMap_fieldRange_eq_of_isSeparable (A := A) (B := B) E
  refine ⟨A₁, inferInstance, hdom, hdvr, inferInstance, hmf, hext, algψ, htower, hlhψ, hwu,
    fun z hz => ?_, ?_⟩
  · rw [hfr, IntermediateField.mem_toSubfield]
    exact habs z hz
  · rw [hfr]
    intro y hy
    exact hmin (perfectCoreIntermediateField (ResidueField A) (ResidueField B) p)
      (fun z hz => hs z hz) ((IntermediateField.mem_toSubfield E y).mp hy)

end Stacks.EppTheorem
