module

public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison
public import StacksFrontier.Homology.DerivedComplete.PowerQuotientAdicCompletion
import all StacksFrontier.Homology.DerivedComplete.CompletionAdjunction

/-!
# The formal-functions sequence in degree zero

Let `A` be a commutative ring, `f ∈ A` and `K ∈ D(A)`. The comparison diagram of Stacks 0H32
(`PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison`) contains, as its
top row, the short exact sequence
`0 ⟶ lim_n Hᵖ(K)/fⁿHᵖ(K) ⟶ lim_n Hᵖ(K ⊗ᴸ_A A/fⁿ) ⟶ T_f(H^{p+1}(K)) ⟶ 0`
of Stacks 0BLD. That theorem is stated for an arbitrary reflector onto the `(f)`-adically
derived-complete objects together with an adjunction witnessing the reflection, which the caller
has to supply; nothing in the library supplied one, so the sequence was unusable. This file
supplies the reflection and extracts the top row unconditionally, then reads off the degree-zero
case.

In degree zero the left-hand term is the ordinary `f`-adic completion of `H⁰(K)`
(`Stacks.PowerQuotient.isIso_completionComparison`), so the sequence collapses to an isomorphism
`H⁰(K) ≅ lim_n H⁰(K ⊗ᴸ_A A/fⁿ)` as soon as `H⁰(K)` is `f`-adically complete and the `f`-adic Tate
module of `H¹(K)` vanishes. Those are exactly the two outer-term hypotheses that
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ComplementSectionsComplete.lean`
discharges for derived sections away from `V(𝔞)`.

The isomorphism is pinned down: its `n`-th component is the canonical map
`H⁰(K) ⟶ H⁰(K ⊗ᴸ_A A/fⁿ)` induced by the second map of the cone triangle of `fⁿ` on `K`, so the
statement is not satisfied by an arbitrary isomorphism between the two sides.

What is *not* here is the comparison of the derived tower `K ⊗ᴸ_A A/fⁿ` with the tower of actual
quotient sheaves `F/fⁿF` of Stacks 0BLD. For `K = RΓ(U, F)` the two differ by the `fⁿ`-torsion of
`F`, which is what the bounded-torsion hypothesis of Stacks 0BLD controls; that comparison needs
`RΓ(U, -)` to be an exact functor into the derived category, which this library does not yet have.

## Main definitions

* `Stacks.FormalFunctions.tensorHomologySystem` — the inverse system `Hᵖ(K ⊗ᴸ_A A/f^(n+1))`.
* `Stacks.FormalFunctions.derivedTensorUnit` — the canonical map `K ⟶ K ⊗ᴸ_A A/f^(n+1)`.

## Main results

* `Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint` — the inclusion of the
  `(f)`-adically derived-complete objects into `D(A)` has a left adjoint, for a principal ideal.
  This is the input Stacks 0H32 and Stacks 0BKG demand of their callers.
* `Stacks.FormalFunctions.exists_topRow` — **the top row of the formal-functions diagram of
  Stacks 0BLD, with no hypotheses**, in every degree: a short exact sequence
  `0 ⟶ lim_n Hᵖ(K)/fⁿ ⟶ lim_n Hᵖ(K ⊗ᴸ A/fⁿ) ⟶ T_f(H^{p+1}K) ⟶ 0` whose first map is induced by
  the canonical reductions.
* `Stacks.FormalFunctions.exists_iso_limit_tensorHomology_zero` — **Stacks 0BLD in degree zero**:
  if `H⁰(K)` is `f`-adically complete and `T_f(H¹(K))` vanishes, then `H⁰(K)` is the inverse limit
  of `H⁰(K ⊗ᴸ_A A/fⁿ)` by the canonical maps.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DerivedCategory
  PrincipalTorsionTower

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.FormalFunctions

/-- **The inclusion of the `(f)`-adically derived-complete objects has a left adjoint.** This is
the reflection of Stacks 0G3E for the principal ideal `(f)`, in the form that the comparison
diagram of Stacks 0H32 takes as a hypothesis. -/
public theorem derivedComplete_principal_ι_isRightAdjoint (A : Type u) [CommRing A] (f : A) :
    (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L).ι.IsRightAdjoint := by
  have he : Ideal.span (Set.range (fun _ : Fin 1 ↦ f)) = Ideal.span {f} := by
    congr 1
    exact Set.range_const
  rw [← he]
  exact CompletionAdjunction.derivedComplete_ι_isRightAdjoint A (fun _ : Fin 1 ↦ f)

variable (A : Type u) [CommRing A] (f : A) (K : DerivedCategory (ModuleCat.{u} A))

/-- The inverse system `Hᵖ(K ⊗ᴸ_A (A →[f^(n+1)] A))` of the cohomology of the principal derived
tensor tower. -/
public abbrev tensorHomologySystem (p : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  principalDerivedTensorSystem A f K ⋙ homologyFunctor (ModuleCat.{u} A) p

/-- The canonical map `K ⟶ K ⊗ᴸ_A (A →[f^(n+1)] A)`: the second map of the cone triangle of
multiplication by `f ^ (n + 1)` on the chosen complex representing `K`. -/
public abbrev derivedTensorUnit (n : ℕ) :
    K ⟶ (principalDerivedTensorSystem A f K).obj ⟨n⟩ :=
  (DerivedCategory.Q.objObjPreimageIso K).inv ≫
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (f ^ (n + 1) • 𝟙 (DerivedCategory.Q.objPreimage K)))).mor₂

/-- **The top row of the principal formal-functions diagram of Stacks 0BLD, unconditionally.**
For every `K ∈ D(A)` and every degree `p` there is a short exact sequence
`0 ⟶ lim_n Hᵖ(K)/f^(n+1)Hᵖ(K) ⟶ lim_n Hᵖ(K ⊗ᴸ_A A/f^(n+1)) ⟶ T_f(H^{p+1}(K)) ⟶ 0`
whose first map is the limit of the maps induced on the quotient tower by the canonical maps
`K ⟶ K ⊗ᴸ_A A/f^(n+1)`.

Stacks 0H32 states this with a reflector onto the derived-complete objects and an adjunction as
hypotheses; `derivedComplete_principal_ι_isRightAdjoint` discharges them. -/
public theorem exists_topRow (p : ℤ) :
    let H (q : ℤ) := (homologyFunctor (ModuleCat.{u} A) q).obj K
    ∃ (termIn : CompletionSequences.powerQuotientSystem A (H p) f ⟶
        tensorHomologySystem A f K p)
      (topIn : limit (CompletionSequences.powerQuotientSystem A (H p) f) ⟶
        limit (tensorHomologySystem A f K p))
      (topOut : limit (tensorHomologySystem A f K p) ⟶
        CompletionSequences.adicTateModule A (H (p + 1)) f)
      (htop : topIn ≫ topOut = 0),
      (ShortComplex.mk topIn topOut htop).ShortExact ∧
      (∀ n : ℕ,
        cokernel.π (powerMultiplication A (H p) (f ^ (n + 1))) ≫ termIn.app ⟨n⟩ =
          (homologyFunctor (ModuleCat.{u} A) p).map (derivedTensorUnit A f K n)) ∧
      (∀ n : ℕ, topIn ≫ limit.π (tensorHomologySystem A f K p) ⟨n⟩ =
        limit.π (CompletionSequences.powerQuotientSystem A (H p) f) ⟨n⟩ ≫ termIn.app ⟨n⟩) := by
  intro H
  have : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  have hadj := derivedComplete_principal_ι_isRightAdjoint A f
  have h := PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison A f K p
  dsimp only at h
  obtain ⟨S, hS⟩ := h (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L).ι.leftAdjoint
    (Adjunction.ofIsRightAdjoint _)
  dsimp only at hS
  obtain ⟨termIn, termOut, previousOut, productIso, topIn, topOut, htop, columnIn, columnOut,
    hcolumn, bottom, h1, h2, h3, h4, h5, h6, h7, h8, h9, hTopExact, hrest⟩ := hS
  exact ⟨termIn, topIn, topOut, htop, hTopExact, h1, h4⟩

/-- **Stacks 0BLD in degree zero.** If the degree-zero cohomology of `K` is `f`-adically complete
and the `f`-adic Tate module of its degree-one cohomology vanishes, then `H⁰(K)` is the inverse
limit of `H⁰(K ⊗ᴸ_A A/f^(n+1))`, by the canonical maps.

The two hypotheses are the two outer terms of the degree-zero formal-functions sequence; they are
what Stacks 0EII provides for derived sections away from a closed subscheme. -/
public theorem exists_iso_limit_tensorHomology_zero
    (hcomplete : IsAdicComplete (Ideal.span {f}) ((homologyFunctor (ModuleCat.{u} A) 0).obj K))
    (hTate : IsZero (CompletionSequences.adicTateModule A
      ((homologyFunctor (ModuleCat.{u} A) 1).obj K) f)) :
    ∃ e : (homologyFunctor (ModuleCat.{u} A) 0).obj K ≅ limit (tensorHomologySystem A f K 0),
      ∀ n : ℕ, e.hom ≫ limit.π (tensorHomologySystem A f K 0) ⟨n⟩ =
        (homologyFunctor (ModuleCat.{u} A) 0).map (derivedTensorUnit A f K n) := by
  have := hcomplete
  obtain ⟨termIn, topIn, topOut, htop, hexact, hterm, htopπ⟩ := exists_topRow A f K 0
  have hzero : topOut = 0 := hTate.eq_zero_of_tgt _
  have hepi : Epi topIn := by
    have hex := hexact.exact
    rw [ShortComplex.exact_iff_epi _ hzero] at hex
    exact hex
  have hmono : Mono topIn := hexact.mono_f
  have : IsIso topIn := isIso_of_mono_of_epi topIn
  refine ⟨Stacks.PowerQuotient.isoLimitPowerQuotient _ f ≪≫ asIso topIn, ?_⟩
  intro n
  rw [Iso.trans_hom, Stacks.PowerQuotient.isoLimitPowerQuotient_hom, asIso_hom,
    Category.assoc, htopπ n, ← Category.assoc,
    Stacks.PowerQuotient.completionComparison_π]
  exact hterm n

end Stacks.FormalFunctions

end
