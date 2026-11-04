module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Bound07QAHypotheses

/-!
# The monomorphism hypothesis of [Stacks, Tag 07QA], in sharp form

`SmallSite/Bound07QAHypotheses.lean` reduces the second hypothesis of the cokernel half of
[Stacks, Tag 07QA] — that `ℋ^0` of the comparison map of [Stacks, Tag 07Q9] be a monomorphism —
to injectivity of the crystalline adjunction unit,

`Mono (...SmallSite.crisUnit S S' fS fX hf F)`,  `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ`,

by `...SmallSite.mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit`.  That reduction
runs in one direction only, and it overshoots: every step of its proof is already an *iff*, and
the unit itself is never used — only its image under `u_{X/S, *}`.  This file states the
reduction in the sharp form the steps support, and separately identifies what injectivity of the
unit is, as a property of `f_cris^{-1}`.

## What is sharpened

**The hypothesis is `u_{X/S, *}` of the unit, not the unit.**
`mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` proves

`Mono (ℋ^0(Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'))  ↔  Mono (u_{X/S, *}(ℱ ⟶ f_{cris, *}ℱ'))`,

an equivalence.  The three steps of
`...SmallSite.mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit` are
`...SmallSite.mono_homologyMap_derivedZariskiComparison_iff` (an iff), the invertibility on `ℋ^0`
of the degree-zero comparison `f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]` (composition with an
isomorphism neither creates nor destroys a monomorphism, in both directions) and
`...SmallSite.mono_homologyFunctor_derivedZariskiDirectImage_map_iff` (an iff).  So nothing
between the bound and `Mono (u_{X/S, *}(crisUnit))` is lost, and the right-hand side is the
*exact* content of the hypothesis rather than a sufficient condition for it.

`Mono (u_{X/S, *}(crisUnit ...))` is strictly weaker than `Mono (crisUnit ...)`: `u_{X/S, *}` is
a right adjoint, hence left exact, hence preserves monomorphisms, and the converse implication
would need `u_{X/S, *}` to be faithful, which this library does not prove.  So
`exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit` below subsumes
`...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_crisUnit`.

**Injectivity of the unit is faithfulness of `f_cris^{-1}`.**  `mono_crisUnit_iff` reads
`Mono (crisUnit ... F)` as the statement that `f_cris^{-1}` kills no nonzero map *into* `F`, and
`faithful_crisInverseImage_iff_forall_mono_crisUnit` assembles those into
`(f_cris^{-1}).Faithful`.  Both directions are Mathlib's
`CategoryTheory.Adjunction.unit_mono_of_L_faithful` and
`CategoryTheory.Adjunction.faithful_L_of_mono_unit_app`; the pointwise form is
`Stacks.Adjunction.mono_unit_app_iff` below, which Mathlib does not have.  This is what says that
the hypothesis is the assertion that `f_cris` is a *surjection of topoi*, and in particular that
it is **false without a hypothesis on `fX`** — for `X' = ∅` the functor `f_cris^{-1}` is zero and
the unit is zero — so no declaration here proves it and none is tagged.

## What the library has towards the hypothesis, and what it does not

The splitness that [Stacks, Tag 07Q9]'s proof rests on **is proved, for the uncompleted
extension**: `Crystalline.PthRootExtension.primeRetraction` is the `B`-linear coordinate of the
basis vector `1` in the free `B`-module `B[z]⟨ξ⟩/(ξ - (z^p - λ))`,
`Crystalline.PthRootExtension.primeRetraction_comp` says it is a left inverse of
`B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`, and
`Crystalline.PthRootExtension.universallyInjective_toPrimeRing` upgrades that to universal
injectivity — all in
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PurelyInseparablePullback.lean`.  The
other thing the module documentation of `SmallSite/Bound07QAHypotheses.lean` records,
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootFormsDecomposition.lean`, is the
homotopy inverse of the de Rham complexes and a different statement.

The `p`-adic completion of that splitness is also proved, in
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/CompletedPthRootExtension.lean`:
`Crystalline.PthRootExtension.completedPrimeRetraction_comp_completedToPrimeRing` completes the
retraction along `(p)`, and `Crystalline.PthRootExtension.injective_completedToPrimeRing` is the
resulting injectivity of `D ⟶ D'`, with `D'` the `p`-adic completion of
`B[z]⟨ξ⟩/(ξ - (z^p - λ))` as in [Stacks, Tag 07N1] and `D` the `p`-adic completion of `B` (the
source's `D` is already `p`-adically complete, which is not used and not needed).

What is still missing between those and `Mono (u_{X/S, *}(crisUnit ...))` is the passage from the
affine pair `(D, M)` to the sheaf `ℱ` on `Cris(X/S)` — which is [Stacks, Proposition 07LG]
again — and the globalisation over the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X`.  Nothing here closes
either of those.

## Main results

* `Stacks.Adjunction.mono_unit_app_iff` — for an adjunction between preadditive categories with
  both functors additive, `Mono` of the unit at `X` says exactly that the left adjoint kills no
  nonzero morphism into `X`.
* `...SmallSite.mono_crisUnit_iff` — the same, read at the crystalline unit.
* `...SmallSite.faithful_crisInverseImage_iff_forall_mono_crisUnit` — the unit is a
  monomorphism at every sheaf if and only if `f_cris^{-1}` is faithful.
* `...SmallSite.mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` — **the
  monomorphism hypothesis of the cokernel half of [Stacks, Tag 07QA] is exactly
  `Mono (u_{X/S, *}(crisUnit ...))`.**
* `...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit` — the cokernel
  bound with that hypothesis in place of injectivity of the unit.

## No tag is placed

No tag attribute is placed here.  The two theorems about the bound either are unconditional
reductions of a hypothesis or take `...SmallSite.Annihilation07Q9` as an input, for an arbitrary
abelian sheaf.  [Stacks, Tag 07Q9] is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` and
[Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`, both for a
crystal in quasi-coherent modules; the latter's cokernel half uses the module form of the
hypothesis of this file, `Mono (u_{X/S, *}(unit))`, which is
`...SmallSite.mono_zariskiDirectImage_map_crisModuleUnit_of_isIteratedAlphaPCover`.  The abelian
`Mono (crisUnit ...)` is not proved for an arbitrary sheaf, and as noted above it is false for a
general `fX`.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.22.1, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe v v' w w' u u'

noncomputable section

namespace Stacks.Adjunction

/-- **The unit of an adjunction is a monomorphism at `X` exactly when the left adjoint kills no
nonzero morphism into `X`.**  For `L ⊣ R` between preadditive categories with `L` and `R`
additive, `g ≫ η_X` and `L g` correspond under the adjunction, so one vanishes if and only if the
other does; in a preadditive category `Mono` is the vanishing of every left annihilator.

Mathlib has the two implications between faithfulness of `L` and `Mono (η_X)` *for all* `X`
(`CategoryTheory.Adjunction.unit_mono_of_L_faithful`,
`CategoryTheory.Adjunction.faithful_L_of_mono_unit_app`); this is their pointwise refinement. -/
theorem mono_unit_app_iff {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [R.Additive] (X : C) :
    Mono (adj.unit.app X) ↔ ∀ (Z : C) (g : Z ⟶ X), L.map g = 0 → g = 0 := by
  have : L.Additive := adj.left_adjoint_additive
  have key : ∀ (Z : C) (g : Z ⟶ X), g ≫ adj.unit.app X = 0 ↔ L.map g = 0 := fun Z g => by
    rw [← adj.unit_naturality g]
    refine ⟨fun h => ?_, fun h => by rw [h, Functor.map_zero, Limits.comp_zero]⟩
    have hL : L.map (adj.unit.app Z ≫ R.map (L.map g)) ≫ adj.counit.app (L.obj X) =
        L.map g := by simp
    rw [h, Functor.map_zero, Limits.zero_comp] at hL
    exact hL.symm
  rw [Preadditive.mono_iff_cancel_zero]
  exact ⟨fun h Z g hg => h Z g ((key Z g).2 hg), fun h Z g hg => h Z g ((key Z g).1 hg)⟩

end Stacks.Adjunction

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.Cohomology

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-! ### The first of the three units composing the crystalline unit is invertible -/

/-- **The lower shriek `i_{X, !}` is fully faithful**: the unit `ℱ ⟶ i_X^{-1}i_{X, !}ℱ` of
`...SmallSite.smallRestrictionAdjunction` is an isomorphism.

`...CrystallineThickening.ι` is the inclusion of a full subcategory and is both continuous and
cocontinuous for the small and big crystalline topologies, so this is
`CategoryTheory.Functor.isIso_unit_of_sheafPushforwardContinuous` — [Stacks, Tag 00XT] — at the
abelian coefficients of this chapter.  It is the formula `i_X^{-1}i_{X, !} = id` of
[Stacks, Tag 07IJ], and it is stated for an arbitrary model of `i_{X, !}` there, so it applies to
the library's chosen one.

`...SmallSite.crisDirectImageAdjunction` is a composite of three adjunctions, so by
`CategoryTheory.Adjunction.comp_unit_app` its unit `...SmallSite.crisUnit` is a composite of
three maps; this says the first of them, the one for `i_{X, !} ⊣ i_X^{-1}`, is invertible and so
contributes nothing to whether `crisUnit` is a monomorphism.  The other two — the unit of the
change of divided power base and the unit of `i_X^{-1} ⊣ i_{X, *}` on the big site — are where
the geometry sits, and neither is settled here. -/
theorem isIso_smallRestrictionAdjunction_unit (T : GlobalCrystallineSituation.{u}) :
    IsIso (smallRestrictionAdjunction T).unit :=
  Functor.isIso_unit_of_sheafPushforwardContinuous (CrystallineThickening.ι T)
    AddCommGrpCat.{u + 1} (smallTopology T) (topology T) (smallRestrictionAdjunction T)

/-- **`i_{X, !}` is faithful**, being fully faithful by
`isIso_smallRestrictionAdjunction_unit`.  This is the first factor of
`...SmallSite.crisInverseImage`; by `CategoryTheory.Functor.Faithful.comp` the faithfulness of
`f_cris^{-1}` that `faithful_crisInverseImage_iff_forall_mono_crisUnit` asks for therefore needs
only its two remaining factors. -/
theorem faithful_lowerShriek (T : GlobalCrystallineSituation.{u}) :
    (Functor.sheafPullbackConstruction.sheafPullback (CrystallineThickening.ι T)
      AddCommGrpCat.{u + 1} (smallTopology T) (topology T)).Faithful :=
  have := isIso_smallRestrictionAdjunction_unit T
  ((smallRestrictionAdjunction T).fullyFaithfulLOfIsIsoUnit).faithful

/-! ### Injectivity of the crystalline unit is faithfulness of `f_cris^{-1}` -/

section Unit

include hf

/-- **`ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a monomorphism exactly when `f_cris^{-1}` kills no nonzero
map into `ℱ`.**  `...SmallSite.crisUnit` is the unit of `...SmallSite.crisDirectImageAdjunction`,
both of whose functors are additive, so this is `Stacks.Adjunction.mono_unit_app_iff`. -/
theorem mono_crisUnit_iff (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    Mono (crisUnit S S' fS fX hf F) ↔
      ∀ (G : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) (g : G ⟶ F),
        (crisInverseImage S S' fS fX hf).map g = 0 → g = 0 :=
  Stacks.Adjunction.mono_unit_app_iff (crisDirectImageAdjunction S S' fS fX hf) F

/-- **The crystalline unit is a monomorphism at every abelian sheaf if and only if `f_cris^{-1}`
is faithful.**  This is Mathlib's pair
`CategoryTheory.Adjunction.unit_mono_of_L_faithful` and
`CategoryTheory.Adjunction.faithful_L_of_mono_unit_app` at
`...SmallSite.crisDirectImageAdjunction`.

It is what places the hypothesis of the cokernel half of [Stacks, Tag 07QA] in the standard
vocabulary: the assertion is that `f_cris` is a surjection of topoi.  In particular
it needs a hypothesis on `fX` — for `X' = ∅` the inverse image is the zero functor and the unit
is the zero map — and none of the statements of this file supplies one. -/
theorem faithful_crisInverseImage_iff_forall_mono_crisUnit :
    (crisInverseImage S S' fS fX hf).Faithful ↔
      ∀ F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1},
        Mono (crisUnit S S' fS fX hf F) := by
  refine ⟨fun h F => ?_, fun h => ?_⟩
  · have := h
    exact (crisDirectImageAdjunction S S' fS fX hf).unit_mono_of_L_faithful F
  · have : ∀ F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1},
        Mono ((crisDirectImageAdjunction S S' fS fX hf).unit.app F) := h
    exact (crisDirectImageAdjunction S S' fS fX hf).faithful_L_of_mono_unit_app

end Unit

/-! ### The hypothesis of the cokernel half, to its exact content -/

section Mono

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

include hf

/-- **The monomorphism hypothesis of the cokernel half of [Stacks, Tag 07QA] is exactly
`Mono (u_{X/S, *}(ℱ ⟶ f_{cris, *}ℱ'))`.**  `ℋ^0` of the comparison map
`Ru_{X/S, *}ℱ ⟶ Rf_{Zar, *}Ru_{X'/S, *}ℱ'` of [Stacks, Tag 07Q9] is a monomorphism if and only if
`u_{X/S, *}` of the crystalline adjunction unit is one.

Each of the three steps of
`...SmallSite.mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit` is reversible and they
are used here in that form: the commutation `sq` of the square of topoi drops out by
`...SmallSite.mono_homologyMap_derivedZariskiComparison_iff`; the derived unit splits as
`u_{X/S, *}` of the underived unit followed by the degree-zero comparison
`f_{cris, *}ℱ'[0] ⟶ Rf_{cris, *}ℱ'[0]`, which is an *isomorphism* on `ℋ^0` by
`Stacks.Cohomology.isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app`,
so composing with it changes nothing in either direction; and
`...SmallSite.mono_homologyFunctor_derivedZariskiDirectImage_map_iff` identifies
`ℋ^0 ∘ Ru_{X/S, *}` on a sheaf placed in degree zero with the underived `u_{X/S, *}`.

The right-hand side is strictly weaker than `Mono (...SmallSite.crisUnit S S' fS fX hf F)`, which
is what `...SmallSite.mono_homologyMap_derivedZariskiComparison_of_mono_crisUnit` asks for:
`u_{X/S, *}` is a right adjoint, so it preserves monomorphisms, and the converse implication
would need `u_{X/S, *}` to be faithful, which this library does not prove. -/
theorem mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit
    (sq : CrisZariskiSquare S S' fS fX hf)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) :
    Mono ((DerivedCategory.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map (DerivedCategory.Plus.ι.map
      (derivedZariskiComparison S S' fS fX hf sq F))) ↔
      Mono ((zariskiDirectImage S').map (crisUnit S S' fS fX hf F)) := by
  rw [mono_homologyMap_derivedZariskiComparison_iff S S' fS fX hf sq F]
  have hiso : IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
        ((derivedZariskiDirectImageFunctor S').map
          ((singleRightDerivedUnit (crisDirectImage S S' fS fX hf)).app
            (crisPullback S S' fS fX hf F)))) :=
    isIso_homologyFunctor_rightDerivedFunctorPlus_map_singleRightDerivedUnit_app
      (crisDirectImage S S' fS fX hf) (zariskiDirectImage S') (crisPullback S S' fS fX hf F)
  have heq : (DerivedCategory.Plus.homologyFunctor
        (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
          ((derivedZariskiDirectImageFunctor S').map (derivedCrisUnit S S' fS fX hf F)) =
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiDirectImageFunctor S').map
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallTopology S') AddCommGrpCat.{u + 1}) 0).map
                  (crisUnit S S' fS fX hf F))) ≫
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) 0).map
            ((derivedZariskiDirectImageFunctor S').map
              ((Stacks.Cohomology.singleRightDerivedUnit
                (crisDirectImage S S' fS fX hf)).app (crisPullback S S' fS fX hf F))) := by
    conv_rhs => rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [heq]
  exact (mono_comp_iff_of_isIso_snd _ _ hiso).trans
    (mono_homologyFunctor_derivedZariskiDirectImage_map_iff S' (crisUnit S S' fS fX hf F))

end Mono

/-! ### The cokernel bound with the exact hypothesis -/

section Bound

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

include hf

/-- **The cokernel half of [Stacks, Tag 07QA] on Zariski hypercohomology groups, with the
monomorphism hypothesis in its exact form.**  Given the conclusion of [Stacks, Tag 07Q9] and
that `u_{X/S, *}` of the crystalline unit `ℱ ⟶ f_{cris, *}f_cris^{-1}ℱ` is a monomorphism,
`q^{i + 1}` times any class in `H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')` is in the image of

`H^i(X_Zar, Ru_{X/S, *}ℱ) ⟶ H^i(X_Zar, Rf_{Zar, *}Ru_{X'/S, *}ℱ')`.

This subsumes `...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_crisUnit`, whose
hypothesis `Mono (...SmallSite.crisUnit S S' fS fX hf F)` implies this one because `u_{X/S, *}` is
left exact.  By `mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit` the hypothesis
is not merely sufficient but equivalent to what
`...SmallSite.exists_hypercohomologyMap_eq_pow_smul_07QA` consumes, so the whole hypothesis block
of the cokernel bound is the annihilation of [Stacks, Tag 07Q9] — `Annihilation07Q9`, for a
single cone by `...SmallSite.annihilation07Q9_of_exists` — together with this one monomorphism.
No tag attribute is placed on this lemma, which is stated for an arbitrary abelian sheaf;
[Stacks, Tag 07QA] is
`...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover`. -/
theorem exists_hypercohomologyMap_eq_pow_smul_07QA_of_mono_map_crisUnit (q i : ℕ)
    (F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1})
    (hann : Annihilation07Q9 S' q
      (derivedZariskiComparison S S' fS fX hf (crisZariskiSquare S S' fS fX hf) F))
    (hmono : Mono ((zariskiDirectImage S').map (crisUnit S S' fS fX hf F)))
    (y : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} (i : ℤ)).obj
      ((derivedZariskiGlobalSectionsFunctor S').obj
        ((derivedZariskiPushforwardFunctor S S' fX).obj
          ((derivedZariskiDirectImage S).obj (crisPullback S S' fS fX hf F))))) :
    ∃ x, ((q : ℤ) ^ (i + 1)) • y =
      zariskiHypercohomologyComparisonMap S S' fS fX hf F i x :=
  exists_hypercohomologyMap_eq_pow_smul_07QA S S' fS fX hf q i F hann
    ((mono_homologyMap_derivedZariskiComparison_iff_mono_map_crisUnit S S' fS fX hf
      (crisZariskiSquare S S' fS fX hf) F).2 hmono) y

end Bound

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
