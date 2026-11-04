/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomialAffine
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomialBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.GraphAmbientTensorAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource

/-!
# `Mor^{P, ℳ}_B(Y, X) ⟶ B` is separated and of finite presentation (Stacks 0DPR)

Let `B` be an algebraic space over `Spec ℤ`, `Y ⟶ B` flat, proper and of finite presentation and
`X ⟶ B` separated and of finite presentation; below, `Y ⟶ B` is `z : Z ⟶ Q` and `X ⟶ B` is
`x : X ⟶ Q`. Let `𝒩` be ample on `Y/B` and `ℒ` ample on `X/B` (Stacks 0D31),
`ℳ = pr₁^*𝒩 ⊗ pr₂^*ℒ` on `Y ×_B X` and `P` a numerical polynomial. Then `Mor^{P, ℳ}_B(Y, X)` is
an algebraic space and `Mor^{P, ℳ}_B(Y, X) ⟶ B` is separated and of finite presentation.

## Main results

* `AlgebraicGeometry.Space.isSeparated_and_isFinitePresentation_relativeHomHilbertPolynomial`:
  `Mor^{P, ℳ}_B(Y, X)` is an algebraic space, separated and of finite presentation over `B`.

## References

* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase ℤS

/-- Let `Q` be an algebraic space over `Spec ℤ`, `z : Z ⟶ Q` flat, proper and of finite
presentation, `x : X ⟶ Q` separated and of finite presentation, `N` an invertible module ample on
`Z/Q` and `L` an invertible module ample on `X/Q` (Stacks 0D31), and `P` a numerical polynomial.
Then for `ℳ = pr₁^*N ⊗ pr₂^*L` on `Z ×_Q X` (`AlgebraicGeometry.Space.graphAmbientTensor`),
`Mor^{P, ℳ}_Q(Z, X)` (`AlgebraicGeometry.Space.relativeHomHilbertPolynomial`) is an algebraic
space and its morphism to `Q` is separated and of finite presentation. -/
@[stacks 0DPR]
theorem isSeparated_and_isFinitePresentation_relativeHomHilbertPolynomial
    {Z X Q : (BigFppfOver B integerBase ℤS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B integerBase ℤS Z) (hX : IsAlgebraicSpace B integerBase ℤS X)
    (hQ : IsAlgebraicSpace B integerBase ℤS Q)
    (hsep : IsSeparated B integerBase ℤS x) (hxfp : IsFinitePresentation B integerBase ℤS x)
    (hfp : IsFinitePresentation B integerBase ℤS z) (hflat : IsFlat B integerBase ℤS z)
    (hproper : IsProper B integerBase ℤS z)
    (N : Modules.{u, u} B integerBase ℤS Z hZ)
    [hNi : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS Z)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS Z hZ).O)).property N]
    (L : Modules.{u, u} B integerBase ℤS X hX)
    [hLi : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS X)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS X hX).O)).property L]
    (hN : IsRelativelyAmple B integerBase ℤS
      (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩) N)
    (hL : IsRelativelyAmple B integerBase ℤS
      (ObjectProperty.homMk x : (⟨X, hX⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩) L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    IsAlgebraicSpace B integerBase ℤS (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat
        hproper (graphAmbientTensor z x hZ hX hQ N L) P).toFunctor ∧
      IsSeparated B integerBase ℤS ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat
        hproper (graphAmbientTensor z x hZ hX hQ N L) P).ι ≫
          relativeHomProjection B integerBase ℤS Z X Q z x hZ hX hQ) ∧
      IsFinitePresentation B integerBase ℤS ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp
        hflat hproper (graphAmbientTensor z x hZ hX hQ N L) P).ι ≫
          relativeHomProjection B integerBase ℤS Z X Q z x hZ hX hQ) := by
  have hMa := isRelativelyAmple_graphAmbientTensor N L hN hL
  set M := graphAmbientTensor z x hZ hX hQ N L
  have hzr : yoneda.relativelyRepresentable z := hN.1
  have hxr : yoneda.relativelyRepresentable x := hL.1
  have hsepF := isSeparated_relativeHomHilbertPolynomial_comp hZ hX hQ hsep hxfp hfp hflat hproper
    M P
  have hlfpF := isLocallyOfFinitePresentation_relativeHomHilbertPolynomial_comp hZ hX hQ hsep hxfp
    hfp hflat hproper M P
  obtain ⟨halg, hqc⟩ := isAlgebraicSpace_isQuasiCompact_of_isAffine B integerBase ℤS
    (isSheaf_relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P) hQ _
    (fun W ξ hW => by
      have : IsAffine ((𝒯).obj W) := hW
      let hW' := isAlgebraicSpace_yoneda B integerBase ℤS W
      let z' := pullback.fst ξ z
      let x' := pullback.fst ξ x
      have hZ' := isAlgebraicSpace_pullback B integerBase ℤS ξ z hW' hZ hQ
      have hX' := isAlgebraicSpace_pullback B integerBase ℤS ξ x hW' hX hQ
      have hsep' : IsSeparated B integerBase ℤS x' :=
        isSeparated_pullbackFst B integerBase ℤS ξ hsep
      have hxfp' : IsFinitePresentation B integerBase ℤS x' :=
        (isFinitePresentation_isStableUnderBaseChange B integerBase ℤS).of_isPullback
          (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS
            (ObjectProperty.homMk ξ : (⟨_, hW'⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)
            (ObjectProperty.homMk x : (⟨X, hX⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)).flip
          hxfp
      have hfp' : IsFinitePresentation B integerBase ℤS z' :=
        (isFinitePresentation_isStableUnderBaseChange B integerBase ℤS).of_isPullback
          (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS
            (ObjectProperty.homMk ξ : (⟨_, hW'⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)
            (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)).flip
          hfp
      have hflat' : IsFlat B integerBase ℤS z' :=
        (isFlat_isStableUnderBaseChange B integerBase ℤS).of_isPullback
          (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS
            (ObjectProperty.homMk ξ : (⟨_, hW'⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)
            (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B integerBase ℤS) ⟶ ⟨Q, hQ⟩)).flip
          hflat
      have hproper' : IsProper B integerBase ℤS z' :=
        isProper_pullback_fst B integerBase ℤS hZ hQ hW' z ξ hproper
      have hzr' : yoneda.relativelyRepresentable z' := MorphismProperty.pullback_fst ξ z hzr
      have hxr' : yoneda.relativelyRepresentable x' := MorphismProperty.pullback_fst ξ x hxr
      have hMa' := isRelativelyAmple_baseChange
        (isPullback_graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW') M hMa
      have := stacksIsInvertible_modulePullback_obj B integerBase ℤS
        (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW') M
      obtain ⟨t, ht⟩ := exists_isPullback_relativeHomHilbertPolynomial_baseChange hZ hX hQ hsep
        hxfp hfp hflat hproper ξ hZ' hX' hW' hsep' hxfp' hfp' hflat' hproper' M P
      obtain ⟨Y, s, q, hs, hq⟩ := exists_isPullback_relativeHomHilbertPolynomial_of_isAffine W
        hZ' hX' hW' hsep' hxfp' hfp' hflat' hproper' hzr' hxr'
        ((modulePullback B integerBase ℤS (graphAmbientBaseChangeHom hZ hX hQ ξ hZ' hX' hW')).obj M)
        hMa' hP
      refine ⟨Y, s ≫ t, q, ?_, hq⟩
      have h := hs.paste_horiz ht
      rwa [Category.id_comp] at h)
  exact ⟨halg, hsepF, hlfpF, hqc, isQuasiSeparated_of_isSeparated B integerBase ℤS hsepF⟩

end AlgebraicGeometry.Space

end
