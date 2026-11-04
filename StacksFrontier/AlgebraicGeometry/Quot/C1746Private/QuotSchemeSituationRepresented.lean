/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialAmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotHilbertPolynomialModuleIso

/-!
# `Quot^P` over an affine scheme, represented by a scheme separated and of finite presentation

The affine case of the proof of Stacks 0DPD works with the Quot situation `F/U/W` of a morphism
of schemes `q : U ⟶ W` of the site, read as algebraic spaces, and with the inverse image on `U`
of `𝒪(1)` along a morphism `i : U ⟶ ℙⁿ_W` over `W`. This file names these, and the property
that a subfunctor of the Quot presheaf over the algebraic space of a scheme `W` is represented by
a scheme `Z` with `Z ⟶ W` separated, locally of finite presentation and quasi-compact — the
form in which the reduction
`isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented` (in
`AlgebraicGeometry.Space.QuotSituation`) asks for the affine case — together with its invariance
under isomorphisms of subfunctors over the base.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.schemeQuotSituation`: the Quot situation `F/U/W`.
* `AlgebraicGeometry.Space.QuotSituation.projectiveTwist`: `i^*𝒪(1)` on `h_U`.
* `AlgebraicGeometry.Space.QuotSituation.IsRepresentedSeparatedFinitePresentation`: the
  representability property.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.IsRepresentedSeparatedFinitePresentation.of_iso`:
  invariance under an isomorphism of subfunctors over the base.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **The Quot situation `F/U/W` of a morphism of schemes `q : U ⟶ W` of the site**, read as a
morphism of algebraic spaces, for a quasi-coherent module `F` on `h_U`. -/
abbrev schemeQuotSituation {U W : BigFppfOver B integerBase ℤS} (q : U ⟶ W)
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) : QuotSituation B integerBase ℤS where
  X := schemeSpace U
  Y := schemeSpace W
  f := schemeSpaceMap q
  F := F
  quasicoherent := hF
  finitePresentation := hq

/-- **`i^*𝒪(1)` on `h_U`** for a morphism `i : U ⟶ ℙⁿ_W` of the site: the inverse image of the
twisting module `𝒪(1)` of `ℙⁿ_ℤ` along `h_U ⟶ h_{ℙⁿ_W} ≅ h_W × ℙⁿ_ℤ ⟶ ℙⁿ_ℤ`. -/
abbrev projectiveTwist {U W : BigFppfOver B integerBase ℤS} {n : ℕ}
    (i : U ⟶ projectiveSite B n W) :
    Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2 :=
  (modulePullback B integerBase ℤS (schemeSpaceMap i ≫ (projectiveSiteProductIso n W).hom)).obj
    ((modulePullback B integerBase ℤS (productFst n (schemeSpace W))).obj (twistingModuleBase B n))

/-- The module `projectiveTwist i` is invertible. -/
instance isInvertible_projectiveTwist {U W : BigFppfOver B integerBase ℤS} {n : ℕ}
    (i : U ⟶ projectiveSite B n W) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS (schemeSpace U).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (schemeSpace U).1 (schemeSpace U).2).O)).property (projectiveTwist i) :=
  haveI := stacksIsInvertible_modulePullback_obj B integerBase ℤS
    (productFst n (schemeSpace W)) (twistingModuleBase B n)
  stacksIsInvertible_modulePullback_obj B integerBase ℤS _ _

variable (D : QuotSituation B integerBase B.contains_integerBase)

/-- **A subfunctor `Q` of the Quot presheaf is represented, over a scheme `W`, by a scheme
separated, locally of finite presentation and quasi-compact over `W`**: for a morphism
`ν : h_W ⟶ B` (in practice an identification), there are an object `Z` of the site, a morphism
`r : Z ⟶ W` whose morphism of schemes is separated, locally of finite presentation and
quasi-compact, and an identification `h_Z ≅ Q` under which the canonical morphism `Q ⟶ B` is
`h_r ≫ ν`. -/
def IsRepresentedSeparatedFinitePresentation (W : BigFppfOver B integerBase ℤS)
    (ν : yoneda.obj W ⟶ D.Y.obj) (Q : Subfunctor D.quotSitePresheaf) : Prop :=
  ∃ (Z : BigFppfOver B integerBase ℤS) (r : Z ⟶ W)
    (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅ Q.toFunctor),
    e.hom ≫ Q.ι ≫ D.quotSitePresheafToBase =
        Functor.whiskerRight (yoneda.map r ≫ ν) uliftFunctor.{u + 1, u} ∧
      _root_.AlgebraicGeometry.IsSeparated ((𝒯).map r) ∧
        LocallyOfFinitePresentation ((𝒯).map r) ∧ QuasiCompact ((𝒯).map r)

variable {D}

/-- Representability over `W` through `ν` transfers along an equality of subfunctors. -/
theorem IsRepresentedSeparatedFinitePresentation.of_eq {W : BigFppfOver B integerBase ℤS}
    {ν : yoneda.obj W ⟶ D.Y.obj} {Q Q' : Subfunctor D.quotSitePresheaf} (h : Q = Q')
    (hQ : D.IsRepresentedSeparatedFinitePresentation W ν Q) :
    D.IsRepresentedSeparatedFinitePresentation W ν Q' :=
  h ▸ hQ

/-- **Representability moves along an isomorphism of subfunctors over the base**: if `Q` is
represented over `W` through `ν`, and `i : Q ≅ Q'` is compatible with the canonical morphisms to
the bases through `φ : B ⟶ B'`, then `Q'` is represented over `W` through `ν ≫ φ`. -/
theorem IsRepresentedSeparatedFinitePresentation.of_iso {D' : QuotSituation B integerBase ℤS}
    {W : BigFppfOver B integerBase ℤS} {ν : yoneda.obj W ⟶ D.Y.obj}
    {ν' : yoneda.obj W ⟶ D'.Y.obj} (φ : D.Y.obj ⟶ D'.Y.obj) (hν : ν ≫ φ = ν')
    {Q : Subfunctor D.quotSitePresheaf} {Q' : Subfunctor D'.quotSitePresheaf}
    (i : Q.toFunctor ≅ Q'.toFunctor)
    (hi : i.hom ≫ Q'.ι ≫ D'.quotSitePresheafToBase =
      Q.ι ≫ D.quotSitePresheafToBase ≫ Functor.whiskerRight φ uliftFunctor.{u + 1, u})
    (hQ : D.IsRepresentedSeparatedFinitePresentation W ν Q) :
    D'.IsRepresentedSeparatedFinitePresentation W ν' Q' := by
  obtain ⟨Z, r, e, he, hr⟩ := hQ
  refine ⟨Z, r, e ≪≫ i, ?_, hr⟩
  rw [Iso.trans_hom, Category.assoc, hi, ← hν]
  simp only [← Category.assoc] at he ⊢
  rw [he]
  simp only [Functor.whiskerRight_comp, Category.assoc]

end AlgebraicGeometry.Space.QuotSituation

end
