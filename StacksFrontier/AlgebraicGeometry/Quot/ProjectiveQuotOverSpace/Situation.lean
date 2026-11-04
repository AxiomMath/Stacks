/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteSituation

/-!
# The Quot situation of a module on `B × ℙⁿ_ℤ` over an algebraic space `B`

Stacks 0DPB is about an algebraic space `B`, the product `X = B × ℙⁿ_ℤ` and an `𝒪_X`-module `ℱ`
of finite presentation.  On the big fppf site over `Spec ℤ` (`AlgebraicGeometry.integerBase`)
this file builds that situation: `X` is the fibre product of the structure morphism
`ℙⁿ_ℤ ⟶ Spec ℤ` (the morphism of `AlgebraicGeometry.ProjectiveQuot.quotSituation`) with the
unique morphism `B ⟶ Spec ℤ`, and `X ⟶ B` is the second projection, of finite presentation as a
base change of `ℙⁿ_ℤ ⟶ Spec ℤ`.

For a test scheme `T` over `B` the base change `X_T = X ×_B T` is identified with the algebraic
space represented by the scheme `ℙⁿ_T`: both are base changes of `ℙⁿ_ℤ ⟶ Spec ℤ` along the unique
morphism `T ⟶ Spec ℤ` (pasting of cartesian squares).  Under these identifications the morphisms
of base changes induced by morphisms of test schemes are the morphisms of projective spaces.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuotOverSpace.toBaseSpace`: the unique morphism `B ⟶ Spec ℤ`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.productSpace`: `X = B × ℙⁿ_ℤ`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.situation`: the Quot situation `ℱ/X/B` of
  Stacks 09TR at the data of Stacks 0DPB.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.spaceIso`: `h_{ℙⁿ_T} ≅ X_T`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.spaceIso_hom_relativeMap`: the morphisms of base
  changes are the morphisms of projective spaces.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} (n : ℕ)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-! ### The product `B × ℙⁿ_ℤ` -/

/-- The presheaf represented by the base `Spec ℤ` is terminal among presheaves on the site. -/
def isTerminal_yoneda_siteBase :
    IsTerminal (yoneda.obj (siteBase B)) :=
  IsTerminal.isTerminalObj yoneda _ (isTerminal_siteBase B)

/-- **The unique morphism `B ⟶ Spec ℤ`** of an algebraic space over `Spec ℤ`. -/
def toBaseSpace (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    Y ⟶ schemeSpace (siteBase B) :=
  ObjectProperty.homMk (isTerminal_yoneda_siteBase.from Y.obj)

/-- **`X = B × ℙⁿ_ℤ`**, the fibre product of `ℙⁿ_ℤ ⟶ Spec ℤ` with `B ⟶ Spec ℤ`. -/
abbrev productSpace (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    AlgebraicSpaces B integerBase B.contains_integerBase :=
  AlgebraicSpaces.fiberProduct B integerBase B.contains_integerBase
    (quotSituation B n 0).f (toBaseSpace Y)

/-- The first projection `B × ℙⁿ_ℤ ⟶ ℙⁿ_ℤ`. -/
abbrev productFst (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    productSpace n Y ⟶ (quotSituation B n 0).X :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The second projection `B × ℙⁿ_ℤ ⟶ B`, the morphism of the situation. -/
abbrev productSnd (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    productSpace n Y ⟶ Y :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The square formed by the two projections of `B × ℙⁿ_ℤ`, the structure morphism
`ℙⁿ_ℤ ⟶ Spec ℤ` and the unique morphism `B ⟶ Spec ℤ` is cartesian. -/
theorem isPullback_productSpace (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    IsPullback (productFst n Y) (productSnd n Y) (quotSituation B n 0).f (toBaseSpace Y) :=
  AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase _ _

/-- The projection `B × ℙⁿ_ℤ ⟶ B` is of finite presentation, as a base change of
`ℙⁿ_ℤ ⟶ Spec ℤ`. -/
theorem isFinitePresentation_productSnd (Y : AlgebraicSpaces B integerBase B.contains_integerBase) :
    Space.IsFinitePresentation B integerBase B.contains_integerBase (productSnd n Y).hom :=
  (Space.isFinitePresentation_isStableUnderBaseChange B integerBase
    B.contains_integerBase).of_isPullback (isPullback_productSpace n Y)
    (quotSituation B n 0).finitePresentation

/-- **The Quot situation of Stacks 0DPB**: the projection `X = B × ℙⁿ_ℤ ⟶ B` together with a
quasi-coherent `𝒪_X`-module `ℱ` (Stacks 09TR). -/
abbrev situation (Y : AlgebraicSpaces B integerBase B.contains_integerBase)
    (F : Space.Modules.{u, u} B integerBase B.contains_integerBase (productSpace n Y).1
      (productSpace n Y).2) (hF : F.IsQuasicoherentOnSite) :
    Space.QuotSituation B integerBase B.contains_integerBase where
  X := productSpace n Y
  Y := Y
  f := productSnd n Y
  F := F
  quasicoherent := hF
  finitePresentation := isFinitePresentation_productSnd n Y

/-! ### Projective frames -/

variable (B) in
/-- **A projective frame** on a Quot situation `F/X/Y` over `Spec ℤ`: a cartesian square
exhibiting `X ⟶ Y` as the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along the unique morphism
`Y ⟶ Spec ℤ`, that is, an identification `X = Y × ℙⁿ_ℤ` over `Y`. -/
structure ProjectiveFrame (D : Space.QuotSituation B integerBase B.contains_integerBase) where
  /-- The projection `X ⟶ ℙⁿ_ℤ`. -/
  toProjective : D.X ⟶ (quotSituation B n 0).X
  /-- The square is cartesian. -/
  isPullback : IsPullback toProjective D.f (quotSituation B n 0).f (toBaseSpace D.Y)

/-- The situation of Stacks 0DPB carries its projective frame. -/
def situationFrame (Y : AlgebraicSpaces B integerBase B.contains_integerBase)
    (F : Space.Modules.{u, u} B integerBase B.contains_integerBase (productSpace n Y).1
      (productSpace n Y).2) (hF : F.IsQuasicoherentOnSite) :
    ProjectiveFrame B n (situation n Y F hF) :=
  ⟨productFst n Y, isPullback_productSpace n Y⟩

/-! ### The base changes are projective spaces -/

variable {n} {D : Space.QuotSituation B integerBase B.contains_integerBase}
  (E : ProjectiveFrame B n D)

/-- The composite `T ⟶ B ⟶ Spec ℤ` is the morphism represented by `T ⟶ Spec ℤ`. -/
theorem hom_comp_toBaseSpace (T : Space.SchemesOver D.Y) :
    T.hom ≫ toBaseSpace D.Y = schemeSpaceMap (toSiteBase B T.left) :=
  Subsingleton.elim (α := (schemeSpaceFunctor B integerBase B.contains_integerBase).obj T.left ⟶
    schemeSpace (siteBase B)) _ _

/-- `X_T ⟶ ℙⁿ_ℤ` and `X_T ⟶ T` exhibit `X_T` as the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along
`T ⟶ Spec ℤ` (pasting). -/
theorem isPullback_space (T : Space.SchemesOver D.Y) :
    IsPullback (D.sourceProjection T ≫ E.toProjective)
      (D.projection T) (quotSituation B n 0).f
      (schemeSpaceMap (toSiteBase B T.left)) := by
  have h₁ : IsPullback (D.sourceProjection T)
      (D.projection T) (D.f) T.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B integerBase B.contains_integerBase
      (D.f) T.hom
  rw [← hom_comp_toBaseSpace T]
  exact h₁.paste_horiz E.isPullback

/-- **The base change `X_T` of `X = B × ℙⁿ_ℤ` is the algebraic space of `ℙⁿ_T`.** -/
def spaceIso (T : Space.SchemesOver D.Y) :
    schemeSpace (projectiveSite B n T.left) ≅ D.space T :=
  (isPullback_projectiveSiteSpace (r := 0) T.left).isoIsPullback _ _ (isPullback_space E T)

/-- Under `spaceIso`, the projection `X_T ⟶ X ⟶ ℙⁿ_ℤ` is the morphism `ℙⁿ_T ⟶ ℙⁿ_ℤ` induced by
`T ⟶ Spec ℤ`. -/
@[reassoc (attr := simp)]
theorem spaceIso_hom_sourceProjection_toProjective (T : Space.SchemesOver D.Y) :
    (spaceIso E T).hom ≫ D.sourceProjection T ≫ E.toProjective =
      schemeSpaceMap (projectiveSiteMap B n (toSiteBase B T.left)) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Under `spaceIso`, the projection `X_T ⟶ T` is the structure morphism `ℙⁿ_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem spaceIso_hom_projection (T : Space.SchemesOver D.Y) :
    (spaceIso E T).hom ≫ D.projection T =
      schemeSpaceMap (projectiveSiteStructure B n T.left) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The morphisms of base changes are the morphisms of projective spaces.** -/
theorem spaceIso_hom_relativeMap {T' T : Space.SchemesOver D.Y} (h : T' ⟶ T) :
    (spaceIso E T').hom ≫ D.relativeMap h =
      schemeSpaceMap (projectiveSiteMap B n h.left) ≫ (spaceIso E T).hom := by
  refine (isPullback_space E T).hom_ext ?_ ?_
  · rw [Category.assoc, Space.baseChangeMap_comp_projection_assoc,
      spaceIso_hom_sourceProjection_toProjective, Category.assoc,
      spaceIso_hom_sourceProjection_toProjective]
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map _ = yoneda.map _ ≫ yoneda.map _
    rw [← Functor.map_comp, ← projectiveSiteMap_comp]
    exact congrArg (fun k => yoneda.map (projectiveSiteMap B n k))
      ((isTerminal_siteBase B).hom_ext _ _)
  · rw [Category.assoc, Space.baseChangeMap_comp_inclusion, ← Category.assoc,
      spaceIso_hom_projection, Category.assoc, spaceIso_hom_projection]
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
    rw [← Functor.map_comp, ← Functor.map_comp, (isPullback_projectiveSite B n h.left).w]

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
