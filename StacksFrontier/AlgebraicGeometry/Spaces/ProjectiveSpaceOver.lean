module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Size.UniversallyClosedCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted

/-!
# Relative projective space over an algebraic space

Projective `n`-space over a presheaf `X` on the big fppf site of `S` is the product of `X` with
the restricted functor of points of projective `n`-space over `S`, exactly as relative affine
`n`-space `AlgebraicGeometry.Space.affineSpaceOver` is the product of `X` with the restricted
functor of points of affine `n`-space over `S`.  The standard affine chart `D₊(T₀)` of
projective space gives a morphism from relative affine `n`-space to relative projective
`n`-space over `X`, and it is an open immersion.

## Main definitions

* `AlgebraicGeometry.Space.projectiveSpaceOver` is relative projective `n`-space over a
  presheaf on the big fppf site of `S`.
* `AlgebraicGeometry.Space.affineSpaceOverToProjectiveSpaceOver` is the standard open chart
  `𝔸ⁿ_X ⟶ ℙⁿ_X`, over `X`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_affineSpaceOverToProjectiveSpaceOver`: the standard
  chart is an open immersion.
* `AlgebraicGeometry.Space.affineSpaceOverToProjectiveSpaceOver_fst`: it lies over `X`.

## Implementation notes

Projective `n`-space over `S` belongs to the big fppf site, by
`AlgebraicGeometry.Space.contains_projectiveSpaceOver`, and so does affine `n`-space.  The
open-immersion property of the chart is therefore the image under the Yoneda embedding of a
morphism of the site whose underlying scheme morphism is the open immersion
`AlgebraicGeometry.projectiveSpaceOver.affineChart`, followed by the product with `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative projective `n`-space over a presheaf on the big fppf site of `S`**: the product
of the presheaf with the restricted functor of points
`AlgebraicGeometry.Space.projectiveSpaceFunctor` of projective `n`-space over `S`.

The first projection is the structure morphism. -/
noncomputable abbrev projectiveSpaceOver
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  X ⨯ projectiveSpaceFunctor B S hS n

/-- The index equivalence of the standard chart `D₊(T₀)` of projective `n`-space. -/
noncomputable abbrev standardChartEquiv (n : ℕ) :
    ULift.{u} (Fin n) ≃ {j : Fin (n + 1) // j ≠ 0} :=
  Equiv.ulift.trans (finSuccAboveEquiv 0)

/-- The standard chart `D₊(T₀)` of projective `n`-space over `S`, as a morphism of schemes over
`S` from affine `n`-space. -/
noncomputable abbrev standardChartOver (n : ℕ) :
    Over.mk (AffineSpace.over (ULift.{u} (Fin n)) S).hom ⟶
      Over.mk (_root_.AlgebraicGeometry.projectiveSpaceOver n S ↘ S) :=
  Over.homMk (_root_.AlgebraicGeometry.projectiveSpaceOver.affineChart n 0 (standardChartEquiv n) S)
    (_root_.AlgebraicGeometry.projectiveSpaceOver.affineChart_over n 0 (standardChartEquiv n) S)

/-- **The standard open chart `𝔸ⁿ_X ⟶ ℙⁿ_X`** over a presheaf `X` on the big fppf site of
`S`: the product of `X` with the standard chart `D₊(T₀)` of projective `n`-space over `S`. -/
noncomputable def affineSpaceOverToProjectiveSpaceOver
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) :
    affineSpaceOver B S hS X n ⟶ projectiveSpaceOver B S hS X n :=
  prod.map (𝟙 X) ((Over.post B.inclusion).op.whiskerLeft (yoneda.map (standardChartOver S n)))

/-- The standard open chart lies over `X`. -/
@[reassoc (attr := simp)]
theorem affineSpaceOverToProjectiveSpaceOver_fst
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) :
    affineSpaceOverToProjectiveSpaceOver B S hS X n ≫ prod.fst = prod.fst := by
  simp [affineSpaceOverToProjectiveSpaceOver]

/-- The standard chart `D₊(T₀)` of projective `n`-space over `S`, as a morphism of the big fppf
category over `S`: affine and projective `n`-space over `S` are both objects of the site. -/
noncomputable abbrev standardChartSite (n : ℕ) :
    (Over.mk (ObjectProperty.homMk (X := B.obj (B.contains_affineSpace hS n)) (Y := B.obj hS)
        (AffineSpace.over (ULift.{u} (Fin n)) S).hom) : BigFppfOver B S hS) ⟶
      Over.mk (ObjectProperty.homMk (X := B.obj (contains_projectiveSpaceOver B S hS n))
        (Y := B.obj hS) (_root_.AlgebraicGeometry.projectiveSpaceOver n S ↘ S)) :=
  Over.homMk (ObjectProperty.homMk
      (_root_.AlgebraicGeometry.projectiveSpaceOver.affineChart n 0 (standardChartEquiv n) S))
    (ObjectProperty.hom_ext _
      (_root_.AlgebraicGeometry.projectiveSpaceOver.affineChart_over n 0 (standardChartEquiv n) S))

/-- The standard chart of projective `n`-space over `S`, on restricted functors of points, is an
open immersion of presheaves on the big fppf site of `S`. -/
theorem isOpenImmersion_standardChartPoints (n : ℕ) :
    IsOpenImmersion B S hS
      ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map (standardChartOver S n))) := by
  let T := BigFppfOver.toScheme B S hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u}) T
  have : Q.IsStableUnderBaseChange := ⟨by
    intro W Y Z T' f' g' f g h hf
    exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion.{u})
      (h.map T) hf⟩
  have : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Q.presheaf.RespectsIso := inferInstance
  let c := standardChartSite B S hS n
  have hc : IsOpenImmersion B S hS (yoneda.map c) := by
    apply MorphismProperty.relative_map (P := Q)
    change _root_.AlgebraicGeometry.IsOpenImmersion
      (_root_.AlgebraicGeometry.projectiveSpaceOver.affineChart n 0 (standardChartEquiv n) S)
    infer_instance
  have heq : F.op.whiskerLeft (yoneda.map (standardChartOver S n)) =
      (F ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ (Type u)).obj F.op).map c := rfl
  rw [heq]
  exact (MorphismProperty.arrow_mk_iso_iff Q.presheaf
    (Arrow.isoOfNatIso (restrictedYonedaIso F) (Arrow.mk c))).mpr hc

/-- The product with a presheaf `X` of an open immersion of presheaves is an open immersion. -/
theorem isOpenImmersion_prod_map_id (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z) (hg : IsOpenImmersion B S hS g) :
    IsOpenImmersion B S hS (prod.map (𝟙 X) g) := by
  have sq : IsPullback prod.snd (prod.map (𝟙 X) g) g prod.snd := by
    apply (IsPullback.of_prod_fst_with_id g X).of_iso'
      (prod.braiding X Y) (Iso.refl _) (prod.braiding X Z) (Iso.refl _)
    all_goals ext <;> simp
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
    (BigFppfOver.toScheme B S hS)
  have : Q.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange Q
  exact MorphismProperty.of_isPullback (P := Q.presheaf) sq hg

/-- **The standard chart `𝔸ⁿ_X ⟶ ℙⁿ_X` is an open immersion**, for any presheaf `X` on the big
fppf site of `S`. -/
theorem isOpenImmersion_affineSpaceOverToProjectiveSpaceOver
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) :
    IsOpenImmersion B S hS (affineSpaceOverToProjectiveSpaceOver B S hS X n) :=
  isOpenImmersion_prod_map_id B S hS X _ (isOpenImmersion_standardChartPoints B S hS n)

end AlgebraicGeometry.Space

end
