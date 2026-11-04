module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecQuotientOverAffineBase

/-!
# Relative projective space over an algebraic space is representable over it

Let `Y` be a presheaf on the big fppf site of a scheme `S`.  The projection
`ℙⁿ_Y = Y × ℙⁿ_S ⟶ Y` of `AlgebraicGeometry.Space.projectiveSpaceOver` is representable.  It is
the base change of the structure morphism `ℙⁿ_S ⟶ S`, which is the image under the Yoneda
embedding of a morphism of the site, along `Y ⟶ S`.  Properness of the projection, for `Y` an
algebraic space, is `AlgebraicGeometry.Space.isProper_projectiveSpaceOver_fst`.

## Main results

* `AlgebraicGeometry.Space.isPullback_projectiveSpaceOver`: `ℙⁿ_Y` is the base change of
  `ℙⁿ_S ⟶ S` along `Y ⟶ S`.
* `AlgebraicGeometry.Space.relativelyRepresentable_projectiveSpaceOver_fst`: `ℙⁿ_Y ⟶ Y` is
  representable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of the restricted functor of points of `ℙⁿ_S` to the presheaf
represented by the base is the image under the Yoneda embedding of the structure morphism of
`ℙⁿ_S` as an object of the site. -/
theorem from_projectiveSpaceFunctor_eq (n : ℕ) :
    (isTerminal_yoneda_obj_base B S hS).from (projectiveSpaceFunctor B S hS n) =
      (projectiveSpaceFunctorIso B S hS n).hom ≫
        yoneda.map (toBaseTerminal B S hS (projectiveSpaceSiteObject B S hS n)) :=
  (isTerminal_yoneda_obj_base B S hS).hom_ext _ _

/-- `ℙⁿ_S ⟶ S` is representable, as a morphism of presheaves on the big fppf site of `S`. -/
theorem relativelyRepresentable_from_projectiveSpaceFunctor (n : ℕ) :
    yoneda.relativelyRepresentable
      ((isTerminal_yoneda_obj_base B S hS).from (projectiveSpaceFunctor B S hS n)) := by
  rw [from_projectiveSpaceFunctor_eq]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (Functor.relativelyRepresentable.map _
      (toBaseTerminal B S hS (projectiveSpaceSiteObject B S hS n)))

/-- `ℙⁿ_Y` is the base change of `ℙⁿ_S ⟶ S` along `Y ⟶ S`. -/
theorem isPullback_projectiveSpaceOver (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (n : ℕ) :
    IsPullback (prod.fst : projectiveSpaceOver B S hS Y n ⟶ Y) prod.snd
      ((isTerminal_yoneda_obj_base B S hS).from Y)
      ((isTerminal_yoneda_obj_base B S hS).from (projectiveSpaceFunctor B S hS n)) :=
  IsPullback.of_is_product (prodIsProd Y _) (isTerminal_yoneda_obj_base B S hS)

/-- **The projection `ℙⁿ_Y ⟶ Y` is representable**, being the base change of the morphism
`ℙⁿ_S ⟶ S` coming from a morphism of the site. -/
theorem relativelyRepresentable_projectiveSpaceOver_fst (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (n : ℕ) : yoneda.relativelyRepresentable (prod.fst : projectiveSpaceOver B S hS Y n ⟶ Y) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOver B S hS Y n).flip
    (relativelyRepresentable_from_projectiveSpaceFunctor B S hS n)

end AlgebraicGeometry.Space

end
