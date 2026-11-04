module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverPointVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionBaseChange

/-!
# The dimension of a base change to a one-point scheme

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is of finite type, and
let `c : T ⟶ Y` be a morphism from a scheme `T` whose underlying topological space has at most
one point, for example the spectrum of an Artinian local ring. Then the dimension of the
algebraic space `X ×_Y T` depends only on the image `y ∈ |Y|` of the point of `T`: it is the
dimension of the fibre `X_k = Spec k ×_Y X` over any field-valued point `Spec k ⟶ Y`
representing `y`, which is the fibre dimension of `f` at `y` (Stacks 0D4M).

This is how the infinitesimal neighbourhoods `X_n = Spec(𝒪_{Y,ȳ}/𝔪ⁿ) ×_Y X` of a geometric
fibre `X_ȳ` are seen to have the dimension of `X_ȳ`, as used in the proofs of Stacks 0A4S and
Stacks 0A4T.

## Main results

* `AlgebraicGeometry.Space.dimension_eq_fiberDimension_of_subsingleton`: over a representable
  base whose scheme has at most one point, the dimension of an algebraic space is the fibre
  dimension of its structure morphism at a point of the base.
* `AlgebraicGeometry.Space.dimension_pullback_eq_of_subsingleton`: the dimension of the base
  change of a finite type morphism to a one-point scheme is the dimension of the fibre over any
  field-valued point with the same image.

## Implementation notes

Over a one-point base the relative dimension at a point is the absolute dimension there,
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton`, so the
fibre dimension, an infimum of bounds for relative dimensions over the unique point, is the
supremum of the dimensions at points, which is the dimension. The base change statement then
follows from the invariance of the fibre dimension under base change (Stacks 0D4N) and its
computation on a field-valued point (Stacks 0D4M).

## References

* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
* [Stacks Project, Tag 0D4N](https://stacks.math.columbia.edu/tag/0D4N)
* [Stacks Project, Tag 0A4T](https://stacks.math.columbia.edu/tag/0A4T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Over a one-point base the dimension is the fibre dimension.** If `g : X ⟶ T` is a
morphism from an algebraic space to a representable presheaf whose scheme has at most one
point, then the dimension of `X` is the fibre dimension of `g` at a point of `T`. -/
theorem dimension_eq_fiberDimension_of_subsingleton {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    (hT : Subsingleton ((BigFppfOver.toScheme B S hS).obj T)) (g : X ⟶ yoneda.obj T)
    (t : points B S hS (yoneda.obj T)) :
    dimension B S hS X hX = fiberDimension B S hS g t := by
  refine le_antisymm (le_sInf fun d hd => iSup_le fun x => ?_)
    (sInf_le fun x _ => ?_)
  · obtain ⟨e, he, hed⟩ := hd x ((pointsEquivScheme B S hS T).injective (Subsingleton.elim _ _))
    rw [(hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton B S hS hX hT g x e).1 he]
    exact hed
  · have hne := dimensionAtPoint_ne_bot B S hS X hX x
    refine ⟨(dimensionAtPoint B S hS X hX x).unbot hne,
      (hasRelativeDimensionAt_iff_dimensionAtPoint_eq_of_subsingleton B S hS hX hT g x _).2
        (WithBot.coe_unbot _ hne).symm, ?_⟩
    rw [WithBot.coe_unbot]
    exact le_iSup (fun z => dimensionAtPoint B S hS X hX z) x

/-- **The dimension of a base change to a one-point scheme.** Let `f : X ⟶ Y` be a finite type
morphism of algebraic spaces, `c : T ⟶ Y` a morphism from a representable presheaf whose scheme
has at most one point `t`, and `p` a field-valued point of `Y` with the same image in `|Y|` as
`t`. Then `X ×_Y T` and the fibre `Spec k ×_Y X` of `f` over `p` have the same dimension. -/
theorem dimension_pullback_eq_of_subsingleton {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFiniteType B S hS f) {T : BigFppfOver B S hS}
    (hT : Subsingleton ((BigFppfOver.toScheme B S hS).obj T)) (c : yoneda.obj T ⟶ Y)
    (t : points B S hS (yoneda.obj T)) (p : FieldValuedPoint B S hS Y)
    (hp : pointsMap B S hS (yoneda.obj T) c t = p.class B S hS Y) :
    dimension B S hS (pullback f c)
        (isAlgebraicSpace_pullback B S hS f c hX (isAlgebraicSpace_yoneda B S hS T) hY) =
      dimension B S hS (pullback (yonedaEquiv.symm p.value) f)
        (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
          (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY) := by
  rw [dimension_eq_fiberDimension_of_subsingleton B S hS _ hT (pullback.snd f c) t,
    fiberDimension_pullback_snd B S hS f c hX hY (isAlgebraicSpace_yoneda B S hS T) hf,
    Function.comp_apply, hp]
  exact (fiberDimension_eq_dimension_pullback B S hS f hX hY hf p).1

end AlgebraicGeometry.Space

end
