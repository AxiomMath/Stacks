module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionFieldFibre

/-!
# The fibre dimension under base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is of finite type and
let `g : Y' ⟶ Y` be arbitrary. The fibre-dimension function of the base change
`X ×_Y Y' ⟶ Y'` is the fibre-dimension function of `f` composed with the map `|Y'| → |Y|`:
base change does not change the fibres.

## Main results

* `AlgebraicGeometry.Space.fiberDimension_pullback_snd` is **Stacks 0D4N**.

## Implementation notes

Both sides are computed at a point of `|Y'|` by Stacks 0D4M, as the dimension of a fibre over a
field-valued representative `p` of that point. The two fibres, `(X ×_Y Y') ×_{Y'} Spec k` and
`X ×_Y Spec k`, are isomorphic by the pasting of pullback squares, and isomorphic algebraic
spaces have the same dimension.

## References

* [Stacks Project, Tag 0D4N](https://stacks.math.columbia.edu/tag/0D4N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0D4N.** The fibre-dimension function of the base change of a finite type morphism of
algebraic spaces over `S` is the pullback of the fibre-dimension function of the morphism along
the map on points of the morphism of targets. -/
@[stacks 0D4N]
theorem fiberDimension_pullback_snd {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (hf : IsFiniteType B S hS f) :
    fiberDimension B S hS (pullback.snd f g) =
      fiberDimension B S hS f ∘ pointsMap B S hS Y' g := by
  classical
  have hXY' : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hY' hY
  have hfg : IsFiniteType B S hS (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) ↦ IsFiniteType B S hS k.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) hf
  funext y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  set a : yoneda.obj (p.siteObject B S hS Y') ⟶ Y' := yonedaEquiv.symm p.value with hadef
  set q := FieldValuedPoint.map B S hS Y' g p with hqdef
  have hvalue : yonedaEquiv.symm q.value = a ≫ g :=
    (yonedaEquiv_symm_naturality_right (p.siteObject B S hS Y') g p.value).symm
  have hleft := (fiberDimension_eq_dimension_pullback B S hS (pullback.snd f g) hXY' hY' hfg p).1
  have hright := (fiberDimension_eq_dimension_pullback B S hS f hX hY hf q).1
  rw [hvalue] at hright
  have hdim := dimension_eq_of_iso B S hS
    (isAlgebraicSpace_pullback B S hS a (pullback.snd f g)
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y')) hXY' hY')
    (isAlgebraicSpace_pullback B S hS (a ≫ g) f
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y')) hX hY)
    ((pullbackSymmetry a (pullback.snd f g)).trans
      ((pullbackLeftPullbackSndIso f g a).trans (pullbackSymmetry f (a ≫ g))))
  exact hleft.trans (hdim.trans hright.symm)

end AlgebraicGeometry.Space

end
