module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare

/-!
# Restricting the stages of a limit along a morphism of the base

For presheaves `p : X ⟶ X₀`, `w : W₀ ⟶ X₀` and `y : Y₀ ⟶ W₀`, the fibre product
`X ×_{X₀} Y₀` maps to `X ×_{X₀} W₀` (`AlgebraicGeometry.Space.baseChangeOverRestrict`), and this
map is the base change of `y` along the projection `X ×_{X₀} W₀ ⟶ W₀`. For a morphism
`a : X ⟶ X'` over `X₀` the square formed with the base changes of `a` is cartesian. When
`Yᵢ ⟶ X' ×_{X₀} W₀` is any base change of `y` along the projection, the square with `Yᵢ` in
place of `X' ×_{X₀} Y₀` is still cartesian.

For a subfunctor `U ⊆ W₀`, a morphism `f : V₀ ⟶ W₀` and `s : W' ⟶ W₀`, the intersection of `s⁻¹U`
and `V₀ ×_{W₀} W'` is the base change along `s` of `U ×_{W₀} V₀`
(`AlgebraicGeometry.Space.isPullback_preimage_inter`).

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for these presheaf-category limit instances exceeds the default budget
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_RestrictedStagesEtaleSquares :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site over `S` exists. -/
local instance (priority := high) hasPullback_presheaf_RestrictedStagesEtaleSquares
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Restrict

variable {X X' X₀ Y₀ W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (y : Y₀ ⟶ W₀) (w : W₀ ⟶ X₀)

/-- The morphism `X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀` induced by `y : Y₀ ⟶ W₀`. -/
def baseChangeOverRestrict (p : X ⟶ X₀) : pullback p (y ≫ w) ⟶ pullback p w :=
  pullback.lift (pullback.fst p (y ≫ w)) (pullback.snd p (y ≫ w) ≫ y)
    (by rw [pullback.condition, Category.assoc])

/-- The first projection of `baseChangeOverRestrict` is the first projection of `X ×_{X₀} Y₀`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverRestrict_fst (p : X ⟶ X₀) :
    baseChangeOverRestrict B S hS y w p ≫ pullback.fst p w = pullback.fst p (y ≫ w) :=
  pullback.lift_fst _ _ _

/-- The second projection of `baseChangeOverRestrict` is the second projection of `X ×_{X₀} Y₀`
followed by `y`. -/
@[reassoc (attr := simp)]
theorem baseChangeOverRestrict_snd (p : X ⟶ X₀) :
    baseChangeOverRestrict B S hS y w p ≫ pullback.snd p w = pullback.snd p (y ≫ w) ≫ y :=
  pullback.lift_snd _ _ _

/-- `X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀` is the base change of `y` along the projection to `W₀`. -/
theorem isPullback_baseChangeOverRestrict (p : X ⟶ X₀) :
    IsPullback (baseChangeOverRestrict B S hS y w p) (pullback.snd p (y ≫ w))
      (pullback.snd p w) y := by
  refine IsPullback.of_right ?_ (baseChangeOverRestrict_snd B S hS y w p)
    (IsPullback.of_hasPullback p w)
  rw [baseChangeOverRestrict_fst]
  exact IsPullback.of_hasPullback p (y ≫ w)

/-- Restriction along `y` commutes with the base changes of a morphism `a : X ⟶ X'` over `X₀`. -/
theorem baseChangeOverRestrict_comp_baseChangeOverMap (p : X ⟶ X₀) (p' : X' ⟶ X₀) (a : X ⟶ X')
    (hcomm : a ≫ p' = p) :
    baseChangeOverRestrict B S hS y w p ≫ baseChangeOverMap B S hS p p' a hcomm w =
      baseChangeOverMap B S hS p p' a hcomm (y ≫ w) ≫ baseChangeOverRestrict B S hS y w p' := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **The square of a morphism over `X₀` and a base change of `y`.** If `Yᵢ`, with
`j : Yᵢ ⟶ X' ×_{X₀} W₀` and `q : Yᵢ ⟶ Y₀`, is a base change of `y` along the projection, then
`X ×_{X₀} Y₀ ⟶ X ×_{X₀} W₀` is the base change of `j` along `X ×_{X₀} W₀ ⟶ X' ×_{X₀} W₀`, the
map to `Yᵢ` being the base change of `a` followed by the comparison `X' ×_{X₀} Y₀ ⟶ Yᵢ`. -/
theorem isPullback_baseChangeOverMap_comp_lift (p : X ⟶ X₀) (p' : X' ⟶ X₀) (a : X ⟶ X')
    (hcomm : a ≫ p' = p) {Yᵢ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : Yᵢ ⟶ pullback p' w)
    (q : Yᵢ ⟶ Y₀) (hY : IsPullback j q (pullback.snd p' w) y) :
    IsPullback (baseChangeOverRestrict B S hS y w p)
      (baseChangeOverMap B S hS p p' a hcomm (y ≫ w) ≫
        hY.lift (baseChangeOverRestrict B S hS y w p') (pullback.snd p' (y ≫ w))
          (baseChangeOverRestrict_snd B S hS y w p'))
      (baseChangeOverMap B S hS p p' a hcomm w) j := by
  refine IsPullback.of_bot ?_ ?_ hY
  · rw [Category.assoc, IsPullback.lift_snd, baseChangeOverMap_snd, baseChangeOverMap_snd]
    exact isPullback_baseChangeOverRestrict B S hS y w p
  · rw [Category.assoc, IsPullback.lift_fst, baseChangeOverRestrict_comp_baseChangeOverMap]

end Restrict

section Pieces

variable {W₀ V₀ W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor W₀) (f : V₀ ⟶ W₀)
  (s : W' ⟶ W₀)

/-- **The intersection of the pieces of a base-changed square is a base change.** For
`U ⊆ W₀`, `f : V₀ ⟶ W₀` and `s : W' ⟶ W₀`, the intersection `s⁻¹U ×_{W'} (V₀ ×_{W₀} W')` is the
base change along `s` of `U ×_{W₀} V₀ ⟶ W₀`. -/
theorem isPullback_preimage_inter :
    IsPullback (pullback.fst (U.preimage s).ι (pullback.snd f s) ≫ (U.preimage s).ι)
      (pullback.lift (pullback.fst (U.preimage s).ι (pullback.snd f s) ≫ U.fromPreimage s)
        (pullback.snd (U.preimage s).ι (pullback.snd f s) ≫ pullback.fst f s) (by
          rw [Category.assoc, Category.assoc, (Subfunctor.isPullback_preimage s U).w,
            pullback.condition_assoc, pullback.condition (f := f) (g := s)]))
      s (pullback.fst U.ι f ≫ U.ι) := by
  have hU := Subfunctor.isPullback_preimage s U
  have outer := (IsPullback.of_hasPullback (U.preimage s).ι (pullback.snd f s)).flip.paste_horiz
    (IsPullback.of_hasPullback f s)
  refine (IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback U.ι f).flip).flip.paste_horiz hU.flip
  · rw [pullback.lift_snd, hU.w]
    exact outer
  · exact pullback.lift_fst _ _ _

end Pieces

end AlgebraicGeometry.Space
