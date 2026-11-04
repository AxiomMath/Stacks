module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Fibres of a pullback of topological spaces

For a pullback `X ×[Z] T` of topological spaces, the fibre of the second projection over a point
`t` of `T` is canonically homeomorphic to the fibre of the first map over the image of `t`.

## Main definitions

* `AlgebraicGeometry.ProEtale.fiber_pullback_snd_homeomorphic_fiber`: the canonical
  homeomorphism between the two fibres.

## Main results

* `AlgebraicGeometry.ProEtale.fiber_pullback_snd_homeomorphic_fiber_apply_coe`: on points, that
  homeomorphism is the first pullback projection.

## Implementation notes

The fibres are subtypes carrying their subspace topologies. The equation on the homeomorphism
records that it is induced by the first projection, which is what identifies it at later use
sites.
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory Limits

universe u

/-- Two points of a pullback of topological spaces with the same images under both projections
are equal. -/
private theorem pullback_point_ext {X T Z : TopCat.{u}} (f : X ⟶ Z) (g : T ⟶ Z)
    (x y : ↑(pullback f g)) (hfst : (pullback.fst f g) x = (pullback.fst f g) y)
    (hsnd : (pullback.snd f g) x = (pullback.snd f g) y) : x = y := by
  let cx : TopCat.of PUnit ⟶ pullback f g :=
    TopCat.ofHom ⟨fun _ => x, continuous_const⟩
  let cy : TopCat.of PUnit ⟶ pullback f g :=
    TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have h : cx = cy := pullback.hom_ext (by ext; exact hfst) (by ext; exact hsnd)
  exact ConcreteCategory.congr_hom h PUnit.unit

/-- The canonical homeomorphism from the fibre of the second projection of `X ×[Z] T` over `t`
to the fibre of `f` over `g t`. -/
noncomputable def fiber_pullback_snd_homeomorphic_fiber
    {X T Z : TopCat.{u}} (f : X ⟶ Z) (g : T ⟶ Z) (t : T) :
    { y : (pullback f g : TopCat.{u}) // (pullback.snd f g) y = t } ≃ₜ
      { x : X // f x = g t } :=
  let fiberX : TopCat := TopCat.of { x : X // f x = g t }
  let first : fiberX ⟶ X :=
    TopCat.ofHom ⟨fun x => x.1, continuous_subtype_val⟩
  let second : fiberX ⟶ T := TopCat.ofHom ⟨fun _ => t, continuous_const⟩
  have compat : first ≫ f = second ≫ g := by
    ext x
    exact x.2
  let lift : fiberX ⟶ pullback f g := pullback.lift first second compat
  let toFun : { y : (pullback f g : TopCat.{u}) // (pullback.snd f g) y = t } →
      { x : X // f x = g t } := fun y =>
    ⟨pullback.fst f g y.1, by
      simpa [y.2] using ConcreteCategory.congr_hom (pullback.condition (f := f) (g := g)) y.1⟩
  { toFun := toFun
    invFun := fun x => ⟨lift x, by
      simpa [lift, second] using
        ConcreteCategory.congr_hom (pullback.lift_snd first second compat) x⟩
    left_inv := fun y => by
      refine Subtype.ext (pullback_point_ext f g _ _ ?_ ?_)
      · simpa [lift, first, toFun] using
          ConcreteCategory.congr_hom (pullback.lift_fst first second compat) (toFun y)
      · simpa [lift, second, y.2] using
          ConcreteCategory.congr_hom (pullback.lift_snd first second compat) (toFun y)
    right_inv := fun x => Subtype.ext (by
      simpa [lift, first] using
        ConcreteCategory.congr_hom (pullback.lift_fst first second compat) x)
    continuous_toFun :=
      ((pullback.fst f g).hom.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := lift.hom.continuous.subtype_mk _ }

/-- On points, the canonical fibre homeomorphism is the first projection. -/
theorem fiber_pullback_snd_homeomorphic_fiber_apply_coe
    {X T Z : TopCat.{u}} (f : X ⟶ Z) (g : T ⟶ Z) (t : T)
    (y : { y : (pullback f g : TopCat.{u}) // (pullback.snd f g) y = t }) :
    ((fiber_pullback_snd_homeomorphic_fiber f g t) y).1 =
      (pullback.fst f g) y.1 :=
  rfl

end AlgebraicGeometry.ProEtale
