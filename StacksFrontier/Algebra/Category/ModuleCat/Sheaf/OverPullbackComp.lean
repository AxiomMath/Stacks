module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictCompCoherence

/-!
# Restriction along a composite of arrows of the site, read on the right adjoints

For a site `(C, J)` with fibre products and a sheaf of rings `R`, restriction of sheaves of
`R`-modules along an arrow `f : V ⟶ U` of `C` is `SheafOfModules.overMap R f`, and
`SheafOfModules.overMapPushforwardAdj` exhibits it as a *left* adjoint, with right adjoint
`SheafOfModules.overPullback R f`, the pushforward along `CategoryTheory.Over.pullback f`.

`Stacks.SheafOfModules.overMapCompIso` compares restriction along `f` followed by restriction
along `g : W ⟶ V` with restriction along `g ≫ f`.  This file records the corresponding
comparison of the *right* adjoints,

    `overPullback R (g ≫ f) ≅ overPullback R g ⋙ overPullback R f`,

and identifies it as the mate of `Stacks.SheafOfModules.overMapCompIso`.

## Main definitions

* `Stacks.SheafOfModules.overPullbackComp`: `SheafOfModules.overPullback` turns a composite of
  arrows of the site into the composite of the two functors, in the other order.
* `Stacks.SheafOfModules.overPullbackCongr`: `SheafOfModules.overPullback` along equal arrows of
  the site agrees.

## Main results

* `Stacks.SheafOfModules.conjugateIsoEquiv_overMapCompIso` and
  `Stacks.SheafOfModules.conjugateIsoEquiv_symm_overPullbackComp`: the two comparisons are
  mates of one another, with respect to the adjunction
  `SheafOfModules.overMapPushforwardAdj` at `g ≫ f` and the composite of those at `f` and at `g`.
* `Stacks.SheafOfModules.conjugateIsoEquiv_overMapCongrIso`: the mate of the congruence
  isomorphism of restriction is the congruence isomorphism of `SheafOfModules.overPullback`.
* `Stacks.SheafOfModules.conjugateIsoEquiv_overMapCompIso_trans_overMapCongrIso`: the mate of a
  composition comparison followed by a congruence.

## Implementation notes

`Stacks.SheafOfModules.overPullbackComp` is defined as the conjugate of
`Stacks.SheafOfModules.overMapCompIso`, as `CategoryTheory.Over.pullbackComp` is defined as the
conjugate of `CategoryTheory.Over.mapComp`, so `conjugateIsoEquiv_overMapCompIso` holds by `rfl`.

Nothing in this file unfolds `SheafOfModules.overMap` or `SheafOfModules.overPullback`: those
functors are pushforwards along reducible slice-category constructions, and unfolding them at a
concrete structure sheaf exhausts the elaborator's budget.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) {U V W : C}

/-! ### Restriction along equal arrows, on the right adjoints -/

/-- For equal arrows `a = b : W ⟶ U` of the site, the transport
`SheafOfModules.overPullback R a ≅ SheafOfModules.overPullback R b`. -/
public noncomputable def overPullbackCongr {a b : W ⟶ U} (e : a = b) :
    SheafOfModules.overPullback.{w} R a ≅ SheafOfModules.overPullback.{w} R b :=
  eqToIso (congrArg (fun k : W ⟶ U => SheafOfModules.overPullback.{w} R k) e)

/-- The congruence isomorphism of a reflexive equality of arrows is the identity. -/
@[simp] public theorem overPullbackCongr_refl (a : W ⟶ U) :
    overPullbackCongr R (rfl : a = a) = Iso.refl (SheafOfModules.overPullback.{w} R a) :=
  eqToIso_refl _

/-- The mate of the congruence isomorphism of restriction along `e : a = b` is the inverse of the
congruence isomorphism of `SheafOfModules.overPullback` along `e`. -/
public theorem conjugateIsoEquiv_overMapCongrIso {a b : W ⟶ U} (e : a = b) :
    conjugateIsoEquiv (SheafOfModules.overMapPushforwardAdj R b)
        (SheafOfModules.overMapPushforwardAdj R a) (overMapCongrIso R e) =
      (overPullbackCongr R e).symm := by
  subst e
  rw [← overMap_eqToIso, eqToIso_refl, overPullbackCongr_refl, Iso.refl_symm]
  exact Iso.ext (by simp)

/-! ### Restriction along a composite, on the right adjoints -/

/-- For `f : V ⟶ U` and `g : W ⟶ V`, the isomorphism

    `overPullback R (g ≫ f) ≅ overPullback R g ⋙ overPullback R f`,

defined as the mate of `Stacks.SheafOfModules.overMapCompIso` with respect to the adjunctions
`SheafOfModules.overMapPushforwardAdj`. -/
public noncomputable def overPullbackComp (f : V ⟶ U) (g : W ⟶ V) :
    SheafOfModules.overPullback.{w} R (g ≫ f) ≅
      SheafOfModules.overPullback.{w} R g ⋙ SheafOfModules.overPullback.{w} R f :=
  conjugateIsoEquiv (SheafOfModules.overMapPushforwardAdj R (g ≫ f))
    ((SheafOfModules.overMapPushforwardAdj R f).comp
      (SheafOfModules.overMapPushforwardAdj R g))
    (overMapCompIso R f g)

/-- The mate of the composition comparison `Stacks.SheafOfModules.overMapCompIso` of restriction
is the composition comparison `Stacks.SheafOfModules.overPullbackComp` of
`SheafOfModules.overPullback`. -/
public theorem conjugateIsoEquiv_overMapCompIso (f : V ⟶ U) (g : W ⟶ V) :
    conjugateIsoEquiv (SheafOfModules.overMapPushforwardAdj R (g ≫ f))
        ((SheafOfModules.overMapPushforwardAdj R f).comp
          (SheafOfModules.overMapPushforwardAdj R g)) (overMapCompIso R f g) =
      overPullbackComp R f g :=
  rfl

/-- The composition comparison `Stacks.SheafOfModules.overMapCompIso` of restriction is the
inverse mate of `Stacks.SheafOfModules.overPullbackComp`. -/
public theorem conjugateIsoEquiv_symm_overPullbackComp (f : V ⟶ U) (g : W ⟶ V) :
    (conjugateIsoEquiv (SheafOfModules.overMapPushforwardAdj R (g ≫ f))
          ((SheafOfModules.overMapPushforwardAdj R f).comp
            (SheafOfModules.overMapPushforwardAdj R g))).symm (overPullbackComp R f g) =
      overMapCompIso R f g :=
  (conjugateIsoEquiv _ _).symm_apply_apply _

/-- For `f : V ⟶ U`, `g : W ⟶ V` and `e : g ≫ f = a`, the mate of

    `overMap R f ⋙ overMap R g ≅ overMap R (g ≫ f) ≅ overMap R a`

is the congruence isomorphism of `SheafOfModules.overPullback` from `a` to `g ≫ f` followed by
`Stacks.SheafOfModules.overPullbackComp`. -/
public theorem conjugateIsoEquiv_overMapCompIso_trans_overMapCongrIso (f : V ⟶ U) (g : W ⟶ V)
    {a : W ⟶ U} (e : g ≫ f = a) :
    conjugateIsoEquiv (SheafOfModules.overMapPushforwardAdj R a)
        ((SheafOfModules.overMapPushforwardAdj R f).comp
          (SheafOfModules.overMapPushforwardAdj R g))
        (overMapCompIso R f g ≪≫ overMapCongrIso R e) =
      overPullbackCongr R e.symm ≪≫ overPullbackComp R f g := by
  subst e
  rw [← overMap_eqToIso, eqToIso_refl, Iso.trans_refl, overPullbackCongr_refl, Iso.refl_trans]
  exact conjugateIsoEquiv_overMapCompIso R f g

end Stacks.SheafOfModules

end
