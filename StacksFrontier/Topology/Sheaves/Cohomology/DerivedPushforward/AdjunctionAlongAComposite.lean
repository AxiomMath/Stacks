module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The derived pullback–pushforward adjunction along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`StacksDraft.Ch20.Sec28.Tag079WKFlat` gives the adjunction `Lf^* ⊣ Rf_*` for each of `f`, `g`
and `f ≫ g`, and `StacksDraft.Ch20.Sec27Pullback.Tag0D5SKFlat` identifies
`Lg^* ⋙ Lf^*` with `L(f ≫ g)^*`.  Transporting the composite adjunction along that
identification makes `Rf_* ⋙ Rg_*` a right adjoint of `L(f ≫ g)^*`, and uniqueness of right
adjoints then produces the composition isomorphism for derived pushforward and the coherence of
the three adjunctions with it.

## Main definitions

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` is the composition
  isomorphism
  `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` obtained from uniqueness of right adjoints.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp`: the adjunction for `f
  ≫ g` *is* the composite
  adjunction transported along the two composition isomorphisms.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp_counit`: the counit for
  `f ≫ g` is the composite of the
  two counits under those isomorphisms.
* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_comp_homEquiv`:
  transposition under the adjunction for
  `f ≫ g` is successive transposition under the two adjunctions, which is the coherence needed
  for vertical pasting of mates.

## Implementation notes

*Two composition isomorphisms for derived pushforward, and the bridge between them is open.*
`Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompIso` is the composition
  isomorphism obtained from the
universal property of the right derived functor, and it carries the hypothesis
`Stacks.Cohomology.DerivedPushforwardComposition.PushforwardComputesDerived`.  The isomorphism
  built here carries no hypothesis,
because it comes from uniqueness of right adjoints instead.  The two are isomorphisms between
the same pair of functors, but they are *not* known here to be the same map:
`Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardComparison` is characterized by
  its factorization through the
comparison `αgf`, and this one by its factorization through the units of the adjunctions.
Identifying them is what would discharge the last hypothesis of Tag 0D5T, and that
identification is not proved in this file.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for the chosen derived
pushforwards.

Both functors are right adjoints of `L(f ≫ g)^*`: the composite of the two derived adjunctions
is an adjunction `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*`, and `Stacks.DerivedPullback.Composition` identifies
  its left side with
`L(f ≫ g)^*`.  The isomorphism is the uniqueness isomorphism of right adjoints, which is the
construction the source proof of Tag 0D5T uses. -/
def derivedPushforwardCompIso :
    derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (f ≫ g) :=
  Adjunction.rightAdjointUniq
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g))
    (derivedAdjunction (f ≫ g))

/-- The derived adjunction for a composite is the composite adjunction, transported along the
composition isomorphisms for derived pullback and derived pushforward.

Two adjunctions between the same pair of functors agree as soon as their units do, and the unit
of the uniqueness isomorphism of right adjoints is defined so that they do. -/
theorem derivedAdjunction_comp :
    (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g)).ofNatIsoRight
          (derivedPushforwardCompIso f g) =
      derivedAdjunction (f ≫ g) :=
  Adjunction.ext (Adjunction.unit_rightAdjointUniq_hom _ _)

/-- The counit of the derived adjunction for a composite is the composite of the two counits,
read under the composition isomorphisms for derived pullback and derived pushforward. -/
theorem derivedAdjunction_comp_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullback (f ≫ g)).map ((derivedPushforwardCompIso f g).hom.app K) ≫
        (derivedAdjunction (f ≫ g)).counit.app K =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).inv.app
          ((derivedPushforward g).obj ((derivedPushforward f).obj K)) ≫
        (derivedPullback f).map
          ((derivedAdjunction g).counit.app ((derivedPushforward f).obj K)) ≫
        (derivedAdjunction f).counit.app K := by
  simpa only [derivedPushforwardCompIso, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.comp_obj, Functor.whiskerLeft_app, Adjunction.comp_counit_app, Category.assoc] using
    Adjunction.rightAdjointUniq_hom_app_counit
      (((derivedAdjunction g).comp (derivedAdjunction f)).ofNatIsoLeft
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g))
      (derivedAdjunction (f ≫ g)) K

/-- Transposition under the derived adjunction for a composite agrees with successive
transposition under the two derived adjunctions and the canonical composition maps.  This is the
composition coherence needed for vertical pasting of mates. -/
theorem derivedAdjunction_comp_homEquiv
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (φ : (derivedPullback (f ≫ g)).obj M ⟶ K) :
    (derivedAdjunction g).homEquiv _ _
        ((derivedAdjunction f).homEquiv _ _
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app M ≫ φ))
            ≫
        (derivedPushforwardCompIso f g).hom.app K =
      (derivedAdjunction (f ≫ g)).homEquiv M K φ := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, Equiv.trans_apply] using
    congrArg (fun a => a.homEquiv M K φ) (derivedAdjunction_comp f g)

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
