module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites

/-!
# The universe lift of sheaves of commutative rings is trivial at a single universe

`AlgebraicGeometry.SheafOfModules.commRingCatULift` lifts the sections of a sheaf of commutative
rings into a universe containing the site, so that the tensor product of sheaves of modules is
available there; flatness of a morphism of sheaves of commutative rings is asserted after that
lift, as `AlgebraicGeometry.SheafOfModules.IsFlatMapULift`.

When the sections already live at the universe of the site, the lift changes nothing: `ULift R`
is isomorphic to `R` as a ring, naturally in `R`, so the lifting functor is isomorphic to the
identity and so is the induced functor on sheaves. This file records those two isomorphisms.

They are what reduces the lifted flatness predicate to the unlifted one on a site whose objects,
morphisms and sections share a universe — the `AlgebraicGeometry.RingedTopos.{u, u, u}` size at
which the inverse-image and change-of-rings results about flatness are stated.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.commRingCatULiftIsoId`: lifting commutative rings into their
  own universe is isomorphic to the identity functor.
* `AlgebraicGeometry.SheafOfModules.sheafULiftIsoId`: lifting a sheaf of commutative rings into
  the universe of its own site is isomorphic to the identity functor.

## Implementation notes

The underlying ring isomorphism is Mathlib's `ULift.ringEquiv`, and its naturality holds by
`rfl`: the lifting functor sends a morphism to the conjugate of that morphism by `ULift.ringEquiv`
in both directions, so composing with the isomorphism cancels one of the two conjugating factors
syntactically.

On sheaves the comparison is the previous one whiskered with the sheaf's own presheaf, since
`AlgebraicGeometry.SheafOfModules.sheafULift` acts by postcomposition with the lifting functor.
It is assembled by hand rather than through `CategoryTheory.sheafCompose`, because `sheafULift`
carries its own proof of the sheaf condition rather than being literally `sheafCompose` of the
lifting functor.

Both are stated only at the single-universe instantiation. The lifting functor
`commRingCatULift.{w, z}` lands in `CommRingCat.{max w z}`, so it is an endofunctor exactly when
`max w z = w`, and that constraint cannot be written as a hypothesis — it has to be imposed by
instantiating the universe arguments, which is what is done here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- **Lifting commutative rings into their own universe is isomorphic to the identity.** The
component at `R` is `ULift.ringEquiv`, and naturality holds by `rfl`. -/
def commRingCatULiftIsoId : commRingCatULift.{u, u} ≅ 𝟭 CommRingCat.{u} :=
  NatIso.ofComponents (fun R ↦ (ULift.ringEquiv (R := R)).toCommRingCatIso)
    (by intros; rfl)

/-- **Lifting a sheaf of commutative rings into the universe of its own site is isomorphic to the
identity.** The lift acts by postcomposition with `commRingCatULift`, so the comparison is
`commRingCatULiftIsoId` whiskered with the presheaf underlying the sheaf. -/
def sheafULiftIsoId {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) :
    sheafULift.{u, u, u} J ≅ 𝟭 (Sheaf J CommRingCat.{u}) :=
  NatIso.ofComponents
    (fun O ↦ ⟨⟨(Functor.isoWhiskerLeft O.obj commRingCatULiftIsoId.{u}).hom⟩,
      ⟨(Functor.isoWhiskerLeft O.obj commRingCatULiftIsoId.{u}).inv⟩,
      by ext1; exact (Functor.isoWhiskerLeft O.obj commRingCatULiftIsoId.{u}).hom_inv_id,
      by ext1; exact (Functor.isoWhiskerLeft O.obj commRingCatULiftIsoId.{u}).inv_hom_id⟩)
    (by intros; ext1; rfl)

end AlgebraicGeometry.SheafOfModules

end
