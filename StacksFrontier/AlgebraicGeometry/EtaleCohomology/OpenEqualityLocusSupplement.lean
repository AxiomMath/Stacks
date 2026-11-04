module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.OpenEqualityLocus
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheavesSupplement

/-!
# Representable presheaves on the small étale site

The canonical functor from the small étale site of a scheme `S` to the schemes over `S` is fully
faithful, so the presheaf on the small étale site represented by an object is the restriction of
the presheaf it represents on the schemes over `S`. In particular, the presheaf represented by an
open subscheme of `S` is represented by that open as an object of the small étale site.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toOverFullyFaithful`: the functor from the small étale site of
  `S` to the schemes over `S` is fully faithful.
* `AlgebraicGeometry.SmallEtale.representablePresheafIso`: the presheaf represented by an object
  of the small étale site is the restriction of the presheaf it represents over `S`.
* `AlgebraicGeometry.SmallEtale.openRepresentableIso`: the presheaf represented by an open of `S`
  is the presheaf represented by that open in the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **The canonical functor from the small étale site of `S` to the schemes over `S` is fully
faithful.** The small étale site is a full subcategory of the big étale slice over `S`, and
`CategoryTheory.Over.post` of a fully faithful functor is fully faithful. -/
def SmallEtale.toOverFullyFaithful (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.toOver B S hS).FullyFaithful := by
  letI : B.inclusion.Full := ObjectProperty.full_ι _
  letI : B.inclusion.Faithful := ObjectProperty.faithful_ι _
  letI : (SmallEtale.inclusion B S hS).Full := ObjectProperty.full_ι _
  letI : (SmallEtale.inclusion B S hS).Faithful := ObjectProperty.faithful_ι _
  haveI : (Over.post (X := B.obj S hS) B.inclusion).Full := inferInstance
  haveI : (Over.post (X := B.obj S hS) B.inclusion).Faithful := inferInstance
  haveI : (SmallEtale.toOver B S hS).Full := Functor.Full.comp _ _
  haveI : (SmallEtale.toOver B S hS).Faithful := Functor.Faithful.comp _ _
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **The presheaf on the small étale site represented by an object of that site is the
restriction of the presheaf it represents on the schemes over `S`.**

The comparison is full faithfulness of `AlgebraicGeometry.SmallEtale.toOver`, the canonical
functor to the schemes over `S`; on sections over an object `T` it is `Equiv.ulift` on either
side of `AlgebraicGeometry.SmallEtale.toOverFullyFaithful`'s bijection on hom types.

The sections universe `w` of the lift is free. `AlgebraicGeometry.openRepresentable'` is stated
at `max u w`, at or above the universe `u` of the schemes, but the comparison itself needs nothing
of `w`, and at `w := u` — the sections universe of the small étale ringed topos, which is where
Stacks 04IE for this site is stated — the lift is removed again by
`CategoryTheory.uliftYonedaIsoYoneda`. -/
def SmallEtale.representablePresheafIso (S : Scheme.{u}) (hS : B.Contains S)
    (A : SmallEtale B S hS) :
    (SmallEtale.toOver B S hS).op ⋙
        uliftYoneda.{w}.obj ((SmallEtale.toOver B S hS).obj A) ≅
      (uliftYoneda.{w} (C := SmallEtale B S hS)).obj A := by
  let FF := SmallEtale.toOverFullyFaithful B S hS
  refine NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.trans
    ((FF.homEquiv (X := X.unop) (Y := A)).symm.trans Equiv.ulift.symm))) ?_
  intro X Y f
  ext x
  cases x with
  | up x =>
      change (SmallEtale.toOver B S hS).obj X.unop ⟶ (SmallEtale.toOver B S hS).obj A at x
      apply ULift.ext
      change FF.preimage ((SmallEtale.toOver B S hS).map f.unop ≫ x) = f.unop ≫ FF.preimage x
      apply FF.homEquiv.injective
      change (SmallEtale.toOver B S hS).map
          (FF.preimage ((SmallEtale.toOver B S hS).map f.unop ≫ x)) =
        (SmallEtale.toOver B S hS).map (f.unop ≫ FF.preimage x)
      rw [FF.map_preimage, Functor.map_comp, FF.map_preimage]

/-- **The presheaf represented by an open subscheme of `S` is the presheaf represented by that
open viewed as an object of the small étale site**, i.e. by
`AlgebraicGeometry.opensToBoundedEtale` applied to it.

This is `AlgebraicGeometry.SmallEtale.representablePresheafIso` at that object, the point being
that `AlgebraicGeometry.SmallEtale.toOver` sends it back to `V` with its open immersion into `S`.
The sections universe `w` is free, for the reason recorded there; the presheaf represented by the
open is `AlgebraicGeometry.openRepresentable'`, which allows every sections universe `max u w`. -/
def SmallEtale.openRepresentableIso (S : Scheme.{u}) (hS : B.Contains S) (W : S.Opens) :
    openRepresentable'.{u, w} B S hS W ≅
      (uliftYoneda.{max u w} (C := SmallEtale B S hS)).obj
        ((opensToBoundedEtale B S hS).obj W) :=
  SmallEtale.representablePresheafIso.{u, max u w} B S hS
    ((opensToBoundedEtale B S hS).obj W)

end AlgebraicGeometry

end
