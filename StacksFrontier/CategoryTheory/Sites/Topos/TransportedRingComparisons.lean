module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkInverseImageModules

/-!
# Two comparisons of transported ring structures

The ring structure that `CategoryTheory.Sheaf.ringObjRing` transports to the image of the
underlying sheaf of sets of a sheaf of rings along a finite-product-preserving functor to types
depends on two arguments, the sheaf of rings and the functor.  This file identifies the transported
ring as each of the two varies.

A natural isomorphism of finite-product-preserving functors to types induces a ring isomorphism of
the transported rings, with underlying map `CategoryTheory.Sheaf.ringObjHom` of the forward
direction.  The ring transported from an inverse image `Φ⁻¹𝒪` along `Q` and the ring transported
from `𝒪` along `Φ⁻¹ ⋙ Q` are the same operations on the same type, so the identity map is a ring
isomorphism between them.

## Main definitions

* `CategoryTheory.Sheaf.ringObjEquivOfNatIso`: the ring isomorphism of transported rings induced by
  a natural isomorphism of finite-product-preserving functors to types.
* `CategoryTheory.Sheaf.pullbackRingObjEquiv`: the identity map, as a ring isomorphism from the
  ring transported from an inverse image to the ring transported along the composite functor.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe t w w' v v' u u'

namespace CategoryTheory.Sheaf

attribute [local instance] CategoryTheory.Sheaf.ringObjRing

/-! ### Varying the functor along a natural isomorphism -/

section OfNatIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] (R : Sheaf J RingCat.{w})
  {P P' : Sheaf J (Type w) ⥤ Type t} [PreservesFiniteProducts P] [PreservesFiniteProducts P']

/-- **A natural isomorphism of finite-product-preserving functors to types induces a ring
isomorphism of the transported rings**, with underlying map `CategoryTheory.Sheaf.ringObjHom` of
the forward direction. -/
def ringObjEquivOfNatIso (e : P ≅ P') : P.obj (ringSheaf R) ≃+* P'.obj (ringSheaf R) :=
  RingEquiv.ofBijective (ringObjHom R e.hom)
    ((isIso_iff_bijective (e.hom.app (ringSheaf R))).1 inferInstance)

/-- `ringObjEquivOfNatIso R e` is given by the component of `e.hom` at `ringSheaf R`. -/
@[simp]
theorem ringObjEquivOfNatIso_apply (e : P ≅ P') (x : P.obj (ringSheaf R)) :
    ringObjEquivOfNatIso R e x = e.hom.app (ringSheaf R) x :=
  rfl

end OfNatIso

/-! ### Varying the sheaf of rings along an inverse image -/

section Pullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{w'}) (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts Q]

/-- **The ring transported from an inverse-image sheaf of rings is the ring transported along the
composite functor**, by the identity map on the underlying type.

The underlying sheaf of sets of `Stacks.Sheaves.ToposPullback.pullbackRingSheaf` is the inverse
image of the underlying sheaf of sets on the nose, so the two rings are two ring structures on one
type, and the addition and the multiplication of the two agree. -/
def pullbackRingObjEquiv :
    haveI : PreservesFiniteProducts (Φ ⋙ Q) := inferInstance
    Q.obj (ringSheaf (pullbackRingSheaf J Φ R)) ≃+* (Φ ⋙ Q).obj (ringSheaf R) :=
  have : PreservesFiniteProducts (Φ ⋙ Q) := inferInstance
  { toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun x y => ringAddObj_pullbackRingSheaf J Φ R Q x y
    map_mul' := fun x y => ringMulObj_pullbackRingSheaf J Φ R Q x y }

/-- `pullbackRingObjEquiv J Φ R Q` is the identity map on the underlying type. -/
@[simp]
theorem pullbackRingObjEquiv_apply (x : Q.obj (ringSheaf (pullbackRingSheaf J Φ R))) :
    pullbackRingObjEquiv J Φ R Q x = x :=
  rfl

end Pullback

end CategoryTheory.Sheaf

end
