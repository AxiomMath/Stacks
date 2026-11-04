module

public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf

/-!
# Isomorphisms of the commutative lift of a sheaf of rings

`Stacks.CommRingSheaf.sheaf` reads a sheaf of rings whose sections commute as a sheaf of
commutative rings, keeping the carrier and the operations and only adding a field, and
`Stacks.CommRingSheaf.homMk` reads a morphism of sheaves of rings *into* such a sheaf of rings as
a morphism of sheaves of commutative rings. This file adds the opposite direction and the
isomorphism built from the two: an isomorphism of sheaves of rings between a sheaf of rings with
commuting sections and the underlying sheaf of rings of a sheaf of commutative rings is an
isomorphism of sheaves of commutative rings, with no transport.

## Main definitions

* `Stacks.CommRingSheaf.homMk'`: a morphism of sheaves of rings out of a sheaf of rings with
  commuting sections and into the underlying sheaf of rings of a sheaf of commutative rings, read
  as a morphism of sheaves of commutative rings out of the commutative lift.
* `Stacks.CommRingSheaf.isoMk`: **the commutative lift of an isomorphism of sheaves of rings.**

## Main results

* `Stacks.CommRingSheaf.isoMk_hom_app`: on sections, the forward morphism of `isoMk O h e` is
  that of `e`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CommRingSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A morphism of sheaves of rings out of a sheaf of rings whose sections commute and into the
underlying sheaf of rings of a sheaf of commutative rings, read as a morphism of sheaves of
commutative rings out of the commutative lift. -/
def homMk' (O : Sheaf J CommRingCat.{u}) {S : Sheaf J RingCat.{u}}
    (h : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a)
    (f : S ⟶ (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :
    sheaf S h ⟶ O :=
  ObjectProperty.homMk
    { app := fun W =>
        @CommRingCat.ofHom (S.obj.obj W) (O.obj.obj W) (commRing (S.obj.obj W) (h W))
          inferInstance (f.hom.app W).hom
      naturality := fun W W' g => by
        ext x
        exact congrArg (fun φ => RingCat.Hom.hom φ x) (f.hom.naturality g) }

/-- **The commutative lift of an isomorphism of sheaves of rings** between a sheaf of rings whose
sections commute and the underlying sheaf of rings of a sheaf of commutative rings. -/
def isoMk (O : Sheaf J CommRingCat.{u}) {S : Sheaf J RingCat.{u}}
    (h : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a)
    (e : S ≅ (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) :
    sheaf S h ≅ O where
  hom := homMk' O h e.hom
  inv := homMk O h e.inv
  hom_inv_id := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext
      (RingHom.ext fun x => ?_)))
    exact congrArg (fun φ : S ⟶ S => RingCat.Hom.hom (φ.hom.app W) x) e.hom_inv_id
  inv_hom_id := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun W => CommRingCat.hom_ext
      (RingHom.ext fun x => ?_)))
    exact congrArg
      (fun φ : (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O ⟶
          (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O =>
        RingCat.Hom.hom (φ.hom.app W) x) e.inv_hom_id

/-- On sections over `W`, the forward morphism of `isoMk O h e` acts as the forward morphism of
`e`. -/
theorem isoMk_hom_app (O : Sheaf J CommRingCat.{u}) {S : Sheaf J RingCat.{u}}
    (h : ∀ (W : Cᵒᵖ) (a b : S.obj.obj W), a * b = b * a)
    (e : S ≅ (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O) (W : Cᵒᵖ)
    (x : S.obj.obj W) :
    ((isoMk O h e).hom.hom.app W).hom x = (e.hom.hom.app W).hom x :=
  rfl

end Stacks.CommRingSheaf

end
