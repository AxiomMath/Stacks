module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex

/-!
# Transport of the coefficient modules along an isomorphism of the sheaf of rings

An isomorphism `B ≅ B'` of sheaves of commutative rings on a site identifies the sheaves of
`B`-modules with the sheaves of `B'`-modules, by restriction of scalars along its inverse: this
leaves the underlying sheaves of abelian groups and all morphisms between them untouched and
only rewrites the scalar action through the isomorphism. This is the equivalence that identifies
the two categories in which the cotangent complexes of `B` and of `B'` live.

## Main definitions

* `CategoryTheory.Sheaf.ringSheafMapIso` is the isomorphism of the underlying sheaves of rings.
* `CategoryTheory.Sheaf.targetModulesTransport` is the equivalence
  `targetModules J B ≌ targetModules J B'`.

## Main results

* `CategoryTheory.Sheaf.targetModulesTransport_functor_obj_val_obj` and
  `CategoryTheory.Sheaf.targetModulesTransport_functor_map_val_app_apply` describe the
  equivalence on objects and on morphisms: the sections in degree `U` are those of the original
  module with scalars restricted along `e.inv`, and a morphism acts on sections by the same
  function as before.
* `CategoryTheory.Sheaf.targetModulesTransport_functor_obj_toSheaf` records that the underlying
  sheaf of abelian groups is unchanged.

## Implementation notes

The equivalence is `Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso` applied to the
isomorphism of the underlying sheaves of rings; its functor and inverse are therefore literally
the two restriction-of-scalars functors, which is what makes the whole API below hold by
reflexivity. The universe of sections is the one of the site, as in
`CategoryTheory.Sheaf.cotangentComplex`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {B B' : Sheaf J CommRingCat.{max u v w}}

/-- The isomorphism of sheaves of rings underlying an isomorphism of sheaves of commutative
rings. -/
noncomputable abbrev ringSheafMapIso (e : B ≅ B') :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B ≅
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B' :=
  (sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).mapIso e

/-- An isomorphism `B ≅ B'` of sheaves of commutative rings identifies the sheaves of
`B`-modules with the sheaves of `B'`-modules, by restriction of scalars along its inverse. -/
noncomputable def targetModulesTransport (e : B ≅ B') :
    targetModules.{u, v, w} J B ≌ targetModules.{u, v, w} J B' :=
  Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso (ringSheafMapIso J e)

/-- The transport along `e : B ≅ B'` restricts scalars along `e.inv`. -/
lemma targetModulesTransport_functor (e : B ≅ B') :
    (targetModulesTransport.{u, v, w} J e).functor =
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map e.inv) :=
  rfl

/-- The inverse of the transport along `e : B ≅ B'` restricts scalars along `e.hom`. -/
lemma targetModulesTransport_inverse (e : B ≅ B') :
    (targetModulesTransport.{u, v, w} J e).inverse =
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map e.hom) :=
  rfl

/-- The sections of a transported module in degree `U` are those of the original module with
the scalar action restricted along `e.inv`. -/
@[simp]
lemma targetModulesTransport_functor_obj_val_obj (e : B ≅ B')
    (M : targetModules.{u, v, w} J B) (U : Cᵒᵖ) :
    ((targetModulesTransport.{u, v, w} J e).functor.obj M).val.obj U =
      (ModuleCat.restrictScalars (e.inv.hom.app U).hom).obj (M.val.obj U) :=
  rfl

/-- A transported morphism acts on sections by the same function as the original morphism. -/
@[simp]
lemma targetModulesTransport_functor_map_val_app_apply (e : B ≅ B')
    {M N : targetModules.{u, v, w} J B} (g : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((targetModulesTransport.{u, v, w} J e).functor.map g).val.app U).hom x =
      (g.val.app U).hom x :=
  rfl

/-- Transport along `e : B ≅ B'` does not change the underlying sheaf of abelian groups. -/
@[simp]
lemma targetModulesTransport_functor_obj_toSheaf (e : B ≅ B')
    (M : targetModules.{u, v, w} J B) :
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B')).obj
        ((targetModulesTransport.{u, v, w} J e).functor.obj M) =
      (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).obj M :=
  rfl

end CategoryTheory.Sheaf

end
