module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitRestrictScalarsIsoAnySite
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTrivial

/-!
# Flatness of a morphism of sheaves of rings is invariant under isomorphisms

Flatness of `f : O ⟶ O'` is flatness of `O'` as an `O`-module. Composing `f` with an isomorphism on
either side therefore changes nothing: on the right it replaces the module by an isomorphic one,
and on the left it reads the same module over an isomorphic ring.

When the sections of the sheaves of rings already live at the universe of the site, the universe
lift in `AlgebraicGeometry.SheafOfModules.IsFlatMapULift` is isomorphic to the identity, so the
lifted morphism is the original one conjugated by isomorphisms, and the lifted and unlifted
flatness predicates agree.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso`: flatness of a morphism of sheaves of
  commutative rings is preserved by composing with an isomorphism on each side.
* `AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap`: at a site whose objects,
  morphisms and sections share a universe, the universe-lifted flatness predicate is the unlifted
  one.

## Implementation notes

The right-hand composition is handled by
`Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite`, which identifies the
target ring read over an isomorphic ring with the unit module, followed by
`AlgebraicGeometry.SheafOfModules.isFlat_of_iso`. The left-hand one is a change of base ring and is
`Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso`, whose equivalence
has `AlgebraicGeometry.SheafOfModules.restrictScalars` of the *inverse* as its functor — which is
why the isomorphism is supplied reversed.

Restriction of scalars along a composite is restriction along the two factors in turn, by `rfl`, so
no comparison is needed once the composite has been split.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem isFlat_restrictScalars_restrictScalars_unit
    {O O' P' : Sheaf J CommRingCat.{u}} {f : O ⟶ O'} (e₂ : O' ≅ P')
    (hf : IsFlatMap f) :
    IsFlat (O := O)
      ((_root_.SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf J).map f)).obj
        ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf J).map e₂.hom)).obj
          (_root_.SheafOfModules.unit (Stacks.commRingSheafToRingSheaf P')))) :=
  isFlat_of_iso
    ((_root_.SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf J).map f)).mapIso
      (Stacks.SheafOfModules.ChangeOfRings.unitRestrictScalarsIsoOfIsoAnySite
        ((Stacks.forgetCommRingSheaf J).mapIso e₂))) hf

/-- **Flatness of a morphism of sheaves of commutative rings survives composition with an
isomorphism on each side.** -/
theorem isFlatMap_comp_iso {O O' P P' : Sheaf J CommRingCat.{u}}
    (e₁ : P ≅ O) {f : O ⟶ O'} (e₂ : O' ≅ P') (hf : IsFlatMap f) :
    IsFlatMap (e₁.hom ≫ f ≫ e₂.hom) := by
  change IsFlat (O := P)
    ((_root_.SheafOfModules.restrictScalars
      ((Stacks.forgetCommRingSheaf J).map (e₁.hom ≫ f ≫ e₂.hom))).obj
      (_root_.SheafOfModules.unit (Stacks.commRingSheafToRingSheaf P')))
  rw [Functor.map_comp, Functor.map_comp]
  exact Stacks.SheafOfModules.FlatRingTransport.isFlat_restrictScalarsEquivalenceOfIso
    e₁.symm
    ((_root_.SheafOfModules.restrictScalars ((Stacks.forgetCommRingSheaf J).map f)).obj
      ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf J).map e₂.hom)).obj
        (_root_.SheafOfModules.unit (Stacks.commRingSheafToRingSheaf P'))))
    (isFlat_restrictScalars_restrictScalars_unit e₂ hf)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})] [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The universe lift of a morphism of sheaves of commutative rings is that morphism conjugated
by the comparison of the lift with the identity. -/
theorem sheafULift_map_eq {O O' : Sheaf J CommRingCat.{u}} (f : O ⟶ O') :
    (sheafULift.{u, u, u} J).map f =
      ((sheafULiftIsoId J).app O).hom ≫ f ≫ ((sheafULiftIsoId J).app O').inv :=
  ((sheafULiftIsoId J).app O').eq_comp_inv.mpr ((sheafULiftIsoId J).hom.naturality f)

/-- **At a site whose objects, morphisms and sections share a universe, the universe-lifted
flatness predicate for a morphism of sheaves of commutative rings is the unlifted one.** -/
theorem isFlatMapULift_iff_isFlatMap {O O' : Sheaf J CommRingCat.{u}} (f : O ⟶ O') :
    IsFlatMapULift.{u, u, u} f ↔ IsFlatMap f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [sheafULift_map_eq f] using isFlatMap_comp_iso ((sheafULiftIsoId J).app O).symm
      ((sheafULiftIsoId J).app O') (f := (sheafULift.{u, u, u} J).map f) h
  · simpa only [Iso.symm_hom, ← sheafULift_map_eq f] using
      isFlatMap_comp_iso ((sheafULiftIsoId J).app O) ((sheafULiftIsoId J).app O').symm h

end AlgebraicGeometry.SheafOfModules

end
