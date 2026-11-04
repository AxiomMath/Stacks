module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackUnit

/-!
# The canonical map `f^*𝒪 ⟶ 𝒪` across the object form of the transport of the inverse image

`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackUnit.lean` proves that
`AlgebraicGeometry.Space.representedModulePullbackIso` — the identification of the inverse image
of modules along a represented morphism with pullback along the morphism of small étale ringed
sites of [Stacks Project, Tag 070R] (2) of the underlying morphism of schemes — carries the
canonical map `φ^*𝒪 ⟶ 𝒪` of one to the canonical map of the other.  That statement is at the
**functor** level, between the two *inverse* functors of the comparison equivalences.

What the comparison chain of part (2) of [Stacks Project, Tag 04G2] consumes is the same
compatibility for `AlgebraicGeometry.Space.representedModuleObjPullbackIso`, the object form
between the two *functors* of those equivalences.  This file carries it across.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_functor_obj_unit`: the
  comparison equivalence carries the structure sheaf of the representing scheme, read as a module
  over itself, to the structure sheaf of the representable algebraic space.  True by `rfl`.
* `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_counitIso_app_unit`: its counit
  at that module is the identity.  True by `rfl`, and **the counit is not the identity in
  general** — at the inverse image of that module along a represented morphism it is not even
  type-correct, so this is a statement about the unit module and not a triviality.
* `AlgebraicGeometry.Space.representedModuleObjPullbackIso_unit_obj` and
  `AlgebraicGeometry.Space.representedModuleObjPullbackIso_unit`: the object form of the
  comparison, read at the unit module, with the unit correction removed — in the spelling the
  definition produces and in the spelling the functor-level compatibility uses, bridged by
  `AlgebraicGeometry.Space.representedModulePullbackIso_unit_spelling`.
* `AlgebraicGeometry.Space.structureModulePullbackMap_representedModuleObjPullbackIso`: **the
  object form of the comparison carries the canonical map `φ^*𝒪 ⟶ 𝒪` of
  `AlgebraicGeometry.Space.structureModulePullbackMap` to
  `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` of the structure map of the morphism of
  small étale ringed sites of the underlying morphism of schemes.**

## Route

`AlgebraicGeometry.Space.representedModuleObjPullbackIso` is
`AlgebraicGeometry.Space.representedModulePullbackIso` read at one module and corrected by the
unit and the counit of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`.  At the
unit module the *unit* correction is `CategoryTheory.Iso.refl` by `rfl`, so it disappears; the
*counit* correction does not, and is removed at the end by its naturality together with the fact
that the counit at the unit module is the identity.  In between sits the functor-level statement
`AlgebraicGeometry.Space.structureModulePullbackMap_representedModulePullbackIso`.

## Implementation notes

Every structural step is an instantiation of a lemma of `CategoryTheory` stated at variables —
`CategoryTheory.trans_functor_mapIso_refl`,
`CategoryTheory.Equivalence.counitIso_inv_app_comp_map_map` and
`CategoryTheory.Functor.map_comp_of_eq` — and each geometric step is its own declaration.  Both
are forced, declaration by declaration:

* the functoriality step written as `(F.map_comp _ _).symm.trans (congrArg F.map h)` with the
  two morphisms left to unification exhausts the `isDefEq` budget; the same step through
  `CategoryTheory.Functor.map_comp_of_eq` with all four arguments written out is free;
* the removal of the counit correction written as one term exhausts the `whnf` budget; split
  into the generic counit lemma and the substitution of the identity it is free;
* and the two spellings of the module at which the comparison is read — the one the definition
  of `AlgebraicGeometry.Space.representedModuleObjPullbackIso` produces, the image under
  `(representedSmallEtaleModuleEquivalence B S hS T).functor` of
  `SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)`, and the one the functor-level
  statement uses, `SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj T, _⟩)`
  — can be bridged **only at the isomorphism**.  Each as its own declaration: the
  objects themselves are `rfl` and free; the two isomorphisms are `rfl` and free; the two `hom`
  components are a `whnf` timeout, and so are their images under the comparison equivalence.
  So a concrete comparison moves by `congrArg` as an isomorphism and never through its `hom`,
  which is why `AlgebraicGeometry.Space.representedModulePullbackIso_unit_spelling` is stated
  where it is.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

/-- **A composite with the image of an identity isomorphism.** -/
theorem trans_functor_mapIso_refl {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
    {X : D} {W : C} (α : X ≅ G.obj W) : α ≪≫ G.mapIso (Iso.refl W) = α := by
  rw [Functor.mapIso_refl, Iso.trans_refl]

/-- **The functor image of a composite, with the composite given by name.**  Stated so that a
consumer supplies all four morphisms; leaving them to unification at a geometric instance costs
a heartbeat budget, as the implementation notes of this file record. -/
theorem Functor.map_comp_of_eq {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : c = a ≫ b) :
    F.map a ≫ F.map b = F.map c := by
  rw [h, F.map_comp]

/-- **The counit of an equivalence cancels the image of the inverse image of a morphism.**  For
`h : X ⟶ Y` in the target category, the inverse of the counit at `X`, followed by the image under
the equivalence of the image under its inverse of `h`, followed by the counit at `Y`, is `h`. -/
theorem Equivalence.counitIso_inv_app_comp_map_map {C : Type*} [Category C] {D : Type*}
    [Category D] (E : C ≌ D) {X Y : D} (h : X ⟶ Y) :
    (E.counitIso.app X).inv ≫ E.functor.map (E.inverse.map h) ≫ E.counitIso.hom.app Y = h := by
  have hnat := E.counitIso.hom.naturality h
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [hnat]
  exact Iso.inv_hom_id_assoc (E.counitIso.app X) h

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The comparison equivalence carries the structure sheaf of the representing scheme to the
structure sheaf of the representable algebraic space.**  Both are the unit module of a ring
sheaf, and the two ring sheaves are the same one read across the identification of the two small
étale sites; true by `rfl`. -/
theorem representedSmallEtaleModuleEquivalence_functor_obj_unit :
    (representedSmallEtaleModuleEquivalence B S hS T).functor.obj
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)) =
      SheafOfModules.unit (structureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) :=
  rfl

/-- **The counit of the comparison equivalence at the structure sheaf is the identity.**

This is a statement about the unit module, not a triviality about the equivalence: at the
inverse image along a represented morphism of the structure sheaf the counit is not the
identity, and the corresponding equation is not even type-correct. -/
theorem representedSmallEtaleModuleEquivalence_counitIso_app_unit :
    (representedSmallEtaleModuleEquivalence B S hS T).counitIso.app
        (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)) =
      Iso.refl _ :=
  rfl

/-- **The object form of the transport of the inverse image, read at the unit module.**  The
unit correction of `AlgebraicGeometry.Space.representedModuleObjPullbackIso` is
`CategoryTheory.Iso.refl` there, so only the counit correction and the functor-level comparison
remain.

The module is written as the image of the structure sheaf of the representing scheme under the
comparison equivalence, which is the spelling the definition produces. -/
theorem representedModuleObjPullbackIso_unit_obj :
    representedModuleObjPullbackIso B S hS g hg
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)) =
      ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
                (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))))).symm ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((representedModulePullbackIso B S hS g hg).app
            ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)))) :=
  congrArg (fun t ↦ ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
        ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
            (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))))).symm ≪≫
      (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso t)
    (trans_functor_mapIso_refl
      (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
      ((representedModulePullbackIso B S hS g hg).app
        ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)))))

/-- **The two spellings of the structure sheaf of the representing scheme, bridged as an
isomorphism.**  By
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence_functor_obj_unit` the two objects
are equal by `rfl`, so the two isomorphisms are the same term.

The bridge is made **at the isomorphism** and not at either `hom` component: the same equation
between the `hom` components, and even between their images under the comparison equivalence,
exhausts the `whnf` budget.  See the implementation notes. -/
theorem representedModulePullbackIso_unit_spelling :
    ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
                (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))))).symm ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((representedModulePullbackIso B S hS g hg).app
            ((representedSmallEtaleModuleEquivalence B S hS T).functor.obj
              (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)))) =
      ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)))).symm ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((representedModulePullbackIso B S hS g hg).app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))) :=
  rfl

/-- `AlgebraicGeometry.Space.representedModuleObjPullbackIso_unit_obj` with the module written as
the structure sheaf of the representable algebraic space, which is the spelling the
functor-level compatibility uses. -/
theorem representedModuleObjPullbackIso_unit :
    representedModuleObjPullbackIso B S hS g hg
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)) =
      ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)))).symm ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          ((representedModulePullbackIso B S hS g hg).app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))) :=
  (representedModuleObjPullbackIso_unit_obj B S hS g hg).trans
    (representedModulePullbackIso_unit_spelling B S hS g hg)

/-- The object form of the comparison, read on `hom` and reassociated against the canonical map
of the pullback of the unit module.  Its own declaration, so that the reassociation and the two
steps below do not share a heartbeat budget. -/
theorem representedModuleObjPullbackIso_hom_unit_comp :
    (representedModuleObjPullbackIso B S hS g hg
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g)) =
      ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app
            ((modulePullback B S hS (representedSpaceMap B S hS g)).obj
              (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)))).inv ≫
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.map
            ((representedModulePullbackIso B S hS g hg).hom.app
              (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))) ≫
          (representedSmallEtaleModuleEquivalence B S hS T').functor.map
            (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g))) :=
  (eq_whisker (congrArg Iso.hom (representedModuleObjPullbackIso_unit B S hS g hg)) _).trans
    (Category.assoc _ _ _)

/-- The functor-level compatibility
`AlgebraicGeometry.Space.structureModulePullbackMap_representedModulePullbackIso`, read under
the functor of the comparison equivalence. -/
theorem functor_map_structureModulePullbackMap_representedModulePullbackIso :
    (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((representedModulePullbackIso B S hS g hg).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩))) ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g)) =
      (representedSmallEtaleModuleEquivalence B S hS T').functor.map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) :=
  Functor.map_comp_of_eq (representedSmallEtaleModuleEquivalence B S hS T').functor
    ((representedModulePullbackIso B S hS g hg).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS
        ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)))
    (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g))
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
      (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)))
    (structureModulePullbackMap_representedModulePullbackIso B S hS g hg)

/-- The counit correction at the target of the canonical map is the identity, so it may be
dropped from the composite. -/
theorem functor_map_inverse_map_structureModulePullbackMap_comp_counit :
    (representedSmallEtaleModuleEquivalence B S hS T').functor.map
            ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
              (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) ≫
          (representedSmallEtaleModuleEquivalence B S hS T').counitIso.hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS
              ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)) =
      (representedSmallEtaleModuleEquivalence B S hS T').functor.map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) :=
  (congrArg (fun t ↦ (representedSmallEtaleModuleEquivalence B S hS T').functor.map
        ((representedSmallEtaleModuleEquivalence B S hS T').inverse.map
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g))) ≫ t)
      (congrArg Iso.hom
        (representedSmallEtaleModuleEquivalence_counitIso_app_unit B S hS (T := T')))).trans
    (Category.comp_id _)

/-- **The object form of the transport of the inverse image carries the canonical map
`φ^*𝒪 ⟶ 𝒪` to the canonical map of the morphism of small étale ringed sites.**

This is
`AlgebraicGeometry.Space.structureModulePullbackMap_representedModulePullbackIso` carried from
`AlgebraicGeometry.Space.representedModulePullbackIso` to
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`: at the unit module the unit correction
of the object form is the identity and the counit correction cancels. -/
theorem structureModulePullbackMap_representedModuleObjPullbackIso :
    (representedModuleObjPullbackIso B S hS g hg
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          (SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g)) =
      structureModulePullbackMap B S hS (representedSpaceMap B S hS g) :=
  (representedModuleObjPullbackIso_hom_unit_comp B S hS g hg).trans
    ((whisker_eq _ (functor_map_structureModulePullbackMap_representedModulePullbackIso
          B S hS g hg)).trans
      ((whisker_eq _ (functor_map_inverse_map_structureModulePullbackMap_comp_counit
            B S hS g)).symm.trans
        (Equivalence.counitIso_inv_app_comp_map_map
          (representedSmallEtaleModuleEquivalence B S hS T')
          (structureModulePullbackMap B S hS (representedSpaceMap B S hS g)))))

end AlgebraicGeometry.Space

end
