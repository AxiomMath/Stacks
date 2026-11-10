module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedSectionsCounit

/-!
# Forgetting the module structure on the derived counit of Stacks 0G72

Let `Z` be a closed subset of a ringed space `X`.  On sheaves of `𝒪_X`-modules the canonical map
`i_* R𝓗_Z(K) ⟶ K` of [Stacks, Tag 0G72] is
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId`; on sheaves of abelian groups
it is `Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedSectionsToId`.  The
comparison of [Stacks, Tag 0G74] part (2), with `i_*` folded in, is
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`.

This file proves that the three fit into a commuting square: **forgetting the module structure
carries the module counit to the abelian counit**.

## Main results

* `whiskerRight_derivedSupportedSectionsToId`: the equation

  `whiskerRight (derivedSupportedSectionsToId X Z RH aH) Φ
      = abelianSupportedEndoForgetComparison X Z RHab aHab RH aH ≫
        whiskerLeft Φ (derivedAbelianSupportedSectionsToId X Z RHab aHab)`

  of natural transformations `RH ⋙ Φ ⟶ Φ`, where
  `Φ = underlyingDerivedSheaf (structureSheafRing X)` is the forgetful functor on derived
  categories, `RH` is an arbitrary right derived functor of `ℱ ↦ i_*ℋ_Z(ℱ)` on `𝒪_X`-modules with
  derivation unit `aH`, and `RHab` an arbitrary right derived functor of `F ↦ i_*ℋ_Z(F)` on
  abelian sheaves with derivation unit `aHab`.

* `isIso_abelianSupportedEndoForgetComparison`: **that comparison is invertible**, for a closed
  subset `Z`.  This is [Stacks, Tag 0G74] part (2) with `i_*` folded in, the endofunctor form of
  `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` of the namespace
  `Stacks.Cohomology.SupportedComplexes`.

* `forgetIso_hom_comp_toId_complex`, `forgetIso_hom_comp_toId_homotopy` and
  `forgetIso_hom_comp_toId_derived`: the underived compatibility
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedSectionsForgetIso_hom_comp_toId`
  transported successively to complexes, to the homotopy category and to the derived category of
  abelian sheaves.  These are `private`.

## Implementation notes

**Carried hypotheses.**  `whiskerRight_derivedSupportedSectionsToId` carries **no** closedness
hypothesis, no hypothesis on the coefficient sheaf and no quasi-coherence: its only hypotheses
are that `RH` and `RHab` are right derived functors of the respective supported-sections
endofunctors at their given derivation units, plus the standing size conditions that instance
search discharges.  In particular the equation holds for an *arbitrary* choice of the two derived
functors, exactly as its two sides are defined.

`isIso_abelianSupportedEndoForgetComparison` carries one further hypothesis, `hZ : IsClosed Z`,
and so do the three `private` lemmas feeding it
(`abelianEndoUnit_isIso_at_underlying_kInjective`,
`isIso_abelianSupportedEndoForgetUnit_app`; `isIso_forgetfulSupportedEndoUnit_app` does not).
Closedness is where flasqueness enters, through
`Stacks.Cohomology.SupportedComplexes.supportedSections_map_quasiIso_of_kInjectiveModule`: the
underlying abelian complex of a K-injective complex of `𝒪_X`-modules with injective terms is
neither K-injective nor a complex of injectives, yet still computes `R𝓗_Z^{ab}` because its
terms are flasque.  No quasi-coherence and no hypothesis on the coefficient sheaf appears there
either.

**Why the file is split the way it is.**  The whole equation reduces, by
`CategoryTheory.Functor.rightDerived_ext` applied to `forgetfulSupportedEndoUnit`, to one
identity between morphisms of the derived category of abelian sheaves at each object `K` of the
homotopy category of `𝒪_X`-modules, and that identity is the underived compatibility transported
along four different comparisons.  Elaborating the transport in one step exceeds the default
heartbeat limit, so it is cut into the following chain, each link of which is one rewrite step
with its type written out in full:

* `compIso_hom_app` and `compIso_refl_inv_app`: the two components of
  `CategoryTheory.Functor.mapHomotopyCategoryCompIso` that occur, identified with the
  localization of a map of complexes and with an identity.  Both restate `private` lemmas of
  `StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitGlobalSections` and
  `StacksFrontier.Algebra.Homology.HomotopyCategoryTransition`, with the same proofs.
* `homotopyIdentityIso_hom_app` and `abelianHomotopyIdentityIso_hom_app`: the two unitors
  identified with the localization of `CategoryTheory.Functor.mapHomologicalComplexIdIso`.
* `forgetIso_hom_comp_toId_complex`: the underived compatibility degreewise on a complex, the
  only step that touches the mathematics; it is `HomologicalComplex.hom_ext` followed by the
  underived statement at `K.X i`.
* `forgetIso_hom_comp_toId_homotopy`, then `forgetIso_hom_comp_toId_derived`: the same identity
  in the homotopy category, then in the derived category.
* `unit_comp_module_counit` and `unit_comp_abelian_counit`: the two sides of the goal composed
  with the derivation unit, each collapsed by the characterising factorisation of the
  corresponding counit (`derivedSupportedSectionsToId_fac`,
  `derivedAbelianSupportedSectionsToId_fac`, `abelianSupportedEndoForgetComparison_fac`) and,
  for the abelian side, the naturality of the derived abelian counit.
* `factorsh_transport`: the naturality of
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the forgetful functor, which is what
  moves the identity from the homotopy category back to the derived category.

The expensive link is `forgetIso_hom_comp_toId_homotopy`: it is where the four comparisons are
rewritten simultaneously into localizations of maps of complexes.  The two abbreviations
`forgetCompIso` and `reflCompIso` exist so that the instance arguments of
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` are spelled here exactly as they are spelled
in `abelianSupportedEndoForgetUnit`; the two spellings of the abelian sheaf category described in
the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedSectionsCounit` make
instance search unreliable there, which is why that definition uses explicit instances.

**No `set_option` is used anywhere in this file**, and in particular `maxHeartbeats` is left at
its default.

**Invertibility.**  The invertibility proof is the one of the `Z`-side statement, transported:
`abelianEndoUnit_isIso_at_underlying_kInjective`, then the seven-factor invertibility chain
`isIso_abelianSupportedEndoForgetUnit_app` (which needs the small `isIso_comp_app`,
`isIso_whiskerLeft_app` and friends of `Stacks.Cohomology.SupportedComplexes`, because the
additivity instances in the functors are only definitionally equal and so `simp` cannot match
them), then `isIso_forgetfulSupportedEndoUnit_app`, then the factorisation.
`isIso_comp_left_iff` restates a `private` lemma of
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDirectImage`.

**Not reached.**  Step (ii) of [Stacks, Tag 0G85] is not assembled here: nothing below states the
non-linear comparison square itself, only the two inputs to it.  Also not reached: any
identification of `abelianSupportPushCounit` with the counit of a derived adjunction, the
naturality in a merely additive morphism of the augmentation of [Stacks, Tag 0G7L], and anything
about the Čech cokernel of [Stacks, Tag 0G7Q].

**No declaration here carries a `@[stacks ...]` attribute.**

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 17.5.6 (Tag 01AZ)](https://stacks.math.columbia.edu/tag/01AZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.RestrictionCover (homotopyIdentityIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.AbelianSupportedCounitForget

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.abelianSheaves_isGrothendieckAbelian

/-! ### Components of the comparisons of homotopy categories -/

/-- The comparison of homotopy categories attached to an isomorphism `F ⋙ G ≅ H` of additive
functors is, at an object, the localization of the induced map of complexes.

This restates `CategoryTheory.mapHomotopyCategoryCompIso_hom_app` of
`StacksFrontier.Algebra.Homology.HomotopyCategoryTransition`, with the same proof, so that this
file need not import that module. -/
private lemma compIso_hom_app {V₁ V₂ V₃ : Type*} [Category* V₁] [Category* V₂] [Category* V₃]
    [Preadditive V₁] [Preadditive V₂] [Preadditive V₃]
    {F : V₁ ⥤ V₂} {G : V₂ ⥤ V₃} {H : V₁ ⥤ V₃} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] {ι : Type*} (c : ComplexShape ι)
    (K : HomotopyCategory V₁ c) :
    (Functor.mapHomotopyCategoryCompIso e c).hom.app K =
      (HomotopyCategory.quotient V₃ c).map
        ((NatTrans.mapHomologicalComplex e.hom c).app K.as) :=
  rfl

/-- The comparison of homotopy categories attached to the identity isomorphism of a composite of
additive functors is, at an object, the identity: it is the localization of an identity.

This restates a `private` lemma of
`StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitGlobalSections`, with the
same proof. -/
private lemma compIso_refl_inv_app {V₁ V₂ V₃ : Type*} [Category* V₁] [Category* V₂]
    [Category* V₃] [Preadditive V₁] [Preadditive V₂] [Preadditive V₃]
    (F : V₁ ⥤ V₂) (G : V₂ ⥤ V₃) [F.Additive] [G.Additive] {ι : Type*} (c : ComplexShape ι)
    (K : HomotopyCategory V₁ c) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).inv.app K = 𝟙 _ := by
  change (HomotopyCategory.quotient V₃ c).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier)

/-- The unitor of the homotopy category of `𝒪_X`-modules is, at an object, the localization of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`.  This holds by definition, the unitor being
lifted from that isomorphism through the quotient. -/
private lemma homotopyIdentityIso_hom_app
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (homotopyIdentityIso (structureSheafRing X)).hom.app K =
      (HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).hom.app K.as) :=
  rfl

/-- The unitor of the homotopy category of abelian sheaves on `X` is, at an object, the
localization of `CategoryTheory.Functor.mapHomologicalComplexIdIso`.  This holds by definition,
the unitor being lifted from that isomorphism through the quotient. -/
private lemma abelianHomotopyIdentityIso_hom_app
    (L : HomotopyCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      (ComplexShape.up ℤ)) :
    (abelianHomotopyIdentityIso X).hom.app L =
      (HomotopyCategory.quotient
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexIdIso
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).hom.app L.as) :=
  rfl

/-- A quasi-isomorphism of cochain complexes becomes invertible in the derived category, after
passing to the homotopy category. -/
private lemma isIso_Qh_map_quotient_map {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)) :=
  (DerivedCategory.isIso_Qh_map_iff _).mpr ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    ‹_›)

/-- The comparison of homotopy categories induced by `abelianSupportedSectionsForgetIso`, with
the instance arguments spelled exactly as in `abelianSupportedEndoForgetUnit`. -/
abbrev forgetCompIso :
    (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) :=
  @Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
    (abelianSupportedSectionsForgetIso X Z)
    (by exact supportedSectionsFunctor_additive_endo X Z)
    (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
    (by exact forget_abelianSupportedSections_additive X Z)
    (ComplexShape.up ℤ)

/-- The comparison of homotopy categories induced by the identity isomorphism of the composite
of the forgetful functor with abelian supported sections, with the instance arguments spelled
exactly as in `abelianSupportedEndoForgetUnit`. -/
private abbrev reflCompIso :
    (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) :=
  @Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
    (Iso.refl (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSupportedSections Z))
    (by exact inferInstanceAs (_root_.SheafOfModules.toSheaf (structureSheafRing X)).Additive)
    (by exact abelianSupportedSections_additive Z)
    (by exact forget_abelianSupportedSections_additive X Z)
    (ComplexShape.up ℤ)

/-! ### The underived compatibility, transported -/

/-- The underived compatibility
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedSectionsForgetIso_hom_comp_toId`
applied degreewise to a complex of `𝒪_X`-modules.  Both sides are, in each degree, the inclusion
of the sections supported on `Z` into the ambient sections, so this is the underived statement at
`K.X i`. -/
private lemma forgetIso_hom_comp_toId_complex
    (K : HomologicalComplex (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (supportedSectionsSubsheafInclusion X Z)
              (ComplexShape.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexIdIso (_root_.SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).hom.app K) =
      (NatTrans.mapHomologicalComplex (abelianSupportedSectionsForgetIso X Z).hom
          (ComplexShape.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex
            (𝟙 (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSupportedSections Z))
            (ComplexShape.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex (abelianSupportedSectionsToId X Z)
            (ComplexShape.up ℤ)).app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexIdIso
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
            (ComplexShape.up ℤ)).hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  have h := congr_app (abelianSupportedSectionsForgetIso_hom_comp_toId X Z) (K.X i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simpa using h.symm

/-- The underived compatibility in the homotopy category of abelian sheaves: the forgetful
functor carries the localization of the supported-sections inclusion to the localization of the
abelian one, past the two comparisons of homotopy categories and the two unitors.

This is the expensive step; every term on both sides is rewritten into the localization of a map
of complexes, and the identity then follows from `forgetIso_hom_comp_toId_complex` applied to the
representing complex. -/
private lemma forgetIso_hom_comp_toId_homotopy
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X Z)
              (ComplexShape.up ℤ)).app K ≫
          (homotopyIdentityIso (structureSheafRing X)).hom.app K) =
      (forgetCompIso X Z).hom.app K ≫
        (reflCompIso X Z).inv.app K ≫
        (NatTrans.mapHomotopyCategory (abelianSupportedSectionsToId X Z)
            (ComplexShape.up ℤ)).app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (abelianHomotopyIdentityIso X).hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) :=
  congrArg
    (HomotopyCategory.quotient
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ)).map
    (forgetIso_hom_comp_toId_complex X Z K.as)

/-- The underived compatibility in the derived category of abelian sheaves: the previous identity
after applying the localization functor, with the four factors kept apart on the left so that it
can be used as a rewrite inside a longer composite. -/
private lemma forgetIso_hom_comp_toId_derived
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((forgetCompIso X Z).hom.app K) ≫
        DerivedCategory.Qh.map ((reflCompIso X Z).inv.app K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (abelianSupportedSectionsToId X Z)
            (ComplexShape.up ℤ)).app
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map
          ((abelianHomotopyIdentityIso X).hom.app
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) =
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).map
        ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X Z)
              (ComplexShape.up ℤ)).app K ≫
          (homotopyIdentityIso (structureSheafRing X)).hom.app K) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Functor.comp_map,
    forgetIso_hom_comp_toId_homotopy]

/-- The naturality of the comparison identifying the forgetful functor on derived categories with
the forgetful functor applied degreewise.  This is what carries an identity in the homotopy
category of abelian sheaves back to the derived category of `𝒪_X`-modules: the comparison is
invertible, so conjugating by it is the same as applying the forgetful functor on derived
categories. -/
private lemma factorsh_transport
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (h : ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ)).obj K ⟶ K) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map h ≫
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app
          K =
      (DerivedCategory.Qh ⋙
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategory).map h := by
  rw [← Category.assoc,
    ← (_root_.SheafOfModules.toSheaf
      (structureSheafRing X)).mapDerivedCategoryFactorsh.hom.naturality h,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-! ### The derived compatibility -/

section Forget

variable
  (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
    DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))
  (aHab : (abelianSupportedSections Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
  (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
  (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)

/-- The module side of the goal, composed with the derivation unit of `RH` and then forgotten:
by the characterising factorisation of `derivedSupportedSectionsToId` it collapses to the
forgetful image of the localized supported-sections inclusion. -/
private lemma unit_comp_module_counit
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (forgetfulSupportedEndoUnit X Z RH aH).app K ≫
        (underlyingDerivedSheaf (structureSheafRing X)).map
          ((derivedSupportedSectionsToId X Z RH aH).app (DerivedCategory.Qh.obj K)) =
      (underlyingDerivedSheaf (structureSheafRing X)).map
        (DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X Z)
                (ComplexShape.up ℤ)).app K ≫
            (homotopyIdentityIso (structureSheafRing X)).hom.app K)) := by
  have h := congr_app (derivedSupportedSectionsToId_fac X Z RH aH) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  dsimp only [forgetfulSupportedEndoUnit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id]
  rw [← Functor.map_comp, h, ← Functor.map_comp]

/-- The abelian side of the goal, composed with the derivation unit of `RH` and then forgotten.
The composite with `abelianSupportedEndoForgetComparison` is the unit
`abelianSupportedEndoForgetUnit`; composing that with the derived abelian counit, the naturality
of the counit moves the comparison of derived categories to the right and the characterising
factorisation of `derivedAbelianSupportedSectionsToId` collapses what remains. -/
private lemma unit_comp_abelian_counit
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (abelianSupportedEndoForgetUnit X Z RHab aHab).app K ≫
        (derivedAbelianSupportedSectionsToId X Z RHab aHab).app
          ((underlyingDerivedSheaf (structureSheafRing X)).obj (DerivedCategory.Qh.obj K)) =
      (underlyingDerivedSheaf (structureSheafRing X)).map
        (DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X Z)
                (ComplexShape.up ℤ)).app K ≫
            (homotopyIdentityIso (structureSheafRing X)).hom.app K)) := by
  have hfac := congr_app (derivedAbelianSupportedSectionsToId_fac X Z RHab aHab)
    (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hfac
  dsimp only [abelianSupportedEndoForgetUnit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  have hnat : RHab.map
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app
            K) ≫
        (derivedAbelianSupportedSectionsToId X Z RHab aHab).app
          ((underlyingDerivedSheaf (structureSheafRing X)).obj (DerivedCategory.Qh.obj K)) =
      (derivedAbelianSupportedSectionsToId X Z RHab aHab).app
          (DerivedCategory.Qh.obj
            (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K)) ≫
        (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app
          K :=
    (derivedAbelianSupportedSectionsToId X Z RHab aHab).naturality _
  rw [hnat, reassoc_of% hfac, reassoc_of% (forgetIso_hom_comp_toId_derived X Z K)]
  exact (factorsh_transport X Z K _).trans (Functor.comp_map _ _ _)

/-- **Forgetting the module structure carries the counit of [Stacks, Tag 0G72] to the abelian
counit.**  For arbitrary right derived functors `RH` of `ℱ ↦ i_*ℋ_Z(ℱ)` on `𝒪_X`-modules and
`RHab` of `F ↦ i_*ℋ_Z(F)` on abelian sheaves, with derivation units `aH` and `aHab`, the square

`(i_* R𝓗_Z(K))_ab ⟶ i_* R𝓗_Z^{ab}(K_ab) ⟶ K_ab`

commutes with the forgetful image of `i_* R𝓗_Z(K) ⟶ K`.  Both sides are maps `RH ⋙ Φ ⟶ Φ`,
where `Φ` is the forgetful functor on derived categories, read through the unitors.

This is blocker (2) of step (ii) of [Stacks, Tag 0G85].  Since the forgetful functor is exact,
`RH ⋙ Φ` is itself a right derived functor of `ℱ ↦ i_*ℋ_Z(ℱ)_ab`, so the two sides agree as soon
as they agree after composing with the derivation unit, which is the content of
`unit_comp_module_counit`, `unit_comp_abelian_counit`, `forgetIso_hom_comp_toId_derived` and
`factorsh_transport`. -/
public theorem whiskerRight_derivedSupportedSectionsToId
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    (Functor.whiskerRight (derivedSupportedSectionsToId X Z RH aH)
        (underlyingDerivedSheaf (structureSheafRing X)) :
      RH ⋙ underlyingDerivedSheaf (structureSheafRing X) ⟶
        underlyingDerivedSheaf (structureSheafRing X)) =
      abelianSupportedEndoForgetComparison X Z RHab aHab RH aH ≫
        Functor.whiskerLeft (underlyingDerivedSheaf (structureSheafRing X))
          (derivedAbelianSupportedSectionsToId X Z RHab aHab) := by
  refine Functor.rightDerived_ext (RH ⋙ underlyingDerivedSheaf (structureSheafRing X))
    (forgetfulSupportedEndoUnit X Z RH aH)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ))
    (underlyingDerivedSheaf (structureSheafRing X)) _ _ ?_
  rw [Functor.whiskerLeft_comp, ← Category.assoc,
    abelianSupportedEndoForgetComparison_fac X Z RHab aHab RH aH]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [unit_comp_module_counit X Z RH aH K, unit_comp_abelian_counit X Z RHab aHab K]

/-! ### Invertibility of the comparison -/

/-- Composing with an isomorphism on the left does not change whether a morphism is an
isomorphism.  This restates a `private` lemma of
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDirectImage`. -/
private lemma isIso_comp_left_iff {C : Type*} [Category* C] {A A' B : C}
    (e : A ≅ A') (β : A' ⟶ B) : IsIso (e.hom ≫ β) ↔ IsIso β :=
  ⟨fun _ => IsIso.of_isIso_comp_left e.hom β, fun _ => inferInstance⟩

/-- **The derivation unit of an abelian right derived functor of `F ↦ i_*ℋ_Z(F)` is invertible at
the underlying abelian complex of a K-injective complex of `𝒪_X`-modules with injective terms.**

This is the endofunctor form of
`Stacks.Cohomology.SupportedComplexes.abelianSupportedUnit_isIso_at_underlying_kInjective`, and
is proved the same way, from the endofunctor form
`Stacks.Cohomology.SupportedComplexes.supportedSections_map_quasiIso_of_kInjectiveModule` of the
flasqueness input: a K-injective resolution of the underlying abelian complex stays a
quasi-isomorphism after applying `F ↦ i_*ℋ_Z(F)`, the unit is invertible at the K-injective
resolution, and naturality transports invertibility back. -/
private lemma abelianEndoUnit_isIso_at_underlying_kInjective (hZ : IsClosed Z)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n)) :
    IsIso (aHab.app
      (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I))) := by
  let Ab := Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}
  let A := abelianSupportedSections Z
  let M : CochainComplex Ab ℤ :=
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
  let J : CochainComplex Ab ℤ := (Stacks.Injectives.kInjectiveResolutionFunctor Ab).obj M
  let q : M ⟶ J := (Stacks.Injectives.kInjectiveResolutionInclusion Ab).app M
  let Q := HomotopyCategory.quotient Ab (ComplexShape.up ℤ)
  have hαJ : IsIso (aHab.app (Q.obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (A.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RHab aHab J
  have hqA : IsIso ((A.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).map (Q.map q)) := by
    have := supportedSections_map_quasiIso_of_kInjectiveModule (structureSheafRing X) Z hZ I hI J
      (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective Ab M n) q
    exact isIso_Qh_map_quotient_map ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  have hqD : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map q
  have hqR : IsIso ((DerivedCategory.Qh ⋙ RHab).map (Q.map q)) := by
    change IsIso (RHab.map (DerivedCategory.Qh.map (Q.map q)))
    infer_instance
  have hcomp : IsIso (aHab.app (Q.obj M) ≫ (DerivedCategory.Qh ⋙ RHab).map (Q.map q)) := by
    rw [← aHab.naturality (Q.map q)]
    infer_instance
  change IsIso (aHab.app (Q.obj M))
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Qh ⋙ RHab).map (Q.map q))

/-- The comparison unit `abelianSupportedEndoForgetUnit` is invertible at a K-injective complex
of `𝒪_X`-modules with injective terms: it is a composite of seven factors, six of which are
components of isomorphisms or identities, the seventh being the derivation unit of `RHab`, which
`abelianEndoUnit_isIso_at_underlying_kInjective` makes invertible there. -/
private lemma isIso_abelianSupportedEndoForgetUnit_app (hZ : IsClosed Z)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n)) :
    IsIso ((abelianSupportedEndoForgetUnit X Z RHab aHab).app
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := by
  have hα := abelianEndoUnit_isIso_at_underlying_kInjective X Z RHab aHab hZ I hI
  unfold abelianSupportedEndoForgetUnit
  refine isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_
    (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ ?_)))))
  · exact isIso_whiskerLeft_isoHom_app _ _ _
  · exact isIso_associator_inv_app _ _ _ _
  · exact isIso_whiskerRight_isoHom_app _ _ _
  · exact isIso_whiskerRight_isoInv_app _ _ _
  · exact isIso_associator_hom_app _ _ _ _
  · exact isIso_whiskerLeft_app _ aHab _ hα
  · exact isIso_whiskerRight_isoInv_app _ _ _

/-- The derivation unit of `RH ⋙ Φ` is invertible at a K-injective complex of `𝒪_X`-modules: it
is the derivation unit of `RH` there, which is invertible because the complex is K-injective,
followed by the forgetful functor and an identity. -/
private lemma isIso_forgetfulSupportedEndoUnit_app
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((forgetfulSupportedEndoUnit X Z RH aH).app
      ((HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I)) := by
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    ((supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) RH aH I
  dsimp only [forgetfulSupportedEndoUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  infer_instance

/-- **The comparison of [Stacks, Tag 0G74] part (2), with `i_*` folded in, is invertible.**
For a closed subset `Z` of `X`, arbitrary right derived functors `RH` of `ℱ ↦ i_*ℋ_Z(ℱ)` on
`𝒪_X`-modules and `RHab` of `F ↦ i_*ℋ_Z(F)` on abelian sheaves, the canonical map

`(i_* R𝓗_Z(K))_ab ⟶ i_* R𝓗_Z^{ab}(K_ab)`

is an isomorphism of endofunctors of the derived categories.

The proof is that of `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` of
`Stacks.Cohomology.SupportedComplexes`,
with `i_*` folded in: it is enough to check invertibility at the image of a K-injective complex,
a K-injective resolution with injective terms has the same image in the derived category, and
there both derivation units are invertible, so the characterising factorisation
`abelianSupportedEndoForgetComparison_fac` forces the comparison to be invertible. -/
public theorem isIso_abelianSupportedEndoForgetComparison (hZ : IsClosed Z)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    IsIso (abelianSupportedEndoForgetComparison X Z RHab aHab RH aH) := by
  let Md := _root_.SheafOfModules.{u} (structureSheafRing X)
  apply Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives
  intro K _
  let Q := HomotopyCategory.quotient Md (ComplexShape.up ℤ)
  let I : CochainComplex Md ℤ := (Stacks.Injectives.kInjectiveResolutionFunctor Md).obj K
  let q : K ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion Md).app K
  have hq : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map q
  rw [NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Qh.map (Q.map q)))]
  have hβI := isIso_abelianSupportedEndoForgetUnit_app X Z RHab aHab hZ I
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective Md K n)
  have haI := isIso_forgetfulSupportedEndoUnit_app X Z RH aH I
  have hfac : (forgetfulSupportedEndoUnit X Z RH aH).app (Q.obj I) ≫
      (abelianSupportedEndoForgetComparison X Z RHab aHab RH aH).app
        (DerivedCategory.Qh.obj (Q.obj I)) =
      (abelianSupportedEndoForgetUnit X Z RHab aHab).app (Q.obj I) := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
      congr_app (abelianSupportedEndoForgetComparison_fac X Z RHab aHab RH aH) (Q.obj I)
  have hprod : IsIso ((forgetfulSupportedEndoUnit X Z RH aH).app (Q.obj I) ≫
      (abelianSupportedEndoForgetComparison X Z RHab aHab RH aH).app
        (DerivedCategory.Qh.obj (Q.obj I))) := by
    rwa [hfac]
  exact (isIso_comp_left_iff
    (asIso ((forgetfulSupportedEndoUnit X Z RH aH).app (Q.obj I))) _).mp hprod

end Forget

end Stacks.Cohomology.AbelianSupportedCounitForget

end
