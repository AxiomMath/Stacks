module

public import StacksFrontier.AlgebraicGeometry.Bridge.EssentialImage
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Sections supported on a closed subset, as a right adjoint to pushforward

Let `Z` be a closed subset of a ringed space `X`, equipped with the restricted structure sheaf
`𝒪_X|_Z = i⁻¹𝒪_X`, and let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the inclusion. The sections of an
`𝒪_X`-module `F` supported on `Z` form a submodule sheaf of `F` which is pushed forward from
`Z`; choosing a preimage functorially realizes them as a functor
`H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)`, and that functor is right adjoint to `i_*`.

## Main definitions

* `supportedSectionsFunctor`: taking sections supported on `Z`, as an endofunctor of
  `𝒪_X`-modules.
* `supportedSectionsOnClosedFunctor`: its realization `H_Z` as a functor into
  `𝒪_X|_Z`-modules.

## Main results

* `supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`: pushing `H_Z` forward
  recovers the supported-sections subsheaf.
* `modulePushforward_supportedSectionsOnClosed_adjunction`: **Stacks 0G6P**, `i_*` is left
  adjoint to `H_Z`.

## Implementation notes

The comorphism of `i` is the unit `𝒪_X ⟶ i_* i⁻¹𝒪_X`, which is locally surjective because
every germ map of `i` is an isomorphism and the stalks of `i_* i⁻¹𝒪_X` off `Z` are terminal.
So `i` satisfies the hypotheses of Stacks 08KS: `i_*` is fully faithful and its essential image
consists of the modules annihilated by the kernel ideal of the comorphism. The supported
sections are annihilated by it — a section of the kernel ideal has vanishing germs on `Z`, a
supported section has vanishing germs off `Z`, so the product has no nonvanishing germ at all —
and `H_Z` is therefore obtained by factoring the supported-sections endofunctor through the
essential image, using `CategoryTheory.Functor.essImage.liftFunctor`. Its defining property is
recorded by the natural isomorphism
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` after pushforward, not by an
equation between chosen objects, and everything downstream is stated through it.

The adjunction is built from its hom-set bijection. The left adjoint is fully faithful, so a
map `i_* A ⟶ B` is determined by a map `A ⟶ H_Z B`; the bijection factors a map out of `i_* A`
through the supported-sections subsheaf of `B`, which is possible because `i_* A` is supported
on `Z`, and then transports along the realization isomorphism. Naturality in the right variable
uses that the factorization is unique, the inclusion of the subsheaf being a monomorphism.

This is the module-level counterpart of the abelian-sheaf statement
`ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction`
(Stacks 01AZ).

## References

* [Stacks Project, Lemma 17.13.6 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.SheafOfModules.SupportedSections

/-- The comorphism `𝒪_X ⟶ i_*(i⁻¹𝒪_X)` of the projection from an inverse-image ringed space is
locally surjective when `i` is a closed embedding: at a point of `Z` the germ map of the
projection is an isomorphism, and off `Z` the stalk of `i_*(i⁻¹𝒪_X)` is the zero ring. -/
theorem isLocallySurjective_inverseImageProjection_c (X : RingedSpace.{u, u})
    {Z : TopCat.{u}} (i : Z ⟶ X.carrier)
    (hi : Topology.IsClosedEmbedding (ConcreteCategory.hom i)) :
    TopCat.Presheaf.IsLocallySurjective
      (RingedSpace.inverseImageProjection X i).hom.c := by
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hx : x ∈ Set.range (ConcreteCategory.hom i)
  · obtain ⟨z, rfl⟩ := hx
    have hfac : (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (ConcreteCategory.hom i z)).map
          (RingedSpace.inverseImageProjection X i).hom.c ≫
        (RingedSpace.inverseImage X i).presheaf.stalkPushforward CommRingCat.{u} i z =
        (RingedSpace.inverseImageProjection X i).hom.stalkMap z := rfl
    have hbijpush := (ConcreteCategory.isIso_iff_bijective
      ((RingedSpace.inverseImage X i).presheaf.stalkPushforward CommRingCat.{u} i z)).mp
      (TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        CommRingCat.{u} hi.isInducing _ z)
    have hbijmap := (ConcreteCategory.isIso_iff_bijective _).mp
      (RingedSpace.isIso_stalkMap_inverseImageProjection X i z)
    intro b
    obtain ⟨a, ha⟩ := hbijmap.2
      ((RingedSpace.inverseImage X i).presheaf.stalkPushforward CommRingCat.{u} i z b)
    exact ⟨a, hbijpush.1 ((ConcreteCategory.congr_hom hfac a).trans ha)⟩
  · have hss := CommRingCat.subsingleton_of_isTerminal
      (ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
        i (RingedSpace.inverseImage X i).IsSheaf hi x hx)
    exact fun _ => ⟨0, hss.elim _ _⟩

/-- A morphism of `𝒪_X`-modules carries sections supported on `Z` to sections supported on `Z`,
because the support of the image of a section is contained in the support of the section. -/
noncomputable def supportedSectionsMap {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ G) :
    (supportedSectionsSheaf Z F).1 ⟶ (supportedSectionsSheaf Z G).1 :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun s => ⟨f.val.app U s.1, fun _ hx =>
          s.2 (RingedSpace.ModuleSheaf.suppSection_map_subset
            (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F)
            (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G) f.val (unop U) s.1 hx)⟩)
        (fun a b => Subtype.ext (map_add (ConcreteCategory.hom (f.val.app U)) a.1 b.1))
      naturality := fun U V j => by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val j s.1) }
    (fun U r s => Subtype.ext ((f.val.app U).hom.map_smul r s.1))⟩

/-- On sections, the restriction of a morphism to the supported sections is the morphism. -/
@[simp]
theorem supportedSectionsMap_val_app {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ G) (U : (Opens X.carrier)ᵒᵖ)
    (s : (supportedSectionsSheaf Z F).1.val.obj U) :
    ((supportedSectionsMap Z f).val.app U s).1 = f.val.app U s.1 :=
  rfl

/-- **Stacks 0G6N.** Taking the sections supported on `Z`, as an endofunctor of
`𝒪_X`-modules. -/
noncomputable def supportedSectionsFunctor (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing X) where
  obj F := (supportedSectionsSheaf Z F).1
  map f := supportedSectionsMap Z f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The supported-sections functor sends `F` to the subsheaf of sections supported on `Z`. -/
@[simp]
theorem supportedSectionsFunctor_obj (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsFunctor X Z).obj F = (supportedSectionsSheaf Z F).1 :=
  rfl

/-- The supported-sections functor acts on a morphism `f` by `supportedSectionsMap Z f`. -/
@[simp]
theorem supportedSectionsFunctor_map (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ G) :
    (supportedSectionsFunctor X Z).map f = supportedSectionsMap Z f :=
  rfl

/-- The inclusion of the supported-sections subsheaf is natural in the module. -/
theorem supportedSectionsSheafι_naturality {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    {F G : _root_.SheafOfModules.{u} (structureSheafRing X)} (f : F ⟶ G) :
    (supportedSectionsFunctor X Z).map f ≫ supportedSectionsSheafι Z G =
      supportedSectionsSheafι Z F ≫ f := by
  ext U s
  rfl

/-- A section of a sheaf of modules whose germ vanishes at every point of its open set is zero:
it vanishes on a covering of that open set, and the sheaf condition does the rest. -/
private theorem section_eq_zero_of_sectionGerm_eq_zero {X : RingedSpace.{u, u}}
    (F : RingedSpace.ModuleSheaf.{u} X) (U : Opens X.carrier)
    (s : F.toPresheaf.obj (op U))
    (hs : ∀ (x : X.carrier) (hx : x ∈ U), F.sectionGerm U x hx s = 0) :
    s = 0 := by
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X.carrier)
      (F.abPresheaf ⋙ forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf F.abPresheaf F.isSheaf)
  choose V hxV j hzero using fun x : U =>
    (F.sectionGerm_eq_zero_iff U x.1 x.2 s).mp (hs x.1 x.2)
  have hV (x : U) : V x ≤ U := (j x).le
  refine (hF.isSheafFor (.ofArrows V fun x => homOfLE (hV x)) ?_).isSeparatedFor.ext ?_
  · intro x hx
    exact ⟨V ⟨x, hx⟩, homOfLE (hV _), Sieve.ofArrows_mk _ _ _, hxV _⟩
  · rintro _ _ ⟨x⟩
    change F.toPresheaf.map (homOfLE (hV x)).op s = F.toPresheaf.map (homOfLE (hV x)).op 0
    rw [show homOfLE (hV x) = j x from Subsingleton.elim _ _, hzero x, map_zero]

/-- A section of the kernel ideal of the comorphism of `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` has
vanishing germs at the points of `Z`, because the germ maps of `i` are isomorphisms. -/
theorem germ_eq_zero_of_mem_kernelIdeal (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (U : Opens X.carrier)
    (a : (structureSheafRing X).obj.obj (op U))
    (ha : a ∈ Stacks.Tag08KS.kernelIdeal
      (RingedSpace.inverseImageProjection X (ClosedImmersionSheaves.closedSubsetInclusion Z)) U)
    (x : X.carrier) (hx : x ∈ U) (hxZ : x ∈ Z) :
    X.presheaf.germ U x hx a = 0 := by
  set j := ClosedImmersionSheaves.closedSubsetInclusion Z
  set i := RingedSpace.inverseImageProjection X j
  have hinj : Function.Injective
      (i.hom.stalkMap (⟨x, hxZ⟩ : (RingedSpace.inverseImage X j).carrier)) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp
      (RingedSpace.isIso_stalkMap_inverseImageProjection X j ⟨x, hxZ⟩)).1
  have hgerm := AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply i.hom U
    (⟨x, hxZ⟩ : (RingedSpace.inverseImage X j).carrier) hx a
  have ha0 : (ConcreteCategory.hom (i.hom.c.app (op U))) a = 0 := ha
  have hz : (ConcreteCategory.hom (i.hom.stalkMap
      (⟨x, hxZ⟩ : (RingedSpace.inverseImage X j).carrier)))
      ((ConcreteCategory.hom (X.presheaf.germ U x hx)) a) = 0 :=
    hgerm.trans (by rw [ha0, map_zero])
  exact hinj (hz.trans (map_zero _).symm)

/-- **Stacks 08KS, applied to a closed subset.** The sections of `F` supported on a closed
subset `Z` are annihilated by the kernel ideal of the comorphism of the inclusion
`i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)`: a section of the kernel ideal has vanishing germs on `Z` and a
supported section has vanishing germs off `Z`, so the product has no nonvanishing germ. -/
theorem isAnnihilatedByKernelIdeal_supportedSectionsSheaf (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    Stacks.Tag08KS.IsAnnihilatedByKernelIdeal
      (RingedSpace.inverseImageProjection X (ClosedImmersionSheaves.closedSubsetInclusion Z))
      (supportedSectionsSheaf Z F).1 := by
  intro U a ha m
  have hinj : Function.Injective
      (ConcreteCategory.hom ((supportedSectionsSheafι Z F).val.app (op U))) :=
    (supportedSectionsSheaf Z F).2.2.1 (op U)
  apply hinj
  rw [map_smul, map_zero]
  set s : ↑(F.val.obj (op U)) :=
    (ConcreteCategory.hom ((supportedSectionsSheafι Z F).val.app (op U))) m
  refine section_eq_zero_of_sectionGerm_eq_zero
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F) U (a • s) fun x hx => ?_
  change TopCat.Presheaf.germ F.val.presheaf U x hx (a • s) = 0
  rw [PresheafOfModules.germ_ringCat_smul]
  by_cases hxZ : x ∈ Z
  · have hscalar : (ConcreteCategory.hom
        (TopCat.Presheaf.germ (structureSheafRing X).obj U x hx)) a = 0 := by
      refine (SemilinearStalk.commStalkRingEquiv X.presheaf x).injective ?_
      exact ((SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hx a).trans
        (germ_eq_zero_of_mem_kernelIdeal X Z U a ha x hx hxZ)).trans
        (map_zero (SemilinearStalk.commStalkRingEquiv X.presheaf x)).symm
    rw [hscalar, zero_smul]
  · have hm : TopCat.Presheaf.germ F.val.presheaf U x hx s = 0 := by
      by_contra hne
      exact hxZ (m.2 ⟨hx, hne⟩).1
    rw [hm, smul_zero]

/-- The inclusion of a closed subset of a ringed space is a closed embedding of underlying
spaces. -/
theorem isClosedEmbedding_closedSubsetInclusion (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    Topology.IsClosedEmbedding (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z)).hom.base :=
  hZ.isClosedEmbedding_subtypeVal

/-- **Stacks 08KS.** Pushforward of modules along the inclusion of a closed subset of a ringed
space is fully faithful. -/
noncomputable def fullyFaithfulModulePushforwardClosedSubset (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z))).FullyFaithful :=
  have := Stacks.Tag08KS.modulePushforward_full _
    (isClosedEmbedding_closedSubsetInclusion X Z hZ)
    (isLocallySurjective_inverseImageProjection_c X _ hZ.isClosedEmbedding_subtypeVal)
  have := Stacks.Tag08KS.modulePushforward_faithful _
    (isClosedEmbedding_closedSubsetInclusion X Z hZ)
    (isLocallySurjective_inverseImageProjection_c X _ hZ.isClosedEmbedding_subtypeVal)
  .ofFullyFaithful _

/-- **Stacks 08KS.** The sheaf of sections supported on a closed subset `Z` is pushed forward
from `Z`: it lies in the essential image of `i_*`, being annihilated by the kernel ideal of the
comorphism of `i`. -/
theorem supportedSectionsSheaf_mem_modulePushforward_essImage (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z))).essImage
      ((supportedSectionsSheaf Z F).1) :=
  (Stacks.Tag08KS.modulePushforward_essImage_iff_kernelIdeal_annihilates _
    (isClosedEmbedding_closedSubsetInclusion X Z hZ)
    (isLocallySurjective_inverseImageProjection_c X _ hZ.isClosedEmbedding_subtypeVal)
    _).2 (isAnnihilatedByKernelIdeal_supportedSectionsSheaf X Z F)

/-- **Stacks 0G6N.** The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on a
closed subset `Z`, realized as a sheaf of modules on `Z`. It is characterised, up to the
natural isomorphism `supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`, by the
property that its pushforward to `X` is the supported-sections subsheaf. -/
@[stacks 0G6N "H_Z as a functor Mod(O_X) ⥤ Mod(O_X|_Z)"]
noncomputable def supportedSectionsOnClosedFunctor (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing (RingedSpace.inverseImage X
        (ClosedImmersionSheaves.closedSubsetInclusion Z))) :=
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).full
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  Functor.essImage.liftFunctor (supportedSectionsFunctor X Z)
    (modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z)))
    (fun F => supportedSectionsSheaf_mem_modulePushforward_essImage X Z hZ F)

/-- Pushing the realization `H_Z` forward to `X` recovers the subsheaf of sections supported
on `Z`, naturally in the module. -/
noncomputable def supportedSectionsOnClosedFunctor_comp_modulePushforward_iso
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) :
    supportedSectionsOnClosedFunctor X Z hZ ⋙
        modulePushforward (RingedSpace.inverseImageProjection X
          (ClosedImmersionSheaves.closedSubsetInclusion Z)) ≅
      supportedSectionsFunctor X Z :=
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).full
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  Functor.essImage.liftFunctorCompIso (supportedSectionsFunctor X Z)
    (modulePushforward (RingedSpace.inverseImageProjection X
      (ClosedImmersionSheaves.closedSubsetInclusion Z)))
    (fun F => supportedSectionsSheaf_mem_modulePushforward_essImage X Z hZ F)

/-- A morphism into `F` out of a module supported on `Z` factors through the subsheaf of
sections of `F` supported on `Z`. This is the data refining
`hom_to_supportedSectionsSheaf_of_supp_subset`; the factorization is unique, the inclusion of
the subsheaf being a monomorphism. -/
noncomputable def liftToSupportedSectionsSheaf {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (f : G ⟶ F)
    (hG : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp ⊆ Z) :
    G ⟶ (supportedSectionsSheaf Z F).1 :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
        (fun s => ⟨f.val.app U s, fun _ hx =>
          ⟨hG ((RingedSpace.ModuleSheaf.mem_supp_iff _ _).2 ⟨unop U, s,
            RingedSpace.ModuleSheaf.suppSection_map_subset
              (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G)
              (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F) f.val (unop U) s hx⟩),
            hx.1⟩⟩)
        (fun s t => Subtype.ext (map_add (ConcreteCategory.hom (f.val.app U)) s t))
      naturality := fun U V j => by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val j s) }
    (fun U r s => Subtype.ext ((f.val.app U).hom.map_smul r s))⟩

/-- The lift of `f` to the supported-sections subsheaf, followed by the inclusion, is `f`. -/
@[simp]
theorem liftToSupportedSectionsSheaf_comp {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (f : G ⟶ F)
    (hG : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules G).supp ⊆ Z) :
    liftToSupportedSectionsSheaf Z F G f hG ≫ supportedSectionsSheafι Z F = f := by
  ext U s
  rfl

/-- **Stacks 01AX.** A module pushed forward from a closed subset `Z` is supported on `Z`:
away from `Z` the stalks of `i_* A` are terminal. -/
theorem supp_modulePushforward_subset (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z)
    (A : _root_.SheafOfModules.{u} (structureSheafRing (RingedSpace.inverseImage X
      (ClosedImmersionSheaves.closedSubsetInclusion Z)))) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      ((modulePushforward (RingedSpace.inverseImageProjection X
        (ClosedImmersionSheaves.closedSubsetInclusion Z))).obj A)).supp ⊆ Z := by
  intro x hx
  by_contra hxZ
  obtain ⟨b, hb⟩ := hx
  refine hb ?_
  have hrange : x ∉ Set.range (ConcreteCategory.hom
      (ClosedImmersionSheaves.closedSubsetInclusion Z)) := by
    rintro ⟨z, rfl⟩
    exact hxZ z.property
  have hterm : IsTerminal ((AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      ((modulePushforward (RingedSpace.inverseImageProjection X
        (ClosedImmersionSheaves.closedSubsetInclusion Z))).obj A)).abPresheaf.stalk x) :=
    ClosedImmersionSheaves.isTerminalStalkPushforwardOfNotMemRange
      (ClosedImmersionSheaves.closedSubsetInclusion Z) A.isSheaf
      hZ.isClosedEmbedding_subtypeVal x hrange
  have : Limits.PreservesLimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u}) :=
    inferInstance
  have := Limits.Concrete.uniqueOfTerminalOfPreserves _ hterm
  exact Subsingleton.elim _ _

/-- **Stacks 0G6P.** For a closed subset `Z` of a ringed space `X`, with the restricted
structure sheaf `𝒪_X|_Z`, pushforward of modules along the inclusion `i : (Z, 𝒪_X|_Z) ⟶ X` is
left adjoint to the functor `H_Z` of sections supported on `Z`. -/
@[stacks 0G6P]
noncomputable def modulePushforward_supportedSectionsOnClosed_adjunction (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    modulePushforward (RingedSpace.inverseImageProjection X
        (ClosedImmersionSheaves.closedSubsetInclusion Z)) ⊣
      supportedSectionsOnClosedFunctor X Z hZ := by
  let MZ := _root_.SheafOfModules.{u} (structureSheafRing (RingedSpace.inverseImage X
    (ClosedImmersionSheaves.closedSubsetInclusion Z)))
  let MX := _root_.SheafOfModules.{u} (structureSheafRing X)
  let P : MZ ⥤ MX := modulePushforward (RingedSpace.inverseImageProjection X
    (ClosedImmersionSheaves.closedSubsetInclusion Z))
  let R : MX ⥤ MZ := supportedSectionsOnClosedFunctor X Z hZ
  let S : MX ⥤ MX := supportedSectionsFunctor X Z
  let ρ : R ⋙ P ≅ S := supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ
  let ι : ∀ B : MX, S.obj B ⟶ B := fun B => supportedSectionsSheafι Z B
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).full
  haveI := (fullyFaithfulModulePushforwardClosedSubset X Z hZ).faithful
  let ff := Functor.FullyFaithful.ofFullyFaithful P
  let factor : ∀ {A : MZ} {B : MX}, (P.obj A ⟶ B) → (P.obj A ⟶ S.obj B) :=
    fun {A B} f => liftToSupportedSectionsSheaf Z B (P.obj A) f
      (supp_modulePushforward_subset X Z hZ A)
  have factor_comp : ∀ (A : MZ) (B : MX) (f : P.obj A ⟶ B), factor f ≫ ι B = f :=
    fun A B f => liftToSupportedSectionsSheaf_comp Z B (P.obj A) f _
  have hmono : ∀ B : MX, Mono (ι B) := fun B => supportedSectionsSheafι_mono Z B
  have factor_naturality : ∀ (A : MZ) (B B' : MX) (f : P.obj A ⟶ B) (g : B ⟶ B'),
      factor (f ≫ g) = factor f ≫ S.map g := by
    intro A B B' f g
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext s
    rfl
  let homEquiv : (A : MZ) → (B : MX) → (P.obj A ⟶ B) ≃ (A ⟶ R.obj B) :=
    fun A B => {
      toFun := fun f => ff.preimage (factor f ≫ (ρ.app B).inv)
      invFun := fun g => P.map g ≫ (ρ.app B).hom ≫ ι B
      left_inv f := by
        change P.map (ff.preimage (factor f ≫ (ρ.app B).inv)) ≫ (ρ.app B).hom ≫ ι B = f
        rw [ff.map_preimage, Category.assoc, Iso.inv_hom_id_assoc]
        exact factor_comp A B f
      right_inv g := by
        have hfactor : factor (P.map g ≫ (ρ.app B).hom ≫ ι B) = P.map g ≫ (ρ.app B).hom := by
          refine (cancel_mono (ι B)).1 ?_
          rw [factor_comp A B (P.map g ≫ (ρ.app B).hom ≫ ι B), Category.assoc]
        apply P.map_injective
        rw [ff.map_preimage, hfactor, Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  refine Adjunction.mkOfHomEquiv (F := P) (G := R) {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      dsimp only [homEquiv]
      simp only [Equiv.coe_fn_symm_mk, Functor.map_comp, Category.assoc]
    homEquiv_naturality_right := by
      intro A B B' f g
      dsimp only [homEquiv]
      simp only [Equiv.coe_fn_mk]
      apply P.map_injective
      rw [ff.map_preimage, factor_naturality A B B' f g]
      simp only [Functor.map_comp, Category.assoc]
      rw [ff.map_preimage]
      have h := ρ.inv.naturality g
      change S.map g ≫ (ρ.app B').inv = (ρ.app B).inv ≫ P.map (R.map g) at h
      simpa only [Category.assoc] using congrArg (fun k => factor f ≫ k) h }

end Stacks.SheafOfModules.SupportedSections

end
