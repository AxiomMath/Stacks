module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionVanishingUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FlasqueSoftUnivLE

/-!
# The comparison map of [Stacks, Tag 09V3], in a coefficient universe of its own
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat Abelian
open Stacks.Cohomology.FreeYonedaUnivLE

namespace Stacks.Topology

universe uC vC w w' t s

noncomputable section

variable {X : TopCat.{s}} (Z : Set X)

/-- **The restriction of abelian sheaves to a subset, at a coefficient universe independent of
the space, with its type written in the spelling the `Ext`-groups are taken in.**
`Stacks.Topology.restrictionFunctorUnivLE` has the same body but ascribes the spelling
`TopCat.Sheaf C X`; the two are definitionally equal (`siteRestrictionUnivLE_eq` below), but
instance search and `rw` do not cross the `nonrec def` between them, and it is this spelling that
`CategoryTheory.Sheaf.cohomologyPresheaf`, `HasExt` and
`Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda` are stated in. -/
abbrev siteRestrictionUnivLE (X : TopCat.{s}) (Z : Set X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t} :=
  (Opens.map (Stacks.subsetInclusion X Z)).sheafPullback AddCommGrpCat.{max s t}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))

/-- The two spellings are the same functor. -/
theorem siteRestrictionUnivLE_eq (X : TopCat.{s}) (Z : Set X) :
    siteRestrictionUnivLE.{t} X Z = restrictionFunctorUnivLE.{max s t} X Z :=
  rfl

/-- The sheaf-level inverse-image/direct-image adjunction along the inclusion of `Z`, at a
coefficient universe independent of the space. -/
abbrev subsetAdjunctionUnivLE (X : TopCat.{s}) (Z : Set X) :
    siteRestrictionUnivLE.{t} X Z ⊣
      (Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous
        AddCommGrpCat.{max s t} (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (TopCat.of Z)) :=
  (Opens.map (Stacks.subsetInclusion X Z)).sheafAdjunctionContinuous AddCommGrpCat.{max s t}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z))

/-- The restriction of abelian sheaves to `Z` is a left adjoint. -/
instance isLeftAdjoint_siteRestrictionUnivLE :
    (siteRestrictionUnivLE.{t} X Z).IsLeftAdjoint :=
  (subsetAdjunctionUnivLE.{t} X Z).isLeftAdjoint

/-- The restriction of abelian sheaves to `Z` preserves finite limits. -/
instance preservesFiniteLimits_siteRestrictionUnivLE :
    PreservesFiniteLimits (siteRestrictionUnivLE.{t} X Z) :=
  preservesFiniteLimits_restrictionFunctorUnivLE.{max s t} X Z

/-- The restriction of abelian sheaves to `Z` preserves finite colimits. -/
instance preservesFiniteColimits_siteRestrictionUnivLE :
    PreservesFiniteColimits (siteRestrictionUnivLE.{t} X Z) :=
  (subsetAdjunctionUnivLE.{t} X Z).leftAdjoint_preservesColimits.preservesFiniteColimits.{max s t,
    max s t}

/-- The restriction of abelian sheaves to `Z` is an additive functor. -/
instance additive_siteRestrictionUnivLE :
    (siteRestrictionUnivLE.{t} X Z).Additive :=
  letI := (subsetAdjunctionUnivLE.{t} X Z).leftAdjoint_preservesColimits
  letI : PreservesBinaryBiproducts (siteRestrictionUnivLE.{t} X Z) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

section Naturality

variable {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}} (β : F ⟶ G)

/-- Applying the direct image to a map of restrictions and evaluating at an open `U` of `X` is
evaluating the map of restrictions at `i^{-1} U`. -/
theorem subsetPushforward_map_app (U : Opens X) :
    (((Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous
          AddCommGrpCat.{max s t} (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z))).map
        ((siteRestrictionUnivLE.{t} X Z).map β)).hom.app (op U) =
      ((siteRestrictionUnivLE.{t} X Z).map β).hom.app
        (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U)) :=
  rfl

/-- **The section of a restriction induced by a section is natural in the sheaf**, at a
coefficient universe independent of the space. This is `Stacks.Topology.ambientSection_naturality`
with the coefficients freed, and it is short where the pinned statement is long: the pinned
`ambientSection` is the *presheaf*-level adjunction unit followed by `toSheafify` and Mathlib's
`sheafPullbackPresheafIso`, so its naturality has to concatenate four separate squares, while
`Stacks.Topology.ambientSectionUnivLE` is the unit of the *sheaf*-level adjunction
`Functor.sheafAdjunctionContinuous`, which is natural in the sheaf by construction. -/
theorem ambientSectionUnivLE_naturality {U : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U) :
    ambientSectionUnivLE.{max s t} F Z h ≫
        ((siteRestrictionUnivLE.{t} X Z).map β).hom.app (op V) =
      β.hom.app (op U) ≫ ambientSectionUnivLE.{max s t} G Z h := by
  have hunit : β ≫ subsetUnit.{max s t} G Z =
      subsetUnit.{max s t} F Z ≫
        ((Opens.map (Stacks.subsetInclusion X Z)).sheafPushforwardContinuous
          AddCommGrpCat.{max s t} (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z))).map
            ((siteRestrictionUnivLE.{t} X Z).map β) :=
    (subsetAdjunctionUnivLE.{t} X Z).unit.naturality β
  have hsq : ((siteRestrictionUnivLE.{t} X Z).obj F).obj.map (homOfLE h).op ≫
      ((siteRestrictionUnivLE.{t} X Z).map β).hom.app (op V) =
    ((siteRestrictionUnivLE.{t} X Z).map β).hom.app
        (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U)) ≫
      ((siteRestrictionUnivLE.{t} X Z).obj G).obj.map (homOfLE h).op :=
    ((siteRestrictionUnivLE.{t} X Z).map β).hom.naturality (homOfLE h).op
  calc ambientSectionUnivLE.{max s t} F Z h ≫
        ((siteRestrictionUnivLE.{t} X Z).map β).hom.app (op V)
      = (subsetUnit.{max s t} F Z).hom.app (op U) ≫
          (((siteRestrictionUnivLE.{t} X Z).obj F).obj.map (homOfLE h).op ≫
            ((siteRestrictionUnivLE.{t} X Z).map β).hom.app (op V)) :=
        Category.assoc _ _ _
    _ = (subsetUnit.{max s t} F Z).hom.app (op U) ≫
          ((((siteRestrictionUnivLE.{t} X Z).map β).hom.app
              (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U)) ≫
            ((siteRestrictionUnivLE.{t} X Z).obj G).obj.map (homOfLE h).op)) :=
        congrArg ((subsetUnit.{max s t} F Z).hom.app (op U) ≫ ·) hsq
    _ = ((subsetUnit.{max s t} F Z).hom.app (op U) ≫
          ((siteRestrictionUnivLE.{t} X Z).map β).hom.app
            (op ((Opens.map (Stacks.subsetInclusion X Z)).obj U))) ≫
          ((siteRestrictionUnivLE.{t} X Z).obj G).obj.map (homOfLE h).op :=
        (Category.assoc _ _ _).symm
    _ = (β.hom.app (op U) ≫ (subsetUnit.{max s t} G Z).hom.app (op U)) ≫
          ((siteRestrictionUnivLE.{t} X Z).obj G).obj.map (homOfLE h).op := by
        refine congrArg
          (· ≫ ((siteRestrictionUnivLE.{t} X Z).obj G).obj.map (homOfLE h).op) ?_
        exact (congrArg (fun m ↦ NatTrans.app m.hom (op U)) hunit).symm
    _ = β.hom.app (op U) ≫ ambientSectionUnivLE.{max s t} G Z h := Category.assoc _ _ _

/-- `ambientSectionUnivLE_naturality` on elements. -/
theorem ambientSectionUnivLE_naturality_apply {U : Opens X} {V : Opens (TopCat.of Z)}
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (σ : ToType (F.obj.obj (op U))) :
    ((siteRestrictionUnivLE.{t} X Z).map β).hom.app (op V)
        (ambientSectionUnivLE.{max s t} F Z h σ) =
      ambientSectionUnivLE.{max s t} G Z h (β.hom.app (op U) σ) :=
  (ConcreteCategory.comp_apply _ _ σ).symm.trans
    ((ConcreteCategory.congr_hom (ambientSectionUnivLE_naturality.{t} Z β h) σ).trans
      (ConcreteCategory.comp_apply _ _ σ))

end Naturality

/-- `Stacks.Topology.ambientSectionUnivLE_map` on elements. -/
theorem ambientSectionUnivLE_map_apply (F : X.Sheaf AddCommGrpCat.{max s t})
    {U U' : Opens X} {V : Opens (TopCat.of Z)} (m : U' ⟶ U)
    (h : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U')
    (h' : V ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U)
    (σ : ToType (F.obj.obj (op U))) :
    ambientSectionUnivLE.{max s t} F Z h (F.presheaf.map m.op σ) =
      ambientSectionUnivLE.{max s t} F Z h' σ :=
  (ConcreteCategory.comp_apply _ _ σ).symm.trans
    (ConcreteCategory.congr_hom (ambientSectionUnivLE_map.{max s t} F Z m h h') σ)

section Comparison

/-- **The canonical map from the free abelian sheaf on the whole of `Z` to the restriction of the
free abelian sheaf on an open neighbourhood of `Z`**, at a coefficient universe independent of
the space. This is `Stacks.Topology.freeRestrictionMap` with the coefficients freed. -/
def freeRestrictionMapUnivLE (U : OpenNhdsSet Z) :
    (freeYoneda.{max s t} (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤ ⟶
      (siteRestrictionUnivLE.{t} X Z).obj
        ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) :=
  (sectionsEquiv.{max s t} ⊤ _).symm
    (ambientSectionUnivLE.{max s t}
      ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) Z
      (top_le_map_openNhdsSet U) (gen.{max s t} U.obj))

/-- The section of the restricted free abelian sheaf corresponding to
`freeRestrictionMapUnivLE Z U` is the ambient section of the generator on `U`. -/
theorem sectionsEquiv_freeRestrictionMapUnivLE (U : OpenNhdsSet Z) :
    sectionsEquiv.{max s t} ⊤ _ (freeRestrictionMapUnivLE.{t} Z U) =
      ambientSectionUnivLE.{max s t}
        ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) Z
        (top_le_map_openNhdsSet U) (gen.{max s t} U.obj) :=
  (sectionsEquiv.{max s t} ⊤ _).apply_symm_apply _

/-- **The canonical maps from the free abelian sheaf on `Z` are compatible with shrinking the
neighbourhood**, at a coefficient universe independent of the space. -/
theorem freeRestrictionMapUnivLE_comp {U V : OpenNhdsSet Z} (h : V.obj ⟶ U.obj) :
    freeRestrictionMapUnivLE.{t} Z V ≫ (siteRestrictionUnivLE.{t} X Z).map
        ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).map h) =
      freeRestrictionMapUnivLE.{t} Z U := by
  have hgen : ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).map h).hom.app (op V.obj)
        (gen.{max s t} V.obj) =
      ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj).obj.map h.op
        (gen.{max s t} U.obj) :=
    (sectionsEquiv_eq_app_gen.{max s t} V.obj _ _).symm.trans
      ((congrArg (sectionsEquiv.{max s t} V.obj _) (Category.comp_id _).symm).trans
        (sectionsEquiv_naturality_left.{max s t} h _ (𝟙 _)))
  refine (sectionsEquiv.{max s t} ⊤ _).injective ?_
  rw [sectionsEquiv_naturality.{max s t}, sectionsEquiv_freeRestrictionMapUnivLE.{t},
    sectionsEquiv_freeRestrictionMapUnivLE.{t}]
  refine (ambientSectionUnivLE_naturality_apply.{t} Z
    ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).map h) (top_le_map_openNhdsSet V)
    (gen.{max s t} V.obj)).trans ?_
  exact (congrArg _ hgen).trans
    (ambientSectionUnivLE_map_apply.{t} Z _ h _ _ _)

section Map

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [HasExt.{max s t}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})

/-- The diagram `U ↦ H^p(U, F)` over the open neighbourhoods of `Z`, at a coefficient universe
independent of the space. -/
def openNeighborhoodCohomologyUnivLE (p : ℕ) :
    (OpenNhdsSet Z)ᵒᵖ ⥤ AddCommGrpCat.{max s t} :=
  (openNhdsSetInclusion Z).op ⋙ cohomologyPresheaf.{max s t, max s t} F p

/-- The comparison at a single open neighbourhood of `Z`, at a coefficient universe independent
of the space. -/
def cohomologyOfClosedMapCompUnivLE (p : ℕ) (U : OpenNhdsSet Z) :
    Ext.{max s t} ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) F p →+
      Ext.{max s t} ((freeYoneda.{max s t} (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤)
        ((siteRestrictionUnivLE.{t} X Z).obj F) p :=
  ((Ext.mk₀ (freeRestrictionMapUnivLE.{t} Z U)).precomp _ (zero_add p)).comp
    ((siteRestrictionUnivLE.{t} X Z).mapExtAddHom _ _ p)

/-- The comparison at an open neighbourhood `U` sends a class `x` to the restriction of `x` to
`Z` precomposed with `freeRestrictionMapUnivLE Z U`. -/
theorem cohomologyOfClosedMapCompUnivLE_apply (p : ℕ) (U : OpenNhdsSet Z)
    (x : Ext.{max s t} ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) F p) :
    cohomologyOfClosedMapCompUnivLE.{t} Z F p U x =
      (Ext.mk₀ (freeRestrictionMapUnivLE.{t} Z U)).comp
        (x.mapExactFunctor (siteRestrictionUnivLE.{t} X Z)) (zero_add p) :=
  rfl

/-- **The comparison maps form a cocone**, at a coefficient universe independent of the space. -/
theorem cohomologyOfClosedMapCompUnivLE_naturality (p : ℕ) {U V : OpenNhdsSet Z}
    (h : V.obj ⟶ U.obj)
    (x : Ext.{max s t} ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) F p) :
    cohomologyOfClosedMapCompUnivLE.{t} Z F p V
        ((Ext.mk₀ ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).map h)).comp x
          (zero_add p)) =
      cohomologyOfClosedMapCompUnivLE.{t} Z F p U x := by
  rw [cohomologyOfClosedMapCompUnivLE_apply, cohomologyOfClosedMapCompUnivLE_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    freeRestrictionMapUnivLE_comp]

/-- **The canonical comparison map of [Stacks, Tag 09V3], at a coefficient universe independent
of the space.** -/
def cohomologyOfClosedMapUnivLE (p : ℕ) :
    colimit (openNeighborhoodCohomologyUnivLE.{t} Z F p) ⟶
      (cohomologyPresheaf.{max s t, max s t}
        ((siteRestrictionUnivLE.{t} X Z).obj F) p).obj (op ⊤) :=
  colimit.desc (openNeighborhoodCohomologyUnivLE.{t} Z F p)
    { pt := (cohomologyPresheaf.{max s t, max s t}
        ((siteRestrictionUnivLE.{t} X Z).obj F) p).obj (op ⊤)
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (cohomologyOfClosedMapCompUnivLE.{t} Z F p U.unop)
          naturality := by
            intro U V a
            refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
            simp only [Functor.const_obj_map]
            exact cohomologyOfClosedMapCompUnivLE_naturality.{t} Z F p
              ((openNhdsSetInclusion Z).map a.unop) x } }

/-- On the image of a class on an open neighbourhood `U` of `Z`, the comparison map is the
comparison at `U`. -/
theorem cohomologyOfClosedMapUnivLE_ι (p : ℕ) (U : (OpenNhdsSet Z)ᵒᵖ)
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U)) :
    cohomologyOfClosedMapUnivLE.{t} Z F p
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x) =
      cohomologyOfClosedMapCompUnivLE.{t} Z F p U.unop x :=
  (ConcreteCategory.comp_apply _ _ x).symm.trans
    (ConcreteCategory.congr_hom (colimit.ι_desc _ _) x)

/-- The forgetful functor from abelian groups preserves `s`-small filtered colimits. -/
private theorem preservesFilteredColimitsOfSize_forget_addCommGrp :
    PreservesFilteredColimitsOfSize.{s, s} (CategoryTheory.forget AddCommGrpCat.{max s t}) :=
  preservesFilteredColimitsOfSize_of_univLE.{max s t, max s t, s, s} _

omit [HasExt.{max s t}
  (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})] in
/-- Every element of the colimit over the open neighbourhoods of `Z` is represented by a class on
one of them. -/
theorem exists_colimit_ι_openNeighborhoodCohomologyUnivLE (p : ℕ)
    (c : ToType (colimit (openNeighborhoodCohomologyUnivLE.{t} Z F p))) :
    ∃ (U : (OpenNhdsSet Z)ᵒᵖ)
      (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U)),
      colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x = c := by
  have := preservesFilteredColimitsOfSize_forget_addCommGrp.{t, s}
  obtain ⟨U, x, e⟩ := Types.jointly_surjective
    (openNeighborhoodCohomologyUnivLE.{t} Z F p ⋙ CategoryTheory.forget AddCommGrpCat.{max s t})
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{max s t})
      (colimit.isColimit _)) c
  exact ⟨U, x, e⟩

section DegreeZero

/-- **The comparison in degree zero is the comparison of sections**, at a coefficient universe
independent of the space. -/
theorem cohomologyOfClosedMapCompUnivLE_zero_apply (U : OpenNhdsSet Z)
    (x : Ext.{max s t} ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj) F 0) :
    extSectionsAddEquiv.{max s t, max s t} ⊤ ((siteRestrictionUnivLE.{t} X Z).obj F)
        (cohomologyOfClosedMapCompUnivLE.{t} Z F 0 U x) =
      ambientSectionUnivLE.{max s t} F Z (top_le_map_openNhdsSet U)
        (extSectionsAddEquiv.{max s t, max s t} U.obj F x) := by
  have hmap : Ext.addEquiv₀ (x.mapExactFunctor (siteRestrictionUnivLE.{t} X Z)) =
      (siteRestrictionUnivLE.{t} X Z).map (Ext.addEquiv₀ x) := by
    refine (Ext.mk₀_bijective _ _).injective ?_
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mapExactFunctor_mk₀, Ext.mk₀_addEquiv₀_apply]
  have key : ∀ g : (freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.obj ⟶ F,
      sectionsEquiv.{max s t} ⊤ ((siteRestrictionUnivLE.{t} X Z).obj F)
          (freeRestrictionMapUnivLE.{t} Z U ≫ (siteRestrictionUnivLE.{t} X Z).map g) =
        ambientSectionUnivLE.{max s t} F Z (top_le_map_openNhdsSet U)
          (sectionsEquiv.{max s t} U.obj F g) := by
    intro g
    rw [sectionsEquiv_naturality.{max s t}, sectionsEquiv_freeRestrictionMapUnivLE.{t}]
    exact (ambientSectionUnivLE_naturality_apply.{t} Z g (top_le_map_openNhdsSet U)
      (gen.{max s t} U.obj)).trans (congrArg _ (sectionsEquiv_eq_app_gen.{max s t} U.obj F g).symm)
  rw [cohomologyOfClosedMapCompUnivLE_apply]
  dsimp only [extSectionsAddEquiv, AddEquiv.trans_apply]
  rw [addEquiv₀_mk₀_comp.{max s t}, hmap, sectionsAddEquiv_apply.{max s t},
    sectionsAddEquiv_apply.{max s t}]
  exact key _

/-- In degree zero the neighbourhood-cohomology diagram is the neighbourhood-sections diagram, at
a coefficient universe independent of the space. -/
def openNeighborhoodCohomologyZeroIsoUnivLE :
    openNeighborhoodCohomologyUnivLE.{t} Z F 0 ≅ neighborhoodSectionsUnivLE.{max s t} F Z :=
  Functor.isoWhiskerLeft (openNhdsSetInclusion Z).op (cohomologyPresheafIsoSections.{max s t, s} F)

/-- In degree zero, under the identification of `Ext⁰` with sections, the comparison map is the
map from the colimit of the sections over the open neighbourhoods of `Z` to the sections over
`Z`. -/
theorem extSectionsAddEquiv_cohomologyOfClosedMapUnivLE_zero
    (c : ToType (colimit (openNeighborhoodCohomologyUnivLE.{t} Z F 0))) :
    extSectionsAddEquiv.{max s t, max s t} ⊤ ((siteRestrictionUnivLE.{t} X Z).obj F)
        (cohomologyOfClosedMapUnivLE.{t} Z F 0 c) =
      subsetSectionsMapUnivLE.{max s t} F Z
        ((HasColimit.isoOfNatIso
          (openNeighborhoodCohomologyZeroIsoUnivLE.{t} Z F)).hom c) := by
  obtain ⟨U, x, rfl⟩ := exists_colimit_ι_openNeighborhoodCohomologyUnivLE.{t} Z F 0 c
  have hκ : (HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIsoUnivLE.{t} Z F)).hom
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F 0) U x) =
      colimit.ι (neighborhoodSectionsUnivLE.{max s t} F Z) U
        ((openNeighborhoodCohomologyZeroIsoUnivLE.{t} Z F).hom.app U x) :=
    (ConcreteCategory.comp_apply _ _ x).symm.trans
      ((ConcreteCategory.congr_hom
        (HasColimit.isoOfNatIso_ι_hom
          (openNeighborhoodCohomologyZeroIsoUnivLE.{t} Z F) U) x).trans
          (ConcreteCategory.comp_apply _ _ x))
  rw [cohomologyOfClosedMapUnivLE_ι.{t}, hκ]
  refine (cohomologyOfClosedMapCompUnivLE_zero_apply.{t} Z F U.unop x).trans ?_
  refine (congrArg (ambientSectionUnivLE.{max s t} F Z
    (top_le_map_openNhdsSet U.unop))
      (cohomologyPresheafIsoSections_hom_app_apply.{max s t} F U.unop.obj x).symm).trans ?_
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (subsetSectionsMapUnivLE_ι.{max s t} F Z U) _).symm

/-- **The degree-zero case of [Stacks, Tag 09V3], at a coefficient universe independent of the
space.** -/
theorem isIso_cohomologyOfClosedMapUnivLE_zero (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (cohomologyOfClosedMapUnivLE.{t} Z F 0) := by
  have hκ : Function.Bijective
      (HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIsoUnivLE.{t} Z F)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hσ : Function.Bijective (subsetSectionsMapUnivLE.{max s t} F Z) :=
    let := isIso_subsetSectionsMapUnivLE.{max s t} F Z hZ hSep
    ConcreteCategory.bijective_of_isIso _
  have hρ := (extSectionsAddEquiv.{max s t, max s t} (⊤ : Opens (TopCat.of Z))
    ((siteRestrictionUnivLE.{t} X Z).obj F)).bijective
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun c c' hcc ↦ hκ.1 (hσ.1 ?_), fun y ↦ ?_⟩
  · exact ((extSectionsAddEquiv_cohomologyOfClosedMapUnivLE_zero.{t} Z F c).symm.trans
      (congrArg _ hcc)).trans
      (extSectionsAddEquiv_cohomologyOfClosedMapUnivLE_zero.{t} Z F c')
  · obtain ⟨w, hw⟩ := hσ.2 (extSectionsAddEquiv.{max s t, max s t} ⊤
      ((siteRestrictionUnivLE.{t} X Z).obj F) y)
    obtain ⟨c, hc⟩ := hκ.2 w
    exact ⟨c, hρ.1 ((extSectionsAddEquiv_cohomologyOfClosedMapUnivLE_zero.{t} Z F c).trans
      ((congrArg _ hc).trans hw))⟩

end DegreeZero

end Map

section DimensionShift

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [HasExt.{max s t}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]

/-- **The comparison map is compatible with postcomposition by an `Ext`-class**, at a coefficient
universe independent of the space. With `β` the class of a morphism of sheaves this is naturality
in the sheaf; with `β` the class of a short exact sequence it is compatibility with the connecting
map of the long exact sequence, which is what the dimension shift needs. -/
theorem cohomologyOfClosedMapUnivLE_ι_comp
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}} {m : ℕ}
    (β : Ext.{max s t} F G m) (p q : ℕ) (hpq : p + m = q) (U : (OpenNhdsSet Z)ᵒᵖ)
    (x : Ext.{max s t}
      ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.unop.obj) F p) :
    cohomologyOfClosedMapUnivLE.{t} Z G q
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z G q) U (x.comp β hpq)) =
      (cohomologyOfClosedMapUnivLE.{t} Z F p
          (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x)).comp
        (β.mapExactFunctor (siteRestrictionUnivLE.{t} X Z)) hpq := by
  refine (cohomologyOfClosedMapUnivLE_ι.{t} Z G q U (x.comp β hpq)).trans (Eq.trans ?_
    (congrArg (fun y ↦ Ext.comp y (β.mapExactFunctor (siteRestrictionUnivLE.{t} X Z)) hpq)
      (cohomologyOfClosedMapUnivLE_ι.{t} Z F p U x).symm))
  rw [cohomologyOfClosedMapCompUnivLE_apply, cohomologyOfClosedMapCompUnivLE_apply,
    Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ (freeRestrictionMapUnivLE.{t} Z U.unop))
    (x.mapExactFunctor (siteRestrictionUnivLE.{t} X Z))
    (β.mapExactFunctor (siteRestrictionUnivLE.{t} X Z)) (zero_add p) hpq
    (show 0 + p + m = q by lia)).symm

end DimensionShift

end Comparison

/-- Shrinking an open neighbourhood of `Z` induces a map of free abelian sheaves, at a
coefficient universe independent of the space. -/
abbrev freeNhdsMapUnivLE {U V : (OpenNhdsSet Z)ᵒᵖ} (a : U ⟶ V) :
    (freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj V.unop.obj ⟶
      (freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.unop.obj :=
  (freeYoneda.{max s t} (Opens.grothendieckTopology X)).map
    ((openNhdsSetInclusion Z).map a.unop)

section Diagram

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})

/-- The restriction maps of the neighbourhood-cohomology diagram are precomposition with the
induced map of free abelian sheaves. -/
theorem openNeighborhoodCohomologyUnivLE_map_apply (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ} (a : U ⟶ V)
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U)) :
    (openNeighborhoodCohomologyUnivLE.{t} Z F p).map a x =
      Ext.comp (Z := F) (b := p) (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z a)) x (zero_add p) :=
  rfl

/-- Two classes on open neighbourhoods of `Z` defining the same element of the colimit agree
after restriction to a smaller neighbourhood. -/
theorem exists_map_eq_of_colimit_ι_eqUnivLE (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ}
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U))
    (y : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj V))
    (h : colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x =
      colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) V y) :
    ∃ (W : (OpenNhdsSet Z)ᵒᵖ) (f : U ⟶ W) (g : V ⟶ W),
      (openNeighborhoodCohomologyUnivLE.{t} Z F p).map f x =
        (openNeighborhoodCohomologyUnivLE.{t} Z F p).map g y := by
  have := preservesFilteredColimitsOfSize_forget_addCommGrp.{t, s}
  exact Concrete.colimit_exists_of_rep_eq.{max s t} _ x y h

/-- `exists_map_eq_of_colimit_ι_eqUnivLE` with its conclusion as an identity of `Ext`-classes. -/
theorem exists_comp_eq_of_colimit_ι_eqUnivLE (p : ℕ) {U V : (OpenNhdsSet Z)ᵒᵖ}
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U))
    (y : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj V))
    (h : colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x =
      colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) V y) :
    ∃ (W : (OpenNhdsSet Z)ᵒᵖ) (f : U ⟶ W) (g : V ⟶ W),
      Ext.comp (Z := F) (b := p) (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f)) x (zero_add p) =
        Ext.comp (Z := F) (b := p) (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z g)) y (zero_add p) := by
  obtain ⟨W, f, g, hfg⟩ := exists_map_eq_of_colimit_ι_eqUnivLE.{t} Z F p x y h
  exact ⟨W, f, g, hfg⟩

/-- A class vanishing on a smaller open neighbourhood of `Z` is zero in the colimit. -/
theorem colimit_ι_eq_zero_of_map_eq_zeroUnivLE (p : ℕ) {U W : (OpenNhdsSet Z)ᵒᵖ} (f : U ⟶ W)
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U))
    (h : (openNeighborhoodCohomologyUnivLE.{t} Z F p).map f x = 0) :
    colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x = 0 :=
  (((ConcreteCategory.congr_hom
      (colimit.w (openNeighborhoodCohomologyUnivLE.{t} Z F p) f) x).symm).trans
    (ConcreteCategory.comp_apply _ _ x)).trans
    ((congrArg (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) W) h).trans
      (map_zero (ConcreteCategory.hom
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) W))))

/-- `colimit_ι_eq_zero_of_map_eq_zeroUnivLE` with its hypothesis as an identity of
`Ext`-classes. -/
theorem colimit_ι_eq_zero_of_comp_eq_zeroUnivLE (p : ℕ) {U W : (OpenNhdsSet Z)ᵒᵖ} (f : U ⟶ W)
    (x : ToType ((openNeighborhoodCohomologyUnivLE.{t} Z F p).obj U))
    (h : Ext.comp (Z := F) (b := p)
      (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f)) x (zero_add p) = 0) :
    colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z F p) U x = 0 := by
  refine colimit_ι_eq_zero_of_map_eq_zeroUnivLE.{t} Z F p f x ?_
  exact h

end Diagram

section Vanishing

variable [HasExt.{max s t}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
  [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))]

/-- **The positive-degree `Ext`-groups out of the free abelian sheaf on `Z` into the restriction
of an injective abelian sheaf vanish**, at a coefficient universe independent of the space. This
is `Stacks.Topology.isZero_cohomologyPresheaf_restriction_of_isFlasque` of
`CompactSubset/FlasqueSoftUnivLE.lean` at the shape the dimension shift below consumes it — as a
statement about elements, with an injective sheaf in place of a flasque one — and it is the
mixed-universe form of `Stacks.Topology.ext_eq_zero_of_injective_restriction`.

The `HasRightDerivedFunctor` hypothesis is carried rather than discharged: `inferInstance`
through its only route exhausts a 1,000,000-heartbeat `isDefEq` budget, both at a
concrete space and at an abstract one. It is not a pinning — it carries no universe of its own —
and it is inhabited; the pinned `Stacks.Topology.rightAcyclic_sections_of_isSoft` and
`CompactSubset/RestrictionVanishingUnivLE.lean` carry it the same way. -/
theorem ext_eq_zero_of_injective_restrictionUnivLE
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}) [Injective I]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p)
    (y : Ext.{max s t}
      ((freeYoneda.{max s t} (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤)
      ((siteRestrictionUnivLE.{t} X Z).obj I) p) :
    y = 0 := by
  have _hir : HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}) :=
    hasInjectiveResolutions_sheafOpens.{max s t} (TopCat.of Z)
  have _hinj : Injective (C := TopCat.Sheaf AddCommGrpCat.{max s t} X) I := ‹Injective I›
  have _hfl : TopCat.Sheaf.IsFlasque
      (X := X) (C := AddCommGrpCat.{max s t}) I :=
    isFlasque_of_injective I
  have hzero := isZero_cohomologyPresheaf_restriction_of_isFlasque.{w, w', t} (Z := Z) I hZ hSep
    p hp
  exact (AddCommGrpCat.subsingleton_of_isZero hzero).elim y 0

end Vanishing

section DimensionShift

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [HasExt.{max s t}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
  [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))]
  (hZ : IsCompact Z)
  (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
  (p : ℕ)
  (ih : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t},
    Function.Bijective (cohomologyOfClosedMapUnivLE.{t} Z G p))
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}))
  (hS : S.ShortExact) (hinj : Injective S.X₂)

include hZ hSep ih hS hinj in
/-- **The surjectivity half of the dimension shift**, at a coefficient universe independent of
the space. -/
theorem surjective_cohomologyOfClosedMapUnivLE_succ :
    Function.Surjective (cohomologyOfClosedMapUnivLE.{t} Z S.X₁ (p + 1)) := by
  have hLS : (S.map (siteRestrictionUnivLE.{t} X Z)).ShortExact :=
    hS.map_of_exact (siteRestrictionUnivLE.{t} X Z)
  intro y
  have hy0 : Ext.comp y (Ext.mk₀ (S.map (siteRestrictionUnivLE.{t} X Z)).f)
      (add_zero (p + 1)) = 0 :=
    have := hinj
    ext_eq_zero_of_injective_restrictionUnivLE.{w, w', t} Z S.X₂ hZ hSep (p + 1) p.succ_pos _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda.{max s t} (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤) hLS y hy0 rfl
  obtain ⟨c, hc⟩ := (ih S.X₃).2 x₃
  obtain ⟨U, xU, rfl⟩ := exists_colimit_ι_openNeighborhoodCohomologyUnivLE.{t} Z S.X₃ p c
  refine ⟨colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₁ (p + 1)) U
    (Ext.comp xU hS.extClass rfl), ?_⟩
  refine (cohomologyOfClosedMapUnivLE_ι_comp.{t} Z hS.extClass p (p + 1) rfl U xU).trans ?_
  rw [hc, Ext.mapExactFunctor_extClass]
  exact hx₃

omit [HasDerivedCategory.{w}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
  [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))] in
include ih hS hinj in
/-- **The injectivity half of the dimension shift**, at a coefficient universe independent of the
space. -/
theorem injective_cohomologyOfClosedMapUnivLE_succ :
    Function.Injective (cohomologyOfClosedMapUnivLE.{t} Z S.X₁ (p + 1)) := by
  have := hinj
  have hLS : (S.map (siteRestrictionUnivLE.{t} X Z)).ShortExact :=
    hS.map_of_exact (siteRestrictionUnivLE.{t} X Z)
  suffices hker : ∀ c : ToType (colimit
      (openNeighborhoodCohomologyUnivLE.{t} Z S.X₁ (p + 1))),
      cohomologyOfClosedMapUnivLE.{t} Z S.X₁ (p + 1) c = 0 → c = 0 from
    (injective_iff_map_eq_zero
      (ConcreteCategory.hom (cohomologyOfClosedMapUnivLE.{t} Z S.X₁ (p + 1)))).mpr hker
  intro c hc0
  obtain ⟨U, x, rfl⟩ := exists_colimit_ι_openNeighborhoodCohomologyUnivLE.{t} Z S.X₁ (p + 1) c
  have h1 : Ext.comp x (Ext.mk₀ S.f) (add_zero (p + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda.{max s t} (Opens.grothendieckTopology X)).obj U.unop.obj) hS x h1 rfl
  have h2 : Ext.comp (cohomologyOfClosedMapUnivLE.{t} Z S.X₃ p
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₃ p) U b))
      (Ext.mapExactFunctor (siteRestrictionUnivLE.{t} X Z) hS.extClass) rfl = 0 :=
    (cohomologyOfClosedMapUnivLE_ι_comp.{t} Z hS.extClass p (p + 1) rfl U b).symm.trans
      ((congrArg (fun y ↦ cohomologyOfClosedMapUnivLE.{t} Z S.X₁ (p + 1)
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₁ (p + 1)) U y)) hb).trans hc0)
  have h3 : Ext.comp (cohomologyOfClosedMapUnivLE.{t} Z S.X₃ p
        (colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₃ p) U b))
      hLS.extClass rfl = 0 := by
    rw [← Ext.mapExactFunctor_extClass (siteRestrictionUnivLE.{t} X Z) hS]
    exact h2
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃
    ((freeYoneda.{max s t} (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤) hLS _ rfl h3
  obtain ⟨d, hd⟩ := (ih S.X₂).2 x₂
  obtain ⟨V, yV, rfl⟩ := exists_colimit_ι_openNeighborhoodCohomologyUnivLE.{t} Z S.X₂ p d
  have h4 : colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₃ p) U b =
      colimit.ι (openNeighborhoodCohomologyUnivLE.{t} Z S.X₃ p) V
        (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) := by
    refine (ih S.X₃).1 ?_
    refine Eq.trans ?_
      (cohomologyOfClosedMapUnivLE_ι_comp.{t} Z (Ext.mk₀ S.g) p p (add_zero p) V yV).symm
    rw [hd, Ext.mapExactFunctor_mk₀]
    exact hx₂.symm
  obtain ⟨W, g, f, hfg⟩ := exists_comp_eq_of_colimit_ι_eqUnivLE.{t} Z S.X₃ p b _ h4
  refine colimit_ι_eq_zero_of_comp_eq_zeroUnivLE.{t} Z S.X₁ (p + 1) g x ?_
  have hy' : Ext.comp (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) hS.extClass rfl = 0 :=
    (Ext.comp_assoc_of_second_deg_zero yV (Ext.mk₀ S.g) hS.extClass rfl).trans
      ((congrArg (fun m ↦ Ext.comp yV m (show p + 1 = p + 1 from rfl))
        hS.comp_extClass).trans (Ext.comp_zero yV S.X₁ 1 (p + 1) rfl))
  calc Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z g)) x (zero_add (p + 1))
      = Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z g)) (Ext.comp b hS.extClass rfl)
          (zero_add (p + 1)) := by rw [hb]
    _ = Ext.comp (Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z g)) b (zero_add p))
          hS.extClass rfl :=
        (Ext.comp_assoc (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z g)) b hS.extClass (zero_add p) rfl
          (show 0 + p + 1 = p + 1 by lia)).symm
    _ = Ext.comp (Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f))
          (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) (zero_add p)) hS.extClass rfl := by
        rw [hfg]
    _ = Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f))
          (Ext.comp (Ext.comp yV (Ext.mk₀ S.g) (add_zero p)) hS.extClass rfl)
          (zero_add (p + 1)) :=
        Ext.comp_assoc (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f)) _ hS.extClass (zero_add p) rfl
          (show 0 + p + 1 = p + 1 by lia)
    _ = 0 :=
        (congrArg (fun m ↦ Ext.comp (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f)) m
          (zero_add (p + 1))) hy').trans
          (Ext.comp_zero (Ext.mk₀ (freeNhdsMapUnivLE.{t} Z f)) S.X₁ (p + 1) (p + 1) (zero_add _))

end DimensionShift

section Induction

variable [HasExt.{max s t} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [HasExt.{max s t}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w}
    (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{max s t}]
  [((restrictionSectionsFunctor.{t} (TopCat.of Z)).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{max s t}))]
  (hZ : IsCompact Z)
  (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
    ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)

include hZ hSep in
/-- **The comparison map of [Stacks, Tag 09V3] is bijective in every degree**, at a coefficient
universe independent of the space, by induction on the degree with the statement taken for every
abelian sheaf at once. -/
theorem bijective_cohomologyOfClosedMapUnivLE (p : ℕ) :
    ∀ F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t},
      Function.Bijective (cohomologyOfClosedMapUnivLE.{t} Z F p) := by
  induction p with
  | zero =>
    intro F
    have := isIso_cohomologyOfClosedMapUnivLE_zero.{t} Z F hZ hSep
    exact ConcreteCategory.bijective_of_isIso _
  | succ p ih =>
    intro F
    obtain ⟨S, hS, hinjF, rfl⟩ :
        ∃ (S : ShortComplex
            (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}))
          (_ : S.ShortExact) (_ : Injective S.X₂), S.X₁ = F :=
      ⟨ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F)),
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)) },
        Injective.injective_under F, rfl⟩
    exact ⟨injective_cohomologyOfClosedMapUnivLE_succ.{t} Z p ih S hS hinjF,
      surjective_cohomologyOfClosedMapUnivLE_succ.{w, w', t} Z hZ hSep p ih S hS hinjF⟩

include hZ hSep in
/-- **[Stacks, Tag 09V3] at a coefficient universe independent of the space.** For a
quasi-compact subset `Z` of a topological space `X` any two distinct points of which have
disjoint open neighbourhoods in `X`, the canonical map from the colimit of the cohomology of an
abelian sheaf `F` over the open neighbourhoods of `Z` to the cohomology of the restriction of `F`
to `Z` is an isomorphism in every degree. -/
theorem isIso_cohomologyOfClosedMapUnivLE
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max s t}) (p : ℕ) :
    IsIso (cohomologyOfClosedMapUnivLE.{t} Z F p) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_cohomologyOfClosedMapUnivLE.{w, w', t} Z hZ hSep p F

end Induction



section NoWeakening

/-- **Yoneda's lemma for `uliftYoneda` is the ordinary one across
`CategoryTheory.uliftYonedaIsoYoneda`.** At `w := v` the lift is a bijection on each component,
and both correspondences evaluate a natural transformation at the identity, so precomposing with
the isomorphism turns one into the other. -/
private theorem uliftYonedaEquiv_isoYoneda_comp {C : Type uC} [Category.{vC} C] {U : C}
    {F : Cᵒᵖ ⥤ Type vC} (k : yoneda.obj U ⟶ F) :
    uliftYonedaEquiv.{vC} (uliftYonedaIsoYoneda.{vC}.hom.app U ≫ k) = yonedaEquiv k := by
  simp only [uliftYonedaEquiv, yonedaEquiv, Equiv.coe_fn_mk, NatTrans.comp_app]
  rfl

/-- **The two free-abelian-sheaf theories have the same sections**, across
`Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso`. This is what carries a statement about the
freed cohomology back to one about the pinned cohomology: `freeYoneda.{v}` is built on
`uliftYoneda.{v}` and the library's on `yoneda`, and the two section correspondences agree once
the isomorphism between them is inserted. -/
theorem sectionsEquiv_freeYonedaIso_hom_comp {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{vC}] (U : C)
    (F : Sheaf J AddCommGrpCat.{vC})
    (g : (Stacks.Cohomology.FreeYoneda.freeYoneda J).obj U ⟶ F) :
    sectionsEquiv.{vC} U F (((freeYonedaIso.{vC} J).app U).hom ≫ g) =
      Stacks.Cohomology.FreeYoneda.sectionsEquiv U F g := by
  dsimp only [sectionsEquiv, Stacks.Cohomology.FreeYoneda.sectionsEquiv, Equiv.trans_apply]
  rw [show ((freeYonedaIso.{vC} J).app U).hom
      = (presheafToSheaf J AddCommGrpCat.{vC}).map
        (((Functor.whiskeringRight Cᵒᵖ (Type vC) AddCommGrpCat.{vC}).obj
          AddCommGrpCat.free).map (uliftYonedaIsoYoneda.{vC}.hom.app U)) from rfl,
    (sheafificationAdjunction J AddCommGrpCat.{vC}).homEquiv_naturality_left,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left]
  exact uliftYonedaEquiv_isoYoneda_comp _

/-- **The canonical sections of the two free abelian sheaves correspond.** -/
theorem gen_eq_freeYonedaIso_inv_app_gen {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{vC}] (U : C) :
    gen.{vC} (J := J) U =
      ((freeYonedaIso.{vC} J).app U).inv.hom.app (op U)
        (Stacks.Cohomology.FreeYoneda.gen (J := J) U) := by
  have h := sectionsEquiv_naturality.{vC} (J := J) U
    (F := (Stacks.Cohomology.FreeYoneda.freeYoneda J).obj U)
    (G := (freeYoneda.{vC} J).obj U) (((freeYonedaIso.{vC} J).app U).hom)
    (((freeYonedaIso.{vC} J).app U).inv)
  rw [Iso.hom_inv_id] at h
  refine Eq.trans ?_ (h.trans (congrArg _ ?_))
  · rfl
  · exact (sectionsEquiv_freeYonedaIso_hom_comp.{uC, vC} U _ (𝟙 _)).trans rfl

noncomputable section Pinned

variable {X : TopCat.{s}} (Z : Set X)

/-- **Nothing is weakened on the coefficient axis: at `t := s` the restriction functor of this
file is the library's own `Stacks.Topology.restrictionFunctor`**, and not merely isomorphic to
it. -/
theorem siteRestrictionUnivLE_eq_restrictionFunctor :
    siteRestrictionUnivLE.{s} X Z = restrictionFunctor X Z :=
  rfl

/-- **Nothing is weakened on the free-Yoneda axis: at `t := s` the canonical map out of the free
abelian sheaf on `Z` is the library's `Stacks.Topology.freeRestrictionMap`**, conjugated by the
bridge `Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso`.

This is the identity the whole no-weakening rests on, and it is an *equality of morphisms of
sheaves*, not an isomorphism: the two constructions differ only in which model of the free abelian
sheaf they use, `uliftYoneda.{s}` or `yoneda`, and `freeYonedaIso` identifies those. The
ambient-section maps themselves already agree on the nose, by
`Stacks.Topology.ambientSectionUnivLE_eq_ambientSection`. -/
theorem freeRestrictionMapUnivLE_eq (U : OpenNhdsSet Z) :
    freeRestrictionMapUnivLE.{s} Z U =
      ((freeYonedaIso.{s} (Opens.grothendieckTopology (TopCat.of Z))).app ⊤).hom ≫
        freeRestrictionMap Z U ≫
          (restrictionFunctor X Z).map
            (((freeYonedaIso.{s} (Opens.grothendieckTopology X)).app U.obj).inv) := by
  refine (sectionsEquiv.{s} ⊤ _).injective ?_
  refine (sectionsEquiv_freeRestrictionMapUnivLE.{s} Z U).trans (Eq.trans ?_
    (sectionsEquiv_freeYonedaIso_hom_comp.{s, s}
      (J := Opens.grothendieckTopology (TopCat.of Z)) ⊤ _
      (freeRestrictionMap Z U ≫ (restrictionFunctor X Z).map
        (((freeYonedaIso.{s} (Opens.grothendieckTopology X)).app U.obj).inv))).symm)
  refine Eq.trans ?_
    (Stacks.Cohomology.FreeYoneda.sectionsEquiv_naturality ⊤ _ _).symm
  refine Eq.trans ?_ (congrArg _ (sectionsEquiv_freeRestrictionMap Z U).symm)
  refine Eq.trans ?_ (ambientSection_naturality_apply (Stacks.subsetInclusion X Z)
    (((freeYonedaIso.{s} (Opens.grothendieckTopology X)).app U.obj).inv)
    (top_le_map_openNhdsSet U) (Stacks.Cohomology.FreeYoneda.gen U.obj)).symm
  refine Eq.trans (ConcreteCategory.congr_hom
    (ambientSectionUnivLE_eq_ambientSection.{s}
      ((freeYoneda.{s} (Opens.grothendieckTopology X)).obj U.obj) Z
      (top_le_map_openNhdsSet U)) (gen.{s} U.obj)) ?_
  exact congrArg _
    (gen_eq_freeYonedaIso_inv_app_gen.{s, s} (J := Opens.grothendieckTopology X) U.obj)

private theorem mk₀_three_comp {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{w} C]
    {A B D E M : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) {p : ℕ} (y : Ext.{w} E M p) :
    (Ext.mk₀ (f ≫ g ≫ h)).comp y (zero_add p) =
      (Ext.mk₀ f).comp ((Ext.mk₀ g).comp ((Ext.mk₀ h).comp y (zero_add p)) (zero_add p))
        (zero_add p) := by
  simp only [Ext.mk₀_comp_mk₀_assoc]

private theorem mk₀_comp_mk₀_comp_congr {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasExt.{w} C] {A B B' D M : C} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ B') (g' : B' ⟶ D)
    (hfg : f ≫ g = f' ≫ g') {p : ℕ} (x : Ext.{w} D M p) :
    (Ext.mk₀ f).comp ((Ext.mk₀ g).comp x (zero_add p)) (zero_add p) =
      (Ext.mk₀ f').comp ((Ext.mk₀ g').comp x (zero_add p)) (zero_add p) := by
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, hfg]

private theorem mk₀_inv_mk₀_hom_comp {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{w} C]
    {A B M : C} (i : A ≅ B) {p : ℕ} (z : Ext.{w} B M p) :
    (Ext.mk₀ i.inv).comp ((Ext.mk₀ i.hom).comp z (zero_add p)) (zero_add p) = z := by
  rw [Ext.mk₀_comp_mk₀_assoc, i.inv_hom_id, Ext.mk₀_id_comp]

variable [HasExt.{s} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{s})]
  [HasExt.{s} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{s})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{s})

/-- **The leg-level no-weakening identity.** At `t := s` the comparison of this file at a single
open neighbourhood is the library's `Stacks.Topology.cohomologyOfClosedMapComp`, conjugated by
`Stacks.Cohomology.FreeYonedaUnivLE.freeYonedaIso`: the two differ only in which model of the
free abelian sheaf the `Ext`-groups are taken out of.

Both sides are read off `freeRestrictionMapUnivLE_eq` by splitting `Ext.mk₀` of the triple
composite and reassociating. The splitting is done by the term-mode `mk₀_three_comp` rather than
by `rw [← Ext.mk₀_comp_mk₀]`: the surrounding `Ext.comp` carries
`Ext.mapExactFunctor (siteRestrictionUnivLE X Z) x` while the other side carries
`Ext.mapExactFunctor (restrictionFunctor X Z) x`, and those two spellings of one functor are
definitionally equal but not type-correct at `implicit` transparency, so every keyed rewrite under
the composite is refused. -/
theorem cohomologyOfClosedMapCompUnivLE_eq (p : ℕ) (U : OpenNhdsSet Z)
    (x : Ext.{s} ((freeYoneda.{s} (Opens.grothendieckTopology X)).obj U.obj) F p) :
    cohomologyOfClosedMapCompUnivLE.{s} Z F p U x =
      (Ext.mk₀ ((freeYonedaIso.{s} (Opens.grothendieckTopology (TopCat.of Z))).app ⊤).hom).comp
        (cohomologyOfClosedMapComp Z F p U
          ((Ext.mk₀ ((freeYonedaIso.{s} (Opens.grothendieckTopology X)).app U.obj).inv).comp x
            (zero_add p))) (zero_add p) := by
  refine Eq.trans (congrArg (fun f => (Ext.mk₀ f).comp
      (x.mapExactFunctor (siteRestrictionUnivLE.{s} X Z)) (zero_add p))
    (freeRestrictionMapUnivLE_eq Z U)) ?_
  refine Eq.trans (mk₀_three_comp.{_, _, s} _ _ _ _) ?_
  refine congrArg (fun z => (Ext.mk₀
    ((freeYonedaIso.{s} (Opens.grothendieckTopology (TopCat.of Z))).app ⊤).hom).comp z
      (zero_add p)) ?_
  refine Eq.trans ?_ (cohomologyOfClosedMapComp_apply Z F p U _).symm
  refine congrArg (fun z => (Ext.mk₀ (freeRestrictionMap Z U)).comp z (zero_add p)) ?_
  exact ((Ext.mapExactFunctor_comp (F := restrictionFunctor X Z) (Ext.mk₀ _) x
      (zero_add p)).trans
    (congrArg (fun z => Ext.comp z (Ext.mapExactFunctor (restrictionFunctor X Z) x) (zero_add p))
      (Ext.mapExactFunctor_mk₀ (F := restrictionFunctor X Z) _))).symm

/-- **Nothing is weakened on the coefficient axis: at `t := s` the every-degree isomorphism of
this file is the library's [Stacks, Tag 09V3].** The two cohomology diagrams over the open
neighbourhoods of `Z` are not equal — this file's is built on `uliftYoneda.{s}` and the library's
on `yoneda` — but they are isomorphic by
`Stacks.Cohomology.FreeYonedaUnivLE.cohomologyPresheafObjIsoPinned`, naturally in the
neighbourhood, and `cohomologyOfClosedMapCompUnivLE_eq` says the two comparison cocones agree
across that isomorphism. So `isIso_cohomologyOfClosedMapUnivLE` at `t := s` implies
`Stacks.Topology.isIso_cohomologyOfClosedMap`, with no hypothesis added. -/
theorem isIso_cohomologyOfClosedMap_of_univLE (p : ℕ)
    (h : IsIso (cohomologyOfClosedMapUnivLE.{s} Z F p)) :
    IsIso (cohomologyOfClosedMap Z F p) := by
  let e : openNeighborhoodCohomologyUnivLE.{s} Z F p ≅ openNeighborhoodCohomology Z F p :=
    NatIso.ofComponents
      (fun U => cohomologyPresheafObjIsoPinned (Opens.grothendieckTopology X) F p U.unop.obj)
      (fun {U V} a => ConcreteCategory.hom_ext _ _ fun x =>
        mk₀_comp_mk₀_comp_congr _ _ _ _
          (((freeYonedaIso.{s} (Opens.grothendieckTopology X)).inv.naturality
            ((openNhdsSetInclusion Z).map a.unop)).symm) x)
  have hcomp : ∀ (U : (OpenNhdsSet Z)ᵒᵖ)
      (y : Ext.{s} ((freeYoneda.{s} (Opens.grothendieckTopology X)).obj U.unop.obj) F p),
      (e.hom.app U) y =
        (Ext.mk₀ ((freeYonedaIso.{s} (Opens.grothendieckTopology X)).app U.unop.obj).inv).comp
          y (zero_add p) := fun _ _ => rfl
  have htgt : ∀ (z : Ext.{s} ((freeYoneda.{s}
        (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤) ((restrictionFunctor X Z).obj F) p),
      ((cohomologyPresheafObjIsoPinned (Opens.grothendieckTopology (TopCat.of Z))
        ((restrictionFunctor X Z).obj F) p ⊤).hom) z =
        (Ext.mk₀ ((freeYonedaIso.{s}
          (Opens.grothendieckTopology (TopCat.of Z))).app ⊤).inv).comp z (zero_add p) :=
    fun _ => rfl
  have key : (HasColimit.isoOfNatIso e).hom ≫ cohomologyOfClosedMap Z F p =
      cohomologyOfClosedMapUnivLE.{s} Z F p ≫
        (cohomologyPresheafObjIsoPinned (Opens.grothendieckTopology (TopCat.of Z))
          ((restrictionFunctor X Z).obj F) p ⊤).hom := by
    refine colimit.hom_ext fun U => ?_
    have hiP : colimit.ι (openNeighborhoodCohomology Z F p) U ≫ cohomologyOfClosedMap Z F p =
        AddCommGrpCat.ofHom (cohomologyOfClosedMapComp Z F p U.unop) :=
      ConcreteCategory.hom_ext _ _ fun y =>
        (ConcreteCategory.comp_apply _ _ y).trans (cohomologyOfClosedMap_ι Z F p U y)
    have hiU : colimit.ι (openNeighborhoodCohomologyUnivLE.{s} Z F p) U ≫
        cohomologyOfClosedMapUnivLE.{s} Z F p =
        AddCommGrpCat.ofHom (cohomologyOfClosedMapCompUnivLE.{s} Z F p U.unop) :=
      ConcreteCategory.hom_ext _ _ fun y =>
        (ConcreteCategory.comp_apply _ _ y).trans (cohomologyOfClosedMapUnivLE_ι.{s} Z F p U y)
    have middle : e.hom.app U ≫ AddCommGrpCat.ofHom (cohomologyOfClosedMapComp Z F p U.unop) =
        AddCommGrpCat.ofHom (cohomologyOfClosedMapCompUnivLE.{s} Z F p U.unop) ≫
          (cohomologyPresheafObjIsoPinned (Opens.grothendieckTopology (TopCat.of Z))
            ((restrictionFunctor X Z).obj F) p ⊤).hom := by
      refine ConcreteCategory.hom_ext _ _ fun x => ?_
      show cohomologyOfClosedMapComp Z F p U.unop ((e.hom.app U) x) =
        ((cohomologyPresheafObjIsoPinned (Opens.grothendieckTopology (TopCat.of Z))
          ((restrictionFunctor X Z).obj F) p ⊤).hom)
          (cohomologyOfClosedMapCompUnivLE.{s} Z F p U.unop x)
      refine Eq.trans (congrArg (fun y => cohomologyOfClosedMapComp Z F p U.unop y)
        (hcomp U x)) ?_
      refine Eq.trans ?_ (htgt _).symm
      exact Eq.symm ((congrArg (fun z => (Ext.mk₀ ((freeYonedaIso.{s}
            (Opens.grothendieckTopology (TopCat.of Z))).app ⊤).inv).comp z (zero_add p))
          (cohomologyOfClosedMapCompUnivLE_eq Z F p U.unop x)).trans
        (mk₀_inv_mk₀_hom_comp _ _))
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ cohomologyOfClosedMap Z F p)
          (HasColimit.isoOfNatIso_ι_hom e U)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => e.hom.app U ≫ m) hiP).trans middle)))).trans
      ((congrArg (fun m => m ≫ (cohomologyPresheafObjIsoPinned
          (Opens.grothendieckTopology (TopCat.of Z))
          ((restrictionFunctor X Z).obj F) p ⊤).hom) hiU).symm.trans (Category.assoc _ _ _))
  have : IsIso ((HasColimit.isoOfNatIso e).hom ≫ cohomologyOfClosedMap Z F p) := by
    rw [key]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h (Iso.isIso_hom _)
  exact IsIso.of_isIso_comp_left (HasColimit.isoOfNatIso e).hom _
end Pinned

end NoWeakening

end

end Stacks.Topology

end
