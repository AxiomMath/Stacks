module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsOfCoeff

/-!
# The comparison map for cohomology along a quasi-compact separated subset

Let `X` be a topological space, let `Z ⊆ X` be a subset and let `F` be a sheaf of abelian groups
on `X`. Every open neighbourhood `U` of `Z` carries a canonical map

`H^p(U, F) ⟶ H^p(Z, F|_Z)`,

and these are compatible with shrinking `U`. This file builds the resulting map out of the
colimit,

`Stacks.Topology.cohomologyOfClosedMap : colim_{U ⊇ Z open} H^p(U, F) ⟶ H^p(Z, F|_Z)`,

the canonical comparison map of [Stacks, Tag 09V3], and proves that it is an isomorphism in
degree zero when `Z` is quasi-compact and any two of its distinct points have disjoint open
neighbourhoods in `X`.

Cohomology here is Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`, the `Ext`-group out of the
free abelian sheaf on a representable presheaf. On an open neighbourhood `U`, the comparison
carries an `Ext`-class along the exact restriction functor by
`CategoryTheory.Abelian.Ext.mapExactFunctor` and then pulls it back along the canonical map
`freeRestrictionMap` of free abelian sheaves.

## Main definitions

* `Stacks.Topology.restrictionFunctor` is the inverse image of abelian sheaves along the inclusion
  of `Z`.
* `Stacks.Topology.freeRestrictionMap` is the canonical map from the free abelian sheaf on the
  whole of `Z` to the restriction of the free abelian sheaf on an open neighbourhood of `Z`.
* `Stacks.Topology.openNeighborhoodCohomology` is the diagram `U ↦ H^p(U, F)`.
* `Stacks.Topology.cohomologyOfClosedMap` is the comparison map of [Stacks, Tag 09V3].

## Main results

* `Stacks.Topology.ambientSection_naturality`: the section of an inverse image induced by a
  section of the sheaf is natural in the sheaf.
* `Stacks.Topology.freeRestrictionMap_comp`: the canonical maps are compatible with shrinking the
  neighbourhood.
* `Stacks.Topology.cohomologyOfClosedMapComp_naturality`: the comparison maps on the
  neighbourhoods form a cocone.
* `Stacks.Topology.cohomologyOfClosedMapComp_zero_apply`: in degree zero the comparison is the
  comparison of sections, under the identification of degree-zero cohomology with sections.
* `Stacks.Topology.isIso_cohomologyOfClosedMap_zero`: the comparison map is an isomorphism in
  degree zero.
* `Stacks.Topology.cohomologyOfClosedMap_ι_comp`: the comparison map is compatible with
  postcomposition by an `Ext`-class.
* `Stacks.Topology.ext_eq_zero_of_injective_restriction`: the positive-degree `Ext`-groups into
  the restriction of an injective sheaf vanish, stated on elements.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [SGA 4, Expose V bis, 4.1.3]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat Abelian
open Stacks.Cohomology.FreeYoneda

namespace Stacks.Topology

universe v u

noncomputable section Naturality

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- **The section of an inverse image induced by a section is natural in the sheaf.** -/
theorem ambientSection_naturality {F G : Y.Sheaf C} (β : F ⟶ G)
    {U : Opens Y} {V : Opens X} (h : V ≤ (Opens.map f).obj U) :
    ambientSection f F h ≫ ((TopCat.Sheaf.pullback C f).map β).hom.app (op V) =
      β.hom.app (op U) ≫ ambientSection f G h := by
  have hA : ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app F)).inv.app (op V)
    ≫
    ((TopCat.Sheaf.pullback C f).map β).hom.app (op V) =
    (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((Presheaf.pullback C f).map β.hom)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V) :=
    congrArg (fun m ↦ NatTrans.app m (op V))
      (congrArg (fun m ↦ m.hom) ((TopCat.Sheaf.pullbackIso C f).inv.naturality β).symm)
  have hC : ((Presheaf.pullback C f).map β.hom).app (op V) ≫
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f G)).app (op V) =
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f F)).app (op V) ≫
    (CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((Presheaf.pullback C f).map β.hom)).app (op V) :=
    congrArg (fun m ↦ NatTrans.app m (op V))
      (CategoryTheory.toSheafify_naturality (Opens.grothendieckTopology X)
        ((Presheaf.pullback C f).map β.hom))
  have hD : β.hom.app (op U) ≫
    ((Presheaf.pullbackPushforwardAdjunction C f).unit.app G.presheaf).app (op U) =
    ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    ((Presheaf.pullback C f).map β.hom).app (op ((Opens.map f).obj U)) :=
    congrArg (fun m ↦ NatTrans.app m (op U))
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.naturality β.hom)
  have hres : ((Presheaf.pullback C f).map β.hom).app (op ((Opens.map f).obj U)) ≫
    (inverseImagePresheaf f G).map (homOfLE h).op = (inverseImagePresheaf f F).map (homOfLE h).op ≫
    ((Presheaf.pullback C f).map β.hom).app (op V) :=
    (((Presheaf.pullback C f).map β.hom).naturality (homOfLE h).op).symm
  have k1 : ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    ((inverseImagePresheaf f F).map (homOfLE h).op ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f F)).app (op V) ≫
    (((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app F)).inv.app (op V) ≫
    ((TopCat.Sheaf.pullback C f).map β).hom.app (op V)))) =
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
        ((inverseImagePresheaf f F).map (homOfLE h).op ≫
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (inverseImagePresheaf f F)).app (op V) ≫
        ((CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
          ((Presheaf.pullback C f).map β.hom)).app (op V) ≫
        ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V))))
          :=
    congrArg (fun m ↦
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
      ((inverseImagePresheaf f F).map (homOfLE h).op ≫
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (inverseImagePresheaf f F)).app (op V) ≫
      m))) hA
  have k2 : ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    ((inverseImagePresheaf f F).map (homOfLE h).op ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f F)).app (op V) ≫
    ((CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((Presheaf.pullback C f).map β.hom)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))) =
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
        ((inverseImagePresheaf f F).map (homOfLE h).op ≫
        (((Presheaf.pullback C f).map β.hom).app (op V) ≫
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (inverseImagePresheaf f G)).app (op V) ≫
        ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V))))
          :=
    congrArg (fun m ↦
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
      ((inverseImagePresheaf f F).map (homOfLE h).op ≫ m))
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m ↦ m ≫
          ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V))
            hC.symm).trans (Category.assoc _ _ _)))
  have k3 : ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    ((inverseImagePresheaf f F).map (homOfLE h).op ≫
    (((Presheaf.pullback C f).map β.hom).app (op V) ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f G)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))) =
    ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    (((Presheaf.pullback C f).map β.hom).app (op ((Opens.map f).obj U)) ≫
    ((inverseImagePresheaf f G).map (homOfLE h).op ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f G)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))) :=
    congrArg (fun m ↦
      ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
      m)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m ↦ m ≫
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            (inverseImagePresheaf f G)).app (op V) ≫
          ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))
            hres.symm).trans (Category.assoc _ _ _)))
  have k4 : ((Presheaf.pullbackPushforwardAdjunction C f).unit.app F.presheaf).app (op U) ≫
    (((Presheaf.pullback C f).map β.hom).app (op ((Opens.map f).obj U)) ≫
    ((inverseImagePresheaf f G).map (homOfLE h).op ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f G)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))) =
    β.hom.app (op U) ≫
    (((Presheaf.pullbackPushforwardAdjunction C f).unit.app G.presheaf).app (op U) ≫
    ((inverseImagePresheaf f G).map (homOfLE h).op ≫
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (inverseImagePresheaf f G)).app (op V) ≫
    ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V)))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ ((inverseImagePresheaf f G).map (homOfLE h).op ≫
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (inverseImagePresheaf f G)).app (op V) ≫
        ((TopCat.Sheaf.forget C X).mapIso ((TopCat.Sheaf.pullbackIso C f).app G)).inv.app (op V))))
          hD.symm).trans (Category.assoc _ _ _))
  dsimp only [ambientSection, sheafPullbackPresheafIso]
  simp only [Category.assoc]
  exact k1.trans (k2.trans (k3.trans k4))

/-- `ambientSection_naturality` on elements. -/
theorem ambientSection_naturality_apply {F G : Y.Sheaf C} (β : F ⟶ G)
    {U : Opens Y} {V : Opens X} (h : V ≤ (Opens.map f).obj U)
    (s : ToType (F.presheaf.obj (op U))) :
    ((TopCat.Sheaf.pullback C f).map β).hom.app (op V) (ambientSection f F h s) =
      ambientSection f G h (β.hom.app (op U) s) :=
  by rw [← ConcreteCategory.comp_apply, ambientSection_naturality, ConcreteCategory.comp_apply]

end Naturality

noncomputable section Comparison

variable {X : TopCat.{u}}

/-- Restriction of abelian sheaves to a subset, as a functor. -/
abbrev restrictionFunctor (X : TopCat.{u}) (Z : Set X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} (Stacks.subsetInclusion X Z)

/-- The restriction of abelian sheaves to `Z` is additive. -/
instance restrictionFunctor_additive (Z : Set X) :
    (restrictionFunctor X Z).Additive :=
  Stacks.Cohomology.BaseChange.abelianInverseImage_additive (Stacks.subsetInclusion X Z)

/-- The restriction of abelian sheaves to `Z` preserves finite limits. -/
instance restrictionFunctor_preservesFiniteLimits (Z : Set X) :
    PreservesFiniteLimits (restrictionFunctor X Z) :=
  Stacks.Cohomology.BaseChange.abelianInverseImage_preservesFiniteLimits
    (Stacks.subsetInclusion X Z)

/-- The restriction of abelian sheaves to `Z` preserves finite colimits. -/
instance restrictionFunctor_preservesFiniteColimits (Z : Set X) :
    PreservesFiniteColimits (restrictionFunctor X Z) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (Stacks.subsetInclusion X Z)).leftAdjoint_preservesColimits.preservesFiniteColimits.{u, u}

section

variable (Z : Set X)

/-- The free abelian sheaf on an open neighbourhood of `Z`, restricted to `Z`, receives a
canonical map from the free abelian sheaf on the whole of `Z`: the one corresponding, under the
identification of morphisms out of a free abelian sheaf with sections, to the section of the
restriction induced by the canonical section of the free abelian sheaf on the neighbourhood. -/
def freeRestrictionMap (U : OpenNhdsSet Z) :
    (freeYoneda (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤ ⟶
      (restrictionFunctor X Z).obj
        ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj) :=
  (sectionsEquiv ⊤ _).symm
    (ambientSection (Stacks.subsetInclusion X Z)
      ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj)
      (top_le_map_openNhdsSet U) (gen U.obj))

/-- The section of the restricted free abelian sheaf corresponding to `freeRestrictionMap` is the
section induced by the canonical section of the free abelian sheaf on the neighbourhood. -/
theorem sectionsEquiv_freeRestrictionMap (U : OpenNhdsSet Z) :
    sectionsEquiv ⊤ _ (freeRestrictionMap Z U) =
      ambientSection (Stacks.subsetInclusion X Z)
        ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj)
        (top_le_map_openNhdsSet U) (gen U.obj) :=
  (sectionsEquiv ⊤ _).apply_symm_apply _

/-- **The canonical maps from the free abelian sheaf on `Z` are compatible with shrinking the
neighbourhood.** -/
theorem freeRestrictionMap_comp {U V : OpenNhdsSet Z} (h : V.obj ⟶ U.obj) :
    freeRestrictionMap Z V ≫ (restrictionFunctor X Z).map
        ((freeYoneda (Opens.grothendieckTopology X)).map h) =
      freeRestrictionMap Z U := by
  have hgen : ((freeYoneda (Opens.grothendieckTopology X)).map h).hom.app (op V.obj)
        (gen V.obj) =
      ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj).obj.map h.op (gen U.obj) :=
    (sectionsEquiv_eq_app_gen V.obj _ _).symm.trans
      ((congrArg (sectionsEquiv V.obj _) (Category.comp_id _).symm).trans
        (sectionsEquiv_naturality_left h _ (𝟙 _)))
  refine (sectionsEquiv ⊤ _).injective ?_
  rw [sectionsEquiv_naturality, sectionsEquiv_freeRestrictionMap,
    sectionsEquiv_freeRestrictionMap]
  exact (ambientSection_naturality_apply (Stacks.subsetInclusion X Z)
    ((freeYoneda (Opens.grothendieckTopology X)).map h) (top_le_map_openNhdsSet V)
    (gen V.obj)).trans ((congrArg _ hgen).trans
      (ambientSection_map_apply (Stacks.subsetInclusion X Z) _ h _ _ _))

section Map

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})]
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The diagram `U ↦ H^p(U, F)` over the open neighbourhoods of `Z`. -/
def openNeighborhoodCohomology (p : ℕ) : (OpenNhdsSet Z)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (openNhdsSetInclusion Z).op ⋙ F.cohomologyPresheaf p

/-- The comparison at a single open neighbourhood of `Z`: restrict the `Ext`-class along the
exact restriction functor, then pull back along `freeRestrictionMap`. -/
def cohomologyOfClosedMapComp (p : ℕ) (U : OpenNhdsSet Z) :
    Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj) F p →+
      Ext.{u} ((freeYoneda (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤)
        ((restrictionFunctor X Z).obj F) p :=
  ((Ext.mk₀ (freeRestrictionMap Z U)).precomp _ (zero_add p)).comp
    ((restrictionFunctor X Z).mapExtAddHom _ _ p)

/-- `cohomologyOfClosedMapComp` sends `x` to the restriction of `x` composed with the class of
`freeRestrictionMap`. -/
theorem cohomologyOfClosedMapComp_apply (p : ℕ) (U : OpenNhdsSet Z)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj) F p) :
    cohomologyOfClosedMapComp Z F p U x =
      (Ext.mk₀ (freeRestrictionMap Z U)).comp
        (x.mapExactFunctor (restrictionFunctor X Z)) (zero_add p) :=
  rfl

/-- **The comparison maps form a cocone**: they are compatible with shrinking the
neighbourhood. -/
theorem cohomologyOfClosedMapComp_naturality (p : ℕ) {U V : OpenNhdsSet Z} (h : V.obj ⟶ U.obj)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj) F p) :
    cohomologyOfClosedMapComp Z F p V
        ((Ext.mk₀ ((freeYoneda (Opens.grothendieckTopology X)).map h)).comp x (zero_add p)) =
      cohomologyOfClosedMapComp Z F p U x := by
  rw [cohomologyOfClosedMapComp_apply, cohomologyOfClosedMapComp_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc,
    freeRestrictionMap_comp]

/-- **The canonical comparison map**, from the colimit of the cohomology
over the open neighbourhoods of `Z` to the cohomology of the restriction of `F` to `Z`. -/
def cohomologyOfClosedMap (p : ℕ) :
    colimit (openNeighborhoodCohomology Z F p) ⟶
      (((restrictionFunctor X Z).obj F).cohomologyPresheaf p).obj (op ⊤) :=
  colimit.desc (openNeighborhoodCohomology Z F p)
    { pt := (((restrictionFunctor X Z).obj F).cohomologyPresheaf p).obj (op ⊤)
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (cohomologyOfClosedMapComp Z F p U.unop)
          naturality := by
            intro U V a
            refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
            simp only [Functor.const_obj_map]
            exact cohomologyOfClosedMapComp_naturality Z F p
              ((openNhdsSetInclusion Z).map a.unop) x } }

/-- On the class of a neighbourhood, `cohomologyOfClosedMap` is the comparison
`cohomologyOfClosedMapComp` at that neighbourhood. -/
theorem cohomologyOfClosedMap_ι (p : ℕ) (U : (OpenNhdsSet Z)ᵒᵖ)
    (x : ToType ((openNeighborhoodCohomology Z F p).obj U)) :
    cohomologyOfClosedMap Z F p (colimit.ι (openNeighborhoodCohomology Z F p) U x) =
      cohomologyOfClosedMapComp Z F p U.unop x :=
  by rw [← ConcreteCategory.comp_apply, cohomologyOfClosedMap, colimit.ι_desc]; rfl

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})] in
/-- Every element of the colimit over the open neighbourhoods of `Z` is represented by a class on
one of them. -/
theorem exists_colimit_ι_openNeighborhoodCohomology (p : ℕ)
    (t : ToType (colimit (openNeighborhoodCohomology Z F p))) :
    ∃ (U : (OpenNhdsSet Z)ᵒᵖ) (x : ToType ((openNeighborhoodCohomology Z F p).obj U)),
      colimit.ι (openNeighborhoodCohomology Z F p) U x = t :=
  Types.jointly_surjective.{u, u} _
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u}) (colimit.isColimit _)) t

section DegreeZero

/-- **The comparison in degree zero is the comparison of sections.** -/
theorem cohomologyOfClosedMapComp_zero_apply (U : OpenNhdsSet Z)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.obj) F 0) :
    extSectionsAddEquiv ⊤ ((restrictionFunctor X Z).obj F)
        (cohomologyOfClosedMapComp Z F 0 U x) =
      ambientSection (Stacks.subsetInclusion X Z) F (top_le_map_openNhdsSet U)
        (extSectionsAddEquiv U.obj F x) := by
  have hmap : Ext.addEquiv₀ (x.mapExactFunctor (restrictionFunctor X Z)) =
      (restrictionFunctor X Z).map (Ext.addEquiv₀ x) := by
    refine (Ext.mk₀_bijective _ _).injective ?_
    rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mapExactFunctor_mk₀, Ext.mk₀_addEquiv₀_apply]
  rw [cohomologyOfClosedMapComp_apply]
  dsimp only [extSectionsAddEquiv, AddEquiv.trans_apply]
  rw [addEquiv₀_mk₀_comp, hmap, sectionsAddEquiv_apply, sectionsAddEquiv_apply,
    sectionsEquiv_naturality, sectionsEquiv_freeRestrictionMap]
  exact (ambientSection_naturality_apply (Stacks.subsetInclusion X Z) _
    (top_le_map_openNhdsSet U) (gen U.obj)).trans
      (congrArg _ (sectionsEquiv_eq_app_gen U.obj F _).symm)

/-- In degree zero the neighbourhood-cohomology diagram is the neighbourhood-sections diagram. -/
def openNeighborhoodCohomologyZeroIso :
    openNeighborhoodCohomology Z F 0 ≅
      (openNhdsSetInclusion Z).op ⋙
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj F :=
  Functor.isoWhiskerLeft (openNhdsSetInclusion Z).op (cohomologyPresheafIsoSections F)

/-- In degree zero, under the identifications of degree-zero cohomology with sections,
`cohomologyOfClosedMap` is the comparison map `subsetSectionsMap` of sections. -/
theorem extSectionsAddEquiv_cohomologyOfClosedMap_zero
    (c : ToType (colimit (openNeighborhoodCohomology Z F 0))) :
    extSectionsAddEquiv ⊤ ((restrictionFunctor X Z).obj F)
        (cohomologyOfClosedMap Z F 0 c) =
      subsetSectionsMap F Z
        ((HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIso Z F)).hom c) := by
  obtain ⟨U, x, rfl⟩ := exists_colimit_ι_openNeighborhoodCohomology Z F 0 c
  have hκ : (HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIso Z F)).hom
        (colimit.ι (openNeighborhoodCohomology Z F 0) U x) =
      colimit.ι (neighborhoodSections F Z) U
        ((openNeighborhoodCohomologyZeroIso Z F).hom.app U x) :=
    by rw [← ConcreteCategory.comp_apply, HasColimit.ι_isoOfNatIso_hom,
      ConcreteCategory.comp_apply]; rfl
  rw [cohomologyOfClosedMap_ι, hκ]
  exact (cohomologyOfClosedMapComp_zero_apply Z F U.unop x).trans
    ((congrArg (ambientSection (Stacks.subsetInclusion X Z) F
      (top_le_map_openNhdsSet U.unop))
        (cohomologyPresheafIsoSections_hom_app_apply F U.unop.obj x).symm).trans
      (subsetSectionsMap_ι F Z U _).symm)

/-- **The comparison map is an isomorphism in degree zero** when `Z` is quasi-compact and any two
distinct points of `Z` have disjoint open neighbourhoods in `X`. -/
theorem isIso_cohomologyOfClosedMap_zero (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (cohomologyOfClosedMap Z F 0) := by
  have hκ : Function.Bijective
      (HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIso Z F)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hσ : Function.Bijective (subsetSectionsMap F Z) :=
    ⟨injective_subsetSectionsMap F Z, surjective_subsetSectionsMap F hZ hSep⟩
  have hρ := (extSectionsAddEquiv (⊤ : Opens (TopCat.of Z))
    ((restrictionFunctor X Z).obj F)).bijective
  suffices IsIso ((CategoryTheory.forget AddCommGrpCat.{u}).map
      (cohomologyOfClosedMap Z F 0)) from
    isIso_of_reflects_iso (cohomologyOfClosedMap Z F 0) (CategoryTheory.forget AddCommGrpCat.{u})
  rw [isIso_iff_bijective]
  refine ⟨fun c c' hcc ↦ hκ.1 (hσ.1 ?_), fun t ↦ ?_⟩
  · exact ((extSectionsAddEquiv_cohomologyOfClosedMap_zero Z F c).symm.trans
      (congrArg _ hcc)).trans (extSectionsAddEquiv_cohomologyOfClosedMap_zero Z F c')
  · obtain ⟨w, hw⟩ := hσ.2 (extSectionsAddEquiv ⊤ ((restrictionFunctor X Z).obj F) t)
    obtain ⟨c, hc⟩ := hκ.2 w
    exact ⟨c, hρ.1 ((extSectionsAddEquiv_cohomologyOfClosedMap_zero Z F c).trans
      ((congrArg _ hc).trans hw))⟩

end DegreeZero

end Map

section DimensionShift

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})]

/-- **The comparison map is compatible with postcomposition by an `Ext`-class.** -/
theorem cohomologyOfClosedMap_ι_comp
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} {m : ℕ}
    (β : Ext.{u} F G m) (p q : ℕ) (hpq : p + m = q) (U : (OpenNhdsSet Z)ᵒᵖ)
    (x : Ext.{u} ((freeYoneda (Opens.grothendieckTopology X)).obj U.unop.obj) F p) :
    cohomologyOfClosedMap Z G q
        (colimit.ι (openNeighborhoodCohomology Z G q) U (x.comp β hpq)) =
      (cohomologyOfClosedMap Z F p
          (colimit.ι (openNeighborhoodCohomology Z F p) U x)).comp
        (β.mapExactFunctor (restrictionFunctor X Z)) hpq := by
  refine (cohomologyOfClosedMap_ι Z G q U (x.comp β hpq)).trans (Eq.trans ?_
    (congrArg (fun t ↦ Ext.comp t (β.mapExactFunctor (restrictionFunctor X Z)) hpq)
      (cohomologyOfClosedMap_ι Z F p U x).symm))
  rw [cohomologyOfClosedMapComp_apply, cohomologyOfClosedMapComp_apply,
    Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ (freeRestrictionMap Z U.unop))
    (x.mapExactFunctor (restrictionFunctor X Z))
    (β.mapExactFunctor (restrictionFunctor X Z)) (zero_add p) hpq
    (show 0 + p + m = q by lia)).symm

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- **The positive-degree `Ext`-groups out of the free abelian sheaf on `Z` into the restriction
of an injective abelian sheaf vanish**, when `Z` is quasi-compact and any two distinct points of
`Z` have disjoint open neighbourhoods in `X`. -/
theorem ext_eq_zero_of_injective_restriction
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (hp : 0 < p)
    (y : Ext.{u} ((freeYoneda (Opens.grothendieckTopology (TopCat.of Z))).obj ⊤)
      ((restrictionFunctor X Z).obj I) p) :
    y = 0 := by
  let : HasDerivedCategory.{u + 1}
      (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} AddCommGrpCat.{u} := HasDerivedCategory.standard _
  have hinj : Injective (C := TopCat.Sheaf AddCommGrpCat.{u} X) I := ‹Injective I›
  exact (AddCommGrpCat.subsingleton_of_isZero
    (isZero_cohomologyPresheaf_pullback_of_injective I hZ hSep p hp)).elim y 0

end DimensionShift




end


end Comparison

end Stacks.Topology

end
