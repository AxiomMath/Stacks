module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SectionsOnIntersection
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CompactSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a sheaf of sets along a quasi-compact separated subset

Let `X` be a topological space and let `Z ⊆ X` be a quasi-compact subset any two distinct points
of which have disjoint open neighbourhoods in `X`. For a sheaf of sets `F` on `X` this file proves
that the canonical map

`colim_{U ⊇ Z open} F(U) ⟶ Γ(Z, F|_Z)`

is a bijection, where `F|_Z` is the inverse image of `F` along the inclusion `Z → X`. This is the
degree-zero half of [Stacks, Tag 09V3] for sheaves of sets, the form in which it is used by
[Stacks, Tag 0D90] and by the proper base change theorem [Stacks, Tag 09V5].

## Main definitions

* `Stacks.Topology.OpenNhdsSet` is the category of open neighbourhoods of a subset, ordered by
  inclusion; it is cofiltered.
* `Stacks.Topology.openNeighborhoodSections` is the diagram `U ↦ F(U)` over that category.
* `Stacks.Topology.restrictTypeToSubset` is the inverse image of `F` on `Z` with its subspace
  topology.
* `Stacks.Topology.neighborhoodSectionRestriction` restricts a section on a neighbourhood of `Z`
  to `Z`, through the unit of the inverse-image/direct-image adjunction.
* `Stacks.Topology.sectionsOfClosedMap` is the induced map out of the colimit. It is packaged
  separately from the theorem so that the result records that *this* map, rather than merely some
  bijection, is invertible.

## Main results

* `Stacks.Topology.injective_sectionsOfClosedMap`: the comparison is injective for an *arbitrary*
  subset of an arbitrary space — no compactness and no separation.
* `Stacks.Topology.surjective_sectionsOfClosedMap`: the comparison is surjective once `Z` is
  quasi-compact and its distinct points are separated by disjoint opens of `X`.
* `Stacks.Topology.isIso_sectionsOfClosedMap`: the two together, as an isomorphism.

## Implementation notes

The separation hypothesis is [Stacks, Tag 09V3]'s own — distinct points of `Z` are separated by
disjoint opens of `X` — rather than Hausdorffness of `X`, because that is what its application in
[Stacks, Tag 09V5] can supply: there `Z` is the fibre of a *separated* map, which satisfies it by
[Stacks, Tag 0CY2] (3) with no assumption on the ambient space.

The whole argument is carried out in the classical germ model of the inverse image,
`GermPullback.sheaf`: a section of `F|_Z` over `V ⊆ Z` is a function `V → Germs F` which is
locally the family of germs of a single ambient section. The comparison
`Stacks.GermPullbackComparison.pullbackToGerm` of that model with `TopCat.Sheaf.pullback` is
an isomorphism, and
`Stacks.Topology.pullbackToGerm_neighborhoodSectionRestriction` identifies the canonical
restriction map with the passage to germs. Working in the germ model is what makes the two
halves of the proof the two statements of
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/CompactSections.lean`: injectivity is
`exists_opens_restrict_eq_of_germ_eqOn` (sections with the same germs along `Z` agree on a
neighbourhood of `Z`) and surjectivity is `exists_opens_glue_of_isCompact_of_pairwiseSeparated`
(local ambient sections representing the germ family can be shrunk and glued).

Everything is stated for a bundled space `X : TopCat.{u}`; for a space given as a type with a
topology, apply the results to `TopCat.of X`.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
* [SGA 4, Expose V bis, 4.1.3]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GermPullbackComparison (pullbackToGerm pullbackToGerm_unit pullbackToGerm_isIso)

namespace Stacks.Topology

universe u

variable {X : TopCat.{u}}

/-- Open neighbourhoods of a subset, ordered by inclusion. -/
abbrev OpenNhdsSet (Z : Set X) :=
  ObjectProperty.FullSubcategory ((fun U : Opens X ↦ Z ⊆ U) : ObjectProperty (Opens X))

/-- The inclusion of the category of open neighbourhoods of `Z` into all open sets. -/
def openNhdsSetInclusion (Z : Set X) : OpenNhdsSet Z ⥤ Opens X :=
  ObjectProperty.ι ((fun U : Opens X ↦ Z ⊆ U) : ObjectProperty (Opens X))

/-- Open neighbourhoods are cofiltered: intersections give common refinements. -/
instance openNhdsSet_isCofiltered (Z : Set X) : IsCofiltered (OpenNhdsSet Z) where
  nonempty := ⟨⟨⊤, Set.subset_univ Z⟩⟩
  cone_objs U V := ⟨⟨U.obj ⊓ V.obj, fun _ hx ↦ ⟨U.property hx, V.property hx⟩⟩,
    ObjectProperty.homMk (homOfLE inf_le_left),
    ObjectProperty.homMk (homOfLE inf_le_right), trivial⟩
  cone_maps {U _} _ _ := ⟨U, 𝟙 U, ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩

/-- Sections of a sheaf of sets over the open neighbourhoods of a subset. -/
def openNeighborhoodSections (F : X.Sheaf (Type u)) (Z : Set X) :
    (OpenNhdsSet Z)ᵒᵖ ⥤ Type u :=
  (openNhdsSetInclusion Z).op ⋙ F.obj

/-- Restriction of a sheaf of sets to a subset with its subspace topology. -/
noncomputable def restrictTypeToSubset (F : X.Sheaf (Type u)) (Z : Set X) :
    (TopCat.of Z).Sheaf (Type u) :=
  (TopCat.Sheaf.pullback (Type u) (Stacks.subsetInclusion X Z)).obj F

/-- Restrict a section on a neighbourhood of `Z` to the subset. -/
noncomputable def neighborhoodSectionRestriction (F : X.Sheaf (Type u)) (Z : Set X)
    (U : OpenNhdsSet Z) :
    F.obj.obj (op U.obj) ⟶ (restrictTypeToSubset F Z).obj.obj (op ⊤) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
      (Stacks.subsetInclusion X Z)).unit.app F).hom.app (op U.obj) ≫
    (restrictTypeToSubset F Z).obj.map (homOfLE (by
      intro x _
      exact U.property x.property)).op

/-- The comparison with the sheaf of compatible germs carries the canonical restriction of a
section on a neighbourhood of `Z` to the family of its germs along `Z`. -/
theorem pullbackToGerm_neighborhoodSectionRestriction (F : X.Sheaf (Type u)) (Z : Set X)
    (U : OpenNhdsSet Z) (s : F.obj.obj (op U.obj)) :
    (pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app (op ⊤)
      (neighborhoodSectionRestriction F Z U s) =
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion X Z))
        (W := ⊤) (V := U.obj) (fun z ↦ U.property z.1.2) s := by
  set g := Stacks.subsetInclusion X Z with hg
  set W := (Opens.map g).obj U.obj with hW
  have hle : (⊤ : Opens (TopCat.of Z)) ≤ W := fun z _ ↦ U.property z.2
  set H := restrictTypeToSubset F Z with hH
  set m := (pullbackToGerm g F).hom with hm
  set t := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).unit.app F).hom.app
    (op U.obj) s with ht
  have hp : m.app (op ⊤) (H.obj.map (homOfLE hle).op t) =
      (GermPullback.sheaf (ConcreteCategory.hom g) F.obj).obj.map (homOfLE hle).op
        (m.app (op W) t) :=
    congrArg (fun f ↦ f t) (m.naturality (homOfLE hle).op)
  have hu : m.app (op W) t =
      GermPullback.ofSection (g := ConcreteCategory.hom g) (W := W) (V := U.obj)
        (fun z ↦ z.2) s :=
    pullbackToGerm_unit g F U.obj s
  show m.app (op ⊤) (H.obj.map (homOfLE hle).op t) = _
  rw [hp, hu]
  exact GermPullback.ext fun _ ↦ rfl

/-- The comparison with the sheaf of compatible germs is bijective on global sections. -/
theorem bijective_pullbackToGerm_app_top (F : X.Sheaf (Type u)) (Z : Set X) :
    Function.Bijective
      ((pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app (op ⊤)) := by
  have h₁ : IsIso (pullbackToGerm (Stacks.subsetInclusion X Z) F) :=
    pullbackToGerm_isIso (Stacks.subsetInclusion X Z) F
  have h₂ : IsIso ((TopCat.Sheaf.forget (Type u) (TopCat.of Z)).map
      (pullbackToGerm (Stacks.subsetInclusion X Z) F)) := inferInstance
  have h₃ : IsIso (pullbackToGerm (Stacks.subsetInclusion X Z) F).hom := by
    show IsIso ((TopCat.Sheaf.forget (Type u) (TopCat.of Z)).map
      (pullbackToGerm (Stacks.subsetInclusion X Z) F))
    infer_instance
  have h₄ : IsIso ((pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app
      (op ⊤)) := NatIso.isIso_app_of_isIso _ _
  exact (isIso_iff_bijective _).mp h₄

/-- The germ of a restricted section at a point is its germ before restriction. -/
private theorem germs_mk_germ_res (F : X.Sheaf (Type u)) {U V : Opens X} (i : U ⟶ V) {x : X}
    (hx : x ∈ U) (s : F.obj.obj (op V)) :
    (⟨x, F.presheaf.germ U x hx (F.obj.map i.op s)⟩ : GermPullback.Germs F.presheaf) =
      ⟨x, F.presheaf.germ V x (i.le hx) s⟩ :=
  congrArg (fun ξ ↦ (⟨x, ξ⟩ : GermPullback.Germs F.presheaf))
    (F.presheaf.germ_res_apply i x hx s)

/-- Germs of sections at the same point are equal only if the stalk elements are. -/
private theorem germ_eq_of_germs_mk_eq (F : X.Sheaf (Type u)) {x : X} {U V : Opens X}
    {hU : x ∈ U} {hV : x ∈ V} {s : F.obj.obj (op U)} {t : F.obj.obj (op V)}
    (h : (⟨x, F.presheaf.germ U x hU s⟩ : GermPullback.Germs F.presheaf) =
      ⟨x, F.presheaf.germ V x hV t⟩) :
    F.presheaf.germ U x hU s = F.presheaf.germ V x hV t :=
  eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp h).2

/-- The germ families of a section and of its restriction to a smaller neighbourhood of `Z`
coincide. -/
theorem ofSection_top_map (F : X.Sheaf (Type u)) (Z : Set X)
    {U V : OpenNhdsSet Z} (a : V ⟶ U) (s : F.obj.obj (op U.obj)) :
    GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion X Z))
        (W := ⊤) (V := V.obj) (fun z ↦ V.property z.1.2)
        (F.obj.map ((openNhdsSetInclusion Z).map a).op s) =
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion X Z))
        (W := ⊤) (V := U.obj) (fun z ↦ U.property z.1.2) s := by
  refine GermPullback.ext fun z ↦ ?_
  simp only [GermPullback.ofSection_val]
  exact germs_mk_germ_res F ((openNhdsSetInclusion Z).map a) _ s

/-- Restricting a section to a smaller neighbourhood of `Z` does not change the section it
induces on `Z`. -/
theorem neighborhoodSectionRestriction_map (F : X.Sheaf (Type u)) (Z : Set X)
    {U V : OpenNhdsSet Z} (a : V ⟶ U) (s : F.obj.obj (op U.obj)) :
    neighborhoodSectionRestriction F Z V (F.obj.map ((openNhdsSetInclusion Z).map a).op s) =
      neighborhoodSectionRestriction F Z U s :=
  (bijective_pullbackToGerm_app_top F Z).1
    (((pullbackToGerm_neighborhoodSectionRestriction F Z V
          (F.obj.map ((openNhdsSetInclusion Z).map a).op s)).trans
        (ofSection_top_map F Z a s)).trans
      (pullbackToGerm_neighborhoodSectionRestriction F Z U s).symm)

/-- Restriction to a smaller neighbourhood followed by the comparison is the comparison. -/
theorem neighborhoodSectionRestriction_comp (F : X.Sheaf (Type u)) (Z : Set X)
    {U V : OpenNhdsSet Z} (a : V ⟶ U) :
    F.obj.map ((openNhdsSetInclusion Z).map a).op ≫ neighborhoodSectionRestriction F Z V =
      neighborhoodSectionRestriction F Z U := by
  ext s
  exact neighborhoodSectionRestriction_map F Z a s

/-- The canonical map from neighbourhood sections to global sections of the restriction
of a sheaf of sets. -/
noncomputable def sectionsOfClosedMap (F : X.Sheaf (Type u)) (Z : Set X) :
    colimit (openNeighborhoodSections F Z) ⟶ (restrictTypeToSubset F Z).obj.obj (op ⊤) :=
  colimit.desc (openNeighborhoodSections F Z)
    { pt := (restrictTypeToSubset F Z).obj.obj (op ⊤)
      ι :=
        { app := fun U ↦ neighborhoodSectionRestriction F Z U.unop
          naturality := fun _ _ a ↦
            (neighborhoodSectionRestriction_comp F Z a.unop).trans
              (Category.comp_id _).symm } }

/-- The comparison sends each representative to its canonical restriction. -/
@[simp, reassoc (attr := simp)]
theorem colimit_ι_sectionsOfClosedMap (F : X.Sheaf (Type u)) (Z : Set X) (U : OpenNhdsSet Z) :
    colimit.ι (openNeighborhoodSections F Z) (op U) ≫ sectionsOfClosedMap F Z =
      neighborhoodSectionRestriction F Z U :=
  colimit.ι_desc _ _


/-- The comparison evaluated on a representative. -/
theorem sectionsOfClosedMap_ι (F : X.Sheaf (Type u)) (Z : Set X) (U : (OpenNhdsSet Z)ᵒᵖ)
    (s : (openNeighborhoodSections F Z).obj U) :
    sectionsOfClosedMap F Z (colimit.ι (openNeighborhoodSections F Z) U s) =
      neighborhoodSectionRestriction F Z U.unop s :=
  congrArg (fun m : (openNeighborhoodSections F Z).obj U ⟶
      (restrictTypeToSubset F Z).obj.obj (op ⊤) ↦ m s)
    (colimit_ι_sectionsOfClosedMap F Z U.unop)

/-- A representative on a neighbourhood of `Z` and its restriction to a smaller neighbourhood
define the same element of the colimit. -/
theorem colimit_ι_eq_of_le (F : X.Sheaf (Type u)) (Z : Set X) {U : (OpenNhdsSet Z)ᵒᵖ}
    {V : OpenNhdsSet Z} (a : V ⟶ U.unop) (s : (openNeighborhoodSections F Z).obj U) :
    colimit.ι (openNeighborhoodSections F Z) (op V)
        (F.obj.map ((openNhdsSetInclusion Z).map a).op s) =
      colimit.ι (openNeighborhoodSections F Z) U s :=
  congrArg (fun m : (openNeighborhoodSections F Z).obj U ⟶
      colimit (openNeighborhoodSections F Z) ↦ m s)
    (colimit.w (openNeighborhoodSections F Z) (Quiver.Hom.op a))

/-- The comparison with the germ model sends the image of a representative to its germ family. -/
private theorem pullbackToGerm_sectionsOfClosedMap_ι (F : X.Sheaf (Type u)) (Z : Set X)
    (U : (OpenNhdsSet Z)ᵒᵖ) (s : (openNeighborhoodSections F Z).obj U) :
    (pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app (op ⊤)
        (sectionsOfClosedMap F Z (colimit.ι (openNeighborhoodSections F Z) U s)) =
      GermPullback.ofSection (g := ConcreteCategory.hom (Stacks.subsetInclusion X Z))
        (W := ⊤) (V := U.unop.obj) (fun z ↦ U.unop.property z.1.2) s :=
  (congrArg _ (sectionsOfClosedMap_ι F Z U s)).trans
    (pullbackToGerm_neighborhoodSectionRestriction F Z U.unop s)

/-- **Injectivity of the comparison**, for an arbitrary subset of an arbitrary space: two
sections on neighbourhoods of `Z` inducing the same section on `Z` already agree on a
neighbourhood of `Z`. -/
theorem injective_sectionsOfClosedMap (F : X.Sheaf (Type u)) (Z : Set X) :
    Function.Injective (sectionsOfClosedMap F Z) := by
  intro a b hab
  obtain ⟨i, s, ha⟩ := Types.jointly_surjective' a
  obtain ⟨j, t, hb⟩ := Types.jointly_surjective' b
  subst ha hb
  have hg := (pullbackToGerm_sectionsOfClosedMap_ι F Z i s).symm.trans
    ((congrArg ((pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app (op ⊤)) hab).trans
      (pullbackToGerm_sectionsOfClosedMap_ι F Z j t))
  have hgerm : ∀ x, ∀ hx : x ∈ Z,
      F.presheaf.germ (unop i).obj x ((unop i).property hx) s =
        F.presheaf.germ (unop j).obj x ((unop j).property hx) t := fun x hx ↦
    germ_eq_of_germs_mk_eq F
      (congrArg (fun σ ↦ σ.1 (⟨⟨x, hx⟩, trivial⟩ : (⊤ : Opens (TopCat.of Z)))) hg)
  obtain ⟨A, hZA, iAU, iAV, hAeq⟩ :=
    exists_opens_restrict_eq_of_germ_eqOn F s t (unop i).property (unop j).property hgerm
  have hA : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ unop i := ObjectProperty.homMk iAU
  have hA' : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ unop j := ObjectProperty.homMk iAV
  have hAeq' : F.obj.map ((openNhdsSetInclusion Z).map hA).op s =
      F.obj.map ((openNhdsSetInclusion Z).map hA').op t := by
    rw [Subsingleton.elim ((openNhdsSetInclusion Z).map hA) iAU,
      Subsingleton.elim ((openNhdsSetInclusion Z).map hA') iAV]
    exact hAeq
  rw [← colimit_ι_eq_of_le F Z hA s, ← colimit_ι_eq_of_le F Z hA' t]
  exact congrArg (colimit.ι (openNeighborhoodSections F Z)
    (op (⟨A, hZA⟩ : OpenNhdsSet Z))) hAeq'


/-- A global section of the restriction of `F` to `Z` is, near every point of `Z`, the family of
germs of a section of `F` on an open of the ambient space. -/
theorem exists_ambient_repr (F : X.Sheaf (Type u)) (Z : Set X)
    (σ : (GermPullback.sheaf (ConcreteCategory.hom (Stacks.subsetInclusion X Z)) F.obj).obj.obj
      (op ⊤)) (z : Z) :
    ∃ (N : Opens X) (_ : (z : X) ∈ N) (sec : F.obj.obj (op N)),
      ∀ (w : X) (hwZ : w ∈ Z) (hwN : w ∈ N),
        σ.1 ⟨⟨w, hwZ⟩, trivial⟩ = ⟨w, F.presheaf.germ N w hwN sec⟩ := by
  obtain ⟨W₀, hzW₀, iW, V, hV, sec, hsec⟩ := GermPullback.exists_repr σ (z := z) trivial
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp W₀.2
  have hzO : (z : X) ∈ O := by
    have : (z : Z) ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hzW₀
    exact this
  refine ⟨⟨O, hO⟩ ⊓ V, ⟨hzO, hV ⟨z, hzW₀⟩⟩,
    F.obj.map (homOfLE (inf_le_right : (⟨O, hO⟩ ⊓ V : Opens X) ≤ V)).op sec, ?_⟩
  intro w hwZ hwN
  have hwW₀ : (⟨w, hwZ⟩ : Z) ∈ W₀ := by
    have : (⟨w, hwZ⟩ : Z) ∈ Subtype.val ⁻¹' O := hwN.1
    rwa [hOW] at this
  have h := hsec ⟨⟨w, hwZ⟩, hwW₀⟩
  exact h.trans
    (germs_mk_germ_res F (homOfLE (inf_le_right : (⟨O, hO⟩ ⊓ V : Opens X) ≤ V)) hwN sec).symm


/-- **Surjectivity of the comparison** for a quasi-compact subset whose distinct points are
separated by disjoint opens of the ambient space. -/
theorem surjective_sectionsOfClosedMap (F : X.Sheaf (Type u)) {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    Function.Surjective (sectionsOfClosedMap F Z) := by
  classical
  intro y
  choose N hzN sec hsec using fun z : Z ↦ exists_ambient_repr F Z
    ((pullbackToGerm (Stacks.subsetInclusion X Z) F).hom.app (op ⊤) y) z
  have hcover : Z ⊆ ⋃ z : Z, (N z : Set X) := fun w hw ↦
    Set.mem_iUnion.2 ⟨⟨w, hw⟩, hzN ⟨w, hw⟩⟩
  have hcompat : ∀ i j : Z, ∀ x ∈ Z ∩ (N i : Set X) ∩ (N j : Set X),
      ∃ (M : Opens X) (_ : x ∈ M) (iMi : M ⟶ N i) (iMj : M ⟶ N j),
        F.presheaf.map iMi.op (sec i) = F.presheaf.map iMj.op (sec j) := by
    intro i j x hx
    exact F.presheaf.germ_eq x hx.1.2 hx.2 (sec i) (sec j) (germ_eq_of_germs_mk_eq F
      ((hsec i x hx.1.1 hx.1.2).symm.trans (hsec j x hx.1.1 hx.2)))
  obtain ⟨V, iVN, hZV, s, hs⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hZ hSep N sec hcover hcompat
  refine ⟨colimit.ι (openNeighborhoodSections F Z)
    (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) s, ?_⟩
  refine (bijective_pullbackToGerm_app_top F Z).1
    ((pullbackToGerm_sectionsOfClosedMap_ι F Z (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) s).trans ?_)
  refine GermPullback.ext fun w ↦ ?_
  obtain ⟨z', hz'⟩ := Opens.mem_iSup.1 (hZV w.1.2)
  refine Eq.trans ?_ (hsec z' w.1.1 w.1.2 ((iVN z').le hz')).symm
  refine (germs_mk_germ_res F (Opens.leSupr V z') hz' s).symm.trans ?_
  rw [hs z']
  exact germs_mk_germ_res F (iVN z') hz' (sec z')


/-- For a quasi-compact subset whose distinct points have disjoint open neighbourhoods in the
ambient space, the canonical restriction map from the sections on the open neighbourhoods of
`Z` to the global sections of the restriction of `F` to `Z` is an isomorphism. -/
@[stacks 09V3 "degree-zero comparison for sheaves of sets", sga "4 Vbis 4.1.3" "i = 0"]
theorem isIso_sectionsOfClosedMap (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V)
    (F : X.Sheaf (Type u)) :
    IsIso (sectionsOfClosedMap F Z) :=
  (isIso_iff_bijective _).mpr
    ⟨injective_sectionsOfClosedMap F Z, surjective_sectionsOfClosedMap F hZ hSep⟩

end Stacks.Topology

end
