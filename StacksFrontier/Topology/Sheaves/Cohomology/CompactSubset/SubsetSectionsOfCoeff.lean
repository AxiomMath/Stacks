module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.CompactSections
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.SectionsAndStalks
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSections

/-!
# Sections along a quasi-compact separated subset, at arbitrary coefficients

Let `X` be a topological space and let `Z ⊆ X` be a quasi-compact subset any two distinct points
of which have disjoint open neighbourhoods in `X`. For a sheaf `F` on `X` with values in a
concrete category `C` this file proves that the canonical map

`colim_{U ⊇ Z open} F(U) ⟶ Γ(Z, F|_Z)`

is an isomorphism, where `F|_Z` is the inverse image of `F` along the inclusion `Z → X`. This is
the degree-zero half of [Stacks, Tag 09V3] with no restriction on the coefficients — in
particular for sheaves of abelian groups, which is the form in which the positive-degree half of
that tag uses it.

## Main definitions

* `Stacks.Topology.neighborhoodSections` is the diagram `U ↦ F(U)` over the open neighbourhoods
  of `Z`, which are cofiltered.
* `Stacks.Topology.subsetSectionsMap` is the induced map out of the colimit. It is packaged
  separately from the theorem so that the result records that *this* map, rather than merely some
  isomorphism, is invertible.

## Main results

* `Stacks.Topology.injective_subsetSectionsMap`: the comparison is injective for an *arbitrary*
  subset of an arbitrary space — no compactness and no separation.
* `Stacks.Topology.surjective_subsetSectionsMap`: the comparison is surjective once `Z` is
  quasi-compact and its distinct points are separated by disjoint opens of `X`.
* `Stacks.Topology.isIso_subsetSectionsMap`: the two together, as an isomorphism.

## Implementation notes

The separation hypothesis is [Stacks, Tag 09V3]'s own — distinct points of `Z` are separated by
disjoint opens of `X` — rather than Hausdorffness of `X`, because that is what its application in
[Stacks, Tag 09V5] can supply: there `Z` is the fibre of a *separated* map, which satisfies it by
[Stacks, Tag 0CY2] (3) with no assumption on the ambient space.

The whole argument is carried out in stalks, through
`StacksFrontier/Topology/Sheaves/Functors/Pullback/SectionsAndStalks.lean`: a section of `F|_Z` has,
at each point of `Z`, a germ, which is a germ of `F` at that point of `X`, and
`Stacks.Topology.germ_ambientSection`
identifies the germs of the sections induced by ambient sections. Injectivity is then
`Stacks.Topology.exists_opens_restrict_eq_of_germ_eqOn` (sections with the same germs along `Z`
agree on a neighbourhood of `Z`) and surjectivity is
`Stacks.Topology.exists_opens_glue_of_isCompact_of_pairwiseSeparated` (local ambient sections
representing the germs can be shrunk and glued), both from
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/CompactSections.lean`
and both already stated at arbitrary coefficients.

This is the coefficient-general form of `Stacks.Topology.isIso_sectionsOfClosedMap`
(`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/SubsetSections.lean`), which is the same
statement for sheaves of sets proved in the classical germ model `GermPullback.sheaf`; the category
of open neighbourhoods
`Stacks.Topology.OpenNhdsSet` and its cofilteredness are taken from that file rather than
restated. The two comparison maps are built from the two units — the sheaf-level adjunction unit
there, the presheaf-level one followed by sheafification here — the latter being the route along
which the germ computation of
`StacksFrontier/Topology/Sheaves/Functors/Pullback/SectionsAndStalks.lean` is available.

Several identities are applied as terms rather than by `rw`. In these goals one object has two
definitionally but not syntactically equal spellings (`(unop U).obj` versus
`(openNhdsSetInclusion Z).obj (unop U)`, `x` versus `subsetInclusion X Z ⟨x, hx⟩`), and `rw`
matches syntactically at the `implicit` transparency level, so it rejects the rewrite.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 008H](https://stacks.math.columbia.edu/tag/008H)
* [SGA 4, Expose V bis, 4.1.3]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X : TopCat.{v}}

/-- The whole of a subset lies in the inverse image of any of its open neighbourhoods. -/
theorem top_le_map_openNhdsSet {Z : Set X} (U : OpenNhdsSet Z) :
    (⊤ : Opens (TopCat.of Z)) ≤ (Opens.map (Stacks.subsetInclusion X Z)).obj U.obj :=
  fun z _ ↦ U.property z.2

/-- Sections of a sheaf over the open neighbourhoods of a subset. -/
def neighborhoodSections (F : X.Sheaf C) (Z : Set X) : (OpenNhdsSet Z)ᵒᵖ ⥤ C :=
  (openNhdsSetInclusion Z).op ⋙ F.presheaf

/-- The canonical map from the sections of `F` on the open neighbourhoods of a subset `Z` to the
global sections of the restriction of `F` to `Z`. -/
def subsetSectionsMap (F : X.Sheaf C) (Z : Set X) :
    colimit (neighborhoodSections F Z) ⟶
      ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.obj (op ⊤) :=
  colimit.desc (neighborhoodSections F Z)
    { pt := ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.obj (op ⊤)
      ι :=
        { app := fun U ↦
            ambientSection (Stacks.subsetInclusion X Z) F (top_le_map_openNhdsSet U.unop)
          naturality := fun _ _ a ↦
            (ambientSection_map (Stacks.subsetInclusion X Z) F
              ((openNhdsSetInclusion Z).map a.unop) _ _).trans (Category.comp_id _).symm } }

/-- The map `subsetSectionsMap` sends the class of a section `s` on a neighbourhood `U` of `Z` to
the global section of the restriction of `F` to `Z` that `s` determines. -/
theorem subsetSectionsMap_ι (F : X.Sheaf C) (Z : Set X) (U : (OpenNhdsSet Z)ᵒᵖ)
    (s : ToType ((neighborhoodSections F Z).obj U)) :
    subsetSectionsMap F Z (colimit.ι (neighborhoodSections F Z) U s) =
      ambientSection (Stacks.subsetInclusion X Z) F (top_le_map_openNhdsSet U.unop) s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (colimit.ι_desc _ _) s)

omit [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms] in
/-- Every element of the colimit over the open neighbourhoods of `Z` is represented by a section
on one of them. -/
theorem exists_colimit_ι_neighborhoodSections (F : X.Sheaf C) (Z : Set X)
    (t : ToType (colimit (neighborhoodSections F Z))) :
    ∃ (U : (OpenNhdsSet Z)ᵒᵖ) (s : ToType ((neighborhoodSections F Z).obj U)),
      colimit.ι (neighborhoodSections F Z) U s = t := by
  obtain ⟨U, s, e⟩ := Types.jointly_surjective.{v, v} _
    (isColimitOfPreserves (CategoryTheory.forget C) (colimit.isColimit _)) t
  exact ⟨U, s, e⟩

omit [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
  [PreservesFilteredColimits (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).ReflectsIsomorphisms] in
/-- A section on a neighbourhood of `Z` and its restriction to a smaller neighbourhood represent
the same element of the colimit. -/
theorem colimit_ι_neighborhoodSections_map (F : X.Sheaf C) (Z : Set X)
    {U : (OpenNhdsSet Z)ᵒᵖ} {V : OpenNhdsSet Z} (a : V ⟶ U.unop)
    (s : ToType ((neighborhoodSections F Z).obj U)) :
    colimit.ι (neighborhoodSections F Z) (op V)
        (F.presheaf.map ((openNhdsSetInclusion Z).map a).op s) =
      colimit.ι (neighborhoodSections F Z) U s :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    (ConcreteCategory.congr_hom (colimit.w (neighborhoodSections F Z) a.op) s)

/-- **Injectivity of the comparison**, for an arbitrary subset of an arbitrary space: two
sections on neighbourhoods of `Z` which induce the same section of the restriction already agree
on a neighbourhood of `Z`. -/
theorem injective_subsetSectionsMap (F : X.Sheaf C) (Z : Set X) :
    Function.Injective (subsetSectionsMap F Z) := by
  intro α β hαβ
  obtain ⟨i, s, rfl⟩ := exists_colimit_ι_neighborhoodSections F Z α
  obtain ⟨j, t, rfl⟩ := exists_colimit_ι_neighborhoodSections F Z β
  rw [subsetSectionsMap_ι, subsetSectionsMap_ι] at hαβ
  have hgerm : ∀ x, ∀ hx : x ∈ Z,
      F.presheaf.germ i.unop.obj x (i.unop.property hx) s =
        F.presheaf.germ j.unop.obj x (j.unop.property hx) t := by
    intro x hx
    refine ambientStalkHom_injective (Stacks.subsetInclusion X Z) F ⟨x, hx⟩ ?_
    exact ((germ_ambientSection (Stacks.subsetInclusion X Z) F
          (top_le_map_openNhdsSet i.unop) ⟨x, hx⟩ _root_.trivial s).symm.trans
        (congrArg _ hαβ)).trans
      (germ_ambientSection (Stacks.subsetInclusion X Z) F
        (top_le_map_openNhdsSet j.unop) ⟨x, hx⟩ _root_.trivial t)
  obtain ⟨A, hZA, iAi, iAj, hA⟩ :=
    exists_opens_restrict_eq_of_germ_eqOn F s t i.unop.property j.unop.property hgerm
  have hAi : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ i.unop := ObjectProperty.homMk iAi
  have hAj : (⟨A, hZA⟩ : OpenNhdsSet Z) ⟶ j.unop := ObjectProperty.homMk iAj
  rw [← colimit_ι_neighborhoodSections_map F Z hAi s,
    ← colimit_ι_neighborhoodSections_map F Z hAj t]
  refine congrArg (colimit.ι (neighborhoodSections F Z) (op (⟨A, hZA⟩ : OpenNhdsSet Z))) ?_
  rw [Subsingleton.elim ((openNhdsSetInclusion Z).map hAi) iAi,
    Subsingleton.elim ((openNhdsSetInclusion Z).map hAj) iAj]
  exact hA

/-- A section of the restriction of `F` to `Z` over an open `W` is, near every point of `W`,
induced by a section of `F` on an open of the ambient space — and that ambient section can be
chosen so that its germs along the whole of its trace on `Z` are the prescribed ones. -/
theorem exists_ambient_repr_of_subset (F : X.Sheaf C) (Z : Set X) {W : Opens (TopCat.of Z)}
    (σ : ToType (((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.obj
      (op W))) (z : TopCat.of Z) (hzW : z ∈ W) :
    ∃ (N : Opens X) (_ : (z : X) ∈ N)
      (hNW : (Opens.map (Stacks.subsetInclusion X Z)).obj N ≤ W)
      (a : ToType (F.presheaf.obj (op N))),
      ∀ (w : X) (hwZ : w ∈ Z) (hwN : w ∈ N),
        ambientStalkHom (Stacks.subsetInclusion X Z) F ⟨w, hwZ⟩
            (F.presheaf.germ N w hwN a) =
          ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ
            W ⟨w, hwZ⟩ (hNW hwN) σ := by
  obtain ⟨N₀, hzN₀, a₀, ha₀⟩ :=
    exists_ambientSection_germ (Stacks.subsetInclusion X Z) F z
      (((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ
        W z hzW σ)
  have hz : z ∈ (Opens.map (Stacks.subsetInclusion X Z)).obj N₀ := hzN₀
  have h1 : ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ
        ((Opens.map (Stacks.subsetInclusion X Z)).obj N₀) z hz
        (ambientSection (Stacks.subsetInclusion X Z) F le_rfl a₀) =
      ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ
        W z hzW σ :=
    (germ_ambientSection (Stacks.subsetInclusion X Z) F le_rfl z hz a₀).trans ha₀
  obtain ⟨W₀, hzW₀, iW₁, iW₂, heq⟩ :=
    ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ_eq
      z hz hzW _ _ h1
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp W₀.2
  have hmem : ∀ (w : X) (hwZ : w ∈ Z), w ∈ O → (⟨w, hwZ⟩ : TopCat.of Z) ∈ W₀ := by
    intro w hwZ hwO
    have h : (⟨w, hwZ⟩ : TopCat.of Z) ∈ Subtype.val ⁻¹' O := hwO
    rwa [hOW] at h
  have hzO : (z : X) ∈ O := by
    have h : z ∈ Subtype.val ⁻¹' O := by rw [hOW]; exact hzW₀
    exact h
  refine ⟨N₀ ⊓ ⟨O, hO⟩, ⟨hzN₀, hzO⟩, fun w hw ↦ iW₂.le (hmem w.1 w.2 hw.2),
    F.presheaf.map (homOfLE (inf_le_left : N₀ ⊓ ⟨O, hO⟩ ≤ N₀)).op a₀, ?_⟩
  intro w hwZ hwN
  exact ((((congrArg (ambientStalkHom (Stacks.subsetInclusion X Z) F ⟨w, hwZ⟩)
      (F.presheaf.germ_res_apply
        (homOfLE (inf_le_left : N₀ ⊓ ⟨O, hO⟩ ≤ N₀)) w hwN a₀)).trans
    (germ_ambientSection (Stacks.subsetInclusion X Z) F le_rfl ⟨w, hwZ⟩ hwN.1 a₀).symm).trans
    (((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ_res_apply
      iW₁ (⟨w, hwZ⟩ : TopCat.of Z) (hmem w hwZ hwN.2) _).symm).trans (congrArg _ heq)).trans
    (((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F).presheaf.germ_res_apply
      iW₂ (⟨w, hwZ⟩ : TopCat.of Z) (hmem w hwZ hwN.2) σ)

/-- **Surjectivity of the comparison** for a quasi-compact subset whose distinct points are
separated by disjoint opens of the ambient space. -/
theorem surjective_subsetSectionsMap (F : X.Sheaf C) {Z : Set X} (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    Function.Surjective (subsetSectionsMap F Z) := by
  classical
  intro σ
  choose N hzN hNW a ha using fun z : TopCat.of Z ↦
    exists_ambient_repr_of_subset F Z σ z _root_.trivial
  have hcover : Z ⊆ ⋃ z : Z, (N z : Set X) := fun w hw ↦
    Set.mem_iUnion.2 ⟨⟨w, hw⟩, hzN ⟨w, hw⟩⟩
  have hcompat : ∀ p q : Z, ∀ w ∈ Z ∩ (N p : Set X) ∩ (N q : Set X),
      ∃ (M : Opens X) (_ : w ∈ M) (iMp : M ⟶ N p) (iMq : M ⟶ N q),
        F.presheaf.map iMp.op (a p) = F.presheaf.map iMq.op (a q) := by
    intro p q w hw
    have hg : F.presheaf.germ (N p) w hw.1.2 (a p) = F.presheaf.germ (N q) w hw.2 (a q) :=
      ambientStalkHom_injective (Stacks.subsetInclusion X Z) F ⟨w, hw.1.1⟩
        ((ha p w hw.1.1 hw.1.2).trans (ha q w hw.1.1 hw.2).symm)
    exact F.presheaf.germ_eq w hw.1.2 hw.2 _ _ hg
  obtain ⟨V, iVN, hZV, b, hb⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hZ hSep N a hcover hcompat
  refine ⟨colimit.ι (neighborhoodSections F Z)
    (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) b,
    (subsetSectionsMap_ι F Z (op (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) b).trans ?_⟩
  refine TopCat.Presheaf.section_ext
    ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X Z)).obj F) ⊤ _ _ fun z _ ↦ ?_
  obtain ⟨z', hz'⟩ := Opens.mem_iSup.1 (hZV z.2)
  refine (germ_ambientSection (Stacks.subsetInclusion X Z) F
      (top_le_map_openNhdsSet (⟨⨆ z, V z, hZV⟩ : OpenNhdsSet Z)) z _root_.trivial b).trans ?_
  refine (congrArg (ambientStalkHom (Stacks.subsetInclusion X Z) F z)
    ((((F.presheaf.germ_res_apply (Opens.leSupr V z') (z : X) hz' b).symm).trans
        (congrArg (F.presheaf.germ (V z') (z : X) hz') (hb z'))).trans
      (F.presheaf.germ_res_apply (iVN z') (z : X) hz' (a z')))).trans ?_
  exact ha z' (z : X) z.2 ((iVN z').le hz')

/-- **The degree-zero comparison of [Stacks, Tag 09V3] at arbitrary coefficients.** For a
quasi-compact subset `Z` whose distinct points have disjoint open neighbourhoods in the ambient
space, the canonical map from the sections of `F` on the open neighbourhoods of `Z` to the global
sections of the restriction of `F` to `Z` is an isomorphism. -/
theorem isIso_subsetSectionsMap (F : X.Sheaf C) (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B) :
    IsIso (subsetSectionsMap F Z) := by
  suffices IsIso ((CategoryTheory.forget C).map (subsetSectionsMap F Z)) from
    isIso_of_reflects_iso (subsetSectionsMap F Z) (CategoryTheory.forget C)
  rw [isIso_iff_bijective]
  exact ⟨injective_subsetSectionsMap F Z, surjective_subsetSectionsMap F hZ hSep⟩

end

end Stacks.Topology

end
