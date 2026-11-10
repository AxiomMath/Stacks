module

public import StacksFrontier.AlgebraicGeometry.RestrictionComparison.Basic
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The punctured system of affine open neighbourhoods

Let `S` be a scheme, let `s : I → S` be a finite family of closed points and let
`V = S \ {s i | i}` be the open complement, assumed quasi-compact over `S`.  Fix an index `i`
and an affine open neighbourhood `W₀` of `s i`.  Then `Spec 𝒪_{S, s i} ∩ V` is the limit of the
punctured neighbourhoods `W ∩ V`, `W` running over the affine open neighbourhoods of `s i`
contained in `W₀` (`AlgebraicGeometry.isLimitOpensSpecStalkCone`).  This file proves that the
objects of this system are quasi-compact and quasi-separated, the two hypotheses of
[Stacks, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM), that a neighbourhood of `s i` can be
shrunk to avoid all the other points of the family, and the resulting two-member open cover.

## Main results

* `AlgebraicGeometry.isCompact_inter_of_quasiCompact_ι`: the intersection of a quasi-compact
  open immersion's image with a quasi-compact open is quasi-compact, read inside the second
  open.
* `AlgebraicGeometry.compactSpace_opensDiagram_obj_of_isCompact` and
  `AlgebraicGeometry.quasiSeparatedSpace_opensDiagram_obj`: the two hypothesis families of
  Tag 01ZM for a system of preimages of a fixed quasi-compact open.
* `AlgebraicGeometry.compactSpace_puncturedAffineOpenNhdsDiagram_obj` and
  `AlgebraicGeometry.quasiSeparatedSpace_puncturedAffineOpenNhdsDiagram_obj`: those two families
  for the punctured system of affine open neighbourhoods of `s i`.
* `AlgebraicGeometry.complementOfOtherClosedPoints` and
  `AlgebraicGeometry.exists_affineOpenNhds_le_avoiding`: an affine open neighbourhood of `s i`
  inside any prescribed one and avoiding every other `s j`.
* `AlgebraicGeometry.preimage_complementOfClosedPoints_of_avoiding`: on such a neighbourhood the
  open complement of the whole family is the complement of the single point `s i`.
* `AlgebraicGeometry.sup_complementOfClosedPoints_inf_complementOfOtherClosedPoints`: the
  complement of the whole family together with such a neighbourhood covers the complement of the
  family *with `i` removed*.

## References

* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Compactness

/-- **A quasi-compact open immersion meets a quasi-compact open in a quasi-compact set**, read
as a subset of the second open. -/
theorem isCompact_inter_of_quasiCompact_ι {S : Scheme.{u}} (V W : S.Opens)
    (hqc : QuasiCompact V.ι) (hW : IsCompact (W : Set S)) :
    IsCompact ((W.ι ⁻¹ᵁ V : Set (W : Scheme.{u}))) := by
  have h := (hqc.isCompact_preimage _ W.2 hW).image V.ι.continuous
  rw [Set.image_preimage_eq_inter_range, V.range_ι] at h
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  change IsCompact (W.ι '' (W.ι ⁻¹' (V : Set S)))
  rwa [Set.image_preimage_eq_inter_range, W.range_ι, Set.inter_comm]

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- If `U` is a quasi-compact open of `D.obj i`, every object of
`AlgebraicGeometry.opensDiagram D i U`, the preimage of `U` along a transition morphism, is
quasi-compact. -/
theorem compactSpace_opensDiagram_obj_of_isCompact (i : I) (U : (D.obj i).Opens)
    (hU : IsCompact (U : Set (D.obj i))) (j : Over i) :
    CompactSpace ((opensDiagram D i U).obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ U.2 hU)

omit [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- If every stage of `D` is quasi-separated, every object of
`AlgebraicGeometry.opensDiagram D i U` is quasi-separated. -/
theorem quasiSeparatedSpace_opensDiagram_obj [∀ j : I, QuasiSeparatedSpace (D.obj j)] (i : I)
    (U : (D.obj i).Opens) (j : Over i) :
    QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).2).mp
    (.of_quasiSeparatedSpace _)

end Compactness

section Punctured

variable {S : Scheme.{u}} {I : Type u} [Finite I] (s : I → S)
  (hs : ∀ i, s i ∈ closedPoints S)

include hs in
/-- If the open complement of the family is quasi-compact over `S`, every punctured affine open
neighbourhood of `s i` contained in a fixed one is quasi-compact. -/
theorem compactSpace_puncturedAffineOpenNhdsDiagram_obj
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) (i : I)
    (W₀ : AffineOpenNhds S (s i)) (j : Over W₀) :
    CompactSpace ((opensDiagram (affineOpenNhdsDiagram S (s i)) W₀
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ complementOfClosedPoints s hs)).obj j) :=
  compactSpace_opensDiagram_obj_of_isCompact _ _ _
    (isCompact_inter_of_quasiCompact_ι (complementOfClosedPoints s hs) W₀.obj.1 hqc
      W₀.property.isCompact) j

omit [Finite I] in
/-- Every punctured affine open neighbourhood of `s i` is quasi-separated, being an open
subscheme of an affine one. -/
theorem quasiSeparatedSpace_puncturedAffineOpenNhdsDiagram_obj (i : I)
    (W₀ : AffineOpenNhds S (s i)) (V : S.Opens) (j : Over W₀) :
    QuasiSeparatedSpace ((opensDiagram (affineOpenNhdsDiagram S (s i)) W₀
      (Scheme.Opens.ι (X := S) W₀.obj.1 ⁻¹ᵁ V)).obj j) :=
  quasiSeparatedSpace_opensDiagram_obj _ _ _ j

/-- The open complement of every member of the family *except* `s i`. -/
def complementOfOtherClosedPoints (i : I) : S.Opens where
  carrier := ⋂ j : {j : I // j ≠ i}, ({s j.1}ᶜ : Set S)
  is_open' :=
    isOpen_iInter_of_finite fun j ↦ (mem_closedPoints_iff.mp (hs j.1)).isOpen_compl

include hs in
/-- The complement of the whole family is contained in the complement of all but one of its
members. -/
theorem complementOfClosedPoints_le_complementOfOtherClosedPoints (i : I) :
    complementOfClosedPoints s hs ≤ complementOfOtherClosedPoints s hs i :=
  fun _ hx ↦ Set.mem_iInter.mpr fun j ↦ Set.mem_iInter.mp hx j.1

include hs in
/-- For an injective family, the point `s i` lies in the complement of all the other points of
the family. -/
theorem mem_complementOfOtherClosedPoints (hinj : Function.Injective s) (i : I) :
    s i ∈ complementOfOtherClosedPoints s hs i :=
  Set.mem_iInter.mpr fun j (h : s i = s j.1) ↦ j.2 (hinj h.symm)

include hs in
/-- With one index, the complement of the other points is the whole scheme. -/
theorem complementOfOtherClosedPoints_eq_top (i : I) (hI : ∀ j : I, j = i) :
    complementOfOtherClosedPoints s hs i = ⊤ :=
  TopologicalSpace.Opens.ext
    (Set.eq_univ_of_forall fun _ ↦ Set.mem_iInter.mpr fun j ↦ absurd (hI j.1) j.2)

include hs in
/-- For an injective family, inside any affine open neighbourhood of `s i` there is one avoiding
every other point of the family. -/
theorem exists_affineOpenNhds_le_avoiding (hinj : Function.Injective s) (i : I)
    (W₀ : AffineOpenNhds S (s i)) :
    ∃ W : AffineOpenNhds S (s i), W.obj.1 ≤ W₀.obj.1 ∧ ∀ j, j ≠ i → s j ∉ W.obj.1 := by
  obtain ⟨W, hW⟩ := exists_affineOpenNhds_le S (s i)
    ⟨W₀.obj.1 ⊓ complementOfOtherClosedPoints s hs i,
      ⟨W₀.obj.2, mem_complementOfOtherClosedPoints s hs hinj i⟩⟩
  have hle : W.obj.1 ≤ W₀.obj.1 ⊓ complementOfOtherClosedPoints s hs i := hW
  exact ⟨W, le_trans hle inf_le_left, fun j hj hmem ↦
    Set.mem_iInter.mp (le_trans hle inf_le_right hmem) ⟨j, hj⟩ rfl⟩

include hs in
/-- On an open `W` avoiding every `s j` with `j ≠ i`, the open complement of the whole family is
the complement of the single point `s i`. -/
theorem preimage_complementOfClosedPoints_of_avoiding (i : I) (W : S.Opens)
    (hW : ∀ j, j ≠ i → s j ∉ W) :
    W.ι ⁻¹ᵁ complementOfClosedPoints s hs = W.ι ⁻¹ᵁ ⟨({s i}ᶜ : Set S),
      (mem_closedPoints_iff.mp (hs i)).isOpen_compl⟩ := by
  refine TopologicalSpace.Opens.ext (Set.ext fun w ↦ ?_)
  refine ⟨fun h ↦ Set.mem_iInter.mp h i, fun h ↦ Set.mem_iInter.mpr fun j ↦ ?_⟩
  by_cases hji : j = i
  · exact hji ▸ h
  · exact fun (hmem : _ ∈ ({s j} : Set S)) ↦ hW j hji (hmem ▸ w.2)

include hs in
/-- The complement of the whole family, together with an open neighbourhood `W` of `s i` cut
down to the complement of the other members, is the complement of the family with `i`
removed. -/
theorem sup_complementOfClosedPoints_inf_complementOfOtherClosedPoints (i : I) (W : S.Opens)
    (hiW : s i ∈ W) :
    complementOfClosedPoints s hs ⊔ (W ⊓ complementOfOtherClosedPoints s hs i) =
      complementOfOtherClosedPoints s hs i := by
  refine le_antisymm (sup_le
    (complementOfClosedPoints_le_complementOfOtherClosedPoints s hs i) inf_le_right)
    fun x hx ↦ ?_
  by_cases hxi : x = s i
  · exact Or.inr ⟨hxi ▸ hiW, hx⟩
  · refine Or.inl (Set.mem_iInter.mpr fun j ↦ ?_)
    by_cases hji : j = i
    · exact fun (hmem : _ ∈ ({s j} : Set S)) ↦ hxi (hji ▸ hmem)
    · exact Set.mem_iInter.mp hx ⟨j, hji⟩

end Punctured

end AlgebraicGeometry

end
