module

public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FiniteGroupoidThickening
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FittingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible

/-!
# The invariant thickening of a finite groupoid of finite presentation

Let `G` be a groupoid scheme whose source and target maps are finite, and assume in addition
that the source map is of finite presentation. Then every member of the Fitting stratification
is a closed immersion of finite presentation, and therefore

* the inclusion of the invariant closed thickening into the invariant open constructed for a
  finite groupoid is itself of finite presentation, because on each stage it is cut out of a
  chosen open by one member of the stratification; and
* every point whose orbit consists of generic points of irreducible components of the object
  scheme lies in that invariant open.

## Main results

* `AlgebraicGeometry.finitePresentation_layerThickeningInclusion`: part (1).
* `AlgebraicGeometry.mem_layerUnionOpen_of_orbit_subset_genericPoints`: part (2).

## Implementation notes

The invariant open and its thickening are the ones constructed in
`AlgebraicGeometry.layerUnionOpen` and `AlgebraicGeometry.layerThickening`; the source's
statement refers to the subschemes produced in the proof of the preceding lemma, so the two
assertions are stated about those and not about an abstract pair with the same properties.

For part (2) the supports of the members of the stratification are locally constructible,
because the corresponding closed immersions are quasi-compact and locally of finite
presentation. The orbit of the given point lies in one difference of two consecutive supports;
local constructibility then produces an open neighbourhood of each orbit point inside that
difference, which forces the point to lie in the open chosen at the corresponding stage.

## References

* [Stacks Project, Tag 0ABB](https://stacks.math.columbia.edu/tag/0ABB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms Topology

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0ABB (1).** For a groupoid scheme with finite source and target whose
source map is of finite presentation, the inclusion of the invariant closed thickening into the
invariant open is of finite presentation: on each stage it is the base change of one member of
the Fitting stratification along the inclusion of the open chosen there. -/
@[stacks 0ABB "finite_presentation"]
theorem finitePresentation_layerThickeningInclusion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left) :
    FinitePresentation (layerThickeningInclusion G) := by
  have hcomp (n : ULift.{u} ℕ) :
      LocallyOfFinitePresentation (layerFittingProj G n ≫ layerPieceToUnion G n.down) := by
    have hstratum : LocallyOfFinitePresentation (finiteStratification G n.down).subschemeι :=
      (finitePresentation_finiteStratification_subschemeι G hs n.down).1
    have hproj : LocallyOfFinitePresentation (layerFittingProj G n) := inferInstance
    infer_instance
  have hlfp : LocallyOfFinitePresentation (layerThickeningInclusion G) := by
    have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    rw [layerThickeningInclusion_eq_sigmaDesc]
    exact IsZariskiLocalAtSource.sigmaDesc hcomp
  exact FinitePresentation.mk hlfp inferInstance inferInstance

/-- The support of a member of the Fitting stratification is locally constructible, because the
closed immersion cutting it out is quasi-compact and locally of finite presentation. -/
theorem isLocallyConstructible_support_finiteStratification {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left) (n : ℕ) :
    IsLocallyConstructible
      ((finiteStratification G n).support : Set G.objects.left) := by
  have hfp := finitePresentation_finiteStratification_subschemeι G hs n
  have h₁ : LocallyOfFinitePresentation (finiteStratification G n).subschemeι := hfp.1
  have h₂ : QuasiCompact (finiteStratification G n).subschemeι := hfp.2.1
  simpa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] using
    (finiteStratification G n).subschemeι.isLocallyConstructible_image
      IsLocallyConstructible.univ

/-- A point of the open chosen at an earlier stage avoids every later member of the Fitting
stratification. -/
theorem notMem_support_finiteStratification_of_mem_layerPiece {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left]
    {j k : ℕ} (hjk : j < k) {z : G.objects.left}
    (hz : z ∈ (layerPiece G j : Set G.objects.left)) :
    z ∉ (finiteStratification G k).support := fun hzk ↦
  (layerPiece_subset_stratum G j hz).2
    (support_finiteStratification_antitone G (Nat.succ_le_of_lt hjk) hzk)

/-- Between a stage whose stratification member contains a point and one that does not, there is
a stage where the point enters and leaves. -/
theorem exists_mem_support_notMem_support_succ {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (x : G.objects.left) (n : ℕ)
    (hzero : x ∈ (finiteStratification G 0).support)
    (hn : x ∉ (finiteStratification G n).support) :
    ∃ k, x ∈ (finiteStratification G k).support ∧
      x ∉ (finiteStratification G (k + 1)).support := by
  induction n with
  | zero => exact absurd hzero hn
  | succ n ih =>
      by_cases hxn : x ∈ (finiteStratification G n).support
      · exact ⟨n, hxn, hn⟩
      · exact ih hxn

/-- **Stacks Project, Tag 0ABB (2).** For a groupoid scheme with finite source and target whose
source map is of finite presentation, a point whose orbit consists of generic points of
irreducible components of the object scheme lies in the invariant open constructed for the
groupoid. -/
@[stacks 0ABB "generic_orbit_mem"]
theorem mem_layerUnionOpen_of_orbit_subset_genericPoints {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left]
    (hs : FinitePresentation G.source.left) (x : G.objects.left)
    (hx : ∀ y : G.objects.left,
      (∃ r : G.arrows.left, G.source.left r = x ∧ G.target.left r = y) →
        y ∈ genericPoints G.objects.left) :
    x ∈ layerUnionOpen G := by
  obtain ⟨n, hn⟩ := finiteStratification_exhaustive G x
  have hzero : x ∈ (finiteStratification G 0).support := by
    rw [finiteStratification_zero]
    trivial
  obtain ⟨k, hxk, hxk'⟩ := exists_mem_support_notMem_support_succ G x n hzero hn
  have hlayer (y : G.objects.left) (r : G.arrows.left)
      (hr : G.source.left.base r = x ∧ G.target.left.base r = y) :
      y ∈ (finiteStratification G k).support ∧
        y ∉ (finiteStratification G (k + 1)).support := by
    have hmem₁ := (mem_support_finiteStratification_iff G k r).1 (hr.1 ▸ hxk)
    have hsrcNot : G.source.left.base r ∉ (finiteStratification G (k + 1)).support := by
      simpa [hr.1] using hxk'
    exact ⟨hr.2 ▸ hmem₁, hr.2 ▸ fun htgt ↦
      hsrcNot ((mem_support_finiteStratification_iff G (k + 1) r).2 htgt)⟩
  have hxopen : x ∈ (layerUnionOpen G : Set G.objects.left) := by
    rw [layerUnionOpen_coe]
    by_cases hk : k = 0
    · subst k
      refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      rw [layerPiece_eq_zero]
      simpa using hxk'
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      have hkidx : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
      have hkidx2 : k - 1 + 2 = k + 1 := by omega
      have hp : x ∈ (layerPiece G (k - 1 + 1) : Set G.objects.left) := by
        rw [layerPiece_eq_succ' G (k - 1), hkidx, hkidx2]
        refine ⟨hxk, hxk', ?_⟩
        rintro ⟨r, hrA, htx⟩
        have hrtarget : G.target.left.base r = x := by simpa using htx
        have hinvsrc : G.source.left.base (G.inverse.left r) = x := by
          simpa [hrtarget] using
            congrArg (fun f : G.arrows ⟶ G.objects ↦ f.left.base r) G.source_inverse
        have hinvtgt :
            G.target.left.base (G.inverse.left r) = G.source.left.base r := by
          simpa using
            congrArg (fun f : G.arrows ⟶ G.objects ↦ f.left.base r) G.target_inverse
        have hzgeneric : G.source.left.base r ∈ genericPoints G.objects.left :=
          hx _ ⟨G.inverse.left r, hinvsrc, hinvtgt⟩
        have hzk : G.source.left.base r ∈ (finiteStratification G k).support :=
          (hlayer _ (G.inverse.left r) ⟨hinvsrc, hinvtgt⟩).1
        obtain ⟨V, hVsub, hVopen, hzV⟩ := mem_nhds_iff.mp
          (mem_nhds_of_isLocallyConstructible_of_mem_genericPoints
            (isLocallyConstructible_support_finiteStratification G hs k) hzgeneric hzk)
        have hVdisj : ∀ w ∈ V,
            w ∉ ⋃ r ∈ Set.Iic (k - 1), closure (layerPiece G r : Set G.objects.left) := by
          intro w hwV hwA
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hwA
          obtain ⟨hjle, hwcl⟩ := Set.mem_iUnion.mp hj
          have hjk : j < k :=
            lt_of_le_of_lt (by simpa using hjle) (Nat.sub_lt hkpos Nat.one_pos)
          rw [mem_closure_iff] at hwcl
          obtain ⟨b, hbV, hbPiece⟩ := hwcl V hVopen hwV
          exact notMem_support_finiteStratification_of_mem_layerPiece G hjk hbPiece
            (hVsub hbV)
        refine absurd hrA (fun hzA ↦ ?_)
        have hnotcl : G.source.left.base r ∉
            closure (⋃ r ∈ Set.Iic (k - 1),
              closure (layerPiece G r : Set G.objects.left)) := by
          intro hzcl
          rw [mem_closure_iff] at hzcl
          obtain ⟨w, hwV, hwA⟩ := hzcl V hVopen hzV
          exact hVdisj w hwV hwA
        exact hnotcl (subset_closure hzA)
      simpa [hkidx] using hp
  exact hxopen

end AlgebraicGeometry

end
