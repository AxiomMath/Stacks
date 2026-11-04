module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Topology.NowhereDense.Local
public import StacksCore.Topology.NowhereDense.OpenMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.FiniteCover
public import StacksFrontier.Topology.NowhereDense.FiniteUnion

/-!
# Images of nowhere dense subsets under finite morphisms

A finite morphism of schemes carries closed nowhere dense subsets of its source to closed
nowhere dense subsets of its target. Closedness of the image is automatic, a finite morphism
being universally closed; the content is nowhere denseness.

The argument is local on the target, so one may assume the target affine. There a finite
morphism becomes, after a surjective finite locally free base change, a closed subscheme of a
scheme which is set-theoretically covered by finitely many closed sections of a finite locally
free morphism to the new base. Both base change and descent of nowhere denseness are available
because a finite locally free morphism is open and, in the chosen cover, surjective. What
remains is a statement about topological spaces: if a continuous map admits finitely many
closed continuous sections whose images cover the source, then it carries closed nowhere dense
subsets to nowhere dense subsets.

## Main results

* `Stacks.Morphisms.isNowhereDense_image_of_isFinite`: the image of a closed nowhere dense
  subset under a finite morphism of schemes is nowhere dense.
* `Stacks.Morphisms.isClosedNowhereDense_image_of_isFinite`: the same image is closed nowhere
  dense, which is the two assertions together.

## Implementation notes

The purely topological step is the private lemma
`Stacks.Morphisms.isNowhereDense_image_of_closed_sections`. Given a nonempty open subset of a
section's preimage of `T`, one shrinks it so that each of the finitely many sections either
has its image meeting it everywhere or nowhere; over such a subset the chosen section's image
is open, lies inside `T`, and is nonempty, contradicting nowhere denseness of `T`.

Closedness of the image is `AlgebraicGeometry.Scheme.Hom.isClosedMap`, available because a
finite morphism is integral and hence universally closed.

## References

* [Stacks Project, Tag 03HX](https://stacks.math.columbia.edu/tag/03HX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Morphisms

/-- A continuous map with finitely many closed continuous sections whose images cover its
source carries closed nowhere dense subsets to nowhere dense subsets. -/
private theorem isNowhereDense_image_of_closed_sections
    {Y X : Type u} [TopologicalSpace Y] [TopologicalSpace X]
    (f : Y → X) (hf : Continuous f) {n : ℕ} (s : Fin n → X → Y)
    (hs_cont : ∀ i, Continuous (s i)) (hfs : ∀ i x, f (s i x) = x)
    (hs_closed : ∀ i, IsClosed (Set.range (s i)))
    (hs_cover : ∀ y, ∃ i x, s i x = y)
    {T : Set Y} (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsNowhereDense (f '' T) := by
  classical
  by_contra hnot
  have himage_eq : f '' T = ⋃ i, s i ⁻¹' T := by
    ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, hyT, rfl⟩
      obtain ⟨i, z, rfl⟩ := hs_cover y
      exact Set.mem_iUnion.2 ⟨i, by rw [hfs]; exact hyT⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact ⟨s i x, hi, hfs i x⟩
  -- Some section's preimage of `T` fails to be nowhere dense.
  obtain ⟨i, hi⟩ : ∃ i : Fin n, ¬ IsNowhereDense (s i ⁻¹' T) := by
    by_contra h
    simp only [not_exists, not_not] at h
    refine hnot ?_
    rw [himage_eq, show (⋃ i, s i ⁻¹' T) = ⋃ i ∈ Finset.univ, s i ⁻¹' T by simp]
    exact isNowhereDense_finite_union _ _ fun j _ ↦ h j
  set V₀ := interior (s i ⁻¹' T) with hV₀
  have hV₀_nonempty : V₀.Nonempty := Set.nonempty_iff_ne_empty.mpr fun he ↦
    hi ((hT_closed.preimage (hs_cont i)).isNowhereDense_iff.mpr he)
  -- The locus in the base where the `i`-th section meets the `j`-th one.
  set R : Fin n → Set X := fun j ↦ s i ⁻¹' Set.range (s j) with hR
  have hR_closed (j : Fin n) : IsClosed (R j) := (hs_closed j).preimage (hs_cont i)
  -- Shrink `V₀` so that each `R j` either contains it or misses it.
  have shrink : ∀ t : Finset (Fin n), ∃ V : Set X,
      IsOpen V ∧ V.Nonempty ∧ V ⊆ V₀ ∧ ∀ j ∈ t, V ⊆ R j ∨ Disjoint V (R j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨V₀, isOpen_interior, hV₀_nonempty, fun _ h ↦ h, by simp⟩
    | @insert j t hj ih =>
      obtain ⟨V, hVo, hVn, hVs, hstatus⟩ := ih
      by_cases hVR : V ⊆ R j
      · refine ⟨V, hVo, hVn, hVs, fun k hk ↦ ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hkt
        · exact .inl hVR
        · exact hstatus k hkt
      · obtain ⟨x, hxV, hxR⟩ := Set.not_subset.mp hVR
        refine ⟨V \ R j, hVo.sdiff (hR_closed j), ⟨x, hxV, hxR⟩,
          Set.sdiff_subset.trans hVs, fun k hk ↦ ?_⟩
        rcases Finset.mem_insert.mp hk with rfl | hkt
        · exact .inr (Set.disjoint_left.2 fun y hyV hyR ↦ hyV.2 hyR)
        · rcases hstatus k hkt with hsub | hdis
          · exact .inl fun y hy ↦ hsub hy.1
          · exact .inr (Set.disjoint_left.2 fun y hyV hyR ↦
              Set.disjoint_left.mp hdis hyV.1 hyR)
  obtain ⟨V, hVo, hVn, hVsub, hstatus⟩ := shrink Finset.univ
  have hV_in : V ⊆ s i ⁻¹' T := hVsub.trans interior_subset
  -- Over `V` the image of the `i`-th section is the part of `f ⁻¹' V` missing the sections
  -- that `V` avoids, hence open.
  set C : Set Y := ⋃ j : {j : Fin n // ¬ V ⊆ R j}, Set.range (s j.1) with hC
  have hC_closed : IsClosed C := isClosed_iUnion_of_finite fun j ↦ hs_closed j.1
  have hWO : s i '' V = f ⁻¹' V \ C := by
    ext y
    constructor
    · rintro ⟨x, hxV, rfl⟩
      refine ⟨by simpa [hfs] using hxV, fun hyC ↦ ?_⟩
      obtain ⟨j, z, hzy⟩ := Set.mem_iUnion.1 hyC
      have hz : z = x := by simpa only [hfs] using congrArg f hzy
      subst z
      rcases hstatus j.1 (Finset.mem_univ j.1) with hsub | hdis
      · exact j.property hsub
      · exact Set.disjoint_left.mp hdis hxV ⟨x, hzy⟩
    · rintro ⟨hyO, hyC⟩
      obtain ⟨j, x, hxy⟩ := hs_cover y
      have heq : x = f y := by simpa only [hfs] using congrArg f hxy
      have hxV : x ∈ V := by rw [heq]; exact hyO
      have hjgood : V ⊆ R j := by
        by_contra hjbad
        exact hyC (Set.mem_iUnion.2 ⟨⟨j, hjbad⟩, ⟨x, hxy⟩⟩)
      obtain ⟨z, hzs⟩ := hjgood hxV
      have hz : z = x := by simpa only [hfs] using congrArg f hzs
      subst z
      exact ⟨x, hxV, hzs.symm.trans hxy⟩
  have hW_open : IsOpen (s i '' V) := hWO ▸ (hVo.preimage hf).sdiff hC_closed
  obtain ⟨x, hx⟩ := hVn
  have hW_nonempty : (s i '' V).Nonempty := ⟨s i x, x, hx, rfl⟩
  have hW_int : s i '' V ⊆ interior (closure T) :=
    interior_maximal (Set.image_subset_iff.2 hV_in |>.trans subset_closure) hW_open
  rw [(isNowhereDense_iff_interior_closure_eq_empty T).mp hT] at hW_int
  exact hW_nonempty.ne_empty (Set.subset_empty_iff.mp hW_int)

/-- The image of a closed nowhere dense subset under a finite morphism to an affine scheme is
nowhere dense. -/
private theorem isNowhereDense_image_of_isFinite_of_isAffine
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [IsAffine X]
    {T : Set Y} (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) := by
  classical
  obtain ⟨X', g, hg_surjective, hg_flf, _, ha_flf, Z', p, i,
      hi_closed, hip, hp_flf, m, s, hs, hs_cover⟩ :=
    exists_finiteLocallyFree_cover_closedImmersion f
  set a := pullback.fst f g with ha
  set b := pullback.snd f g with hb
  obtain ⟨hT'_closed, hT'⟩ :=
    isClosedNowhereDense_preimage_of_isOpenMap a.base a.continuous
      (IsFiniteLocallyFree.isOpenMap a) T hT_closed hT
  have : IsFinite p := IsFiniteLocallyFree.isFinite p
  have hsections_base (j : Fin m) (x : X') : p.base ((s j).base x) = x := by
    simpa using congrArg (fun q : X' ⟶ X' ↦ q.base x) (hs j).2
  have hsections_closed (j : Fin m) : IsClosed (Set.range (s j).base) := by
    have : IsClosedImmersion (s j) := (hs j).1
    exact (s j).isClosedEmbedding.isClosed_range
  have hTiImage : IsNowhereDense (p.base '' (i.base '' (a.base ⁻¹' T))) :=
    isNowhereDense_image_of_closed_sections p.base p.continuous
      (fun j ↦ (s j).base) (fun j ↦ (s j).continuous) hsections_base hsections_closed hs_cover
      (i.isClosedEmbedding.isClosedMap _ hT'_closed)
      (i.isClosedEmbedding.isInducing.isNowhereDense_image hT')
  have hImageEq : p.base '' (i.base '' (a.base ⁻¹' T)) = g.base ⁻¹' (f.base '' T) := by
    calc p.base '' (i.base '' (a.base ⁻¹' T)) = (i ≫ p).base '' (a.base ⁻¹' T) := by
          rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base]
      _ = b.base '' (a.base ⁻¹' T) := by rw [hip]
      _ = g.base ⁻¹' (f.base '' T) :=
          Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f g) T
  exact ((isClosedNowhereDense_preimage_iff_of_surjective_isOpenMap g.base g.continuous
    (IsFiniteLocallyFree.isOpenMap g) hg_surjective.surj (f.base '' T)).mpr
      ⟨(f.isClosedMap _ hT_closed).preimage g.continuous, hImageEq ▸ hTiImage⟩).2

/-- **Stacks Project, Tag 03HX.** The image of a closed nowhere dense subset under a finite
morphism of schemes is nowhere dense. -/
@[stacks 03HX "nowhere denseness of the image"]
theorem isNowhereDense_image_of_isFinite {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {T : Set Y} (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) := by
  classical
  refine nowhere_dense_local (fun i : X.affineCover.I₀ ↦ Set.range (X.affineCover.f i).base)
    (fun i ↦ (X.affineCover.f i).isOpenEmbedding.isOpen_range) X.affineCover.iUnion_range
    (f.base '' T) fun i ↦ ?_
  set g := X.affineCover.f i with hg
  set a := pullback.fst f g with ha
  set b := pullback.snd f g with hb
  obtain ⟨hT'_closed, hT'⟩ :=
    isClosedNowhereDense_preimage_of_isOpenMap a.base a.continuous
      a.isOpenEmbedding.isOpenMap T hT_closed hT
  have hEq : b.base '' (a.base ⁻¹' T) = g.base ⁻¹' (f.base '' T) :=
    Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f g) T
  have hLocalImage : IsNowhereDense (g.base ⁻¹' (f.base '' T)) := by
    rw [← hEq]; exact isNowhereDense_image_of_isFinite_of_isAffine b hT'_closed hT'
  set e : X.affineCover.X i ≃ₜ Set.range g.base :=
    g.isOpenEmbedding.isEmbedding.toHomeomorph with he
  have heq : e '' (g.base ⁻¹' (f.base '' T)) =
      (Subtype.val : Set.range g.base → X) ⁻¹' (f.base '' T) := by
    ext z
    refine ⟨?_, fun hz ↦ ⟨e.symm z, ?_, e.apply_symm_apply z⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · have hval : g.base (e.symm z) = z.1 := congrArg Subtype.val (e.apply_symm_apply z)
      change g.base (e.symm z) ∈ f.base '' T
      rw [hval]
      exact hz
  rw [← heq]
  exact e.isInducing.isNowhereDense_image hLocalImage

add_to_stacks 03HX "closedness of the image" AlgebraicGeometry.Scheme.Hom.isClosedMap

/-- **Stacks Project, Tag 03HX.** The image of a closed nowhere dense subset under a finite
morphism of schemes is closed and nowhere dense. -/
theorem isClosedNowhereDense_image_of_isFinite {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {T : Set Y} (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsClosed (f.base '' T) ∧ IsNowhereDense (f.base '' T) :=
  ⟨f.isClosedMap _ hT_closed, isNowhereDense_image_of_isFinite f hT_closed hT⟩

end Stacks.Morphisms

end
