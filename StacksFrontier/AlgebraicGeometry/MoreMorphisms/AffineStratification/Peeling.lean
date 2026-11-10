module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Peeling and re-attaching the top stratum of an affine stratification

Two moves on affine stratifications, and the affineness criterion that both rely on.

The first move restricts an affine stratification indexed by `Fin (m + 2)` to a closed subscheme
whose underlying space misses the top stratum: the strata below the top one, pulled back, form an
affine stratification of that subscheme indexed by `Fin (m + 1)`. The second move is the inverse:
an affine open `U` with affine inclusion, together with an affine stratification indexed by
`Fin (m + 1)` of a closed subscheme carrying the complement of `U`, assemble into an affine
stratification of the ambient scheme indexed by `Fin (m + 2)` whose top stratum is `U`.

## Main results

* `AlgebraicGeometry.isAffineOfSurjectiveImmersion`: a scheme admitting a surjective immersion
  from an affine scheme is affine, which is [Stacks, Tag 06AD].
* `AlgebraicGeometry.AffineStratification.nonempty_subscheme`: the restriction of a
  stratification to a closed subscheme missing the top stratum.
* `AlgebraicGeometry.AffineStratification.nonempty_of_isAffineOpen_compl`: the assembly of a
  stratification from an affine open and a stratified closed complement.

## Implementation notes

[Stacks, Tag 06AD] is obtained from `Stacks.Thickenings.isAffine_of_isThickening`: a surjective
immersion is a surjective closed immersion, that is a thickening, and a thickening of an affine
scheme is affine.

In `AffineStratification.nonempty_subscheme` the closed subscheme is presented by an ideal sheaf
rather than by an abstract closed immersion, because the affineness of a stratum is checked by
lifting a reduced affine scheme through it, and the lifting criterion
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support` is
stated for the inclusion of the subscheme cut out by an ideal sheaf. The reduced affine scheme
in question is the part of a stratum lying over the subscheme, cut out of the reduced induced
scheme on that stratum by the vanishing ideal of the preimage of the support.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S)
* [Stacks Project, Tag 0F2Y](https://stacks.math.columbia.edu/tag/0F2Y)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-! ### Affineness of a scheme with a surjective immersion from an affine scheme -/

/-- **[Stacks, Tag 06AD].** A scheme admitting a surjective immersion from an affine scheme is
affine: a surjective immersion has closed image, hence is a surjective closed immersion, that is
a thickening, and a thickening of an affine scheme is affine. -/
theorem isAffineOfSurjectiveImmersion : IsAffineOfSurjectiveImmersion.{u} := by
  intro Y Z g hg hrange hZ
  have : IsImmersion g := hg
  have : IsAffine Z := hZ
  have hclosed : IsClosed (Set.range g.base) := hrange ▸ isClosed_univ
  exact Stacks.Thickenings.isAffine_of_isThickening
    ⟨IsClosedImmersion.of_isPreimmersion g hclosed, Set.range_eq_univ.mp hrange⟩

/-! ### Restricting a stratification to a closed subscheme missing the top stratum -/

/-- A closed subset `D` of an affine scheme `W` is the image of an affine scheme mapping to `Z`
by an affine immersion, whenever `W` does so. -/
private theorem exists_affine_immersion_range_eq_image {W Z : Scheme.{u}} [IsAffine W]
    (p : W ⟶ Z) [IsImmersion p] [IsAffineHom p] (D : Closeds W) :
    ∃ (A : Scheme.{u}) (_ : IsAffine A) (_ : IsReduced A) (q : A ⟶ Z),
      IsImmersion q ∧ IsAffineHom q ∧ Set.range q = p '' (D : Set W) := by
  have := isAffine_of_isAffineHom (Scheme.IdealSheafData.vanishingIdeal D).subschemeι
  refine ⟨_, this, inferInstance, (Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫ p,
    inferInstance, inferInstance, ?_⟩
  change Set.range (p.base ∘ (Scheme.IdealSheafData.vanishingIdeal D).subschemeι.base) = _
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]

/-- **Peeling off the top stratum, for an arbitrary closed subscheme.** Let `s` be an affine
stratification of `X` indexed by `Fin (m + 2)` and let `I` be an ideal sheaf whose support misses
the top stratum of `s`. Then the preimages of the strata below the top one form an affine
stratification, indexed by `Fin (m + 1)`, of the closed subscheme cut out by `I`. -/
theorem AffineStratification.nonempty_subscheme {X : Scheme.{u}} {m : ℕ}
    (s : AffineStratification X (Fin (m + 2))) (I : X.IdealSheafData)
    (hI : (I.support : Set X) ⊆ (s.strata (Fin.last (m + 1)))ᶜ) :
    Nonempty (AffineStratification I.subscheme (Fin (m + 1))) := by
  classical
  have hpart := s.isLocallyFiniteStratification.isStratification.isPartition
  set g := I.subschemeι with hgdef
  have hginj : Function.Injective g.base := g.isClosedEmbedding.injective
  have hgrange : Set.range g = (I.support : Set X) := I.range_subschemeι
  set T : Fin (m + 1) → Set I.subscheme := fun i => g ⁻¹' s.strata i.castSucc with hTdef
  have hlc : ∀ A : Set X, IsLocallyClosed A → IsLocallyClosed (g ⁻¹' A) := by
    intro A hA
    obtain ⟨O, C, hO, hC, rfl⟩ := hA
    exact ⟨g ⁻¹' O, g ⁻¹' C, hO.preimage g.continuous, hC.preimage g.continuous,
      Set.preimage_inter⟩
  have hcover : (⋃ i, T i) = Set.univ := by
    rw [hTdef, ← Set.preimage_iUnion, Set.preimage_eq_univ_iff, hgrange]
    refine hI.trans fun x hx => ?_
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hpart.cover ▸ Set.mem_univ x)
    have hjne : j ≠ Fin.last (m + 1) := fun h => hx (h ▸ hxj)
    exact Set.mem_iUnion.mpr ⟨j.castPred hjne, by rwa [Fin.castSucc_castPred]⟩
  have hlf : IsLocallyFiniteStratification T := by
    refine ⟨⟨⟨fun i => hlc _ (hpart.locallyClosed i.castSucc), fun i j hij => ?_, hcover⟩,
      fun i => ?_⟩, locallyFinite_of_finite _⟩
    · exact (hpart.disjoint i.castSucc j.castSucc
        fun hc => hij (Fin.castSucc_injective _ hc)).preimage _
    · intro y hy
      have h1 : g y ∈ closure (s.strata i.castSucc) :=
        g.continuous.closure_preimage_subset (s.strata i.castSucc) hy
      have h2 := s.isLocallyFiniteStratification.isStratification.closure_subset i.castSucc h1
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h2 ⊢
      obtain ⟨j, hji, hgj⟩ := h2
      have hjne : j ≠ Fin.last (m + 1) := by
        rw [Fin.le_def] at hji
        simp only [Fin.val_castSucc] at hji
        have := i.isLt
        rw [ne_eq, Fin.ext_iff]
        simp only [Fin.val_last]
        omega
      refine ⟨j.castPred hjne, ?_, ?_⟩
      · rw [Fin.le_def] at hji ⊢
        simpa only [Fin.val_castSucc, Fin.coe_castPred] using hji
      · change g y ∈ s.strata ((j.castPred hjne).castSucc)
        rw [Fin.castSucc_castPred]
        exact hgj
  have hAff : ∀ i : Fin (m + 1),
      IsAffine (reducedInducedScheme (T i) (hlf.isStratification.isPartition.locallyClosed i)) ∧
        IsAffineHom
          (reducedInducedInclusion (T i) (hlf.isStratification.isPartition.locallyClosed i)) := by
    intro i
    have hTX := hpart.locallyClosed i.castSucc
    have : IsAffine (reducedInducedScheme (s.strata i.castSucc) hTX) := s.isAffine i.castSucc
    have : IsAffineHom (reducedInducedInclusion (s.strata i.castSucc) hTX) :=
      s.isAffineHom i.castSucc
    obtain ⟨J, hJ, hJr, f, hfi, hfa, hfr⟩ := exists_affine_immersion_range_eq_image
      (reducedInducedInclusion (s.strata i.castSucc) hTX) ⊤
    have hfrange : Set.range f = s.strata i.castSucc := by
      rw [hfr]
      simpa using range_reducedInducedInclusion (s.strata i.castSucc) hTX
    obtain ⟨K, hK, hKr, f', hfi', hfa', hf'r⟩ := exists_affine_immersion_range_eq_image f
      ⟨f ⁻¹' (I.support : Set X), I.support.2.preimage f.continuous⟩
    have hf'range : Set.range f' = (I.support : Set X) ∩ s.strata i.castSucc := by
      rw [hf'r]
      change f '' (f ⁻¹' (I.support : Set X)) = _
      rw [Set.image_preimage_eq_inter_range, hfrange]
    obtain ⟨h, hh⟩ :=
      (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support I f').2
        (by rw [hf'range]; exact Set.inter_subset_left)
    have hcomp : ∀ z, g (h z) = f' z := fun z => by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun k => k z) hh
    have : IsImmersion (h ≫ g) := by rw [hgdef, hh]; infer_instance
    have : IsImmersion h := IsImmersion.of_comp h g
    have : IsAffineHom h := by
      refine isAffineHom_of_forall_exists_isAffineOpen h fun y => ?_
      obtain ⟨-, ⟨V, hV, rfl⟩, hyV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g y)) isOpen_univ
      refine ⟨g ⁻¹ᵁ (V : X.Opens), hyV, hV.preimage g, ?_⟩
      have hpre : h ⁻¹ᵁ (g ⁻¹ᵁ (V : X.Opens)) = f' ⁻¹ᵁ (V : X.Opens) := by
        rw [← Scheme.Hom.comp_preimage, hgdef, hh]
      rw [hpre]
      exact hV.preimage f'
    have hhrange : Set.range h = T i := by
      refine Set.eq_of_subset_of_subset ?_ ?_
      · rintro y ⟨z, rfl⟩
        change g (h z) ∈ s.strata i.castSucc
        rw [hcomp z]
        exact (hf'range.le ⟨z, rfl⟩).2
      · intro y hy
        obtain ⟨z, hz⟩ := hf'range.ge ⟨hgrange.le ⟨y, rfl⟩, hy⟩
        exact ⟨z, hginj (by rw [hcomp z, hz])⟩
    exact isAffine_reducedInduced_of_range_eq (T i)
      (hlf.isStratification.isPartition.locallyClosed i) h hhrange
  exact ⟨{ strata := T
           isLocallyFiniteStratification := hlf
           isAffine := fun i => (hAff i).1
           isAffineHom := fun i => (hAff i).2 }⟩

/-! ### Attaching an affine open on top of a stratified closed complement -/

/-- **Re-attaching the top stratum.** Let `U` be an affine open of `Y` whose inclusion is an
affine morphism, and let `j : V ⟶ Y` be a closed immersion with image the complement of `U`. An
affine stratification of `V` indexed by `Fin (m + 1)` extends, by adjoining `U` as the top
stratum, to an affine stratification of `Y` indexed by `Fin (m + 2)`. -/
theorem AffineStratification.nonempty_of_isAffineOpen_compl {Y : Scheme.{u}} {m : ℕ}
    (U : Y.Opens) (hU : IsAffineOpen U) [IsAffineHom U.ι] {V : Scheme.{u}} (j : V ⟶ Y)
    [IsClosedImmersion j] (hj : Set.range j = (U : Set Y)ᶜ)
    (t : AffineStratification V (Fin (m + 1))) :
    Nonempty (AffineStratification Y (Fin (m + 2))) := by
  classical
  have hpart := t.isLocallyFiniteStratification.isStratification.isPartition
  have hjinj : Function.Injective j.base := j.isClosedEmbedding.injective
  have hlcV : ∀ i, IsLocallyClosed (t.strata i) := hpart.locallyClosed
  set f : ∀ i : Fin (m + 1), reducedInducedScheme (t.strata i) (hlcV i) ⟶ Y :=
    fun i => reducedInducedInclusion (t.strata i) (hlcV i) ≫ j with hfdef
  have hfincl : ∀ i, IsImmersion (reducedInducedInclusion (t.strata i) (hlcV i)) := by
    intro i
    unfold reducedInducedInclusion
    infer_instance
  have hfimm : ∀ i, IsImmersion (f i) := by
    intro i
    have := hfincl i
    exact inferInstance
  have hfaff : ∀ i, IsAffineHom (f i) := by
    intro i
    have := t.isAffineHom i
    exact inferInstance
  have hfrange : ∀ i, Set.range (f i) = j '' t.strata i := by
    intro i
    change Set.range (j.base ∘ (reducedInducedInclusion (t.strata i) (hlcV i)).base) = _
    rw [Set.range_comp, range_reducedInducedInclusion]
  set strata : Fin (m + 2) → Set Y :=
    Fin.snoc (fun i : Fin (m + 1) => j '' t.strata i) (U : Set Y) with hstratadef
  have hlast : strata (Fin.last (m + 1)) = (U : Set Y) := Fin.snoc_last _ _
  have hcast : ∀ k : Fin (m + 1), strata k.castSucc = j '' t.strata k :=
    fun k => Fin.snoc_castSucc _ _ k
  have hcompl : ∀ k : Fin (m + 1), j '' t.strata k ⊆ (U : Set Y)ᶜ := by
    rintro k x ⟨y, -, rfl⟩
    exact hj.le ⟨y, rfl⟩
  have hlc : ∀ i : Fin (m + 2), IsLocallyClosed (strata i) := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · have := hfimm k
      rw [hcast k, ← hfrange k]
      exact (f k).isLocallyClosed_range
    · rw [hlast]
      exact U.isOpen.isLocallyClosed
  have hdisj : ∀ i i' : Fin (m + 2), i ≠ i' → Disjoint (strata i) (strata i') := by
    intro i i' hii'
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last i' with ⟨k', rfl⟩ | rfl
    · rw [hcast k, hcast k']
      refine Set.disjoint_left.mpr ?_
      rintro x ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
      have hkk' : k ≠ k' := fun hc => hii' (by rw [hc])
      exact (hpart.disjoint k' k hkk'.symm).le_bot ⟨hy', hjinj hyy' ▸ hy⟩
    · rw [hcast k, hlast]
      exact Set.disjoint_left.mpr fun x hx hx' => (hcompl k hx) hx'
    · rw [hlast, hcast k']
      exact Set.disjoint_left.mpr fun x hx hx' => (hcompl k' hx') hx
    · exact absurd rfl hii'
  have hcover : (⋃ i, strata i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hxU : x ∈ (U : Set Y)
    · exact Set.mem_iUnion.mpr ⟨Fin.last (m + 1), by rw [hlast]; exact hxU⟩
    · obtain ⟨y, hy⟩ := hj.ge hxU
      obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp (hpart.cover ▸ Set.mem_univ y)
      exact Set.mem_iUnion.mpr ⟨k.castSucc, by rw [hcast k]; exact ⟨y, hyk, hy⟩⟩
  have hclosure : ∀ i : Fin (m + 2), closure (strata i) ⊆ ⋃ k ∈ {k | k ≤ i}, strata k := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · rw [hcast k]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := j.isClosedEmbedding.isClosedMap.closure_image_subset _ hx
      have h2 := t.isLocallyFiniteStratification.isStratification.closure_subset k hy
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h2 ⊢
      obtain ⟨l, hlk, hyl⟩ := h2
      exact ⟨l.castSucc, Fin.castSucc_le_castSucc_iff.mpr hlk,
        by rw [hcast l]; exact ⟨y, hyl, rfl⟩⟩
    · intro x _
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨k, Fin.le_last k, hxk⟩
  have hlf : IsLocallyFiniteStratification strata :=
    ⟨⟨⟨hlc, hdisj, hcover⟩, hclosure⟩, locallyFinite_of_finite _⟩
  have hAff : ∀ i : Fin (m + 2),
      IsAffine (reducedInducedScheme (strata i)
          (hlf.isStratification.isPartition.locallyClosed i)) ∧
        IsAffineHom (reducedInducedInclusion (strata i)
          (hlf.isStratification.isPartition.locallyClosed i)) := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · have := t.isAffine k
      have := hfimm k
      have := hfaff k
      exact isAffine_reducedInduced_of_range_eq _ _ (f k) (by rw [hcast k]; exact hfrange k)
    · have : IsAffine U.toScheme := hU
      obtain ⟨A, hA, hAr, q, hqi, hqa, hqr⟩ := exists_affine_immersion_range_eq_image U.ι ⊤
      exact isAffine_reducedInduced_of_range_eq _ _ q (by rw [hqr, hlast]; simp)
  exact ⟨{ strata := strata
           isLocallyFiniteStratification := hlf
           isAffine := fun i => (hAff i).1
           isAffineHom := fun i => (hAff i).2 }⟩

end AlgebraicGeometry

end
