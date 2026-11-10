module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedPrimes

/-!
# The `ℤ`-graded primes of `A[1/f]` and the standard open `D₊(f)`

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a nonnegatively graded ring and `f ∈ 𝒜 d` homogeneous of positive
degree. Contraction along `A → A[1/f]` carries the `ℤ`-graded primes of `A[1/f]` bijectively
onto the standard open `D₊(f) ⊆ Proj 𝒜`, and the inverse is extension of ideals. This is the
left-hand horizontal arrow of the diagram of [Stacks, Tag 01M4] part (1)(f).

## Main results

* `Stacks.ProjStandardOpenBaseChange.proj_algebraMap`: the degree-`i` component of the image of
  `r` in `A[1/f]` is the image of the degree-`i` component of `r`.
* `Stacks.ProjStandardOpenBaseChange.isHomogeneous_comap`,
  `Stacks.ProjStandardOpenBaseChange.isHomogeneous_map`: contraction and extension of ideals
  along `A → A[1/f]` preserve homogeneity.
* `Stacks.ProjStandardOpenBaseChange.gradedPrimesEquivBasicOpen`,
  `Stacks.ProjStandardOpenBaseChange.gradedPrimesHomeoBasicOpen`,
  `Stacks.ProjStandardOpenBaseChange.isHomeomorph_gradedPrimeToProj`: contraction is a
  homeomorphism from the `ℤ`-graded primes of `A[1/f]` onto `D₊(f)`.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.ProjStandardOpenBaseChange

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}

/-- The image in `A[1/f]` of a homogeneous element of `A` is homogeneous of the same degree. -/
public theorem algebraMap_mem_twistAway (hf : f ∈ 𝒜 d) {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    algebraMap A (Localization.Away f) a ∈ twistAway 𝒜 f d (i : ℤ) := by
  refine (mem_twistAway_iff_exists 𝒜 hf (i : ℤ) _).mpr ⟨0, a, ?_, ?_⟩
  · rw [Nat.zero_mul, Nat.cast_zero, zero_add, integerGrading_natCast]
    exact (mem_homogeneousSubmodule (S := A) 𝒜 i a).mpr ha
  · rw [← Localization.mk_one_eq_algebraMap]
    congr 1
    exact Subtype.ext (pow_zero f).symm

/-- The image in `A[1/f]` of a homogeneous element of `A` is a homogeneous element. -/
public theorem isHomogeneousElem_algebraMap (hf : f ∈ 𝒜 d) {a : A}
    (ha : SetLike.IsHomogeneousElem 𝒜 a) :
    SetLike.IsHomogeneousElem (twistAway 𝒜 f d) (algebraMap A (Localization.Away f) a) := by
  obtain ⟨i, hi⟩ := ha
  exact ⟨(i : ℤ), algebraMap_mem_twistAway 𝒜 hf hi⟩

section GradedRing

/-- A ring homomorphism sends `r` to the sum of the images of its homogeneous components. -/
private theorem map_eq_sum_map_decompose {B : Type*} [CommRing B] (φ : A →+* B) (r : A)
    [∀ (i : ℕ) (x : 𝒜 i), Decidable (x ≠ 0)] :
    φ r = ∑ j ∈ DFinsupp.support (DirectSum.decompose 𝒜 r), φ (DirectSum.decompose 𝒜 r j : A) := by
  rw [← map_sum, DirectSum.sum_support_decompose]

variable [GradedRing (twistAway 𝒜 f d)]

/-- **Taking the degree-`i` part commutes with the map `A → A[1/f]`.** The image of `r` is the
sum of the images of the homogeneous components of `r`, and the image of the degree-`i`
component is homogeneous of degree `i`, so it is the degree-`i` component of the image. -/
public theorem proj_algebraMap (hf : f ∈ 𝒜 d) (r : A) (i : ℕ) :
    GradedRing.proj (twistAway 𝒜 f d) (i : ℤ) (algebraMap A (Localization.Away f) r) =
      algebraMap A (Localization.Away f) (GradedRing.proj 𝒜 i r) := by
  classical
  have hcomp : ∀ j : ℕ, GradedRing.proj (twistAway 𝒜 f d) (i : ℤ)
      (algebraMap A (Localization.Away f) (GradedRing.proj 𝒜 j r)) =
      if j = i then algebraMap A (Localization.Away f) (GradedRing.proj 𝒜 i r) else 0 := by
    intro j
    have hmem : algebraMap A (Localization.Away f) (GradedRing.proj 𝒜 j r) ∈
        twistAway 𝒜 f d (j : ℤ) := by
      rw [GradedRing.proj_apply]
      exact algebraMap_mem_twistAway 𝒜 hf (SetLike.coe_mem _)
    rw [GradedRing.proj_apply]
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl]
      exact DirectSum.decompose_of_mem_same _ hmem
    · rw [ite_eq_right hji]
      exact DirectSum.decompose_of_mem_ne _ hmem (by exact_mod_cast hji)
  rw [map_eq_sum_map_decompose 𝒜 (algebraMap A (Localization.Away f)) r, map_sum,
    Finset.sum_eq_single i]
  · rw [← GradedRing.proj_apply, hcomp i, ite_eq_left rfl]
  · intro j _ hji
    rw [← GradedRing.proj_apply, hcomp j, ite_eq_right hji]
  · intro hi
    simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hi
    rw [hi]
    simp

/-- **Contraction along `A → A[1/f]` preserves homogeneity of ideals.** -/
public theorem isHomogeneous_comap (hf : f ∈ 𝒜 d) {J : Ideal (Localization.Away f)}
    (hJ : J.IsHomogeneous (twistAway 𝒜 f d)) :
    (J.comap (algebraMap A (Localization.Away f))).IsHomogeneous 𝒜 := by
  intro i r hr
  have hr' : algebraMap A (Localization.Away f) r ∈ J := hr
  have h := hJ (i : ℤ) hr'
  rw [← GradedRing.proj_apply, proj_algebraMap 𝒜 hf r i, GradedRing.proj_apply] at h
  exact h

/-- **Extension along `A → A[1/f]` preserves homogeneity of ideals.** The homogeneous elements
of a homogeneous ideal generate it, their images are homogeneous, and so they generate a
homogeneous ideal. -/
public theorem isHomogeneous_map (hf : f ∈ 𝒜 d) {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    (I.map (algebraMap A (Localization.Away f))).IsHomogeneous (twistAway 𝒜 f d) := by
  classical
  set φ := algebraMap A (Localization.Away f) with hφ
  set H : Set A := {x | x ∈ I ∧ SetLike.IsHomogeneousElem 𝒜 x} with hH
  have hspan : Ideal.map φ I = Ideal.span (φ '' H) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map, Ideal.span_le]
      rintro z ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, map_eq_sum_map_decompose 𝒜 φ a]
      refine Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨_, ⟨?_, ⟨j, SetLike.coe_mem _⟩⟩, rfl⟩
      exact hI j ha
    · rw [Ideal.span_le]
      rintro z ⟨a, ha, rfl⟩
      exact Ideal.mem_map_of_mem _ ha.1
  rw [hspan]
  refine Ideal.homogeneous_span _ _ ?_
  rintro z ⟨a, ha, rfl⟩
  exact isHomogeneousElem_algebraMap 𝒜 hf ha.2

end GradedRing

/-! ### The bijection with the standard open -/

/-- `f` becomes a unit in `A[1/f]`. -/
public theorem isUnit_algebraMap_self (f : A) :
    IsUnit (algebraMap A (Localization.Away f) f) :=
  IsUnit.unit_spec (IsLocalization.Away.algebraMap_isUnit f :
      IsUnit (algebraMap A (Localization.Away f) f)) ▸ (Stacks.GradedLaurent.awayUnit f).isUnit

/-- `f` lies in the irrelevant ideal when its degree is positive. -/
public theorem mem_irrelevant_self (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 hf (by omega)

/-- A power of `f` never lies in a homogeneous prime missing `f`. -/
public theorem disjoint_powers (p : ProjectiveSpectrum 𝒜)
    (hp : f ∉ p.asHomogeneousIdeal) :
    Disjoint (Submonoid.powers f : Set A) (p.asHomogeneousIdeal.toIdeal : Set A) := by
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ hx
  exact hp (p.isPrime.mem_of_pow_mem n hx)

section Chart

variable [GradedRing (twistAway 𝒜 f d)]

/-- The contraction of a `ℤ`-graded prime of `A[1/f]` does not contain `f`. -/
public theorem notMem_comap (q : gradedPrimes (twistAway 𝒜 f d)) :
    f ∉ q.val.asIdeal.comap (algebraMap A (Localization.Away f)) := fun h =>
  q.val.isPrime.ne_top
    (q.val.asIdeal.eq_top_of_isUnit_mem h (isUnit_algebraMap_self f))

/-- **The point of `Proj 𝒜` under a `ℤ`-graded prime of `A[1/f]`**: its contraction along
`A → A[1/f]`, which is prime, homogeneous and misses `f`, hence misses the irrelevant ideal. -/
public def gradedPrimeToProj (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (q : gradedPrimes (twistAway 𝒜 f d)) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal :=
    ⟨q.val.asIdeal.comap (algebraMap A (Localization.Away f)),
      isHomogeneous_comap 𝒜 hf q.property⟩
  isPrime := Ideal.comap_isPrime _ _ (H := q.val.isPrime)
  not_irrelevant_le h := notMem_comap 𝒜 q (h (mem_irrelevant_self 𝒜 hf hd))

/-- The contraction of a `ℤ`-graded prime of `A[1/f]` lies in the standard open `D₊(f)`. -/
public theorem gradedPrimeToProj_mem_basicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (q : gradedPrimes (twistAway 𝒜 f d)) :
    gradedPrimeToProj 𝒜 hf hd q ∈ ProjectiveSpectrum.basicOpen 𝒜 f :=
  (ProjectiveSpectrum.mem_basicOpen 𝒜 f _).mpr (notMem_comap 𝒜 q)

/-- **The `ℤ`-graded prime of `A[1/f]` under a point of `D₊(f)`**: the extension of its
homogeneous prime ideal, which is prime because no power of `f` lies in it. -/
public def projToGradedPrime (hf : f ∈ 𝒜 d) (p : ProjectiveSpectrum 𝒜)
    (hp : f ∉ p.asHomogeneousIdeal) : gradedPrimes (twistAway 𝒜 f d) :=
  ⟨⟨Ideal.map (algebraMap A (Localization.Away f)) p.asHomogeneousIdeal.toIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f)
        _ p.isPrime (disjoint_powers 𝒜 p hp)⟩,
    isHomogeneous_map 𝒜 hf p.asHomogeneousIdeal.isHomogeneous⟩

/-- **Contraction and extension are mutually inverse bijections between the `ℤ`-graded primes
of `A[1/f]` and the standard open `D₊(f)`.** -/
public def gradedPrimesEquivBasicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    gradedPrimes (twistAway 𝒜 f d) ≃ ↥(ProjectiveSpectrum.basicOpen 𝒜 f) where
  toFun q := ⟨gradedPrimeToProj 𝒜 hf hd q, gradedPrimeToProj_mem_basicOpen 𝒜 hf hd q⟩
  invFun p :=
    projToGradedPrime 𝒜 hf p.1 ((ProjectiveSpectrum.mem_basicOpen 𝒜 f p.1).mp p.2)
  left_inv q := by
    refine Subtype.ext (PrimeSpectrum.ext ?_)
    have h := IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) q.val.asIdeal
    rwa [Ideal.under_def] at h
  right_inv p := by
    refine Subtype.ext (ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_))
    have hp : f ∉ p.1.asHomogeneousIdeal := (ProjectiveSpectrum.mem_basicOpen 𝒜 f p.1).mp p.2
    have h := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p.1.isPrime (disjoint_powers 𝒜 p.1 hp)
    rwa [Ideal.under_def] at h

/-- Both sides of the bijection sit inside `Spec A` compatibly: contracting a graded prime all
the way to `Spec A` is the same as reading off the point of `Proj 𝒜` it determines. -/
public theorem toSpec_comp_equiv (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Proj.toSpec 𝒜 ∘ Subtype.val) ∘ (gradedPrimesEquivBasicOpen 𝒜 hf hd) =
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) ∘ Subtype.val :=
  rfl

/-- **The space of `ℤ`-graded primes of `A[1/f]` is homeomorphic to the standard open
`D₊(f) ⊆ Proj 𝒜`.** This is the left-hand horizontal homeomorphism of the diagram of
[Stacks, Tag 01M4] part (1)(f): contraction along `A → A[1/f]` is a homeomorphism from the
`ℤ`-graded primes of `A[1/f]`, with the subspace topology from `Spec A[1/f]`, onto `D₊(f)` with
the subspace topology from `Proj 𝒜`. -/
public def gradedPrimesHomeoBasicOpen (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    gradedPrimes (twistAway 𝒜 f d) ≃ₜ ↥(ProjectiveSpectrum.basicOpen 𝒜 f) where
  toEquiv := gradedPrimesEquivBasicOpen 𝒜 hf hd
  continuous_toFun := by
    rw [((Proj.isInducing_toSpec 𝒜).comp Topology.IsInducing.subtypeVal).continuous_iff]
    change Continuous ((Proj.toSpec 𝒜 ∘ Subtype.val) ∘ ⇑(gradedPrimesEquivBasicOpen 𝒜 hf hd))
    rw [toSpec_comp_equiv 𝒜 hf hd]
    exact (PrimeSpectrum.continuous_comap _).comp continuous_subtype_val
  continuous_invFun := by
    have hind : Topology.IsInducing
        (PrimeSpectrum.comap (algebraMap A (Localization.Away f)) ∘
          (Subtype.val : gradedPrimes (twistAway 𝒜 f d) → _)) :=
      ((PrimeSpectrum.localization_away_isOpenEmbedding
        (Localization.Away f) f).isEmbedding.isInducing).comp Topology.IsInducing.subtypeVal
    rw [hind.continuous_iff]
    change Continuous ((PrimeSpectrum.comap (algebraMap A (Localization.Away f)) ∘
      (Subtype.val : gradedPrimes (twistAway 𝒜 f d) → _)) ∘
      ⇑(gradedPrimesEquivBasicOpen 𝒜 hf hd).symm)
    have hcomp : (PrimeSpectrum.comap (algebraMap A (Localization.Away f)) ∘
          (Subtype.val : gradedPrimes (twistAway 𝒜 f d) → _)) ∘
        (gradedPrimesEquivBasicOpen 𝒜 hf hd).symm = Proj.toSpec 𝒜 ∘ Subtype.val := by
      rw [← toSpec_comp_equiv 𝒜 hf hd]
      ext p
      simp
    rw [hcomp]
    exact ((Proj.isInducing_toSpec 𝒜).continuous).comp continuous_subtype_val

/-- **The left-hand horizontal arrow of the diagram of [Stacks, Tag 01M4] part (1)(f) is a
homeomorphism.** Sending a `ℤ`-graded prime of `A[1/f]` to its contraction along `A → A[1/f]`
is a homeomorphism from the space of `ℤ`-graded primes of `A[1/f]` onto the standard open
`D₊(f)` of `Proj 𝒜`. -/
public theorem isHomeomorph_gradedPrimeToProj (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    IsHomeomorph (fun q : gradedPrimes (twistAway 𝒜 f d) =>
      (⟨gradedPrimeToProj 𝒜 hf hd q, gradedPrimeToProj_mem_basicOpen 𝒜 hf hd q⟩ :
        ↥(ProjectiveSpectrum.basicOpen 𝒜 f))) :=
  (gradedPrimesHomeoBasicOpen 𝒜 hf hd).isHomeomorph

end Chart

end Stacks.ProjStandardOpenBaseChange

end
