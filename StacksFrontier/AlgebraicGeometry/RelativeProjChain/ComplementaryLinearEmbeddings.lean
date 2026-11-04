module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection

/-!
# Two complementary linear embeddings of projective space, with disjoint images

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings. The morphism
`Proj ℬ ⊇ U(ψ) ⟶ Proj 𝒜` of Stacks Tag 01MY cannot hit a point of `Proj 𝒜` lying in the
standard open `D₊(f)` of an `f` of positive degree with `ψ f = 0`: by part (2) of Tag 01MY the
inverse image of `D₊(f)` is the standard open of `ψ f = 0`, which is empty. So the image of the
morphism is contained in the projective zero locus of the kernel's homogeneous elements of
positive degree — an *upper bound* for the image, which is all that is needed below.

Applying this to the two complementary coordinate blocks
`T_k ↦ (T_0, …, T_n, 0, …, 0)` and `T_k ↦ (0, …, 0, T_0, …, T_m)`
of `ℙ^{n + m + 1}` gives two closed immersions `ℙⁿ ↪ ℙ^{n + m + 1}` and
`ℙᵐ ↪ ℙ^{n + m + 1}` whose images are **disjoint**: a point in both would contain every
variable, hence the whole irrelevant ideal, which no point of `Proj` of a polynomial ring does.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjChain.firstBlockCoords` and
  `Stacks.AlgebraicGeometry.RelativeProjChain.secondBlockCoords`: the two complementary
  coordinate families `Fin (n + m + 2) → R[T_0, …, T_n]` and `Fin (n + m + 2) → R[T_0, …, T_m]`,
  each sending the variables of its own block to the variables of the target and the variables
  of the other block to zero.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjChain.mem_asHomogeneousIdeal_of_mem_range_mapHom`: a
  homogeneous element of positive degree in the kernel of `ψ` lies in every point of the image
  of the morphism `U(ψ) ⟶ Proj 𝒜` of Tag 01MY, and
  `mem_asHomogeneousIdeal_of_mem_range_projToProjectiveSpace` is the same statement for the
  everywhere-defined morphism `Proj S ⟶ ℙᴺ_R` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection`.
* `Stacks.AlgebraicGeometry.RelativeProjChain.irrelevant_le_of_forall_X_mem`: a homogeneous
  ideal of a polynomial ring containing every variable contains the irrelevant ideal. This is
  what makes the two images disjoint.
* `Stacks.AlgebraicGeometry.RelativeProjChain.adjoin_range_eq_top_of_forall_X_mem_range`: a
  family of polynomials whose range contains every variable generates the polynomial ring.
* `Stacks.AlgebraicGeometry.RelativeProjChain`
  `.exists_disjoint_isClosedImmersion_projectiveSpaceAtUniverse`: **the two complementary
  linear embeddings**, as closed immersions of the integral models
  `ℙⁿ, ℙᵐ ↪ ℙ^{n + m + 1}` with disjoint images.

## Implementation notes

What is proved about the image of
`Stacks.AlgebraicGeometry.RelativeProjChain.projToProjectiveSpace` is a *containment*: the
image lies in the closed set cut out by the variables that the coordinate family sends to
zero. The containment is what disjointness needs, since the two complementary blocks send
complementary sets of variables to zero and the two closed sets they cut out meet only where
all variables vanish, which is nowhere on `Proj`.

The containment is a corollary of part (2) of Tag 01MY, which is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`, and the pair of
complementary linear embeddings is a step in the proof of Stacks 089J.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

universe u w w'

namespace Stacks.AlgebraicGeometry.RelativeProjChain

attribute [local instance] MvPolynomial.gradedAlgebra

section Range

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **A homogeneous element of positive degree killed by `ψ` lies in every point of the image
of `Proj ψ`.** -/
theorem mem_asHomogeneousIdeal_of_mem_range_mapHom (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (hψf : ψ f = 0) {q : AlgebraicGeometry.Proj 𝒜}
    (hq : q ∈ Set.range (mapHom 𝒜 ℬ ψ).base) : f ∈ q.asHomogeneousIdeal := by
  obtain ⟨p, rfl⟩ := hq
  by_contra hfq
  have hmem : p ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f := hfq
  rw [mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd, hψf,
    AlgebraicGeometry.Proj.basicOpen_zero] at hmem
  simp at hmem

/-- The same for `projToProjectiveSpace`, which is `mapHom` precomposed with two
isomorphisms. -/
theorem mem_asHomogeneousIdeal_of_mem_range_projToProjectiveSpace {R : Type u} [CommRing R]
    [Algebra R B] (hR : ∀ r : R, algebraMap R B r ∈ ℬ 0) {N : ℕ}
    (x : Fin (N + 1) → B) (hx : ∀ i, x i ∈ ℬ 1)
    (hgen : Algebra.adjoin R (Set.range x) = ⊤) {d : ℕ} (hd : 0 < d)
    {f : MvPolynomial (Fin (N + 1)) R}
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R d)
    (hψf : MvPolynomial.aeval x f = 0)
    {q : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)}
    (hq : q ∈ Set.range (projToProjectiveSpace ℬ hR x hx hgen).base) :
    f ∈ q.asHomogeneousIdeal := by
  refine mem_asHomogeneousIdeal_of_mem_range_mapHom _ ℬ (polyGradedHom ℬ hR x hx) hd hf hψf ?_
  obtain ⟨p, rfl⟩ := hq
  rw [projToProjectiveSpace]
  exact ⟨_, rfl⟩

end Range

section Blocks

variable (R : Type u) [CommRing R]

/-- A variable is homogeneous of degree one. -/
private theorem X_mem_homogeneousSubmodule_one {σ : Type*} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ R) ∈ MvPolynomial.homogeneousSubmodule σ R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)

/-- Constants are homogeneous of degree zero. -/
private theorem algebraMap_mem_homogeneousSubmodule_zero {σ : Type*} (r : R) :
    algebraMap R (MvPolynomial σ R) r ∈ MvPolynomial.homogeneousSubmodule σ R 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ r)

/-- **Generation by the variables is enough.** A family of polynomials whose range contains every
variable generates the polynomial ring as an algebra over the coefficients. -/
theorem adjoin_range_eq_top_of_forall_X_mem_range {σ ι : Type*} (x : ι → MvPolynomial σ R)
    (h : ∀ j : σ, (MvPolynomial.X j : MvPolynomial σ R) ∈ Set.range x) :
    Algebra.adjoin R (Set.range x) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← MvPolynomial.adjoin_range_X (σ := σ) (R := R)]
  exact Algebra.adjoin_mono (Set.range_subset_iff.mpr h)

/-- **A point of `Proj R[T_0, …, T_N]` cannot contain every variable.** The ideal spanned by the
variables contains every homogeneous polynomial of positive degree, hence the irrelevant
ideal. -/
theorem irrelevant_le_of_forall_X_mem {σ : Type*}
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (h : ∀ k : σ, (MvPolynomial.X k : MvPolynomial σ R) ∈ I) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ R) ≤ I := by
  classical
  refine (HomogeneousIdeal.irrelevant_le _).2 fun i hi p hp => ?_
  have hspan : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) ≤ I.toIdeal :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr h)
  refine hspan ?_
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro e he
  have hw := (hp : p.IsHomogeneous i) (MvPolynomial.mem_support_iff.mp he)
  by_contra hc
  push Not at hc
  obtain rfl : e = 0 := Finsupp.ext fun j => hc j (Set.mem_univ j)
  simp at hw
  omega

/-- **The first of two complementary coordinate families.** The `k`-th coordinate of
`ℙ^{n + m + 1}` is sent to `T_k` for `k ≤ n` and to `0` for `k > n`. -/
def firstBlockCoords (n m : ℕ) (k : Fin (n + m + 1 + 1)) : MvPolynomial (Fin (n + 1)) R :=
  if h : (k : ℕ) < n + 1 then MvPolynomial.X ⟨(k : ℕ), h⟩ else 0

/-- **The second of two complementary coordinate families.** The `k`-th coordinate of
`ℙ^{n + m + 1}` is sent to `0` for `k ≤ n` and to `T_{k - n - 1}` for `k > n`. -/
def secondBlockCoords (n m : ℕ) (k : Fin (n + m + 1 + 1)) : MvPolynomial (Fin (m + 1)) R :=
  if h : (k : ℕ) < n + 1 then 0
    else MvPolynomial.X ⟨(k : ℕ) - (n + 1), by have := k.isLt; omega⟩

/-- The coordinate `firstBlockCoords R n m k` vanishes when `k > n`. -/
theorem firstBlockCoords_eq_zero {n m : ℕ} {k : Fin (n + m + 1 + 1)} (h : ¬ (k : ℕ) < n + 1) :
    firstBlockCoords R n m k = 0 :=
  dite_eq_right h

/-- The coordinate `secondBlockCoords R n m k` vanishes when `k ≤ n`. -/
theorem secondBlockCoords_eq_zero {n m : ℕ} {k : Fin (n + m + 1 + 1)} (h : (k : ℕ) < n + 1) :
    secondBlockCoords R n m k = 0 :=
  dite_eq_left h

/-- Each coordinate `firstBlockCoords R n m k` is homogeneous of degree one. -/
theorem firstBlockCoords_mem (n m : ℕ) (k : Fin (n + m + 1 + 1)) :
    firstBlockCoords R n m k ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 := by
  simp only [firstBlockCoords]
  split
  · exact X_mem_homogeneousSubmodule_one R _
  · exact zero_mem _

/-- Each coordinate `secondBlockCoords R n m k` is homogeneous of degree one. -/
theorem secondBlockCoords_mem (n m : ℕ) (k : Fin (n + m + 1 + 1)) :
    secondBlockCoords R n m k ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R 1 := by
  simp only [secondBlockCoords]
  split
  · exact zero_mem _
  · exact X_mem_homogeneousSubmodule_one R _

/-- The coordinates `firstBlockCoords R n m` generate `R[T_0, …, T_n]` as an `R`-algebra. -/
theorem adjoin_range_firstBlockCoords (n m : ℕ) :
    Algebra.adjoin R (Set.range (firstBlockCoords R n m)) = ⊤ := by
  have hle : n + 1 ≤ n + m + 1 + 1 := by omega
  refine adjoin_range_eq_top_of_forall_X_mem_range R _ fun j => ⟨Fin.castLE hle j, ?_⟩
  have hlt : ((Fin.castLE hle j : Fin (n + m + 1 + 1)) : ℕ) < n + 1 := by simpa using j.isLt
  simp only [firstBlockCoords, dite_eq_left hlt]
  congr 1

/-- The coordinates `secondBlockCoords R n m` generate `R[T_0, …, T_m]` as an `R`-algebra. -/
theorem adjoin_range_secondBlockCoords (n m : ℕ) :
    Algebra.adjoin R (Set.range (secondBlockCoords R n m)) = ⊤ := by
  refine adjoin_range_eq_top_of_forall_X_mem_range R _ fun j => ?_
  have hj : (j : ℕ) < m + 1 := j.isLt
  have hnot : ¬ (n + 1 + (j : ℕ) < n + 1) := by omega
  refine ⟨⟨n + 1 + (j : ℕ), by omega⟩, ?_⟩
  simp only [secondBlockCoords, dite_eq_right hnot]
  congr 1
  exact Fin.ext (by simp)

end Blocks

section AtUniverse

/-- **Two complementary linear embeddings of the integral models of projective space.** For all
`n` and `m` there are closed immersions of `ℙⁿ` and of `ℙᵐ` into `ℙ^{n + m + 1}` with *disjoint*
images: the two complementary coordinate blocks. -/
theorem exists_disjoint_isClosedImmersion_projectiveSpaceAtUniverse (n m : ℕ) :
    ∃ (a : projectiveSpaceAtUniverse.{u} n ⟶ projectiveSpaceAtUniverse.{u} (n + m + 1))
      (b : projectiveSpaceAtUniverse.{u} m ⟶ projectiveSpaceAtUniverse.{u} (n + m + 1)),
      IsClosedImmersion a ∧ IsClosedImmersion b ∧
        Disjoint (Set.range a.base) (Set.range b.base) := by
  let R := ULift.{u} ℤ
  let 𝒜 : ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let ℬ : ℕ → Submodule R (MvPolynomial (Fin (m + 1)) R) :=
    MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R
  have halg : ∀ r : R, algebraMap R (MvPolynomial (Fin (n + 1)) R) r ∈ 𝒜 0 :=
    algebraMap_mem_homogeneousSubmodule_zero R
  have hblg : ∀ r : R, algebraMap R (MvPolynomial (Fin (m + 1)) R) r ∈ ℬ 0 :=
    algebraMap_mem_homogeneousSubmodule_zero R
  refine ⟨projToProjectiveSpace 𝒜 halg (firstBlockCoords R n m) (firstBlockCoords_mem R n m)
      (adjoin_range_firstBlockCoords R n m),
    projToProjectiveSpace ℬ hblg (secondBlockCoords R n m) (secondBlockCoords_mem R n m)
      (adjoin_range_secondBlockCoords R n m),
    isClosedImmersion_projToProjectiveSpace 𝒜 halg _ _ _,
    isClosedImmersion_projToProjectiveSpace ℬ hblg _ _ _,
    Set.disjoint_left.mpr fun q hqa hqb => ?_⟩
  refine q.not_irrelevant_le (irrelevant_le_of_forall_X_mem R _ fun k => ?_)
  have hXk := X_mem_homogeneousSubmodule_one R k
  by_cases hk : (k : ℕ) < n + 1
  · exact mem_asHomogeneousIdeal_of_mem_range_projToProjectiveSpace ℬ hblg _ _ _ Nat.one_pos
      hXk (by simp [secondBlockCoords_eq_zero R hk]) hqb
  · exact mem_asHomogeneousIdeal_of_mem_range_projToProjectiveSpace 𝒜 halg _ _ _ Nat.one_pos
      hXk (by simp [firstBlockCoords_eq_zero R hk]) hqa

end AtUniverse

end Stacks.AlgebraicGeometry.RelativeProjChain

end
