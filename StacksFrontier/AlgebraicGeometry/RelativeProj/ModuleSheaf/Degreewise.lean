module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Degreewise
public import StacksFrontier.RingTheory.GradedAlgebra.LiftPresentation

/-!
# Degreewise localization of graded modules

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is, in each degree, the
localization away from a degree-zero element `g` of `𝒜`
(`Stacks.GradedLocalization.IsAwayDegreewise`). This file states the module-theoretic companion
of that hypothesis: a `ℤ`-graded `𝒜`-module `𝒨`, a `ℤ`-graded `ℬ`-module `𝒩`, and a
`φ`-semilinear map `f : M → N` which preserves degrees and exhibits `𝒩 i` as the localization of
`𝒨 i` away from `g`, for every `i`.

Concretely: `f` sends `𝒨 i` into `𝒩 i`; every homogeneous element of `𝒩 i` becomes the image of a
homogeneous element of `𝒨 i` after multiplication by a power of `φ g`; and a homogeneous element
of `𝒨 i` killed by `f` is killed by a power of `g`. From this we derive the two ungraded forms,
by decomposing into homogeneous pieces and clearing with the maximum of the finitely many
exponents, a form producing one *common* power for a homogeneous numerator over `𝒩` and a
homogeneous denominator over `ℬ`, and a form whose exponent exceeds any prescribed bound.

## Main definitions

* `Stacks.GradedLocalization.IsAwayDegreewiseModule` is the hypothesis described above.

## Main results

* `Stacks.GradedLocalization.IsAwayDegreewiseModule.map_decompose`: a degree-preserving
  semilinear map commutes with the graded decomposition.
* `Stacks.GradedLocalization.IsAwayDegreewiseModule.exists_pow_smul_eq_map`: every element of
  `N`, not only every homogeneous one, becomes the image of an element of `M` after multiplication
  by a power of `φ g`.
* `Stacks.GradedLocalization.IsAwayDegreewiseModule.exists_pow_smul_eq_zero`: every element of
  `M` killed by `f`, not only every homogeneous one, is killed by a power of `g`.
* `Stacks.GradedLocalization.IsAwayDegreewiseModule.exists_common_pow_smul_eq_map`: a homogeneous
  element of `N` and a homogeneous element of `B` are simultaneously images of homogeneous
  elements of `M` and of `A` of the same degrees, after one common power of `φ g`.
* `Stacks.GradedLocalization.IsAwayDegreewiseModule.exists_pow_smul_eq_map_of_mem`: a single
  homogeneous element of `N` is such an image after a power of `φ g` whose exponent may be
  demanded to exceed any prescribed bound.

## Implementation notes

The module is graded by `ℤ` while the ring is graded by `ℕ`; that is the grading convention of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf`, which consumes these data.

A *common* power is what makes `exists_common_pow_smul_eq_map` usable on a module fraction `m / s`
with `m` a homogeneous element of `N` and `s` a homogeneous element of `B`. Lifting the numerator
and the denominator separately yields two unrelated exponents, and multiplying numerator and
denominator by different powers of `g` changes the quotient; only a single exponent applied to
both leaves the fraction it represents unchanged. Likewise the prescribed lower bound in
`exists_pow_smul_eq_map_of_mem` is what allows a lift already obtained for one element to be
matched by a lift of another, by taking the larger of the two exponents.

Those two lemmas multiply a homogeneous witness in `𝒨 i` by a power of `g`, so they need the
action of `𝒜` on `𝒨` to respect the gradings. That is taken as an explicit hypothesis
`hsmul : ∀ (j : ℕ) {x : M} {i : ℤ}, x ∈ 𝒨 i → g ^ j • x ∈ 𝒨 i` rather than as an instance binder
`[SetLike.GradedSMul 𝒜 𝒨]`, for two reasons. Such an instance binder needs a `VAdd ℕ ℤ`, and the
one `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` works with is local to the
file declaring it, so a binder here would be at a different, merely definitionally equal, instance
and a caller would not match it. And `hsmul` is all these proofs use: no other statement below
mentions the action of `𝒜` on `𝒨` at all, so none of them carries the hypothesis.

`IsAwayDegreewise φ g` is *not* a field of `IsAwayDegreewiseModule`. The ring hypothesis is needed
only for the denominator half of `exists_common_pow_smul_eq_map`, which takes it as a separate
argument, exactly as the ring-side lemmas keep `hg : g ∈ 𝒜 0` separate.

`map_decompose` is an instance of `DirectSum.coe_decompose_map`, which states the same thing for a
degree-preserving additive map between graded additive monoids whose gradings may be by submodules
over different base rings; a `φ`-semilinear map is in particular such an additive map.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public section

universe u

namespace Stacks.GradedLocalization

variable {A B M N : Type u} {σ τ μ ν : Type*}
  [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  {φ : 𝒜 →+*ᵍ ℬ} {f : M →ₛₗ[φ.toRingHom] N} {g : A}

/-- A `φ`-semilinear map from a `ℤ`-graded `𝒜`-module to a `ℤ`-graded `ℬ`-module which is, in each
degree, the localization away from a degree-zero element `g` of `𝒜`: it preserves degrees, every
homogeneous element of the target is its value on a homogeneous element of the source of the same
degree divided by a power of `φ g`, and its kernel on each homogeneous piece is `g`-power torsion.
This is the module companion of `Stacks.GradedLocalization.IsAwayDegreewise`. -/
public structure IsAwayDegreewiseModule (φ : 𝒜 →+*ᵍ ℬ) (𝒨 : ℤ → μ) (𝒩 : ℤ → ν)
    (f : M →ₛₗ[φ.toRingHom] N) (g : A) : Prop where
  /-- `f` preserves degrees. -/
  map_mem (i : ℤ) {m : M} (hm : m ∈ 𝒨 i) : f m ∈ 𝒩 i
  /-- Every homogeneous element of `𝒩` is the image of a homogeneous element of `𝒨` of the same
  degree after multiplication by a power of the image of `g`. -/
  surj (i : ℤ) (y : N) (hy : y ∈ 𝒩 i) : ∃ (k : ℕ) (x : M), x ∈ 𝒨 i ∧ f x = φ g ^ k • y
  /-- A homogeneous element of `𝒨` in the kernel is killed by a power of `g`. -/
  torsion (i : ℤ) (x : M) (hx : x ∈ 𝒨 i) (h : f x = 0) : ∃ k : ℕ, g ^ k • x = 0

namespace IsAwayDegreewiseModule

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- Semilinearity, written for a power of the scalar `g`: the ring homomorphism along which `f` is
semilinear sends `g ^ j` to `φ g ^ j`. -/
private theorem map_pow_smul (f : M →ₛₗ[φ.toRingHom] N) (j : ℕ) (x : M) :
    f (g ^ j • x) = φ g ^ j • f x := by
  rw [f.map_smulₛₗ, map_pow]; rfl

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- A degree-preserving semilinear map commutes with the graded decomposition: taking the
degree-`i` homogeneous component of an element of `M` and then applying `f` gives the degree-`i`
homogeneous component of its image. -/
public theorem map_decompose (hm : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (x : M) (i : ℤ) :
    f (DirectSum.decompose 𝒨 x i : M) = (DirectSum.decompose 𝒩 (f x) i : N) :=
  (DirectSum.coe_decompose_map (ℳ := 𝒨) (𝒩 := 𝒩) f.toAddMonoidHom
    (fun j _ hj => hm.map_mem j hj) i x).symm

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ]
  [AddSubgroupClass μ M] [DirectSum.Decomposition 𝒨] in
/-- Every element of `N`, not only every homogeneous one, becomes the image of an element of `M`
after multiplication by a power of the image of `g`. -/
public theorem exists_pow_smul_eq_map (hm : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (y : N) :
    ∃ (k : ℕ) (x : M), f x = φ g ^ k • y := by
  classical
  choose k x _ hxy using fun i => hm.surj i _ (DirectSum.decompose 𝒩 y i).2
  refine ⟨(DirectSum.decompose 𝒩 y).support.sup k,
    ∑ i ∈ (DirectSum.decompose 𝒩 y).support,
      g ^ ((DirectSum.decompose 𝒩 y).support.sup k - k i) • x i, ?_⟩
  calc f (∑ i ∈ (DirectSum.decompose 𝒩 y).support,
          g ^ ((DirectSum.decompose 𝒩 y).support.sup k - k i) • x i)
      = ∑ i ∈ (DirectSum.decompose 𝒩 y).support,
          φ g ^ (DirectSum.decompose 𝒩 y).support.sup k •
            ((DirectSum.decompose 𝒩 y i : 𝒩 i) : N) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_pow_smul, hxy i, smul_smul, ← pow_add,
          Nat.sub_add_cancel (Finset.le_sup (f := k) hi)]
    _ = φ g ^ (DirectSum.decompose 𝒩 y).support.sup k • y := by
        rw [← Finset.smul_sum, DirectSum.sum_support_decompose]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- An element of `M` killed by `f`, not only a homogeneous one, is killed by a power of `g`. -/
public theorem exists_pow_smul_eq_zero (hm : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) {x : M}
    (hx : f x = 0) : ∃ k : ℕ, g ^ k • x = 0 := by
  classical
  choose k hk using fun i => hm.torsion i _ (DirectSum.decompose 𝒨 x i).2
    (by rw [hm.map_decompose x i, hx]; simp)
  refine ⟨(DirectSum.decompose 𝒨 x).support.sup k, ?_⟩
  have hsplit : g ^ (DirectSum.decompose 𝒨 x).support.sup k • x =
      ∑ i ∈ (DirectSum.decompose 𝒨 x).support,
        g ^ (DirectSum.decompose 𝒨 x).support.sup k •
          ((DirectSum.decompose 𝒨 x i : 𝒨 i) : M) := by
    rw [← Finset.smul_sum, DirectSum.sum_support_decompose]
  rw [hsplit]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Nat.sub_add_cancel (Finset.le_sup (f := k) hi), pow_add, mul_smul, hk i, smul_zero]

omit [AddSubgroupClass τ B] [GradedRing ℬ] [AddSubgroupClass μ M] [AddSubgroupClass ν N]
  [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
/-- One common power lifts a homogeneous numerator and a homogeneous denominator at once: a
homogeneous element `m` of `N` and a homogeneous element `s` of `B` are simultaneously the image of
a homogeneous element of `M` and of a homogeneous element of `A` of the same degrees, after
multiplication by one common power of `φ g`. The hypothesis `hsmul` says that multiplying by a
power of the degree-zero element `g` preserves degrees in `𝒨`. -/
public theorem exists_common_pow_smul_eq_map (h : IsAwayDegreewise φ g)
    (hm : IsAwayDegreewiseModule φ 𝒨 𝒩 f g) (hg : g ∈ 𝒜 0)
    (hsmul : ∀ (j : ℕ) {x : M} {i : ℤ}, x ∈ 𝒨 i → g ^ j • x ∈ 𝒨 i)
    {d : ℤ} {e : ℕ} {m : N} {s : B} (hmd : m ∈ 𝒩 d) (hs : s ∈ ℬ e) :
    ∃ (m' : M) (s' : A) (i : ℕ), m' ∈ 𝒨 d ∧ s' ∈ 𝒜 e ∧
      f m' = φ g ^ i • m ∧ φ s' = φ g ^ i * s := by
  obtain ⟨i₁, m₁, hm₁, hm₁eq⟩ := hm.surj d m hmd
  obtain ⟨i₂, s₁, hs₁, hs₁eq⟩ := h.surj e s hs
  have hgpow : g ^ (max i₁ i₂ - i₂) ∈ 𝒜 0 := by
    simpa using SetLike.pow_mem_graded (max i₁ i₂ - i₂) hg
  refine ⟨g ^ (max i₁ i₂ - i₁) • m₁, s₁ * g ^ (max i₁ i₂ - i₂), max i₁ i₂,
    hsmul _ hm₁, by simpa using SetLike.mul_mem_graded hs₁ hgpow, ?_, ?_⟩
  · rw [map_pow_smul, hm₁eq, smul_smul, ← pow_add, Nat.sub_add_cancel (le_max_left i₁ i₂)]
  · rw [map_mul, map_pow, hs₁eq, mul_right_comm, ← pow_add,
      Nat.add_sub_cancel' (le_max_right i₁ i₂)]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ]
  [AddSubgroupClass μ M] [AddSubgroupClass ν N] [DirectSum.Decomposition 𝒨]
  [DirectSum.Decomposition 𝒩] in
/-- A single homogeneous element of `N` is the image of a homogeneous element of `M` of the same
degree after multiplication by a power of `φ g`, with the witness multiplied up to any larger
exponent. The hypothesis `hsmul` says that multiplying by a power of `g` preserves degrees in
`𝒨`. -/
public theorem exists_pow_smul_eq_map_of_mem (hm : IsAwayDegreewiseModule φ 𝒨 𝒩 f g)
    (hsmul : ∀ (j : ℕ) {x : M} {i : ℤ}, x ∈ 𝒨 i → g ^ j • x ∈ 𝒨 i)
    {d : ℤ} {m : N} (hmd : m ∈ 𝒩 d) (i : ℕ) :
    ∃ (k : ℕ) (m' : M), m' ∈ 𝒨 d ∧ i ≤ k ∧ f m' = φ g ^ k • m := by
  obtain ⟨k₀, m₀, hm₀, hm₀eq⟩ := hm.surj d m hmd
  refine ⟨max k₀ i, g ^ (max k₀ i - k₀) • m₀, hsmul _ hm₀, le_max_right k₀ i, ?_⟩
  rw [map_pow_smul, hm₀eq, smul_smul, ← pow_add, Nat.sub_add_cancel (le_max_left k₀ i)]

end IsAwayDegreewiseModule

end Stacks.GradedLocalization

end
