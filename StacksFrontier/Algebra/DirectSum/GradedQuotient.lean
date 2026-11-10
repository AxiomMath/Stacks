module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Gradings on quotients of a graded module by a homogeneous submodule

Let `M` be a module over a graded ring `A = ⨁_i 𝒜 i`, graded by a family `ℳ : ℤ → σ` of additive
subgroups carrying a `DirectSum.Decomposition`, and let `K ⊆ M` be a homogeneous submodule — one
containing every graded component of each of its elements (`Submodule.IsHomogeneous`). Then the
quotient `M ⧸ K` is graded by the images of the graded pieces of `M`, compatibly with the grading
of `A`.

The grading of a graded module over a graded ring is by additive subgroups rather than by
submodules, because a graded piece is not a submodule: multiplying by a homogeneous element of
positive degree shifts the degree.

The file also proves some homogeneity facts: a power of a homogeneous ideal is homogeneous, the
submodule `J • ⊤` is homogeneous for a homogeneous ideal `J`, and the kernel of a
degree-preserving map and the supremum of two homogeneous submodules are homogeneous.

## Main definitions

* `Submodule.gradedQuotientPiece` — the degree-`d` part of `M ⧸ K`.

## Main results

* `DirectSum.isInternal_of_eq_zero_of_exists_sum` — a family of additive subgroups which is
  independent and spans is an internal direct sum.
* `DirectSum.coe_decompose_apply_of_mem_graded` — a degree-preserving additive map commutes with
  taking graded components.
* `DirectSum.exists_mem_graded_eq_of_surjective` — a degree-preserving surjection is surjective in
  every degree.
* `Submodule.isInternal_gradedQuotientPiece` — **the quotient by a homogeneous submodule is the
  direct sum of its graded pieces**.
* `DirectSum.mem_graded_of_smul_mem_graded` — **a degree is detected by the homogeneous multiples
  of a torsion-free element**.
* `Submodule.smul_mem_gradedQuotientPiece` — the quotient grading is compatible with the grading
  of `A`.
* `Ideal.IsHomogeneous.pow`, `Submodule.isHomogeneous_smul_top`,
  `Submodule.isHomogeneous_ker`, `Submodule.IsHomogeneous.sup` — the homogeneity facts.

## Implementation notes

Compatibility of the grading of `M` with that of `A` is carried as the explicit hypothesis
`a ∈ 𝒜 i → x ∈ ℳ d → a • x ∈ ℳ (i + d)` rather than as a `SetLike.GradedSMul` instance, which
would need a `VAdd ℕ ℤ` instance in the statements.

## References

* [Stacks Project, Tag 0EL4](https://stacks.math.columbia.edu/tag/0EL4)
* [Stacks Project, Tag 0EKC](https://stacks.math.columbia.edu/tag/0EKC)
-/

@[expose] public section

universe u v w t t'

open DirectSum

namespace DirectSum

/-- **A family of additive subgroups which is independent and spans is an internal direct sum.**
Independence is the statement that a vanishing finite sum of elements of distinct degrees has
vanishing summands; spanning is that every element is such a finite sum. -/
public theorem isInternal_of_eq_zero_of_exists_sum {ι : Type v} [DecidableEq ι] {V : Type w}
    [AddCommGroup V] {σ : Type t} [SetLike σ V] [AddSubgroupClass σ V] (𝒱 : ι → σ)
    (hindep : ∀ (s : Finset ι) (y : ι → V), (∀ i ∈ s, y i ∈ 𝒱 i) → (∑ i ∈ s, y i) = 0 →
      ∀ i₀ ∈ s, y i₀ = 0)
    (hspan : ∀ x : V, ∃ (s : Finset ι) (y : ι → V), (∀ i, y i ∈ 𝒱 i) ∧ (∀ i ∉ s, y i = 0) ∧
      (∑ i ∈ s, y i) = x) :
    DirectSum.IsInternal 𝒱 := by
  classical
  have hval : ∀ ζ : DirectSum ι fun i => ↥(𝒱 i),
      (DirectSum.coeAddMonoidHom 𝒱) ζ = ∑ i ∈ DFinsupp.support ζ, ((ζ i : V)) := fun ζ => by
    conv_lhs => rw [← DirectSum.sum_support_of ζ]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => DirectSum.coeAddMonoidHom_of 𝒱 i (ζ i)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ζ hζ
    refine DFinsupp.ext fun i => ?_
    rw [DFinsupp.zero_apply]
    by_cases hi : i ∈ DFinsupp.support ζ
    · refine Subtype.ext (hindep (DFinsupp.support ζ) (fun i => ((ζ i : V)))
        (fun i _ => (ζ i).2) ?_ i hi)
      rwa [← hval ζ]
    · exact DFinsupp.notMem_support_iff.1 hi
  · intro x
    obtain ⟨s, y, hy, hzero, hsum⟩ := hspan x
    refine ⟨∑ i ∈ s, DirectSum.of _ i (⟨y i, hy i⟩ : ↥(𝒱 i)), ?_⟩
    rw [map_sum, ← hsum]
    exact Finset.sum_congr rfl fun i _ =>
      DirectSum.coeAddMonoidHom_of 𝒱 i (⟨y i, hy i⟩ : ↥(𝒱 i))

/-- The degree-`d` component of a finite sum of homogeneous elements, indexed by `κ` with
`g e` of degree `φ e`, is the sum of the summands whose degree is `d`. -/
private theorem coe_decompose_sum_of_mem_graded {ι : Type v} [DecidableEq ι] {V : Type w}
    [AddCommGroup V] {σ : Type t} [SetLike σ V] [AddSubgroupClass σ V] (𝒱 : ι → σ)
    [DirectSum.Decomposition 𝒱] {κ : Type*} (s : Finset κ) (g : κ → V) (φ : κ → ι)
    (hg : ∀ e ∈ s, g e ∈ 𝒱 (φ e)) (d : ι) :
    ((DirectSum.decompose 𝒱 (∑ e ∈ s, g e) d : V)) = ∑ e ∈ s, if φ e = d then g e else 0 := by
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun e he => ?_
  split_ifs with h
  · exact h ▸ DirectSum.decompose_of_mem_same 𝒱 (hg e he)
  · exact DirectSum.decompose_of_mem_ne 𝒱 (hg e he) h

section Map

variable {ι : Type v} [DecidableEq ι] {V : Type w} {V' : Type w}
  [AddCommGroup V] [AddCommGroup V'] {σ : Type t} {σ' : Type t'}
  [SetLike σ V] [AddSubgroupClass σ V] [SetLike σ' V'] [AddSubgroupClass σ' V']
  (𝒱 : ι → σ) [DirectSum.Decomposition 𝒱] (𝒱' : ι → σ') [DirectSum.Decomposition 𝒱']

/-- **A degree-preserving additive map commutes with taking graded components.** -/
public theorem coe_decompose_apply_of_mem_graded (f : V →+ V')
    (hf : ∀ (d : ι) (x : V), x ∈ 𝒱 d → f x ∈ 𝒱' d) (d : ι) (x : V) :
    ((DirectSum.decompose 𝒱' (f x) d : V')) = f ((DirectSum.decompose 𝒱 x d : V)) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒱 x, map_sum,
    coe_decompose_sum_of_mem_graded 𝒱' _ _ id fun i _ => hf i _ (DirectSum.decompose 𝒱 x i).2]
  simp only [id, Finset.sum_ite_eq', DirectSum.sum_support_decompose]
  split_ifs with hd
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 hd, ZeroMemClass.coe_zero, map_zero]

/-- **A degree-preserving surjection is surjective in every degree**: a homogeneous element of
degree `d` is the image of the degree-`d` component of any preimage. -/
public theorem exists_mem_graded_eq_of_surjective (f : V →+ V')
    (hf : ∀ (d : ι) (x : V), x ∈ 𝒱 d → f x ∈ 𝒱' d) (hsurj : Function.Surjective f)
    {d : ι} {y : V'} (hy : y ∈ 𝒱' d) : ∃ x ∈ 𝒱 d, f x = y := by
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨(DirectSum.decompose 𝒱 x d : V), (DirectSum.decompose 𝒱 x d).2,
    (coe_decompose_apply_of_mem_graded 𝒱 𝒱' f hf d x).symm.trans
      (DirectSum.decompose_of_mem_same 𝒱' hy)⟩

end Map

/-! ### Reading off a degree in a torsion-free graded module -/

section TorsionFree

variable {A : Type u} [CommRing A] {σA : Type w} [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℕ → σA) [GradedRing 𝒜]
  {Y : Type v} [AddCommGroup Y] [Module A Y] {σY : Type t} [SetLike σY Y]
  [AddSubgroupClass σY Y] (𝒴 : ℤ → σY) [DirectSum.Decomposition 𝒴]

omit [AddSubgroupClass σA A] [GradedRing 𝒜] in
/-- **The homogeneous components of a multiple by a homogeneous element.** If `a` is
homogeneous of degree `i` then the degree-`i + d` component of `a • y` is `a` times the
degree-`d` component of `y`. -/
public theorem coe_decompose_smul_of_mem_graded
    (h𝒴 : ∀ (i : ℕ) (d : ℤ) (a : A) (y : Y), a ∈ 𝒜 i → y ∈ 𝒴 d → a • y ∈ 𝒴 ((i : ℤ) + d))
    {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) (d : ℤ) (y : Y) :
    ((DirectSum.decompose 𝒴 (a • y) ((i : ℤ) + d) : Y)) =
      a • ((DirectSum.decompose 𝒴 y d : Y)) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒴 y, Finset.smul_sum,
    coe_decompose_sum_of_mem_graded 𝒴 _ _ (fun e => (i : ℤ) + e)
      fun e _ => h𝒴 i e a _ ha (DirectSum.decompose 𝒴 y e).2]
  simp only [add_right_inj, Finset.sum_ite_eq', DirectSum.sum_support_decompose]
  split_ifs with hd
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 hd, ZeroMemClass.coe_zero, smul_zero]

/-- **A degree is detected by the homogeneous multiples of a torsion-free element.** Let `J` be a
homogeneous ideal and let `Y` be a graded module with no `J^k`-torsion. If every multiple of `y`
by a homogeneous element of `J^k` of degree `i` is homogeneous of degree `i + d`, then `y` itself
is homogeneous of degree `d`. -/
public theorem mem_graded_of_smul_mem_graded
    (h𝒴 : ∀ (i : ℕ) (d : ℤ) (a : A) (y : Y), a ∈ 𝒜 i → y ∈ 𝒴 d → a • y ∈ 𝒴 ((i : ℤ) + d))
    {J : Ideal A} {k : ℕ} (hJ : (J ^ k).IsHomogeneous 𝒜)
    (hYtf : ∀ z : Y, (∀ a ∈ J ^ k, a • z = 0) → z = 0)
    {d : ℤ} {y : Y}
    (hy : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → a ∈ J ^ k → a • y ∈ 𝒴 ((i : ℤ) + d)) :
    y ∈ 𝒴 d := by
  classical
  have hzero : ∀ e : ℤ, e ≠ d → ((DirectSum.decompose 𝒴 y e : Y)) = 0 := by
    intro e hne
    refine hYtf _ fun b hb => ?_
    have hhom : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → a ∈ J ^ k →
        a • ((DirectSum.decompose 𝒴 y e : Y)) = 0 := by
      intro i a ha haJ
      rw [← coe_decompose_smul_of_mem_graded 𝒜 𝒴 h𝒴 ha e y,
        DirectSum.decompose_of_mem_ne 𝒴 (hy i a ha haJ) (fun h => hne (by omega))]
    have hbsum : b = ∑ i ∈ (DirectSum.decompose 𝒜 b).support,
        ((DirectSum.decompose 𝒜 b i : A)) := (DirectSum.sum_support_decompose 𝒜 b).symm
    rw [hbsum, Finset.sum_smul]
    exact Finset.sum_eq_zero fun i _ => hhom i _ (DirectSum.decompose 𝒜 b i).2 (hJ i hb)
  have hyd : y = ((DirectSum.decompose 𝒴 y d : Y)) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒴 y]
    by_cases hd : d ∈ (DirectSum.decompose 𝒴 y).support
    · exact Finset.sum_eq_single_of_mem d hd fun e _ hne => hzero e hne
    · rw [DFinsupp.notMem_support_iff.1 hd, ZeroMemClass.coe_zero]
      exact Finset.sum_eq_zero fun e he => hzero e fun h => hd (h ▸ he)
  rw [hyd]
  exact (DirectSum.decompose 𝒴 y d).2

end TorsionFree

end DirectSum

namespace Submodule

/-! ### Homogeneity facts -/

section Homog

variable {A : Type u} [CommRing A] {σA : Type w} [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℕ → σA) [GradedRing 𝒜]
  {M : Type v} [AddCommGroup M] [Module A M] {σM : Type t} [SetLike σM M]
  [AddSubgroupClass σM M] (ℳ : ℤ → σM) [DirectSum.Decomposition ℳ]

/-- The kernel of a degree-preserving linear map is a homogeneous submodule. -/
public theorem isHomogeneous_ker {N : Type v} [AddCommGroup N] [Module A N] {σN : Type t}
    [SetLike σN N] [AddSubgroupClass σN N] (𝒩 : ℤ → σN) [DirectSum.Decomposition 𝒩]
    (f : M →ₗ[A] N) (hf : ∀ (d : ℤ) (x : M), x ∈ ℳ d → f x ∈ 𝒩 d) :
    (LinearMap.ker f).IsHomogeneous ℳ := by
  intro d x hx
  rw [LinearMap.mem_ker] at hx
  have h := DirectSum.coe_decompose_apply_of_mem_graded ℳ 𝒩 f.toAddMonoidHom hf d x
  rw [LinearMap.mem_ker, show f ((DirectSum.decompose ℳ x d : M)) =
    ((DirectSum.decompose 𝒩 (f x) d : N)) from h.symm, hx]
  simp

/-- The supremum of two homogeneous submodules is homogeneous. -/
public theorem IsHomogeneous.sup {p q : Submodule A M} (hp : p.IsHomogeneous ℳ)
    (hq : q.IsHomogeneous ℳ) : (p ⊔ q).IsHomogeneous ℳ := by
  intro d x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [DirectSum.decompose_add, DFinsupp.add_apply, AddMemClass.coe_add]
  exact Submodule.add_mem_sup (hp d hy) (hq d hz)

/-- A power of a homogeneous ideal is homogeneous. -/
public theorem _root_.Ideal.IsHomogeneous.pow {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (n : ℕ) :
    (J ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero => simpa using Ideal.IsHomogeneous.top 𝒜
  | succ n ih => rw [pow_succ]; exact ih.mul hJ

/-- **`J • ⊤` is homogeneous for a homogeneous ideal `J`.** -/
public theorem isHomogeneous_smul_top
    (hℳ : ∀ (i : ℕ) (d : ℤ) (a : A) (x : M), a ∈ 𝒜 i → x ∈ ℳ d → a • x ∈ ℳ ((i : ℤ) + d))
    {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) :
    (J • (⊤ : Submodule A M)).IsHomogeneous ℳ := by
  classical
  intro d y hy
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha x _
    rw [← DirectSum.sum_support_decompose 𝒜 a, ← DirectSum.sum_support_decompose ℳ x,
      Finset.sum_smul_sum, ← Finset.sum_product',
      coe_decompose_sum_of_mem_graded ℳ _ _ (fun p => (p.1 : ℤ) + p.2) fun p _ =>
        hℳ _ _ _ _ (DirectSum.decompose 𝒜 a p.1).2 (DirectSum.decompose ℳ x p.2).2]
    refine Submodule.sum_mem _ fun p _ => ?_
    split_ifs with hd
    · exact Submodule.smul_mem_smul (hJ p.1 ha) Submodule.mem_top
    · exact zero_mem _
  · intro u v hu hv
    rw [DirectSum.decompose_add, DFinsupp.add_apply, AddMemClass.coe_add]
    exact add_mem hu hv

end Homog

/-! ### The grading of a quotient -/

section Quot

variable {A : Type u} [CommRing A] {σA : Type w} [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℕ → σA) [GradedRing 𝒜]
  {M : Type v} [AddCommGroup M] [Module A M] {σM : Type t} [SetLike σM M]
  [AddSubgroupClass σM M] (ℳ : ℤ → σM) [DirectSum.Decomposition ℳ]

/-- **The degree-`d` part of `M ⧸ K`**: the image of the degree-`d` part of `M`. -/
public def gradedQuotientPiece (K : Submodule A M) (d : ℤ) : AddSubgroup (M ⧸ K) where
  carrier := {z | ∃ x ∈ ℳ d, K.mkQ x = z}
  zero_mem' := ⟨0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, add_mem hx hy, by rw [map_add]⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, neg_mem hx, by rw [map_neg]⟩

omit [DirectSum.Decomposition ℳ] in
/-- The image in `M ⧸ K` of an element of degree `d` lies in the degree-`d` part of `M ⧸ K`. -/
public theorem mkQ_mem_gradedQuotientPiece {K : Submodule A M} {d : ℤ} {x : M} (hx : x ∈ ℳ d) :
    K.mkQ x ∈ gradedQuotientPiece ℳ K d :=
  ⟨x, hx, rfl⟩

/-- **The quotient by a homogeneous submodule is the direct sum of its graded pieces.** -/
public theorem isInternal_gradedQuotientPiece {K : Submodule A M} (hK : K.IsHomogeneous ℳ) :
    DirectSum.IsInternal (gradedQuotientPiece ℳ K) := by
  classical
  refine DirectSum.isInternal_of_eq_zero_of_exists_sum _ ?_ ?_
  · intro s y hy hsum d₀ hd₀
    have hex : ∀ d ∈ s, ∃ x : M, x ∈ ℳ d ∧ K.mkQ x = y d := fun d hd => hy d hd
    choose! x hx hxy using hex
    have hmem : (∑ d ∈ s, x d) ∈ K := by
      rw [← Submodule.ker_mkQ K, LinearMap.mem_ker, map_sum,
        Finset.sum_congr rfl fun d hd => hxy d hd, hsum]
    have hcomp : ((DirectSum.decompose ℳ (∑ d ∈ s, x d) d₀ : M)) = x d₀ := by
      rw [coe_decompose_sum_of_mem_graded ℳ s x id hx]
      simp [Finset.sum_ite_eq', hd₀]
    rw [← hxy d₀ hd₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcomp ▸ hK d₀ hmem
  · intro z
    obtain ⟨x, rfl⟩ := K.mkQ_surjective z
    refine ⟨(DirectSum.decompose ℳ x).support, fun d => K.mkQ ((DirectSum.decompose ℳ x d : M)),
      fun d => mkQ_mem_gradedQuotientPiece ℳ (DirectSum.decompose ℳ x d).2, fun d hd => ?_, ?_⟩
    · change K.mkQ ((DirectSum.decompose ℳ x d : M)) = 0
      rw [DFinsupp.notMem_support_iff.1 hd, ZeroMemClass.coe_zero, map_zero]
    · rw [← map_sum, DirectSum.sum_support_decompose ℳ x]

omit [AddSubgroupClass σA A] [GradedRing 𝒜] [DirectSum.Decomposition ℳ] in
/-- The quotient grading is compatible with the grading of `A`. -/
public theorem smul_mem_gradedQuotientPiece
    (hℳ : ∀ (i : ℕ) (d : ℤ) (a : A) (x : M), a ∈ 𝒜 i → x ∈ ℳ d → a • x ∈ ℳ ((i : ℤ) + d))
    (K : Submodule A M) {i : ℕ} {d : ℤ} {a : A} (ha : a ∈ 𝒜 i) {z : M ⧸ K}
    (hz : z ∈ gradedQuotientPiece ℳ K d) :
    a • z ∈ gradedQuotientPiece ℳ K ((i : ℤ) + d) := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨a • x, hℳ i d a x ha hx, by rw [map_smul]⟩

end Quot

end Submodule

end
