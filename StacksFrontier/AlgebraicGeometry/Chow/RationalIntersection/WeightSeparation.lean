module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import StacksFrontier.LinearAlgebra.AevalIntertwine

/-!
# Separating weights of an endomorphism over a Noetherian space

Let `T` be a Noetherian topological space and let `G` assign to every closed subset `Z ⊆ T` a
`ℚ`-vector space `G(Z)`, functorially in `Z` for inclusions, together with a natural endomorphism
`Ψ` of `G`. Let `w : T → ℤ` be a weight function and `μ : ℤ → ℚ` an injective function. Suppose
`G(∅) = 0` and that, on every nonempty closed `Z`, the endomorphism `Ψ` acts on each element `x`
as a scalar `μ (w z₀)`, for some `z₀ ∈ Z`, modulo the image of `G(Z')` for some closed `Z' ⊊ Z`.
Then an element of `G(T)` which, for every bound `c`, comes from closed subsets on which the weight
is at least `c`, is zero.

The argument has two steps.

* By Noetherian induction on `Z`, every `x ∈ G(Z)` is killed by `∏_{n ∈ s} (Ψ - μ n)` for a finite
  multiset `s` of weights of points of `Z`: if `(Ψ - μ (w z₀)) x` is the image of `y ∈ G(Z')`,
  and `y` is killed by such a product over `Z'`, then by naturality `x` is killed by the product
  with the extra factor `Ψ - μ (w z₀)`.
* Products of linear factors `X - μ n` over disjoint sets of weights are coprime, since `μ` is
  injective. Choosing `c` above every weight of the multiset attached to `x ∈ G(T)`, the
  hypothesis makes `x` a sum of images of elements killed by products over weights `≥ c`, hence
  killed by a single such product. The two coprime polynomials both kill `x`, so `x = 0`.

## Main results

* `Stacks.Chow.WeightSeparation.exists_multiset_aeval_eq_zero`: every element of `G(Z)` is killed
  by a product of factors `Ψ - μ n` over weights `n` of points of `Z`.
* `Stacks.Chow.WeightSeparation.isCoprime_multiset_prod_X_sub_C`: products of linear factors over
  disjoint sets of indices are coprime.
* `Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup`: an element of `G(T)` coming from
  closed subsets of arbitrarily large weight is zero.
* `Stacks.Chow.WeightSeparation.exists_multiset_aeval_eq_zero_of_exists_multiset` and
  `Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup_of_exists_multiset`: the same when each
  step kills an element, modulo smaller supports, by a product of several factors `Ψ - μ n`; the
  single-factor statements above are their special cases.
-/

@[expose] public section

universe v

namespace Stacks.Chow.WeightSeparation

open CategoryTheory TopologicalSpace Polynomial

/-- Products of linear factors `X - μ n` over multisets of indices with no common element are
coprime, when `μ` is injective. -/
theorem isCoprime_multiset_prod_X_sub_C {K ι : Type*} [Field K] {μ : ι → K}
    (hμ : Function.Injective μ) {s t : Multiset ι} (hst : ∀ a ∈ s, ∀ b ∈ t, a ≠ b) :
    IsCoprime (s.map fun n => X - C (μ n)).prod (t.map fun n => X - C (μ n)).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isCoprime_one_left
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine IsCoprime.mul_left ?_ (ih fun a' ha' b hb => hst a' (Multiset.mem_cons_of_mem ha') b hb)
    have ha : ∀ b ∈ t, a ≠ b := hst a (Multiset.mem_cons_self a s)
    clear ih hst
    induction t using Multiset.induction_on with
    | empty => simpa using isCoprime_one_right
    | cons b t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact IsCoprime.mul_right
        (pairwise_coprime_X_sub_C hμ (ha b (Multiset.mem_cons_self b t)))
        (ih fun b' hb' => ha b' (Multiset.mem_cons_of_mem hb'))

/-- A vector killed by two products of linear factors `f - μ n` of an endomorphism `f`, over
multisets of indices with no common element, is zero, when `μ` is injective. -/
theorem eq_zero_of_aeval_multiset_prod_eq_zero {K ι : Type*} [Field K] {μ : ι → K}
    (hμ : Function.Injective μ) {V : Type*} [AddCommGroup V] [Module K V] (f : Module.End K V)
    {s t : Multiset ι} (hst : ∀ a ∈ s, ∀ b ∈ t, a ≠ b) {v : V}
    (hs : aeval f (s.map fun n => X - C (μ n)).prod v = 0)
    (ht : aeval f (t.map fun n => X - C (μ n)).prod v = 0) : v = 0 :=
  Submodule.disjoint_def.1
    (disjoint_ker_aeval_of_isCoprime f (isCoprime_multiset_prod_X_sub_C hμ hst)) v hs ht

variable {T : Type*} [TopologicalSpace T] {G : Closeds T ⥤ ModuleCat.{v} ℚ} (Ψ : G ⟶ G)

/-- Naturality of `Ψ` makes the evaluation of a polynomial at `Ψ` commute with the maps of `G`. -/
theorem map_aeval_app {Z' Z : Closeds T} (h : Z' ≤ Z) (p : ℚ[X]) (y : G.obj Z') :
    (G.map (homOfLE h)).hom (aeval (Ψ.app Z').hom p y) =
      aeval (Ψ.app Z).hom p ((G.map (homOfLE h)).hom y) :=
  LinearMap.apply_aeval_of_apply_eq (fun v => by simp) p y

variable [NoetherianSpace T] {w : T → ℤ} {μ : ℤ → ℚ}

/-- The product over a sum of multisets applies the factors of each summand in turn. -/
private theorem aeval_multiset_add_prod {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : Module.End ℚ V) (s t : Multiset ℤ) (v : V) :
    aeval f ((s + t).map fun n => X - C (μ n)).prod v =
      aeval f (t.map fun n => X - C (μ n)).prod (aeval f (s.map fun n => X - C (μ n)).prod v) := by
  rw [Multiset.map_add, Multiset.prod_add, mul_comm, map_mul, Module.End.mul_apply]

/-- Every element `x` of `G(Z)` is killed by a product `∏_{n ∈ s} (Ψ - μ n)` over a multiset `s` of
weights of points of `Z`, provided `G(∅) = 0` and each element of `G(Z)`, `Z ≠ ∅`, is killed modulo
the image of `G(Z')`, for a closed `Z' ⊊ Z`, by such a product over weights of points of `Z`.
Its case of a single factor at each step is
`Stacks.Chow.WeightSeparation.exists_multiset_aeval_eq_zero`. -/
theorem exists_multiset_aeval_eq_zero_of_exists_multiset (h0 : Subsingleton (G.obj ⊥))
    (hP : ∀ (Z : Closeds T) (x : G.obj Z), Z ≠ ⊥ → ∃ s : Multiset ℤ,
      (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧ ∃ (Z' : Closeds T) (h : Z' < Z),
        aeval (Ψ.app Z).hom (s.map fun n => X - C (μ n)).prod x ∈
          LinearMap.range (G.map (homOfLE h.le)).hom)
    (Z : Closeds T) (x : G.obj Z) :
    ∃ s : Multiset ℤ, (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧
      aeval (Ψ.app Z).hom (s.map fun n => X - C (μ n)).prod x = 0 := by
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
    by_cases hZ : Z = ⊥
    · subst hZ
      exact ⟨0, by simp, by simp [Subsingleton.elim x 0]⟩
    obtain ⟨s₀, hs₀w, Z', hZ', y, hy⟩ := hP Z x hZ
    obtain ⟨s', hs'w, hs'⟩ := ih Z' hZ' y
    refine ⟨s₀ + s', fun n hn => ?_, ?_⟩
    · rcases Multiset.mem_add.1 hn with hn | hn
      · exact hs₀w n hn
      · obtain ⟨z, hz, rfl⟩ := hs'w n hn
        exact ⟨z, hZ'.le hz, rfl⟩
    · rw [aeval_multiset_add_prod, ← hy, ← map_aeval_app, hs', map_zero]

/-- **Separation of weights, several factors at each step.** An element `x` of `G(T)` which, for
every `c : ℤ`, lies in the span of the images of the `G(Z)` over closed `Z` on which the weight
`w` is at least `c`, is zero; here `G(∅) = 0`, `μ` is injective, and each element of `G(Z)`,
`Z ≠ ∅`, is killed modulo the image of `G(Z')`, for a closed `Z' ⊊ Z`, by a product of factors
`Ψ - μ n` over weights `n` of points of `Z`. Its case of a single factor at each step is
`Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup`. -/
theorem eq_zero_of_forall_mem_iSup_of_exists_multiset (hμ : Function.Injective μ)
    (h0 : Subsingleton (G.obj ⊥))
    (hP : ∀ (Z : Closeds T) (x : G.obj Z), Z ≠ ⊥ → ∃ s : Multiset ℤ,
      (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧ ∃ (Z' : Closeds T) (h : Z' < Z),
        aeval (Ψ.app Z).hom (s.map fun n => X - C (μ n)).prod x ∈
          LinearMap.range (G.map (homOfLE h.le)).hom)
    (x : G.obj ⊤)
    (hx : ∀ c : ℤ, x ∈ ⨆ (Z : Closeds T) (_ : ∀ z ∈ Z, c ≤ w z),
      LinearMap.range (G.map (homOfLE (le_top : Z ≤ ⊤))).hom) :
    x = 0 := by
  obtain ⟨s, -, hs⟩ := exists_multiset_aeval_eq_zero_of_exists_multiset Ψ h0 hP ⊤ x
  obtain ⟨b, hb⟩ := s.toFinset.bddAbove
  -- the elements killed by a product of factors `Ψ - μ n` with `n > b`
  let K : Submodule ℚ (G.obj ⊤) :=
    { carrier := {v | ∃ t : Multiset ℤ, (∀ n ∈ t, b < n) ∧
        aeval (Ψ.app ⊤).hom (t.map fun n => X - C (μ n)).prod v = 0}
      add_mem' := by
        rintro v₁ v₂ ⟨t₁, ht₁, hv₁⟩ ⟨t₂, ht₂, hv₂⟩
        refine ⟨t₁ + t₂, fun n hn => (Multiset.mem_add.1 hn).elim (ht₁ n) (ht₂ n), ?_⟩
        rw [map_add, aeval_multiset_add_prod, hv₁, map_zero, add_comm t₁ t₂,
          aeval_multiset_add_prod, hv₂, map_zero, add_zero]
      zero_mem' := ⟨0, by simp, map_zero _⟩
      smul_mem' := by
        rintro a v ⟨t, ht, hv⟩
        exact ⟨t, ht, by rw [map_smul, hv, smul_zero]⟩ }
  have hle : (⨆ (Z : Closeds T) (_ : ∀ z ∈ Z, b + 1 ≤ w z),
      LinearMap.range (G.map (homOfLE (le_top : Z ≤ ⊤))).hom) ≤ K := by
    refine iSup₂_le fun Z hZ => ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨t, htw, ht⟩ := exists_multiset_aeval_eq_zero_of_exists_multiset Ψ h0 hP Z y
    refine ⟨t, fun n hn => ?_, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := htw n hn
      exact Int.lt_of_add_one_le (hZ z hz)
    · rw [← map_aeval_app, ht, map_zero]
  obtain ⟨t, ht, hxt⟩ := hle (hx (b + 1))
  refine eq_zero_of_aeval_multiset_prod_eq_zero hμ _ (fun a ha n hn => ?_) hs hxt
  exact ((hb (Multiset.mem_toFinset.2 ha)).trans_lt (ht n hn)).ne

omit [NoetherianSpace T] in
/-- A single factor `Ψ - μ (w z₀)` is the product over the one-point multiset `{w z₀}`. -/
private theorem aeval_singleton_eq (Z : Closeds T) (x : G.obj Z) (n : ℤ) :
    aeval (Ψ.app Z).hom (({n} : Multiset ℤ).map fun n => X - C (μ n)).prod x =
      (Ψ.app Z).hom x - μ n • x := by
  simp [Algebra.algebraMap_eq_smul_one]

omit [NoetherianSpace T] in
private theorem exists_multiset_of_exists_point
    (hP : ∀ (Z : Closeds T) (x : G.obj Z), Z ≠ ⊥ → ∃ z₀ ∈ Z, ∃ (Z' : Closeds T) (h : Z' < Z),
      (Ψ.app Z).hom x - μ (w z₀) • x ∈ LinearMap.range (G.map (homOfLE h.le)).hom)
    (Z : Closeds T) (x : G.obj Z) (hZ : Z ≠ ⊥) : ∃ s : Multiset ℤ,
      (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧ ∃ (Z' : Closeds T) (h : Z' < Z),
        aeval (Ψ.app Z).hom (s.map fun n => X - C (μ n)).prod x ∈
          LinearMap.range (G.map (homOfLE h.le)).hom := by
  obtain ⟨z₀, hz₀, Z', h, hx⟩ := hP Z x hZ
  exact ⟨{w z₀}, fun n hn => ⟨z₀, hz₀, (Multiset.mem_singleton.1 hn).symm⟩, Z', h,
    (aeval_singleton_eq Ψ Z x _).symm ▸ hx⟩

/-- Every element `x` of `G(Z)` is killed by a product `∏_{n ∈ s} (Ψ - μ n)` over a multiset `s` of
weights of points of `Z`, provided `G(∅) = 0` and `Ψ` acts on each element of `G(Z)`, `Z ≠ ∅`, as a
scalar `μ (w z₀)`, `z₀ ∈ Z`, modulo the image of `G(Z')` for a closed `Z' ⊊ Z`: the case of
`Stacks.Chow.WeightSeparation.exists_multiset_aeval_eq_zero_of_exists_multiset` with one factor
at each step. -/
theorem exists_multiset_aeval_eq_zero (h0 : Subsingleton (G.obj ⊥))
    (hP : ∀ (Z : Closeds T) (x : G.obj Z), Z ≠ ⊥ → ∃ z₀ ∈ Z, ∃ (Z' : Closeds T) (h : Z' < Z),
      (Ψ.app Z).hom x - μ (w z₀) • x ∈ LinearMap.range (G.map (homOfLE h.le)).hom)
    (Z : Closeds T) (x : G.obj Z) :
    ∃ s : Multiset ℤ, (∀ n ∈ s, ∃ z ∈ Z, w z = n) ∧
      aeval (Ψ.app Z).hom (s.map fun n => X - C (μ n)).prod x = 0 :=
  exists_multiset_aeval_eq_zero_of_exists_multiset Ψ h0 (exists_multiset_of_exists_point Ψ hP) Z x

/-- An element `x` of `G(T)` which, for every `c : ℤ`, lies in the span of the images of the
`G(Z)` over closed `Z` on which the weight `w` is at least `c`, is zero; here `G(∅) = 0`, `μ` is
injective, and `Ψ` acts on each element of `G(Z)`, `Z ≠ ∅`, as a scalar `μ (w z₀)`, `z₀ ∈ Z`,
modulo the image of `G(Z')` for a closed `Z' ⊊ Z`: the case of
`Stacks.Chow.WeightSeparation.eq_zero_of_forall_mem_iSup_of_exists_multiset` with one factor at
each step. -/
theorem eq_zero_of_forall_mem_iSup (hμ : Function.Injective μ) (h0 : Subsingleton (G.obj ⊥))
    (hP : ∀ (Z : Closeds T) (x : G.obj Z), Z ≠ ⊥ → ∃ z₀ ∈ Z, ∃ (Z' : Closeds T) (h : Z' < Z),
      (Ψ.app Z).hom x - μ (w z₀) • x ∈ LinearMap.range (G.map (homOfLE h.le)).hom)
    (x : G.obj ⊤)
    (hx : ∀ c : ℤ, x ∈ ⨆ (Z : Closeds T) (_ : ∀ z ∈ Z, c ≤ w z),
      LinearMap.range (G.map (homOfLE (le_top : Z ≤ ⊤))).hom) :
    x = 0 :=
  eq_zero_of_forall_mem_iSup_of_exists_multiset Ψ hμ h0
    (exists_multiset_of_exists_point Ψ hP) x hx

end Stacks.Chow.WeightSeparation
