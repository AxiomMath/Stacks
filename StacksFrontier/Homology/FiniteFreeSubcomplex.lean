module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

Stacks Tag 0FNR (Lemma 15.128.2).

Throughout, `R` is a commutative unital ring and we work with cochain complexes of
`R`-modules indexed by `ℤ`, with differentials raising the degree by one.

Definition 1 (Cochain complex of `R`-modules). A complex `F^•` is a family `(F^n)_{n ∈ ℤ}`
of `R`-modules together with `R`-linear differentials `d_F^n : F^n → F^{n+1}` satisfying
`d_F^{n+1} ∘ d_F^n = 0` for all `n`.

Definition 2 (Subcomplex). A subcomplex `G^• ⊆ F^•` is a family `(G^n)` of `R`-submodules
`G^n ⊆ F^n` such that `d_F^n(G^n) ⊆ G^{n+1}` for all `n`. With the restricted differentials,
`G^•` is itself a complex.

Definition 3 (Bounded above complex). `F^•` is bounded above if there exists `b` with
`F^n = 0` for all `n > b`.

Definition 4 (Bounded complex). `G^•` is bounded if there exist `a ≤ b` with `G^n = 0` for
all `n < a` or `n > b`.

Definition 5/6 (Free / finite free). An `R`-module is free if it admits a basis; finite free
if it is isomorphic to `R^{⊕m}` for some `m ≥ 0`. A complex consists of (finite) free modules
if each term is (finite) free.

Main Statement. Let `F^•` be a bounded above complex of free `R`-modules. Let `N ≥ 0` and let
`(n_i, f_i)` for `i = 1, …, N` be given pairs with `n_i ∈ ℤ` and `f_i ∈ F^{n_i}`. Then there is
a subcomplex `G^• ⊆ F^•` such that (1) `f_i ∈ G^{n_i}` for every `i`; (2) `G^•` is bounded; and
(3) `G^•` consists of finite free `R`-modules.
-/

/-
## Notes on Interpretation

- The source says "ring", meaning a commutative ring with identity. Commutativity is never
  used, so everything below is stated for an arbitrary unital ring `R`.
- `N` may be `0`: with no constraints, the zero subcomplex works.
- "Finite free" means free of finite rank; the zero module (`m = 0`) is finite free.
- A module being "zero" is encoded as the type being `Subsingleton` (equivalently, the
  submodule being `⊥`).
- We model the finite family of pairs `(n_i, f_i)` by an index type `Fin N`, a function
  `n : Fin N → ℤ`, and a dependent function `f : ∀ i, F^{n i}`.
-/

universe u

-- Main Definition(s)

/-- Definition 1. A cochain complex of `R`-modules indexed by `ℤ`, with differentials raising
the degree by one and squaring to zero. -/
@[ega "0 11.2.1" "special case", ega "0 13.2.3", sga "4 XVII 0.4" "special case"]
structure ZComplex (R : Type u) [Ring R] where
  /-- The `R`-module in degree `n`. -/
  obj : ℤ → Type u
  /-- The additive group structure on `F^n`. -/
  addCommGroup : ∀ n, AddCommGroup (obj n)
  /-- The `R`-module structure on `F^n`. -/
  module : ∀ n, Module R (obj n)
  /-- The differential `d^n : F^n → F^{n+1}`. -/
  d : ∀ n, obj n →ₗ[R] obj (n + 1)
  /-- `d^{n+1} ∘ d^n = 0`. -/
  d_comp_d : ∀ n, ∀ x : obj n, d (n + 1) (d n x) = 0

attribute [instance] ZComplex.addCommGroup ZComplex.module

variable {R : Type u} [Ring R]

/-- Definition 2. A subcomplex of a complex `F`: a family of `R`-submodules `G^n ⊆ F^n`
closed under the differentials, i.e. `d_F^n(G^n) ⊆ G^{n+1}`. -/
structure ZComplex.Subcomplex (F : ZComplex R) where
  /-- The submodule of `F^n` in degree `n`. -/
  carrier : ∀ n, Submodule R (F.obj n)
  /-- The differential maps `G^n` into `G^{n+1}`. -/
  d_mem : ∀ n, ∀ x : F.obj n, x ∈ carrier n → F.d n x ∈ carrier (n + 1)

/-- The restricted differential of a subcomplex, as an `R`-linear map between the carriers. -/
def ZComplex.Subcomplex.d {F : ZComplex R} (G : F.Subcomplex) (n : ℤ) :
    G.carrier n →ₗ[R] G.carrier (n + 1) :=
  (F.d n).restrict (fun x hx => G.d_mem n x hx)

/-- The restricted differential of a subcomplex agrees with the ambient differential. -/
@[simp] theorem ZComplex.Subcomplex.coe_d {F : ZComplex R} (G : F.Subcomplex) (n : ℤ)
    (x : G.carrier n) : (G.d n x : F.obj (n + 1)) = F.d n x := rfl

/-- The restricted differential of a subcomplex squares to zero. -/
theorem ZComplex.Subcomplex.d_comp_d {F : ZComplex R} (G : F.Subcomplex) (n : ℤ)
    (x : G.carrier n) : G.d (n + 1) (G.d n x) = 0 := by
  ext
  exact F.d_comp_d n (x : F.obj n)

/-- A subcomplex, regarded as a complex in its own right via the restricted differentials. -/
def ZComplex.Subcomplex.toZComplex {F : ZComplex R} (G : F.Subcomplex) : ZComplex R where
  obj n := G.carrier n
  addCommGroup _ := inferInstance
  module _ := inferInstance
  d := G.d
  d_comp_d := G.d_comp_d

/-- Definition 3. A complex `F` is bounded above if there is `b` with `F^n = 0` (i.e. trivial)
for all `n > b`. -/
@[ega "0 11.2.1" "bounded above", sga "4½ Etat_0 1.2.3" "special case"]
def ZComplex.BoundedAbove (F : ZComplex R) : Prop :=
  ∃ b : ℤ, ∀ n : ℤ, b < n → Subsingleton (F.obj n)

/-- Definition 6 (free version). A complex `F` consists of free `R`-modules if each `F^n` is a
free `R`-module. -/
def ZComplex.IsFree (F : ZComplex R) : Prop :=
  ∀ n : ℤ, Module.Free R (F.obj n)

/-- Definition 4. A subcomplex `G` is bounded if its carrier is `0` (`= ⊥`) outside a finite
range `[a, b]`. -/
@[sga "4½ Etat_0 1.2.3" "special case"]
def ZComplex.Subcomplex.Bounded {F : ZComplex R} (G : F.Subcomplex) : Prop :=
  ∃ a b : ℤ, ∀ n : ℤ, (n < a ∨ b < n) → G.carrier n = ⊥

/-- Definition 6 (finite free version). A subcomplex `G` consists of finite free `R`-modules if
each `G^n` is a finite free `R`-module. -/
def ZComplex.Subcomplex.FiniteFree {F : ZComplex R} (G : F.Subcomplex) : Prop :=
  ∀ n : ℤ, Module.Free R (G.carrier n) ∧ Module.Finite R (G.carrier n)


@[deprecated (since := "2026-09-27"), ega "0 11.2.1" "bounded above"]
alias ZComplex.IsBoundedAbove := ZComplex.BoundedAbove

@[deprecated (since := "2026-09-27")]
alias ZComplex.Subcomplex.IsBounded := ZComplex.Subcomplex.Bounded

@[deprecated (since := "2026-09-27")]
alias ZComplex.Subcomplex.IsFiniteFree := ZComplex.Subcomplex.FiniteFree
/-- A bounded above complex admits a bound beyond which every term is trivial. -/
theorem ZComplex.BoundedAbove.exists_bound {F : ZComplex R} (h : F.BoundedAbove) :
    ∃ b : ℤ, ∀ n : ℤ, b < n → Subsingleton (F.obj n) := h

/-- A complex of free modules is free in each degree. -/
theorem ZComplex.IsFree.free {F : ZComplex R} (h : F.IsFree) (n : ℤ) :
    Module.Free R (F.obj n) := h n

/-- A bounded subcomplex admits a range outside of which its carrier vanishes. -/
theorem ZComplex.Subcomplex.Bounded.exists_bounds {F : ZComplex R} {G : F.Subcomplex}
    (h : G.Bounded) : ∃ a b : ℤ, ∀ n : ℤ, (n < a ∨ b < n) → G.carrier n = ⊥ := h

/-- Each term of a finite free subcomplex is a free module. -/
theorem ZComplex.Subcomplex.FiniteFree.free {F : ZComplex R} {G : F.Subcomplex}
    (h : G.FiniteFree) (n : ℤ) : Module.Free R (G.carrier n) := (h n).1

/-- Each term of a finite free subcomplex is a finite module. -/
theorem ZComplex.Subcomplex.FiniteFree.finite {F : ZComplex R} {G : F.Subcomplex}
    (h : G.FiniteFree) (n : ℤ) : Module.Finite R (G.carrier n) := (h n).2

-- Auxiliary constructions for the proof of `exists_subcomplex_bounded_finiteFree`.

namespace Stacks.FiniteFreeSubcomplex

open Module

/-- The span of a subfamily of a basis is a free module. -/
theorem free_span_image {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}
    (b : Basis ι R M) (s : Set ι) : Module.Free R (Submodule.span R (b '' s)) := by
  rw [Set.image_eq_range]
  exact Module.Free.of_basis (Basis.span (b.linearIndepOn s).linearIndependent)

/-- If the `c`-basis support of `d (b j)` is contained in `s'` for every `j ∈ s`, then `d` maps
`span R (b '' s)` into `span R (c '' s')`. -/
theorem map_mem_span_image_of_support_subset {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ιM ιN : Type*} (b : Basis ιM R M) (c : Basis ιN R N)
    (d : M →ₗ[R] N) {s : Set ιM} {s' : Set ιN}
    (hclose : ∀ j ∈ s, ↑(c.repr (d (b j))).support ⊆ s')
    {x : M} (hx : x ∈ Submodule.span R (b '' s)) :
    d x ∈ Submodule.span R (c '' s') := by
  have hmap : Submodule.map d (Submodule.span R (b '' s)) ≤ Submodule.span R (c '' s') := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro y ⟨z, ⟨j, hj, rfl⟩, rfl⟩
    exact c.mem_span_image.2 (hclose j hj)
  exact hmap (Submodule.mem_map_of_mem hx)

/-- In a subsingleton module every element has empty support with respect to any basis. -/
theorem repr_support_eq_empty {M ι : Type*} [AddCommGroup M] [Module R M] [Subsingleton M]
    (b : Basis ι R M) (x : M) : (b.repr x).support = ∅ := by
  rw [Subsingleton.elim x 0]
  simp

section Closure

variable (F : ZComplex R) [∀ n, Module.Free R (F.obj n)]
  {N : ℕ} (n : Fin N → ℤ) (f : ∀ i, F.obj (n i))

noncomputable section

/-- Chosen basis index type in degree `m`. -/
abbrev BasisIndex (m : ℤ) := Module.Free.ChooseBasisIndex R (F.obj m)
/-- Chosen basis in degree `m`. -/
abbrev chosenBasis (m : ℤ) : Basis (BasisIndex F m) R (F.obj m) :=
  Module.Free.chooseBasis R (F.obj m)
/-- Global basis index, ranging over all degrees. -/
abbrev GradedBasisIndex := Σ m : ℤ, BasisIndex F m

/-- The basis-support, one degree up, of the differential of a basis element. -/
def nextSupport (p : GradedBasisIndex F) : Finset (GradedBasisIndex F) :=
  ((chosenBasis F (p.1 + 1)).repr (F.d p.1 (chosenBasis F p.1 p.2))).support.image
    (fun k => ⟨p.1 + 1, k⟩)

/-- Membership in `nextSupport`. -/
theorem mem_nextSupport {p r : GradedBasisIndex F} : r ∈ nextSupport F p ↔
    ∃ k ∈ ((chosenBasis F (p.1 + 1)).repr (F.d p.1 (chosenBasis F p.1 p.2))).support,
      (⟨p.1 + 1, k⟩ : GradedBasisIndex F) = r := by
  rw [nextSupport, Finset.mem_image]

/-- The seed: basis supports of all the given elements `f i`. -/
def seed : Finset (GradedBasisIndex F) :=
  Finset.univ.biUnion (fun i : Fin N =>
    ((chosenBasis F (n i)).repr (f i)).support.image (fun k => (⟨n i, k⟩ : GradedBasisIndex F)))

/-- Membership in the seed. -/
theorem mem_seed {p : GradedBasisIndex F} : p ∈ seed F n f ↔
    ∃ i : Fin N, ∃ k ∈ ((chosenBasis F (n i)).repr (f i)).support,
      (⟨n i, k⟩ : GradedBasisIndex F) = p := by
  rw [seed, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and, Finset.mem_image]

/-- Iterated closure, starting from the seed: each step adds the next-supports of everything
currently present. -/
def closureIter (k : ℕ) : Finset (GradedBasisIndex F) :=
  Nat.rec (seed F n f) (fun _ C => C ∪ C.biUnion (nextSupport F)) k

/-- The zeroth closure is the seed. -/
@[simp] theorem closureIter_zero : closureIter F n f 0 = seed F n f := rfl
/-- The `(k + 1)`-st closure is one closure step applied to the `k`-th. -/
@[simp] theorem closureIter_succ (k : ℕ) : closureIter F n f (k + 1) =
    closureIter F n f k ∪ (closureIter F n f k).biUnion (nextSupport F) := rfl

/-- Membership in the `(k + 1)`-st closure: either already present, or in the next-support of
something already present. -/
theorem mem_closureIter_succ {k : ℕ} {p : GradedBasisIndex F} : p ∈ closureIter F n f (k + 1) ↔
    p ∈ closureIter F n f k ∨ ∃ q ∈ closureIter F n f k, p ∈ nextSupport F q := by
  rw [closureIter_succ, Finset.mem_union, Finset.mem_biUnion]

/-- The iterated closures form an increasing chain of finite sets. -/
theorem closureIter_mono {k l : ℕ} (h : k ≤ l) : closureIter F n f k ⊆ closureIter F n f l := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- Elements of the next-support of `p` live in degree `p.1 + 1`. -/
private theorem fst_eq_of_mem_nextSupport {p r : GradedBasisIndex F} (h : r ∈ nextSupport F p) :
    r.1 = p.1 + 1 := by
  obtain ⟨_, _, rfl⟩ := (mem_nextSupport F).1 h
  rfl

variable (b0 : ℤ) (hb0 : ∀ m : ℤ, b0 < m → Subsingleton (F.obj m))

include hb0 in
/-- If `F^m` vanishes for `m > b0`, then every index in the `k`-th closure has degree at
most `b0`. -/
theorem fst_le_of_mem_closureIter (k : ℕ) {p : GradedBasisIndex F}
    (hp : p ∈ closureIter F n f k) : p.1 ≤ b0 := by
  have key : ∀ (m : ℤ) (x : F.obj m) (k : BasisIndex F m),
      k ∈ ((chosenBasis F m).repr x).support → m ≤ b0 := by
    intro m x k hk
    by_contra hcon
    push Not at hcon
    have := hb0 _ hcon
    rw [repr_support_eq_empty] at hk
    simp at hk
  induction k generalizing p with
  | zero =>
    rw [closureIter_zero] at hp
    obtain ⟨i, k, hk, rfl⟩ := (mem_seed F n f).1 hp
    exact key _ _ _ hk
  | succ k ih =>
    rcases (mem_closureIter_succ F n f).1 hp with hp | ⟨q, _, hpq⟩
    · exact ih hp
    · obtain ⟨kk, hkk, rfl⟩ := (mem_nextSupport F).1 hpq
      exact key _ _ _ hkk

variable (a : ℤ) (ha : ∀ i, a ≤ n i)

include ha in
/-- If every seed degree `n i` is at least `a`, then every index in the `k`-th closure has degree
at least `a`. -/
theorem le_fst_of_mem_closureIter (k : ℕ) {p : GradedBasisIndex F}
    (hp : p ∈ closureIter F n f k) : a ≤ p.1 := by
  induction k generalizing p with
  | zero =>
    rw [closureIter_zero] at hp
    obtain ⟨i, _, _, rfl⟩ := (mem_seed F n f).1 hp
    exact ha i
  | succ k ih =>
    rcases (mem_closureIter_succ F n f).1 hp with hp | ⟨q, hq, hpq⟩
    · exact ih hp
    · have := ih hq
      have := fst_eq_of_mem_nextSupport F hpq
      omega

include ha in
/-- If every seed degree `n i` is at least `a`, then every index `p` in the `k`-th closure already
lies in the `(p.1 - a).toNat`-th one. -/
theorem mem_closureIter_fst_sub (k : ℕ) {p : GradedBasisIndex F}
    (hp : p ∈ closureIter F n f k) : p ∈ closureIter F n f (p.1 - a).toNat := by
  induction k generalizing p with
  | zero =>
    exact closureIter_mono F n f (Nat.zero_le _) hp
  | succ k ih =>
    rcases (mem_closureIter_succ F n f).1 hp with hp | ⟨q, hq, hpq⟩
    · exact ih hp
    · have hqa : a ≤ q.1 := le_fst_of_mem_closureIter F n f a ha k hq
      have hqearly : q ∈ closureIter F n f (q.1 - a).toNat := ih hq
      have hp2 : p ∈ closureIter F n f ((q.1 - a).toNat + 1) :=
        (mem_closureIter_succ F n f).2 (.inr ⟨q, hqearly, hpq⟩)
      have hp1 := fst_eq_of_mem_nextSupport F hpq
      have : (p.1 - a).toNat = (q.1 - a).toNat + 1 := by omega
      rw [this]
      exact hp2

include ha hb0 in
/-- Under the degree bounds `a ≤ n i` and `F^m = 0` for `m > b0`, the finite set
`closureIter (b0 - a + 1).toNat` is closed under `nextSupport`. -/
theorem nextSupport_subset_closureIter (p : GradedBasisIndex F)
    (hp : p ∈ closureIter F n f (b0 - a + 1).toNat) :
    nextSupport F p ⊆ closureIter F n f (b0 - a + 1).toNat := by
  have hle : p.1 ≤ b0 := fst_le_of_mem_closureIter F n f b0 hb0 _ hp
  have hge : a ≤ p.1 := le_fst_of_mem_closureIter F n f a ha _ hp
  have hearly : p ∈ closureIter F n f (p.1 - a).toNat :=
    mem_closureIter_fst_sub F n f a ha _ hp
  intro r hr
  have hr2 : r ∈ closureIter F n f ((p.1 - a).toNat + 1) :=
    (mem_closureIter_succ F n f).2 (.inr ⟨p, hearly, hr⟩)
  exact closureIter_mono F n f (by omega) hr2

end

end Closure

end Stacks.FiniteFreeSubcomplex

-- Main Statement(s)

/-- **Stacks Tag 0FNR (Lemma 15.128.2).**
Let `R` be a ring and let `F` be a bounded above complex of free `R`-modules. Given a finite
family of pairs `(n i, f i)` (indexed by `i : Fin N`), with `n i ∈ ℤ` and `f i ∈ F^{n i}`,
there exists a subcomplex `G ⊆ F` such that:
1. `f i ∈ G^{n i}` for every `i` (i.e. `G` contains all the `f i`);
2. `G` is bounded; and
3. `G` consists of finite free `R`-modules. -/
@[stacks 0FNR]
theorem exists_subcomplex_bounded_finiteFree (F : ZComplex R) (hFa : F.BoundedAbove) (hFfree :
  F.IsFree)
    {N : ℕ} (n : Fin N → ℤ) (f : ∀ i, F.obj (n i)) :
    ∃ G : F.Subcomplex,
      (∀ i, f i ∈ G.carrier (n i)) ∧ G.Bounded ∧ G.FiniteFree := by
  classical
  have : ∀ m, Module.Free R (F.obj m) := hFfree.free
  obtain ⟨b0, hb0⟩ := hFa.exists_bound
  -- a common lower bound for the seed degrees
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ∀ i, a ≤ n i := Finite.exists_ge n
  set M : ℕ := (b0 - a + 1).toNat
  set C : Finset (Stacks.FiniteFreeSubcomplex.GradedBasisIndex F) :=
    Stacks.FiniteFreeSubcomplex.closureIter F n f M
  -- the finite set of basis indices used in each degree
  set T : ∀ m : ℤ, Finset (Stacks.FiniteFreeSubcomplex.BasisIndex F m) := fun m =>
    C.preimage (fun k => (⟨m, k⟩ : Stacks.FiniteFreeSubcomplex.GradedBasisIndex F))
      (Set.injOn_of_injective sigma_mk_injective)
    with hT
  have hTmem : ∀ (m : ℤ) (k : Stacks.FiniteFreeSubcomplex.BasisIndex F m),
      k ∈ T m ↔ (⟨m, k⟩ : Stacks.FiniteFreeSubcomplex.GradedBasisIndex F) ∈ C := by
    intro m k
    simp [hT, Finset.mem_preimage]
  -- the candidate subcomplex
  refine ⟨{ carrier := fun m => Submodule.span R (Stacks.FiniteFreeSubcomplex.chosenBasis F m '' (T
    m : Set _))
            d_mem := ?_ }, ?_, ?_, ?_⟩
  · -- d_mem
    intro m x hx
    refine Stacks.FiniteFreeSubcomplex.map_mem_span_image_of_support_subset
      (Stacks.FiniteFreeSubcomplex.chosenBasis F m)
      (Stacks.FiniteFreeSubcomplex.chosenBasis F (m + 1)) (F.d m) (fun j hj kk hkk => ?_) hx
    change kk ∈ T (m + 1)
    rw [hTmem (m + 1) kk]
    exact Stacks.FiniteFreeSubcomplex.nextSupport_subset_closureIter F n f b0 hb0 a ha ⟨m, j⟩
      ((hTmem m j).1 hj)
      ((Stacks.FiniteFreeSubcomplex.mem_nextSupport F).2 ⟨kk, hkk, rfl⟩)
  · -- contains f i
    intro i
    refine (Stacks.FiniteFreeSubcomplex.chosenBasis F (n i)).mem_span_image.2
      (Finset.coe_subset.2 fun kk hkk => ?_)
    rw [hTmem (n i) kk]
    refine Stacks.FiniteFreeSubcomplex.closureIter_mono F n f (Nat.zero_le _) ?_
    rw [Stacks.FiniteFreeSubcomplex.closureIter_zero]
    exact (Stacks.FiniteFreeSubcomplex.mem_seed F n f).2 ⟨i, kk, hkk, rfl⟩
  · -- bounded
    refine ⟨a, b0, fun m hm => ?_⟩
    have hTe : T m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      rw [hTmem m k] at hk
      have h1 : a ≤ m := Stacks.FiniteFreeSubcomplex.le_fst_of_mem_closureIter F n f a ha M hk
      have h2 : m ≤ b0 := Stacks.FiniteFreeSubcomplex.fst_le_of_mem_closureIter F n f b0 hb0 M hk
      omega
    simp only [hTe, Finset.coe_empty, Set.image_empty, Submodule.span_empty]
  · -- finite free
    intro m
    exact ⟨Stacks.FiniteFreeSubcomplex.free_span_image (Stacks.FiniteFreeSubcomplex.chosenBasis F m)
      _,
      Module.Finite.span_of_finite R ((T m).finite_toSet.image _)⟩
