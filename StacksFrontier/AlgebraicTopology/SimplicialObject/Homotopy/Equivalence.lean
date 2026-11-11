module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import StacksFrontier.AlgebraicTopology.CechNerve
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic

/-!
# Homotopies

Let `C` be a category and let `U`, `V` be simplicial objects of `C`. A *homotopy* from
`a : U ⟶ V` to `b : U ⟶ V` is, in the combinatorial form of [Stacks, Tag 019M], a family of
morphisms `h_{n, i} : Uₙ ⟶ Vₙ` subject to the relations of [Stacks, Tag 019L]; `a` and `b` are
*homotopic* when they are related by the equivalence relation those generate, and `a` is a
*homotopy equivalence* when it has a homotopy inverse ([Stacks, Tag 019N]). When `C` has the
relevant coproducts a homotopy is the same thing as a morphism `U × Δ[1] ⟶ V`
([Stacks, Tag 019K]); the combinatorial form needs no coproducts.

The cylinder `U × Δ[1]` on a simplicial object is homotopy equivalent to `U`: the projection
`π : U × Δ[1] ⟶ U` has either vertex inclusion `e₀, e₁ : U ⟶ U × Δ[1]` as a homotopy inverse.

A self map of a Čech nerve which is the identity on the base is homotopic to the identity. In
particular, for an arrow `f : Y ⟶ X` with a section `s`, the self map given by `s ∘ f` on each
factor is homotopic to the identity, and the Čech nerve of `f` is homotopy equivalent to the
constant simplicial object `X` through its augmentation ([Stacks, Tag 019P]).

The standard simplex `Δ[m]` is homotopy equivalent to `Δ[0]`, by the contraction onto its
last vertex: the morphism `Δ[m] ⊗ Δ[1] ⟶ Δ[m]` sending a pair `(φ, α)` to
`k ↦ if α k = 0 then φ k else m`.

Homotopies and homotopy equivalences are stable under products: for degreewise products
`P = ∏_t X t` and `Q = ∏_t Y t` in the sense of [Stacks, Tag 016Q], a family of homotopies from
`a t` to `b t` assembles into a homotopy of the products, homotopic families with finitely many
differing coordinates have homotopic products, and a finite product of homotopy equivalences is
a homotopy equivalence.

## Main definitions

* `SSet.IntervalSimplex.stepSimplex`: the `(n + 1)`-simplex `γ_i` of `Δ[1]`, the monotone map
  `⦋n + 1⦌ ⟶ ⦋1⦌` taking the value `0` on `{0, …, i}` and the value `1` on `{i + 1, …, n + 1}`.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalence_proj_cylinder`: the three assertions of
  [Stacks, Tag 019O]. The vertex inclusions are sections of the projection, there is a homotopy
  from `e₀ ∘ π` to the identity of the cylinder, and one from the identity to `e₁ ∘ π`.
* `CategoryTheory.Arrow.nonempty_homotopy_mapCechNerve_id`: for an endomorphism `F` of an
  arrow `f` which is the identity on the base, in the sense that `f ≫ F.right = f`, there is a
  simplicial homotopy from the induced self map `Arrow.mapCechNerve F` of the Čech nerve of `f`
  to the identity.
* `CategoryTheory.Arrow.nonempty_homotopy_mapCechNerve_id_and_homotopyEquivalences`: the whole
  of [Stacks, Tag 019P]. For an arrow `f : Y ⟶ X` with a section `s`, the self map of the Čech
  nerve given by `s ∘ f` on each factor is homotopic to the identity, and the augmentation of the
  Čech nerve to the constant simplicial object `X` is a homotopy equivalence.
* `SSet.stdSimplex.homotopyEquivalences_hom_obj₀`: every morphism `Δ[m] ⟶ Δ[0]` — there is
  exactly one — is a homotopy equivalence of simplicial objects ([Stacks, Tag 019N]), and
  moreover `𝟙 Δ[m]` is homotopic, in the strong directed sense and in that direction, to the
  constant morphism at the last vertex of `Δ[m]`.
* `CategoryTheory.SimplicialObject.nonempty_homotopy_and_homotopyEquivalences_of_isLimit`: the
  three parts of [Stacks, Tag 08Q4], for degreewise products.

## References

* [Stacks, Tag 019O](https://stacks.math.columbia.edu/tag/019O)
* [Stacks, Tag 019P](https://stacks.math.columbia.edu/tag/019P)
* [Stacks, Tag 08Q3](https://stacks.math.columbia.edu/tag/08Q3)
* [Stacks, Tag 08Q4](https://stacks.math.columbia.edu/tag/08Q4)
* [Stacks, Tag 016E](https://stacks.math.columbia.edu/tag/016E)
* [Stacks, Tag 017E](https://stacks.math.columbia.edu/tag/017E)
* [Stacks, Tag 019L](https://stacks.math.columbia.edu/tag/019L)
* [Stacks, Tag 019M](https://stacks.math.columbia.edu/tag/019M)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
-/

@[expose] public section

universe w v u

/-! ### Gluing two monotone maps along a lower set -/

section MonotoneIte

/-- Two monotone maps `f ≤ g` glued along a predicate `p` whose truth set is a lower set, `f`
where `p` holds and `g` where it fails, form a monotone map: the monotone analogue of
`StrictMono.ite`. -/
private lemma monotone_ite {α β : Type*} [Preorder α] [Preorder β] {f g : α → β}
    {p : α → Prop} [DecidablePred p] (hf : Monotone f) (hg : Monotone g)
    (hp : ∀ ⦃x y⦄, x ≤ y → p y → p x) (hfg : ∀ x, f x ≤ g x) :
    Monotone fun x => if p x then f x else g x := by
  intro x y hxy
  dsimp only
  split_ifs with hx hy hy'
  · exact hf hxy
  · exact (hfg x).trans (hg hxy)
  · exact absurd (hp hxy hy') hx
  · exact hg hxy

end MonotoneIte

/-! ### The interval subdivisions `γ_i` of `Δ[1]`

The `(n + 1)`-simplices `γ_i` of `Δ[1]` taking the value `0` on an initial segment and `1` on
its complement, with the face and degeneracy identities between them. They are Mathlib's
`SSet.stdSimplex.objMk₁` indexed by the last vertex carrying the value `0` rather than by the
cut point. -/

namespace SSet.IntervalSimplex

open CategoryTheory Opposite Simplicial SSet

/-- The vertex `Fin.succAbove i k` as a natural number: `k` below `i`, and `k + 1` from `i` on. -/
public lemma val_succAbove {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    ((i.succAbove k : Fin (n + 2)) : ℕ) = if (k : ℕ) < (i : ℕ) then (k : ℕ) else (k : ℕ) + 1 :=
  apply_ite Fin.val (k.castSucc < i) k.castSucc k.succ

/-- The vertex `Fin.predAbove i k` as a natural number: `k - 1` above `i`, and `k` otherwise. -/
public lemma val_predAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    ((i.predAbove k : Fin (n + 1)) : ℕ) = if (i : ℕ) < (k : ℕ) then (k : ℕ) - 1 else (k : ℕ) := by
  rw [Fin.predAbove, apply_dite Fin.val]
  simp [Fin.lt_def]

/-- The `(n + 1)`-simplex `γ_i` of `Δ[1]`: the monotone map `⦋n + 1⦌ ⟶ ⦋1⦌` taking the value
`0` on `{0, …, i}` and the value `1` on `{i + 1, …, n + 1}`. In the notation of
[Stacks, Tag 019J] it is `α^{n + 1}_{i + 1}`. -/
public def stepSimplex {n : ℕ} (i : Fin (n + 1)) : (Δ[1] : SSet.{w}) _⦋n + 1⦌ :=
  stdSimplex.objMk₁ i.succ.castSucc

/-- The value of `γ_i` at the vertex `j`: `0` for `j ≤ i` and `1` beyond. -/
public lemma stepSimplex_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (stepSimplex.{w} i) j = if (j : ℕ) ≤ (i : ℕ) then 0 else 1 := by
  rw [stepSimplex, stdSimplex.objMk₁_apply]
  exact if_congr (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega) rfl rfl

/-- The `i`-th face of a simplex of `Δ[1]` is its precomposition with `Fin.succAbove i`. -/
public lemma delta_apply {n : ℕ} (i : Fin (n + 2)) (x : (Δ[1] : SSet.{w}) _⦋n + 1⦌)
    (k : Fin (n + 1)) : ((Δ[1] : SSet.{w}).δ i x) k = x (i.succAbove k) :=
  rfl

/-- The `i`-th degeneracy of a simplex of `Δ[1]` is its precomposition with `Fin.predAbove i`. -/
public lemma sigma_apply {n : ℕ} (i : Fin (n + 1)) (x : (Δ[1] : SSet.{w}) _⦋n⦌)
    (k : Fin (n + 2)) : ((Δ[1] : SSet.{w}).σ i x) k = x (i.predAbove k) :=
  rfl

/-- The constant `n`-simplex of `Δ[1]` at a vertex `a` takes the value `a` at every vertex. -/
public lemma const_apply {n : ℕ} (a : Fin 2) (k : Fin (n + 1)) :
    (stdSimplex.const 1 a (op ⦋n⦌) : (Δ[1] : SSet.{w}).obj _) k = a :=
  rfl

/-- The `0`-th face of `γ_0` is the constant `1`. -/
public lemma delta_zero_stepSimplex_zero (n : ℕ) :
    (Δ[1] : SSet.{w}).δ 0 (stepSimplex 0) = stdSimplex.const 1 1 (op ⦋n⦌) := by
  ext k
  rw [delta_apply, Fin.zero_succAbove, stepSimplex_apply, const_apply]
  simp

/-- The last face of `γ_n` is the constant `0`. -/
public lemma delta_last_stepSimplex_last (n : ℕ) :
    (Δ[1] : SSet.{w}).δ (Fin.last (n + 1)) (stepSimplex (Fin.last n))
      = stdSimplex.const 1 0 (op ⦋n⦌) := by
  ext k
  rw [delta_apply, Fin.succAbove_last, stepSimplex_apply, const_apply]
  simp only [Fin.val_castSucc, Fin.val_last]
  have := k.isLt
  split_ifs <;> omega

/-- Deleting a vertex `i ≤ j` of `γ_{j + 1}`, which carries the value `0` and is not the cut
point, gives `γ_j`. -/
public lemma delta_castSucc_stepSimplex_succ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    (Δ[1] : SSet.{w}).δ i.castSucc (stepSimplex j.succ) = stepSimplex j := by
  simp only [Fin.le_def, Fin.val_castSucc] at hij
  ext k
  rw [delta_apply, stepSimplex_apply, stepSimplex_apply, val_succAbove]
  simp only [Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- Deleting the vertex `j + 1`, the cut point of `γ_{j + 1}`, does not distinguish `γ_{j + 1}`
from `γ_j`. -/
public lemma delta_stepSimplex_succ_eq {n : ℕ} (j : Fin (n + 1)) :
    (Δ[1] : SSet.{w}).δ j.castSucc.succ (stepSimplex j.succ)
      = (Δ[1] : SSet.{w}).δ j.castSucc.succ (stepSimplex j.castSucc) := by
  ext k
  rw [delta_apply, delta_apply, stepSimplex_apply, stepSimplex_apply, val_succAbove]
  simp only [Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- Deleting a vertex `i + 1` above the cut point of `γ_j`, which carries the value `1`, leaves
the index unchanged. -/
public lemma delta_succ_stepSimplex_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    (Δ[1] : SSet.{w}).δ i.succ (stepSimplex j.castSucc) = stepSimplex j := by
  simp only [Fin.lt_def, Fin.val_castSucc] at hji
  ext k
  rw [delta_apply, stepSimplex_apply, stepSimplex_apply, val_succAbove]
  simp only [Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- Doubling a vertex `i ≤ j` of `γ_j`, which carries the value `0`, raises the index by one. -/
public lemma sigma_castSucc_stepSimplex {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    (Δ[1] : SSet.{w}).σ i.castSucc (stepSimplex j) = stepSimplex j.succ := by
  simp only [Fin.le_def] at hij
  ext k
  rw [sigma_apply, stepSimplex_apply, stepSimplex_apply, val_predAbove]
  simp only [Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- Doubling a vertex `i + 1` above the cut point of `γ_j`, which carries the value `1`, leaves
the index unchanged. -/
public lemma sigma_succ_stepSimplex {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    (Δ[1] : SSet.{w}).σ i.succ (stepSimplex j) = stepSimplex j.castSucc := by
  simp only [Fin.le_def] at hji
  ext k
  rw [sigma_apply, stepSimplex_apply, stepSimplex_apply, val_predAbove]
  simp only [Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

/-- No `γ_i` is the constant `0`: it takes the value `1` at the last vertex. -/
public lemma stepSimplex_ne_const_zero {n : ℕ} (i : Fin (n + 1)) :
    stepSimplex.{w} i ≠ stdSimplex.const 1 0 (op ⦋n + 1⦌) := by
  intro h
  have h2 : (stepSimplex.{w} i) (Fin.last (n + 1))
      = (stdSimplex.const 1 0 (op ⦋n + 1⦌) : (Δ[1] : SSet.{w}).obj _) (Fin.last (n + 1)) := by
    rw [h]
  rw [stepSimplex_apply, const_apply] at h2
  have hi := i.isLt
  simp only [Fin.val_last] at h2
  split_ifs at h2 with hc
  · omega
  · exact absurd h2 (by decide)

/-- The two vertices of `Δ[1]` are distinct in every degree. -/
public lemma const_one_ne_const_zero (n : ℕ) :
    (stdSimplex.const 1 1 (op ⦋n⦌) : (Δ[1] : SSet.{w}).obj _)
      ≠ stdSimplex.const 1 0 (op ⦋n⦌) := by
  intro h
  have h2 : (stdSimplex.const 1 1 (op ⦋n⦌) : (Δ[1] : SSet.{w}).obj _) 0
      = (stdSimplex.const 1 0 (op ⦋n⦌) : (Δ[1] : SSet.{w}).obj _) 0 := by rw [h]
  rw [const_apply, const_apply] at h2
  exact absurd h2 (by decide)

/-- A face of `γ_k` is the constant `0` exactly when the face and the step are both the last
one. -/
public lemma delta_stepSimplex_eq_const_zero_iff {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    (Δ[1] : SSet.{w}).δ i (stepSimplex k) = stdSimplex.const 1 0 (op ⦋n⦌) ↔
      (i = Fin.last (n + 1) ∧ k = Fin.last n) := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; exact delta_last_stepSimplex_last n⟩
  have h₁ : ((Δ[1] : SSet.{w}).δ i (stepSimplex k)) (Fin.last n)
      = (stdSimplex.const 1 0 (op ⦋n⦌) : (Δ[1] : SSet.{w}).obj _) (Fin.last n) := by rw [h]
  rw [delta_apply, stepSimplex_apply, val_succAbove, const_apply, Fin.val_last] at h₁
  have h₂ : (if n < (i : ℕ) then n else n + 1) ≤ (k : ℕ) :=
    not_not.mp fun hc => absurd (ite_eq_left_iff.mp h₁ hc) (by decide)
  have hi := i.isLt
  have hk := k.isLt
  refine ⟨Fin.val_inj.mp ?_, Fin.val_inj.mp ?_⟩ <;> rw [Fin.val_last] <;>
    split_ifs at h₂ <;> omega

/-- Every reindexing of `Δ[1]` carries the constant simplex at a vertex `a` to the constant
simplex at `a`. -/
public lemma map_const {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m') (a : Fin 2) :
    (Δ[1] : SSet.{w}).map φ (stdSimplex.const 1 a m) = stdSimplex.const 1 a m' := rfl

end SSet.IntervalSimplex

/-! ### The cylinder on a simplicial object is homotopy equivalent to it -/

section Cylinder

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet SSet.IntervalSimplex

/-! #### Pointwise operations on the simplices of `Δ[1]` -/

/-- The `m`-simplex of `Δ[1]` obtained by applying a monotone binary operation on `Fin 2`
pointwise to two `m`-simplices `a` and `b`. -/
private def pw (o : Fin 2 →o Fin 2 →o Fin 2) {k : ℕ} (a b : (Δ[1] : SSet.{w}) _⦋k⦌) :
    (Δ[1] : SSet.{w}) _⦋k⦌ :=
  stdSimplex.objMk ⟨fun j => o (a j) (b j), fun j j' h =>
    le_trans (o.monotone (stdSimplex.monotone_apply a h) (b j))
      ((o (a j')).monotone (stdSimplex.monotone_apply b h))⟩

private lemma pw_apply (o : Fin 2 →o Fin 2 →o Fin 2) {k : ℕ}
    (a b : (Δ[1] : SSet.{w}) _⦋k⦌) (j : Fin (k + 1)) : pw o a b j = o (a j) (b j) :=
  rfl

private lemma delta_pw (o : Fin 2 →o Fin 2 →o Fin 2) {k : ℕ} (i : Fin (k + 2))
    (a b : (Δ[1] : SSet.{w}) _⦋k + 1⦌) :
    (Δ[1] : SSet.{w}).δ i (pw o a b)
      = pw o ((Δ[1] : SSet.{w}).δ i a) ((Δ[1] : SSet.{w}).δ i b) :=
  rfl

private lemma sigma_pw (o : Fin 2 →o Fin 2 →o Fin 2) {k : ℕ} (i : Fin (k + 1))
    (a b : (Δ[1] : SSet.{w}) _⦋k⦌) :
    (Δ[1] : SSet.{w}).σ i (pw o a b)
      = pw o ((Δ[1] : SSet.{w}).σ i a) ((Δ[1] : SSet.{w}).σ i b) :=
  rfl

/-- The pointwise minimum, as a monotone binary operation on `Fin 2`. -/
private def minHom : Fin 2 →o Fin 2 →o Fin 2 where
  toFun a := ⟨fun b => min a b, fun _ _ h => min_le_min le_rfl h⟩
  monotone' _ _ h _ := min_le_min h le_rfl

/-- The pointwise maximum, as a monotone binary operation on `Fin 2`. -/
private def maxHom : Fin 2 →o Fin 2 →o Fin 2 where
  toFun a := ⟨fun b => max a b, fun _ _ h => max_le_max le_rfl h⟩
  monotone' _ _ h _ := max_le_max h le_rfl

private lemma minHom_apply (a b : Fin 2) : minHom a b = min a b := rfl

private lemma maxHom_apply (a b : Fin 2) : maxHom a b = max a b := rfl

private lemma min_const_zero : ∀ x : Fin 2, min x 0 = 0 := by decide

private lemma min_const_one : ∀ x : Fin 2, min x 1 = x := by decide

private lemma max_const_zero : ∀ x : Fin 2, max x 0 = x := by decide

private lemma max_const_one : ∀ x : Fin 2, max x 1 = 1 := by decide

/-! #### The simplicial identities in `Δ[1]`, elementwise -/

/-- An equality of maps of sets, evaluated at a point. -/
private lemma elt {A B : Type w} {f g : A ⟶ B} (h : f = g) (x : A) :
    (ConcreteCategory.hom f) x = (ConcreteCategory.hom g) x :=
  congrArg (fun k => (ConcreteCategory.hom k) x) h

private lemma delta_zero_sigma_zero {n : ℕ} (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    (Δ[1] : SSet.{w}).δ 0 ((Δ[1] : SSet.{w}).σ 0 β) = β :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_self' (i := (0 : Fin (n + 1))) (by simp)) β

private lemma delta_last_sigma_last {n : ℕ} (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    (Δ[1] : SSet.{w}).δ (Fin.last (n + 1)) ((Δ[1] : SSet.{w}).σ (Fin.last n) β) = β :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_succ' (i := Fin.last n) (Fin.succ_last n).symm) β

private lemma delta_castSucc_sigma_succ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (β : (Δ[1] : SSet.{w}) _⦋n + 1⦌) :
    (Δ[1] : SSet.{w}).δ i.castSucc ((Δ[1] : SSet.{w}).σ j.succ β)
      = (Δ[1] : SSet.{w}).σ j ((Δ[1] : SSet.{w}).δ i β) :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_of_le hij) β

private lemma delta_succ_sigma_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (β : (Δ[1] : SSet.{w}) _⦋n + 1⦌) :
    (Δ[1] : SSet.{w}).δ i.succ ((Δ[1] : SSet.{w}).σ j.castSucc β)
      = (Δ[1] : SSet.{w}).σ j ((Δ[1] : SSet.{w}).δ i β) :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_of_gt hji) β

private lemma delta_succ_castSucc_sigma_succ {n : ℕ} (j : Fin (n + 1))
    (β : (Δ[1] : SSet.{w}) _⦋n + 1⦌) :
    (Δ[1] : SSet.{w}).δ j.castSucc.succ ((Δ[1] : SSet.{w}).σ j.succ β) = β :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_self' (i := j.succ) (Fin.succ_castSucc j)) β

private lemma delta_succ_castSucc_sigma_castSucc {n : ℕ} (j : Fin (n + 1))
    (β : (Δ[1] : SSet.{w}) _⦋n + 1⦌) :
    (Δ[1] : SSet.{w}).δ j.castSucc.succ ((Δ[1] : SSet.{w}).σ j.castSucc β) = β :=
  elt ((Δ[1] : SSet.{w}).δ_comp_σ_succ (i := j.castSucc)) β

private lemma sigma_castSucc_sigma {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j)
    (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    (Δ[1] : SSet.{w}).σ i.castSucc ((Δ[1] : SSet.{w}).σ j β)
      = (Δ[1] : SSet.{w}).σ j.succ ((Δ[1] : SSet.{w}).σ i β) :=
  elt ((Δ[1] : SSet.{w}).σ_comp_σ hij) β

private lemma sigma_succ_sigma {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i)
    (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    (Δ[1] : SSet.{w}).σ i.succ ((Δ[1] : SSet.{w}).σ j β)
      = (Δ[1] : SSet.{w}).σ j.castSucc ((Δ[1] : SSet.{w}).σ i β) :=
  (elt ((Δ[1] : SSet.{w}).σ_comp_σ hji) β).symm

/-! #### The homotopy attached to a pointwise operation -/

section

variable {C : Type u} [Category.{v} C] {U X : SimplicialObject C}
  (ι : ∀ m : SimplexCategoryᵒᵖ, (Δ[1] : SSet.{w}).obj m → (U.obj m ⟶ X.obj m))
  (hX : ∀ m : SimplexCategoryᵒᵖ,
    IsColimit (Cofan.mk (f := fun _ : (Δ[1] : SSet.{w}).obj m => U.obj m) (X.obj m) (ι m)))
  (hι : ∀ {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m') (α : (Δ[1] : SSet.{w}).obj m),
    ι m α ≫ X.map φ = U.map φ ≫ ι m' ((Δ[1] : SSet.{w}).map φ α))

include hX in
private lemma hom_ext_cofan {m : SimplexCategoryᵒᵖ} {Z : C} {a b : X.obj m ⟶ Z}
    (h : ∀ β, ι m β ≫ a = ι m β ≫ b) : a = b :=
  Cofan.IsColimit.hom_ext (hX m) a b h

include hι in
private lemma ι_comp_delta {n : ℕ} (i : Fin (n + 2)) (β : (Δ[1] : SSet.{w}) _⦋n + 1⦌) :
    ι (op ⦋n + 1⦌) β ≫ X.δ i = U.δ i ≫ ι (op ⦋n⦌) ((Δ[1] : SSet.{w}).δ i β) :=
  hι _ β

include hι in
private lemma ι_comp_sigma {n : ℕ} (i : Fin (n + 1)) (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    ι (op ⦋n⦌) β ≫ X.σ i = U.σ i ≫ ι (op ⦋n + 1⦌) ((Δ[1] : SSet.{w}).σ i β) :=
  hι _ β

/-- The `i`-th component, in degree `n`, of the homotopy attached to a monotone binary
operation `o` on `Fin 2`: on the summand of `X_n` indexed by `β` it is the `i`-th degeneracy of
`U` followed by the inclusion of the summand indexed by `o(β ∘ σ_i, γ_i)`. -/
private noncomputable def cylinderHomotopyMap (o : Fin 2 →o Fin 2 →o Fin 2) {n : ℕ}
    (i : Fin (n + 1)) : X.obj (op ⦋n⦌) ⟶ X.obj (op ⦋n + 1⦌) :=
  Cofan.IsColimit.desc (hX (op ⦋n⦌)) fun β =>
    U.σ i ≫ ι (op ⦋n + 1⦌) (pw o ((Δ[1] : SSet.{w}).σ i β) (stepSimplex i))

private lemma ι_comp_cylinderHomotopyMap (o : Fin 2 →o Fin 2 →o Fin 2) {n : ℕ}
    (i : Fin (n + 1)) (β : (Δ[1] : SSet.{w}) _⦋n⦌) :
    ι (op ⦋n⦌) β ≫ cylinderHomotopyMap ι hX o i
      = U.σ i ≫ ι (op ⦋n + 1⦌) (pw o ((Δ[1] : SSet.{w}).σ i β) (stepSimplex i)) :=
  Cofan.IsColimit.fac (hX (op ⦋n⦌)) _ β

include hι in
/-- The homotopy attached to a monotone binary operation `o` on `Fin 2`, between the two
morphisms of `X` which `o` induces at the two ends of the interval. -/
private noncomputable def cylinderHomotopy (o : Fin 2 →o Fin 2 →o Fin 2) (f g : X ⟶ X)
    (hf : ∀ (n : ℕ) (β : (Δ[1] : SSet.{w}) _⦋n⦌),
      ι (op ⦋n⦌) β ≫ f.app (op ⦋n⦌) = ι (op ⦋n⦌) (pw o β (stdSimplex.const 1 0 (op ⦋n⦌))))
    (hg : ∀ (n : ℕ) (β : (Δ[1] : SSet.{w}) _⦋n⦌),
      ι (op ⦋n⦌) β ≫ g.app (op ⦋n⦌) = ι (op ⦋n⦌) (pw o β (stdSimplex.const 1 1 (op ⦋n⦌)))) :
    SimplicialObject.Homotopy f g where
  h i := cylinderHomotopyMap ι hX o i
  h_zero_comp_δ_zero n := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_delta ι hι,
      ← Category.assoc, U.δ_comp_σ_self' (i := (0 : Fin (n + 1))) (by simp),
      Category.id_comp, delta_pw, delta_zero_sigma_zero, delta_zero_stepSimplex_zero, hg]
  h_last_comp_δ_last n := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_delta ι hι,
      ← Category.assoc,
      U.δ_comp_σ_succ' (i := Fin.last n) (Fin.succ_last n).symm,
      Category.id_comp, delta_pw, delta_last_sigma_last, delta_last_stepSimplex_last, hf]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_delta ι hι,
      ← Category.assoc, U.δ_comp_σ_of_le hij, Category.assoc,
      delta_pw, delta_castSucc_sigma_succ i j hij, delta_castSucc_stepSimplex_succ i j hij,
      ← ι_comp_cylinderHomotopyMap ι hX, ← Category.assoc, ← ι_comp_delta ι hι, Category.assoc]
  h_succ_comp_δ_castSucc_succ j := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_delta ι hι,
      ← Category.assoc,
      U.δ_comp_σ_self' (i := j.succ) (Fin.succ_castSucc j),
      Category.id_comp, ← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc,
      ι_comp_delta ι hι, ← Category.assoc,
      U.δ_comp_σ_succ' (i := j.castSucc) rfl, Category.id_comp,
      delta_pw, delta_pw, delta_succ_castSucc_sigma_succ,
      delta_succ_castSucc_sigma_castSucc, delta_stepSimplex_succ_eq]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_delta ι hι,
      ← Category.assoc, U.δ_comp_σ_of_gt hji, Category.assoc,
      delta_pw, delta_succ_sigma_castSucc i j hji, delta_succ_stepSimplex_castSucc i j hji,
      ← ι_comp_cylinderHomotopyMap ι hX, ← Category.assoc, ← ι_comp_delta ι hι, Category.assoc]
  h_comp_σ_castSucc_of_le i j hij := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_sigma ι hι,
      ← Category.assoc, U.σ_comp_σ hij, Category.assoc,
      sigma_pw, sigma_castSucc_sigma i j hij, sigma_castSucc_stepSimplex i j hij,
      ← ι_comp_cylinderHomotopyMap ι hX, ← Category.assoc, ← ι_comp_sigma ι hι, Category.assoc]
  h_comp_σ_succ_of_lt i j hji := by
    refine hom_ext_cofan ι hX fun β => ?_
    rw [← Category.assoc, ι_comp_cylinderHomotopyMap, Category.assoc, ι_comp_sigma ι hι,
      ← Category.assoc, ← U.σ_comp_σ hji, Category.assoc,
      sigma_pw, sigma_succ_sigma i j hji, sigma_succ_stepSimplex i j hji,
      ← ι_comp_cylinderHomotopyMap ι hX, ← Category.assoc, ← ι_comp_sigma ι hι, Category.assoc]

end

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {U X : SimplicialObject C}

/-- The projection from the cylinder `U × Δ[1]` is a homotopy equivalence, with either vertex
inclusion as a homotopy inverse. Let `U` be a simplicial object of a category `C`, and let `X`
be a cylinder on `U`: a simplicial object together with morphisms `ι m α : U_m ⟶ X_m`, one for
each `m`-simplex `α` of `Δ[1]`, which exhibit `X_m` as the coproduct `∐_{α ∈ Δ[1]_m} U_m` and
satisfy `ι m α ≫ X(φ) = U(φ) ≫ ι m' (Δ[1](φ) α)`; this is the product `U × Δ[1]` of
[Stacks, Tag 017C]. Let `π : X ⟶ U` be the projection, the identity on each summand, and let
`e₀, e₁ : U ⟶ X` be the two vertex inclusions, in degree `m` the inclusions of the summands
indexed by the constant `m`-simplices `SSet.stdSimplex.const 1 0 m` and
`SSet.stdSimplex.const 1 1 m` of `Δ[1]`. Then `π ∘ e₀ = π ∘ e₁ = id_U`, the composite `e₀ ∘ π`
admits a homotopy to `id_X`, and `id_X` admits a homotopy to `e₁ ∘ π`. In particular `π` is a
homotopy equivalence ([Stacks, Tag 019N]), so `U × Δ[1]` is homotopy equivalent to `U`. -/
@[stacks 019O "the cylinder is any object with the universal property of `U × Δ[1]`, in place \
  of a chosen construction, so that the source's finite coproducts on `C` are weakened to the \
  coproducts making it up; the maps of [Stacks, Tag 017E] are pinned by their characterizing \
  equations instead of being reconstructed; and the two homotopies are directed, as the \
  source's proof produces them, which is stronger than the source's symmetric `are homotopic`"]
public theorem homotopyEquivalence_proj_cylinder
    (ι : ∀ m : SimplexCategoryᵒᵖ, (Δ[1] : SSet.{w}).obj m → (U.obj m ⟶ X.obj m))
    (hX : ∀ m : SimplexCategoryᵒᵖ,
      IsColimit (Cofan.mk (f := fun _ : (Δ[1] : SSet.{w}).obj m => U.obj m) (X.obj m) (ι m)))
    (hι : ∀ {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m') (α : (Δ[1] : SSet.{w}).obj m),
      ι m α ≫ X.map φ = U.map φ ≫ ι m' ((Δ[1] : SSet.{w}).map φ α))
    (π : X ⟶ U) (e₀ e₁ : U ⟶ X)
    (hπ : ∀ (m : SimplexCategoryᵒᵖ) (α : (Δ[1] : SSet.{w}).obj m),
      ι m α ≫ π.app m = 𝟙 (U.obj m))
    (he₀ : ∀ m : SimplexCategoryᵒᵖ, e₀.app m = ι m (stdSimplex.const 1 0 m))
    (he₁ : ∀ m : SimplexCategoryᵒᵖ, e₁.app m = ι m (stdSimplex.const 1 1 m)) :
    (e₀ ≫ π = 𝟙 U ∧ e₁ ≫ π = 𝟙 U) ∧
      Nonempty (Homotopy (π ≫ e₀) (𝟙 X)) ∧ Nonempty (Homotopy (𝟙 X) (π ≫ e₁)) := by
  refine ⟨⟨?_, ?_⟩,
    ⟨cylinderHomotopy (ι := ι) (hX := hX) (hι := hι) (o := minHom)
      (f := π ≫ e₀) (g := 𝟙 X) ?_ ?_⟩,
    ⟨cylinderHomotopy (ι := ι) (hX := hX) (hι := hι) (o := maxHom)
      (f := 𝟙 X) (g := π ≫ e₁) ?_ ?_⟩⟩
  · ext m
    rw [NatTrans.comp_app, he₀, hπ, NatTrans.id_app]
  · ext m
    rw [NatTrans.comp_app, he₁, hπ, NatTrans.id_app]
  all_goals
    intro n β
    simp only [NatTrans.comp_app, NatTrans.id_app, ← Category.assoc, hπ, he₀, he₁,
      Category.id_comp, Category.comp_id]
    refine congrArg (ι (op ⦋n⦌)) ?_
    ext k
    simp [const_apply, pw_apply, minHom_apply, maxHom_apply, min_const_one, max_const_one]

end CategoryTheory.SimplicialObject

end Cylinder

/-! ### Self maps of a Čech nerve over its base -/

section CechNerve

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet.IntervalSimplex

/-! #### The two morphisms attached to the vertices of the interval -/

section

variable {C : Type u} [Category.{v} C] {f : Arrow C} (F : f ⟶ f)

/-- The morphism `gᵃ : Y ⟶ Y` attached to a vertex `a` of the interval: `g⁰ = 𝟙 Y` and
`g¹ = F.left`. -/
private def leg (a : Fin 2) : f.left ⟶ f.left := if a = 0 then 𝟙 f.left else F.left

private lemma leg_zero : leg F 0 = 𝟙 f.left := by simp [leg]

private lemma leg_one : leg F 1 = F.left := by simp [leg]

/-- Both morphisms attached to the vertices of the interval are endomorphisms of `f`
over `X`. -/
private lemma leg_comp_hom (hF : f.hom ≫ F.right = f.hom) (a : Fin 2) :
    leg F a ≫ f.hom = f.hom := by
  rw [leg]
  split
  · simp
  · rw [F.w, hF]

end

/-! #### The self maps of the Čech nerve attached to the simplices of the interval -/

section

variable {C : Type u} [Category.{v} C] {f : Arrow C}
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  (F : f ⟶ f) (hF : f.hom ≫ F.right = f.hom)

/-- The self map `(y_0, …, y_n) ↦ (g^{α 0}(y_0), …, g^{α n}(y_n))` of the degree `n` term of
the Čech nerve of `f`, attached to a function `α : Fin (n + 1) → Fin 2`. -/
private noncomputable def selfMap {n : ℕ} (α : Fin (n + 1) → Fin 2) :
    f.cechNerve.obj (op ⦋n⦌) ⟶ f.cechNerve.obj (op ⦋n⦌) :=
  WidePullback.lift (WidePullback.base _) (fun i => WidePullback.π _ i ≫ leg F (α i))
    (fun i => by rw [Category.assoc, leg_comp_hom F hF, WidePullback.π_arrow])

private lemma selfMap_π {n : ℕ} (α : Fin (n + 1) → Fin 2) (i : Fin (n + 1)) :
    selfMap F hF α ≫ WidePullback.π _ i = WidePullback.π _ i ≫ leg F (α i) := by
  rw [selfMap, WidePullback.lift_π]

/-- The self map attached to the constant function `0` is the identity. -/
private lemma selfMap_const_zero {n : ℕ} : selfMap F hF (fun _ : Fin (n + 1) => 0) = 𝟙 _ := by
  refine WidePullback.hom_ext_of_π _ _ fun i => ?_
  rw [selfMap_π, Category.id_comp, leg_zero, Category.comp_id]

/-- The self map attached to the constant function `1` is the degree `n` component of the
morphism of Čech nerves induced by `F`. -/
private lemma selfMap_const_one {n : ℕ} :
    selfMap F hF (fun _ : Fin (n + 1) => 1) = (Arrow.mapCechNerve F).app (op ⦋n⦌) := by
  refine WidePullback.hom_ext_of_π _ _ fun i => ?_
  rw [selfMap_π, leg_one, Arrow.mapCechNerve_app, WidePullback.lift_π]

/-- Reindexing the Čech nerve along `φ` turns the self map attached to `α` into the one
attached to `α ∘ φ`. -/
private lemma selfMap_comp_map {n m : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (α : Fin (n + 1) → Fin 2) :
    selfMap F hF α ≫ f.cechNerve.map φ.op
      = f.cechNerve.map φ.op ≫ selfMap F hF (α ∘ φ.toOrderHom) := by
  refine WidePullback.hom_ext_of_π _ _ fun i => ?_
  simp [Arrow.cechNerve_map, selfMap_π]

private lemma selfMap_comp_δ {n : ℕ} (i : Fin (n + 2)) (α : Fin (n + 2) → Fin 2) :
    selfMap F hF α ≫ f.cechNerve.δ i
      = f.cechNerve.δ i ≫ selfMap F hF (α ∘ i.succAbove) :=
  selfMap_comp_map F hF (SimplexCategory.δ i) α

private lemma selfMap_comp_σ {n : ℕ} (i : Fin (n + 1)) (α : Fin (n + 1) → Fin 2) :
    selfMap F hF α ≫ f.cechNerve.σ i
      = f.cechNerve.σ i ≫ selfMap F hF (α ∘ i.predAbove) :=
  selfMap_comp_map F hF (SimplexCategory.σ i) α

/-- A face map absorbed into a morphism to its left: the self map attached to `α` passes
through `δⱼ` at the price of reindexing `α` along `j.succAbove`. -/
private lemma comp_selfMap_comp_δ {n : ℕ} {Z : C} (u : Z ⟶ f.cechNerve.obj (op ⦋n + 1⦌))
    (α : Fin (n + 2) → Fin 2) (j : Fin (n + 2)) :
    (u ≫ selfMap F hF α) ≫ f.cechNerve.δ j
      = (u ≫ f.cechNerve.δ j) ≫ selfMap F hF (α ∘ j.succAbove) := by
  simp [selfMap_comp_δ]

/-- A degeneracy absorbed into a morphism to its left, as in `comp_selfMap_comp_δ`. -/
private lemma comp_selfMap_comp_σ {n : ℕ} {Z : C} (u : Z ⟶ f.cechNerve.obj (op ⦋n⦌))
    (α : Fin (n + 1) → Fin 2) (j : Fin (n + 1)) :
    (u ≫ selfMap F hF α) ≫ f.cechNerve.σ j
      = (u ≫ f.cechNerve.σ j) ≫ selfMap F hF (α ∘ j.predAbove) := by
  simp [selfMap_comp_σ]

end

/-! #### The subdivisions of the interval -/

/-- The subdivision of the interval of threshold `b`: the function `Fin m → Fin 2` taking the
value `1` on the first `b` vertices `{0, …, b - 1}` and the value `0` on the rest. -/
private def step (b : ℕ) {m : ℕ} : Fin m → Fin 2 := fun j => if (j : ℕ) < b then 1 else 0

private lemma step_zero {m : ℕ} : (step 0 : Fin m → Fin 2) = fun _ => 0 := by
  funext j
  simp [step]

/-- A threshold at least the number of vertices gives the constant function `1`. -/
private lemma step_eq_one_of_le {m b : ℕ} (h : m ≤ b) :
    (step b : Fin m → Fin 2) = fun _ => 1 := by
  funext j
  have : (j : ℕ) < b := j.isLt.trans_le h
  simp [step, this]

/-- Reindexing a subdivision along `φ` gives a subdivision, as soon as `φ` pulls the initial
segment of length `b` back to the initial segment of length `c`. -/
private lemma step_comp_eq_step {m m' b c : ℕ} (φ : Fin m' → Fin m)
    (h : ∀ k : Fin m', ((φ k : ℕ) < b ↔ (k : ℕ) < c)) : step b ∘ φ = step c :=
  funext fun k => by simp [step, h k]

/-- Deleting a vertex which carries the value `1` lowers the threshold by one. -/
private lemma step_comp_succAbove_of_lt {n b : ℕ} (i : Fin (n + 2)) (h : (i : ℕ) < b + 1) :
    step (b + 1) ∘ i.succAbove = step b :=
  step_comp_eq_step _ fun k => by rw [val_succAbove]; split_ifs <;> omega

/-- Deleting a vertex which carries the value `0` leaves the threshold unchanged. -/
private lemma step_comp_succAbove_of_le {n b : ℕ} (i : Fin (n + 2)) (h : b ≤ (i : ℕ)) :
    step b ∘ i.succAbove = step b :=
  step_comp_eq_step _ fun k => by rw [val_succAbove]; split_ifs <;> omega

/-- Doubling a vertex which carries the value `1` raises the threshold by one. -/
private lemma step_comp_predAbove_of_lt {n b : ℕ} (i : Fin (n + 1)) (h : (i : ℕ) < b) :
    step b ∘ i.predAbove = step (b + 1) :=
  step_comp_eq_step _ fun k => by rw [val_predAbove]; split_ifs <;> omega

/-- Doubling a vertex which carries the value `0` leaves the threshold unchanged. -/
private lemma step_comp_predAbove_of_le {n b : ℕ} (i : Fin (n + 1)) (h : b ≤ (i : ℕ)) :
    step b ∘ i.predAbove = step b :=
  step_comp_eq_step _ fun k => by rw [val_predAbove]; split_ifs <;> omega

/-! #### The homotopy -/

section

variable {C : Type u} [Category.{v} C] {f : Arrow C}
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  (F : f ⟶ f) (hF : f.hom ≫ F.right = f.hom)

/-- The homotopy from the self map of the Čech nerve induced by `F` to the identity: its `i`-th
component in degree `n` is the degeneracy `σᵢ` followed by the self map attached to the
subdivision of threshold `i + 1`. -/
private noncomputable def cechHomotopy :
    SimplicialObject.Homotopy (Arrow.mapCechNerve F) (𝟙 f.cechNerve) where
  h i := f.cechNerve.σ i ≫ selfMap F hF (step ((i : ℕ) + 1))
  h_zero_comp_δ_zero n := by
    rw [comp_selfMap_comp_δ, f.cechNerve.δ_comp_σ_self' (i := (0 : Fin (n + 1))) (by simp),
      Category.id_comp, step_comp_succAbove_of_lt _ (by simp), Fin.val_zero, step_zero,
      selfMap_const_zero, NatTrans.id_app]
  h_last_comp_δ_last n := by
    rw [comp_selfMap_comp_δ, f.cechNerve.δ_comp_σ_succ' (i := Fin.last n) (Fin.succ_last n).symm,
      Category.id_comp, step_comp_succAbove_of_le _ (by simp), step_eq_one_of_le (by simp),
      selfMap_const_one]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    rw [Fin.val_succ, comp_selfMap_comp_δ, f.cechNerve.δ_comp_σ_of_le hij, Category.assoc,
      step_comp_succAbove_of_lt (b := (j : ℕ) + 1) i.castSucc
        (by grind)]
  h_succ_comp_δ_castSucc_succ j := by
    rw [Fin.val_succ, Fin.val_castSucc, comp_selfMap_comp_δ,
      f.cechNerve.δ_comp_σ_self' (i := j.succ) (Fin.succ_castSucc j), Category.id_comp,
      step_comp_succAbove_of_lt (b := (j : ℕ) + 1) j.castSucc.succ (by simp),
      comp_selfMap_comp_δ, f.cechNerve.δ_comp_σ_succ' (i := j.castSucc) rfl, Category.id_comp,
      step_comp_succAbove_of_le (b := (j : ℕ) + 1) j.castSucc.succ (by simp)]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    rw [Fin.val_castSucc, comp_selfMap_comp_δ, f.cechNerve.δ_comp_σ_of_gt hji, Category.assoc,
      step_comp_succAbove_of_le (b := (j : ℕ) + 1) i.succ
        (by grind)]
  h_comp_σ_castSucc_of_le i j hij := by
    rw [Fin.val_succ, comp_selfMap_comp_σ, f.cechNerve.σ_comp_σ hij, Category.assoc,
      step_comp_predAbove_of_lt (b := (j : ℕ) + 1) i.castSucc
        (by grind)]
  h_comp_σ_succ_of_lt i j hji := by
    rw [Fin.val_castSucc, comp_selfMap_comp_σ, ← f.cechNerve.σ_comp_σ hji, Category.assoc,
      step_comp_predAbove_of_le (b := (j : ℕ) + 1) i.succ
        (by grind)]

end

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

/-- A self map of a Čech nerve which is the identity on the base is homotopic to the identity. Let
`f : Y ⟶ X` be an arrow of a category `C` whose iterated fibre products `Y ×_X ⋯ ×_X Y` exist, let
`U = f.cechNerve` be the simplicial object of [Stacks, Tag 016E] built from `f`, and let `F` be an
endomorphism of the arrow `f` with `f ≫ F.right = f`, so that the induced self map
`Arrow.mapCechNerve F` of `U`, given by `F.left` on each factor `Y`, is the identity on the base
`X`. Then there is a simplicial homotopy from that self map to `𝟙 U` in the sense of
[Stacks, Tag 019M]; in particular the two are homotopic. -/
@[stacks 019P "the homotopy of the first sentence, in the generality of an arbitrary \
  endomorphism `F` of the arrow `f` with `f.hom ≫ F.right = f.hom`, of which the source's self \
  map is the case `F = (f.hom ≫ s, 𝟙 X)` for a section `s` of `f`; the self map is pinned as \
  `Arrow.mapCechNerve F`, and the conclusion is the existence of a homotopy, which is \
  stronger than the source's `homotopic` of 019M. The whole lemma, with the section `s` and \
  both sentences, is `Arrow.nonempty_homotopy_mapCechNerve_id_and_homotopyEquivalences`"]
public theorem nonempty_homotopy_mapCechNerve_id {f : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    (F : f ⟶ f) (hF : f.hom ≫ F.right = f.hom) :
    Nonempty (SimplicialObject.Homotopy (mapCechNerve F) (𝟙 f.cechNerve)) :=
  ⟨cechHomotopy F hF⟩

/-- **Stacks 019P.** Let `f : Y ⟶ X` be an arrow of a category `C` whose iterated fibre products
`Y ×_X ⋯ ×_X Y` exist, with a section `s : X ⟶ Y`, so `s ≫ f = 𝟙 X`, and let `U = f.cechNerve` be
the simplicial object of [Stacks, Tag 016E] built from `f`. The self map `Arrow.mapCechNerve` of
the arrow endomorphism `(f ≫ s, 𝟙 X)` is in degree `n` the map `(s ∘ f)^{n + 1}` of
`Y ×_X ⋯ ×_X Y`, given by `s ∘ f` on each factor (first conjunct); there is a simplicial homotopy
from it to `𝟙 U`, so the two are homotopic (second conjunct); and the augmentation
`U ⟶ X`, to the constant simplicial object at `X`, is a homotopy equivalence ([Stacks, Tag 019N]),
so `U` is homotopy equivalent to the constant simplicial object `X` (third conjunct). The homotopy
inverse is the section of the augmentation induced by `s`, and the homotopy is Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.homotopy` for the extra degeneracy
`Arrow.AugmentedCechNerve.extraDegeneracy` of the split epimorphism `f`. -/
@[stacks 019P "both sentences, for the section `s` of `f`: the self map `(s ∘ f)^{n + 1}` is \
  `Arrow.mapCechNerve` of the arrow endomorphism `(f.hom ≫ s, 𝟙 X)`, its components being \
  recorded in the first conjunct; the second conjunct is the homotopy to the identity, an \
  existence of a homotopy, stronger than `homotopic` of 019M; the third says that the \
  augmentation `f.augmentedCechNerve.hom : U ⟶ const X` is a homotopy equivalence in the sense \
  of 019N, which is the source's `U` homotopy equivalent to the constant simplicial object `X` \
  with the equivalence named. The fibre products of the source are those of Example 016E, the \
  wide pullbacks `Y ×_X ⋯ ×_X Y` of `Arrow.cechNerve`. The third conjunct uses Mathlib's \
  `Arrow.AugmentedCechNerve.extraDegeneracy` and `ExtraDegeneracy.homotopy`"]
public theorem nonempty_homotopy_mapCechNerve_id_and_homotopyEquivalences {f : Arrow C}
    [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
    (s : f.right ⟶ f.left) (hs : s ≫ f.hom = 𝟙 f.right) :
    (∀ (n : ℕ) (i : Fin (n + 1)),
      (mapCechNerve (homMk (f.hom ≫ s) (𝟙 f.right) (by simp [hs]))).app (op ⦋n⦌) ≫
          WidePullback.π (fun _ : Fin (n + 1) => f.hom) i =
        WidePullback.π (fun _ : Fin (n + 1) => f.hom) i ≫ f.hom ≫ s) ∧
      Nonempty (SimplicialObject.Homotopy
        (mapCechNerve (homMk (f.hom ≫ s) (𝟙 f.right) (by simp [hs]))) (𝟙 f.cechNerve)) ∧
      SimplicialObject.homotopyEquivalences C f.augmentedCechNerve.hom := by
  refine ⟨fun n i => ?_,
    nonempty_homotopy_mapCechNerve_id (homMk (f.hom ≫ s) (𝟙 f.right) (by simp [hs])) (by simp), ?_⟩
  · rw [mapCechNerve_app, WidePullback.lift_π]
    rfl
  · let ed := AugmentedCechNerve.extraDegeneracy f ⟨s, hs⟩
    exact ⟨ed.section_, Relation.EqvGen.rel _ _ ⟨ed.homotopy⟩, ed.section_comp_hom ▸ .refl _⟩

end CategoryTheory.Arrow

end CechNerve

/-! ### The standard simplex is homotopy equivalent to a point -/

section StdSimplexContraction

open CategoryTheory MonoidalCategory Opposite Simplicial SSet.stdSimplex

/-- The contraction of `Δ[m]` onto its last vertex: the morphism `Δ[m] ⊗ Δ[1] ⟶ Δ[m]` sending
a pair `(φ, α)` of maps `⦋n⦌ ⟶ ⦋m⦌`, `⦋n⦌ ⟶ ⦋1⦌` to `k ↦ if α k = 0 then φ k else m`. -/
private noncomputable def lastVertexContraction (m : ℕ) :
    ((Δ[m] : SSet.{u}) ⊗ Δ[1] : SSet.{u}) ⟶ Δ[m] where
  app n := ↾fun ⟨φ, α⟩ => objMk
    ⟨fun k => if asOrderHom α k = 0 then asOrderHom φ k else Fin.last m,
      monotone_ite (asOrderHom φ).monotone monotone_const
        (fun _ _ hab hb => Fin.le_zero_iff.mp (((asOrderHom α).monotone hab).trans_eq hb))
        (fun _ => Fin.le_last _)⟩
  naturality := by intros; rfl

/-- The defining formula of `lastVertexContraction`. -/
private lemma asOrderHom_lastVertexContraction_app (m : ℕ) (n : SimplexCategoryᵒᵖ)
    (z : ((Δ[m] : SSet.{u}) ⊗ Δ[1]).obj n) (k : Fin ((unop n).len + 1)) :
    asOrderHom ((lastVertexContraction.{u} m).app n z) k =
      if asOrderHom z.2 k = 0 then asOrderHom z.1 k else Fin.last m :=
  rfl

private lemma asOrderHom_eq {m : ℕ} {n : SimplexCategoryᵒᵖ} (α : (Δ[m] : SSet.{u}).obj n) :
    asOrderHom α = (objEquiv α).toOrderHom :=
  rfl

/-- Two morphisms to a standard simplex which agree on every vertex of every simplex are
equal. -/
private lemma stdSimplex_hom_ext {X : SSet.{u}} {m : ℕ} {a b : X ⟶ Δ[m]}
    (h : ∀ (n : SimplexCategoryᵒᵖ) (z : X.obj n) (k : Fin ((unop n).len + 1)),
      asOrderHom (a.app n z) k = asOrderHom (b.app n z) k) :
    a = b := by
  ext n z
  refine objEquiv.injective ?_
  ext k : 3
  have hk := h n z k
  rw [asOrderHom_eq, asOrderHom_eq] at hk
  exact hk

/-- `lastVertexContraction` is a homotopy from `𝟙 Δ[m]` to the constant morphism at the last
vertex of `Δ[m]`. -/
private noncomputable def lastVertexHomotopy (m : ℕ) : SSet.Homotopy (𝟙 (Δ[m] : SSet.{u}))
    (SSet.const (obj₀Equiv.symm (Fin.last m))) where
  h := lastVertexContraction m
  h₀ := stdSimplex_hom_ext fun n z k =>
    (asOrderHom_lastVertexContraction_app m n (SSet.ι₀.app n z) k).trans (ite_eq_left rfl)
  h₁ := stdSimplex_hom_ext fun n z k =>
    (asOrderHom_lastVertexContraction_app m n (SSet.ι₁.app n z) k).trans
      (ite_eq_right (show ¬ ((1 : Fin 2) = 0) by decide))
  rel := by
    ext n z
    exact z.1.2.elim

namespace SSet.stdSimplex

/-- The standard simplex `Δ[m]` is homotopy equivalent to `Δ[0]`. The unique morphism
`f : Δ[m] ⟶ Δ[0]` is a homotopy equivalence of simplicial objects ([Stacks, Tag 019N]): a
homotopy inverse is the inclusion `g : Δ[0] ⟶ Δ[m]` of the last `0`-simplex of `Δ[m]`, for
which `g ≫ f = 𝟙 Δ[0]` and, as the second conjunct records, `𝟙 Δ[m]` is homotopic to
`f ≫ g = SSet.const (obj₀Equiv.symm (Fin.last m))` by a homotopy in that direction, namely
`(φ, α) ↦ (k ↦ if α k = 0 then φ k else m)`. -/
@[stacks 08Q3 "the homotopy equivalence, with the homotopy `𝟙 ⟹ f ≫ g` for `g` the last \
  vertex; `g ≫ f = 𝟙` is `SSet.stdSimplex.ext₀`, as `Δ[0]` is terminal"]
public theorem homotopyEquivalences_hom_obj₀ (m : ℕ) :
    (∀ f : (Δ[m] : SSet.{u}) ⟶ Δ[0],
        SimplicialObject.homotopyEquivalences (Type u) f) ∧
      Nonempty (SSet.Homotopy (𝟙 (Δ[m] : SSet.{u}))
        (SSet.const (obj₀Equiv.symm (Fin.last m)))) := by
  refine ⟨fun f => ⟨SSet.const (obj₀Equiv.symm (Fin.last m)), ?_, ?_⟩, ⟨lastVertexHomotopy m⟩⟩
  · rw [SSet.comp_const]
    exact (Relation.EqvGen.rel _ _ ⟨(lastVertexHomotopy m).toSimplicialObjectHomotopy⟩).symm
  · rw [show SSet.const (obj₀Equiv.symm (Fin.last m)) ≫ f = 𝟙 _ from ext₀]
    exact Relation.EqvGen.refl _

end SSet.stdSimplex

end StdSimplexContraction

/-! ### Products of homotopies and of homotopy equivalences -/

section Products

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

section

variable {C : Type u} [Category.{v} C] {T : Type w}
  {X Y : T → SimplicialObject C} {P Q : SimplicialObject C}

/-- A family `p t : P ⟶ X t` of morphisms of simplicial objects whose fan is a limit in every
degree is a limit fan in `SimplicialObject C`. -/
private def isLimitFan (p : ∀ t, P ⟶ X t)
    (hP : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (P.obj n) fun t => (p t).app n)) :
    IsLimit (Fan.mk P p) :=
  evaluationJointlyReflectsLimits _ fun n =>
    (IsLimit.equivOfNatIsoOfIso
      (Discrete.compNatIsoDiscrete X ((evaluation SimplexCategoryᵒᵖ C).obj n)) _
      (Fan.mk (P.obj n) fun t => (p t).app n) (Cone.ext (Iso.refl _) (by simp))).symm (hP n)

/-- For a degreewise limit fan, composing the morphism into `Q.obj n` determined by a family `u`
with the `t`-th projection returns `u t`. -/
@[reassoc]
private lemma lift_comp (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {n : SimplexCategoryᵒᵖ} {A : C} (u : ∀ t, A ⟶ (Y t).obj n) (t : T) :
    Fan.IsLimit.lift (hQ n) u ≫ (q t).app n = u t :=
  Fan.IsLimit.fac (hQ n) u t

attribute [local simp] lift_comp lift_comp_assoc

/-- The product `∏_t c t : P ⟶ Q` of a family of morphisms `c t : X t ⟶ Y t`, for `P` and `Q`
degreewise products of the `X t` and of the `Y t`. -/
private noncomputable def piMap (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    (c : ∀ t, X t ⟶ Y t) : P ⟶ Q :=
  Fan.IsLimit.lift (isLimitFan q hQ) fun t => p t ≫ c t

@[reassoc]
private lemma piMap_comp (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    (c : ∀ t, X t ⟶ Y t) (t : T) : piMap p q hQ c ≫ q t = p t ≫ c t :=
  Fan.IsLimit.fac (isLimitFan q hQ) (fun t => p t ≫ c t) t

attribute [local simp] piMap_comp piMap_comp_assoc

/-- A morphism `P ⟶ Q` satisfying the equations characterizing the product of a family
`c t : X t ⟶ Y t` is that product. -/
private lemma eq_piMap (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {c : ∀ t, X t ⟶ Y t} {f : P ⟶ Q} (hf : ∀ t, f ≫ q t = p t ≫ c t) :
    f = piMap p q hQ c :=
  Fan.IsLimit.hom_ext (isLimitFan q hQ) _ _ fun t => by simpa using hf t

/-- A family of homotopies of the coordinates of two morphisms into a degreewise product is a
homotopy of the two morphisms: given homotopies from `f ≫ q t` to `g ≫ q t` for every `t`, the
morphisms `h_{n, i} : P_n ⟶ Q_{n + 1}` with coordinates the `h_{t, n, i}` are a homotopy from `f`
to `g`. -/
private noncomputable def homotopyOfIsLimit (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {f g : P ⟶ Q} (H : ∀ t, SimplicialObject.Homotopy (f ≫ q t) (g ≫ q t)) :
    SimplicialObject.Homotopy f g where
  h {n} i := Fan.IsLimit.lift (hQ (op ⦋n + 1⦌)) fun t => (H t).h i
  h_zero_comp_δ_zero n := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by simp
  h_last_comp_δ_last n := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by simp
  h_succ_comp_δ_castSucc_of_lt i j hij := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by
    simpa using (H t).h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by
    simpa using (H t).h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by
    simpa using (H t).h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by
    simpa using (H t).h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := Fan.IsLimit.hom_ext (hQ _) _ _ fun t => by
    simpa using (H t).h_comp_σ_succ_of_lt i j hji

/-- The product of a family of homotopies from `c t` to `d t` is a homotopy from `∏_t c t` to
`∏_t d t`: this is part (2) of [Stacks, Tag 08Q4]. -/
private lemma nonempty_homotopy_piMap (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {c d : ∀ t, X t ⟶ Y t}
    (H : ∀ t, Nonempty (SimplicialObject.Homotopy (c t) (d t))) :
    Nonempty (SimplicialObject.Homotopy (piMap p q hQ c) (piMap p q hQ d)) :=
  ⟨homotopyOfIsLimit q hQ fun t => by
    rw [piMap_comp, piMap_comp]; exact (H t).some.precomp (p t)⟩

/-- Changing one coordinate of a family into a homotopic morphism changes its product into a
homotopic one. -/
private lemma eqvGen_piMap_update [DecidableEq T] (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    (d : ∀ t, X t ⟶ Y t) (t₀ : T) {u v : X t₀ ⟶ Y t₀}
    (h : Relation.EqvGen
      (fun x y : X t₀ ⟶ Y t₀ => Nonempty (SimplicialObject.Homotopy x y)) u v) :
    Relation.EqvGen (fun x y : P ⟶ Q => Nonempty (SimplicialObject.Homotopy x y))
      (piMap p q hQ (Function.update d t₀ u)) (piMap p q hQ (Function.update d t₀ v)) := by
  induction h with
  | rel x y hxy =>
      refine Relation.EqvGen.rel _ _ (nonempty_homotopy_piMap p q hQ fun t => ?_)
      by_cases ht : t = t₀
      · subst ht
        simpa using hxy
      · simp only [Function.update_of_ne ht]
        exact ⟨SimplicialObject.Homotopy.refl _⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A function `F` of a family of arguments respects the equivalence relations generated
coordinatewise as soon as it does so in each single coordinate: if `c i` and `d i` are related
for every `i`, and `c i = d i` for `i` outside a finite set `S`, then `F c` and `F d` are
related. -/
private lemma eqvGen_of_forall_eqvGen {ι : Type*} [DecidableEq ι] {A : ι → Type*} {B : Type*}
    {r : ∀ i, A i → A i → Prop} {s : B → B → Prop} (F : (∀ i, A i) → B)
    (hF : ∀ (x : ∀ i, A i) (i : ι) (y z : A i), Relation.EqvGen (r i) y z →
      Relation.EqvGen s (F (Function.update x i y)) (F (Function.update x i z)))
    (S : Finset ι) : ∀ c d : ∀ i, A i, (∀ i, Relation.EqvGen (r i) (c i) (d i)) →
      (∀ i ∉ S, c i = d i) → Relation.EqvGen s (F c) (F d) := by
  induction S using Finset.induction_on with
  | empty =>
      intro c d _ hcd
      obtain rfl : c = d := funext fun i => hcd i (by simp)
      exact Relation.EqvGen.refl _
  | @insert i₀ S hi₀ ih =>
      intro c d hr hcd
      refine Relation.EqvGen.trans _ _ _ (ih c (Function.update d i₀ (c i₀)) ?_ ?_) ?_
      · intro i
        rcases eq_or_ne i i₀ with rfl | hi
        · simpa using Relation.EqvGen.refl (r := r i) _
        · simpa only [Function.update_of_ne hi] using hr i
      · intro i hi
        rcases eq_or_ne i i₀ with rfl | hii₀
        · simp
        · rw [Function.update_of_ne hii₀]
          exact hcd i (by simp [hii₀, hi])
      · simpa using hF d i₀ (c i₀) (d i₀) (hr i₀)

/-- Part (3) of [Stacks, Tag 08Q4], with the finite set of coordinates at which the two families
may differ given as a `Finset`. -/
private lemma eqvGen_piMap (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    (S : Finset T) : ∀ c d : ∀ t, X t ⟶ Y t,
      (∀ t, Relation.EqvGen
        (fun x y : X t ⟶ Y t => Nonempty (SimplicialObject.Homotopy x y)) (c t) (d t)) →
      (∀ t ∉ S, c t = d t) →
      Relation.EqvGen (fun x y : P ⟶ Q => Nonempty (SimplicialObject.Homotopy x y))
        (piMap p q hQ c) (piMap p q hQ d) := by
  classical
  exact eqvGen_of_forall_eqvGen (piMap p q hQ)
    (fun x t _ _ hyz => eqvGen_piMap_update p q hQ x t hyz) S

/-- Part (1) of [Stacks, Tag 08Q4], one composite: for `T` finite, if `c t ≫ e t` is homotopic to
`𝟙 (X t)` for every `t`, then `∏_t c t ≫ ∏_t e t` is homotopic to `𝟙 P`. -/
private lemma eqvGen_piMap_comp_id [Finite T] (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hP : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (P.obj n) fun t => (p t).app n))
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {c : ∀ t, X t ⟶ Y t} {e : ∀ t, Y t ⟶ X t}
    (h : ∀ t, Relation.EqvGen
      (fun x y : X t ⟶ X t => Nonempty (SimplicialObject.Homotopy x y)) (c t ≫ e t) (𝟙 (X t))) :
    Relation.EqvGen (fun x y : P ⟶ P => Nonempty (SimplicialObject.Homotopy x y))
      (piMap p q hQ c ≫ piMap q p hP e) (𝟙 P) := by
  classical
  have _inst := Fintype.ofFinite T
  have hcomp : piMap p q hQ c ≫ piMap q p hP e = piMap p p hP fun t => c t ≫ e t :=
    eq_piMap p p hP fun t => by simp
  have hid : (𝟙 P : P ⟶ P) = piMap p p hP fun t => 𝟙 (X t) := eq_piMap p p hP fun t => by simp
  rw [hcomp, hid]
  exact eqvGen_piMap p p hP Finset.univ _ _ h fun t ht => absurd (Finset.mem_univ t) ht

end

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Products of homotopies and of homotopy equivalences of simplicial objects. Let `X t`, `Y t`
(`t : T`) be families of simplicial objects of a category `C`, and let `p t : P ⟶ X t` and
`q t : Q ⟶ Y t` exhibit `P` and `Q` as the products `∏_t X t` and `∏_t Y t`, that is, degreewise
products in the sense of [Stacks, Tag 016Q]. Let `a t, b t : X t ⟶ Y t` be morphisms and let
`f, g : P ⟶ Q` be their products, pinned by `f ≫ q t = p t ≫ a t` and `g ≫ q t = p t ≫ b t`. Then:
* if there is a homotopy from `a t` to `b t` for every `t`, there is a homotopy from `f` to `g`
  (part (2), no finiteness needed);
* if `a t` and `b t` are homotopic for every `t` and `a t = b t` for all but finitely many `t`,
  then `f` and `g` are homotopic (part (3));
* if `T` is finite and every `a t` is a homotopy equivalence, then `f` is a homotopy
  equivalence, so `∏_t X t` and `∏_t Y t` are homotopy equivalent (part (1)). -/
@[stacks 08Q4 "the three conjuncts are parts (2), (3), (1), in that order. The products are \
  pinned degreewise by limit fans, as in [Stacks, Tag 016Q], instead of by `HasProduct` in \
  `SimplicialObject C`, and `f = ∏ a_t`, `g = ∏ b_t` by their characterizing equations. \
  Part (1) is stated in the stronger form that the product of homotopy equivalences is one, \
  the source's `homotopy equivalent` following by choice; part (3) is stated with the weaker \
  hypothesis that only finitely many coordinates differ. See the module docstring"]
public theorem nonempty_homotopy_and_homotopyEquivalences_of_isLimit
    {T : Type w} {X Y : T → SimplicialObject C} {P Q : SimplicialObject C}
    (p : ∀ t, P ⟶ X t) (q : ∀ t, Q ⟶ Y t)
    (hP : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (P.obj n) fun t => (p t).app n))
    (hQ : ∀ n : SimplexCategoryᵒᵖ, IsLimit (Fan.mk (Q.obj n) fun t => (q t).app n))
    {a b : ∀ t, X t ⟶ Y t} {f g : P ⟶ Q}
    (hf : ∀ t, f ≫ q t = p t ≫ a t) (hg : ∀ t, g ≫ q t = p t ≫ b t) :
    ((∀ t, Nonempty (Homotopy (a t) (b t))) → Nonempty (Homotopy f g)) ∧
      ({t | a t ≠ b t}.Finite →
        (∀ t, Relation.EqvGen (fun u v : X t ⟶ Y t => Nonempty (Homotopy u v)) (a t) (b t)) →
          Relation.EqvGen (fun u v : P ⟶ Q => Nonempty (Homotopy u v)) f g) ∧
      (Finite T → (∀ t, homotopyEquivalences C (a t)) → homotopyEquivalences C f) := by
  have hfa : f = piMap p q hQ a := eq_piMap p q hQ hf
  have hgb : g = piMap p q hQ b := eq_piMap p q hQ hg
  subst hfa
  subst hgb
  refine ⟨nonempty_homotopy_piMap p q hQ, fun hfin hEq =>
    eqvGen_piMap p q hQ hfin.toFinset a b hEq fun t ht =>
      not_not.mp fun h => ht (hfin.mem_toFinset.mpr h), fun _ hae => ?_⟩
  choose B hB₁ hB₂ using hae
  exact ⟨piMap q p hP B, eqvGen_piMap_comp_id p q hP hQ hB₁,
    eqvGen_piMap_comp_id q p hQ hP hB₂⟩

end CategoryTheory.SimplicialObject

end Products

end
