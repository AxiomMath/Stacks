module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation

/-!
# Existence of the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r` and
let `(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ`. Stacks 02U6 says that for a class
`α ∈ A_k(X)` there are **unique** classes `α_j ∈ A_{k-j}(X)`, `0 ≤ j ≤ r`, with `α_0 = α` and

  `∑_{i = 0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*(α_{r-i}) = 0`   in `A_{k-1}(P)`.

This file proves the **existence**, granted the surjectivity of the projective space bundle map
of Stacks 02TX, and defines the family `(α_j)_j`, the cap products `α ↦ α_j` as homomorphisms of
Chow groups, and the projective space bundle isomorphism of Stacks 02TX.

## Main definitions

* `Stacks.Chow.chernFamilyOfSummands` — a family of Chow classes indexed by the summands of the
  relation, read as a family indexed by the degree drop `j` of Stacks 02U6.
* `Stacks.Chow.projectiveBundleChernCapFamily` — the family `(c_j(ℰ) ∩ α)_{0 ≤ j ≤ r}` of a
  class `α ∈ A_k(X)`.
* `Stacks.Chow.chernCapOnChow` — the cap product `c_j(ℰ) ∩ - : A_k(X) ⟶ A_{k-j}(X)`, as an
  additive map.
* `Stacks.Chow.projectiveBundleChernMap` — the projective space bundle map of Stacks 02TX as a
  homomorphism, and `Stacks.Chow.projectiveBundleChowEquiv` the isomorphism it becomes under the
  two halves of that tag.

## Main results

* `Stacks.Chow.exists_isChernCapFamily` — **Stacks 02U6, existence**: granted the surjectivity of
  the projective space bundle map, every class has a family of Chern class cap products.
* `Stacks.Chow.existsUnique_isChernCapFamily` — **Stacks 02U6**: granted both halves of Stacks
  02TX, that family is unique.
* `Stacks.Chow.chernCapOnChow_zero` — `c_0(ℰ) ∩ α = α`.
* `Stacks.Chow.eq_projectiveBundleChernCapFamily` — every family characterizing `α` is the
  constructed one.

## References

* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Two pieces of pure algebra -/

/-- An alternating sum `∑_{i ≤ r} (-1)^i T_i(a_i)` can be made to vanish with its last entry
prescribed, as soon as the unsigned sum of the first `r` summands is surjective in its `r`
arguments. -/
private theorem exists_alternating_sum_eq_zero {r : ℕ} {M : ℕ → Type*} [∀ i, AddCommGroup (M i)]
    {N : Type*} [AddCommGroup N] (T : ∀ i : Fin (r + 1), M i.val →+ N)
    (hsurj : Function.Surjective
      fun β : (∀ i : Fin r, M i.val) ↦ ∑ i : Fin r, T i.castSucc (β i))
    (a : M (Fin.last r).val) :
    ∃ b : ∀ i : Fin (r + 1), M i.val, b (Fin.last r) = a ∧
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val • T i (b i) = 0 := by
  obtain ⟨β, hβ⟩ := hsurj (-((-1 : ℤ) ^ r • T (Fin.last r) a))
  have hβ' : ∑ i : Fin r, T i.castSucc (β i) = -((-1 : ℤ) ^ r • T (Fin.last r) a) := hβ
  refine ⟨Fin.lastCases (motive := fun m : Fin (r + 1) ↦ M m.val) a
    (fun i ↦ (-1 : ℤ) ^ i.val • β i), Fin.lastCases_last, ?_⟩
  have hterm : ∀ i : Fin r, (-1 : ℤ) ^ (i.castSucc.val) •
      T i.castSucc (Fin.lastCases (motive := fun m : Fin (r + 1) ↦ M m.val) a
        (fun j ↦ (-1 : ℤ) ^ j.val • β j) i.castSucc) = T i.castSucc (β i) := by
    intro i
    rw [Fin.lastCases_castSucc, map_zsmul, smul_smul, ← pow_add,
      show i.castSucc.val + i.val = 2 * i.val from by simp [two_mul], pow_mul,
      neg_one_sq, one_pow, one_smul]
  simp only [Fin.sum_univ_castSucc]
  rw [Fin.lastCases_last, Finset.sum_congr rfl (fun i _ ↦ hterm i), hβ']
  exact neg_add_cancel _

/-- A transport of Chow classes along an equality of degrees that holds by reflexivity is the
identity, whatever proof of the equality it is written with. -/
private theorem chowGroupCast_of_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {k : ℤ} (h : k = k) (x : chowGroup C q k) :
    chowGroupCast C q h x = x :=
  rfl

/-- Two members of a family of Chow classes indexed by equal indices agree after transport to a
common degree. -/
private theorem chowGroupCast_family_congr {C : ChowSituation.{u}} {X : Scheme.{u}}
    {q : X ⟶ C.S} [LocallyOfFiniteType q] {ι : Sort*} {f : ι → ℤ}
    (g : ∀ i, chowGroup C q (f i)) {i j : ι} (hij : i = j) {m : ℤ} (hi : f i = m)
    (hj : f j = m) : chowGroupCast C q hi (g i) = chowGroupCast C q hj (g j) := by
  subst hij
  rfl

/-! ### Reindexing a solution of the relation -/

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-- A family of Chow classes indexed by the summands of the relation of Stacks 02U6 — the `i`-th
member in degree `k - (r - i)`, the degree the `i`-th summand reads — as a family indexed by the
degree drop `j`, the indexing of the Chern class cap products. The two indexings are exchanged by
the involution `j ↦ r - j` of `{0, …, r}`. -/
def chernFamilyOfSummands (k : ℤ)
    (γ : ∀ i : Fin (r + 1), chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) (j : Fin (r + 1)) :
    chowGroup C sX (k - (j : ℤ)) :=
  chowGroupCast C sX
    (show k - ((r - (r - j.val) : ℕ) : ℤ) = k - (j : ℤ) from by
      have hj : j.val ≤ r := Nat.lt_succ_iff.mp j.isLt
      have hsub : r - (r - j.val) = j.val := by omega
      rw [hsub])
    (γ ⟨r - j.val, by omega⟩)

/-- The member of the reindexed family read by the `i`-th summand of the relation is the `i`-th
member of the family it was built from. -/
theorem chernFamilyOfSummands_summand (k : ℤ)
    (γ : ∀ i : Fin (r + 1), chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) (i : Fin (r + 1)) :
    chernFamilyOfSummands C sX r k γ ⟨r - i.val, by omega⟩ = γ i := by
  have hi : i.val ≤ r := Nat.lt_succ_iff.mp i.isLt
  rw [chernFamilyOfSummands,
    chowGroupCast_family_congr γ
      (show (⟨r - (r - i.val), by omega⟩ : Fin (r + 1)) = i from
        Fin.val_injective (show r - (r - i.val) = (i : ℕ) from by omega)) _ rfl]
  exact chowGroupCast_of_eq C sX rfl (γ i)

/-- The member of the reindexed family in degree `k` is the last member of the family it was
built from, which is the one the top summand of the relation reads. -/
theorem chowGroupCast_chernFamilyOfSummands_zero (k : ℤ)
    (γ : ∀ i : Fin (r + 1), chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) :
    chowGroupCast C sX
        (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)
        (chernFamilyOfSummands C sX r k γ ⟨0, Nat.zero_lt_succ r⟩) =
      chowGroupCast C sX
        (show k - ((r - (Fin.last r).val : ℕ) : ℤ) = k from by simp) (γ (Fin.last r)) := by
  rw [chernFamilyOfSummands, chowGroupCast_chowGroupCast]
  exact chowGroupCast_family_congr γ
    (show (⟨r - (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 1)) =
      Fin.last r from Fin.val_injective (by simp)) _ _

/-! ### Existence in Stacks 02U6 -/

/-- Granted the surjectivity of the projective space bundle map of Stacks 02TX, every class
`α ∈ A_k(X)` has a family of Chern class cap products: classes `α_j ∈ A_{k-j}(X)` with `α_0 = α`
satisfying the projective-bundle relation. -/
@[stacks 02U6 "existence; carries the projective bundle as a flat morphism of relative dimension
r - 1 with a first Chern class cap operator for its twist (Stacks 01O4, 02SO, 02TI), Stacks 02S1
for its projection, and the surjectivity half of Stacks 02TX"]
theorem exists_isChernCapFamily
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) :
    ∃ c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)),
      IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c := by
  obtain ⟨γ, hlast, hrel⟩ := exists_alternating_sum_eq_zero
    (M := fun n : ℕ ↦ chowGroup C sX (k - ((r - n : ℕ) : ℤ)))
    (fun i : Fin (r + 1) ↦ projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
      (Nat.lt_succ_iff.mp i.isLt))
    (hsurj k)
    (chowGroupCast C sX
      (show k = k - ((r - (Fin.last r).val : ℕ) : ℤ) from by simp) α)
  refine ⟨chernFamilyOfSummands C sX r k γ, ?_, ?_⟩
  · rw [chowGroupCast_chernFamilyOfSummands_zero C sX r k γ, hlast,
      chowGroupCast_chowGroupCast]
    exact chowGroupCast_of_eq C sX rfl α
  · refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ congrArg (fun z ↦ (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
        (Nat.lt_succ_iff.mp i.isLt) z)
      (chernFamilyOfSummands_summand C sX r k γ i)) hrel

/-- Granted both halves of Stacks 02TX, a class `α ∈ A_k(X)` has exactly one family of Chern class
cap products. -/
@[stacks 02U6 "existence and uniqueness together; carries the projective bundle as a flat
morphism of relative dimension r - 1 with a first Chern class cap operator for its twist
(Stacks 01O4, 02SO, 02TI), Stacks 02S1 for its projection, and both halves of Stacks 02TX"]
theorem existsUnique_isChernCapFamily
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) :
    ∃! c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)),
      IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c := by
  obtain ⟨c, hc⟩ := exists_isChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α
  exact ⟨c, hc, fun d hd ↦ eq_of_isChernCapFamily C sX sP π hsP r hπ hfac twist hinj k α hd hc⟩

/-! ### The Chern class cap products -/

/-- **Stacks 02U6.** The family `(c_j(ℰ) ∩ α)_{0 ≤ j ≤ r}` of Chern class cap products of a class
`α ∈ A_k(X)`, the `j`-th member lying in `A_{k-j}(X)`. -/
def projectiveBundleChernCapFamily
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) (j : Fin (r + 1)) : chowGroup C sX (k - (j : ℤ)) :=
  (exists_isChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α).choose j

/-- The family of Chern class cap products of `α` characterizes `α` in the sense of Stacks
02U6. -/
theorem isChernCapFamily_projectiveBundleChernCapFamily
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) :
    IsChernCapFamily C sX sP π hsP r hπ hfac twist k α
      (projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α) :=
  (exists_isChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α).choose_spec

/-- Granted the injectivity half of Stacks 02TX, every family characterizing `α` is the family of
Chern class cap products of `α`. -/
theorem eq_projectiveBundleChernCapFamily
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) {c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))}
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α c) :
    c = projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α :=
  eq_of_isChernCapFamily C sX sP π hsP r hπ hfac twist hinj k α hc
    (isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α)

/-- Granted the injectivity half of Stacks 02TX, the Chern class cap products are additive in the
cycle class. -/
theorem projectiveBundleChernCapFamily_add
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α β : chowGroup C sX k) :
    projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k (α + β) =
      fun j ↦ projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α j +
        projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k β j := by
  have hα := isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α
  have hβ := isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k β
  refine (eq_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hinj hsurj k (α + β)
    ⟨?_, ?_⟩).symm
  · rw [map_add, hα.1, hβ.1]
  · unfold ProjectiveBundleChernRelation at hα hβ ⊢
    simp only [map_add, smul_add]
    rw [Finset.sum_add_distrib, hα.2, hβ.2, add_zero]

/-- **Stacks 02U6.** Intersection with the `j`-th Chern class of `ℰ` as a homomorphism of Chow
groups, `c_j(ℰ) ∩ - : A_k(X) ⟶ A_{k-j}(X)`. -/
def chernCapOnChow (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (j : Fin (r + 1)) : chowGroup C sX k →+ chowGroup C sX (k - (j : ℤ)) :=
  AddMonoidHom.mk'
    (fun α ↦ projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α j)
    fun α β ↦ congrFun
      (projectiveBundleChernCapFamily_add C sX sP π hsP r hπ hfac twist hinj hsurj k α β) j

/-- `chernCapOnChow` sends `α` to the `j`-th member of the family of Chern class cap products of
`α`. -/
@[simp]
theorem chernCapOnChow_apply
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C sX k) :
    chernCapOnChow C sX sP π hsP r hπ hfac twist hinj hsurj k j α =
      projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α j :=
  rfl

/-- **Stacks 02U6.** The zeroth Chern class acts as the identity: `c_0(ℰ) ∩ α = α`. -/
theorem chernCapOnChow_zero
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ)
    (α : chowGroup C sX k) :
    chowGroupCast C sX
        (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)
        (chernCapOnChow C sX sP π hsP r hπ hfac twist hinj hsurj k
          ⟨0, Nat.zero_lt_succ r⟩ α) = α :=
  (isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α).1

/-! ### The projective space bundle isomorphism -/

/-- The projective space bundle map of Stacks 02TX,
`(α_0, …, α_{r-1}) ↦ ∑_{i<r} c₁(O_P(1))^i ∩ π^*α_i`, as a homomorphism
`⨁_{i<r} A_{k-r+i}(X) ⟶ A_{k-1}(P)`. -/
def projectiveBundleChernMap (k : ℤ) :
    (∀ i : Fin r, chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) →+
      chowGroup C sP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) :=
  AddMonoidHom.mk'
    (fun β ↦ ∑ i : Fin r, projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i.val
      i.isLt.le (β i))
    fun a b ↦ by
      simp only [Pi.add_apply, map_add]
      exact Finset.sum_add_distrib

/-- **Stacks 02TX.** Granted its two halves, the projective space bundle map is an isomorphism
`⨁_{i<r} A_{k-r+i}(X) ≅ A_{k-1}(P)`. -/
def projectiveBundleChowEquiv
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist) (k : ℤ) :
    (∀ i : Fin r, chowGroup C sX (k - ((r - i.val : ℕ) : ℤ))) ≃+
      chowGroup C sP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) :=
  AddEquiv.ofBijective (projectiveBundleChernMap C sX sP π hsP r hπ hfac twist k)
    ⟨hinj k, hsurj k⟩

end Stacks.Chow

end
