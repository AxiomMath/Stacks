module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.TotalChernClass
public import StacksCore.Tactic.StacksAttribute

/-!
# The Whitney sum formula in the Chow cohomology ring

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let

  `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules, `ℰᵢ` of rank `rᵢ`. The total Chern
class of a finite locally free module `ℱ` of rank `r` is the element

  `c(ℱ) = c_0(ℱ) + c_1(ℱ) + ⋯ + c_r(ℱ)`

of the Chow cohomology ring `A^*(X) = ⨁_p A^p(X)` of [Stacks, Tag 0B7E], `c_j(ℱ) ∈ A^j(X)` being
the bivariant Chern class of [Stacks, Tag 0B7H]. This file proves
[Stacks, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI):

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`   in `A^*(X)`.

The product formula holds in the ring `∏_{p ≥ 0} A^p(X)` of total classes
(`Stacks.Chow.totalChern_eq_mul_of_shortExact`), where it is checked on the operations on every
test scheme `g : T ⟶ X`: there it is the Whitney formula for the cap products of Stacks 02U6 on the
pulled back sequence, proved by the source's induction on `r₁` from Stacks 02UH, the projective
bundle formula and Stacks 02U8 (`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact`). It is
carried to `A^*(X)` by truncation: a total class vanishing above degree `a` is the finite sum
`∑_{p ≤ a} c_p` in `A^*(X)`, and truncation is multiplicative on classes of bounded degree
(`Stacks.Chow.TotalChowClass.toChowCohomology_mul`), because the product of `A^*(X)` and the
Cauchy product of total classes are both built from the products `A^i(X) × A^j(X) ⟶ A^{i+j}(X)`
of Stacks 0B75 (`Stacks.Chow.chowCohomologyMul_eq_mulId`).

## Main definitions

* `Stacks.Chow.TotalChowClass.toChowCohomology` — the sum `∑_{p < N} c_p ∈ A^*(X)` of the first
  `N` components of a total class.
* `Stacks.Chow.totalChernClassCohomology` — the total Chern class `c(ℱ) ∈ A^*(X)` of a finite
  locally free module of rank `r`.

## Main results

* `Stacks.Chow.chowCohomologyMul_eq_mulId` — the product of `A^*(X)` on homogeneous classes is
  the product of Stacks 0B75 used by total classes.
* `Stacks.Chow.TotalChowClass.toChowCohomology_mul` — truncation is multiplicative on classes of
  bounded degree.
* `Stacks.Chow.totalChernClassCohomology_eq_mul_of_shortExact` — **Stacks 02UI**.
* `Stacks.Chow.totalChernClassCohomology_eq_mul_of_shortExact_of_rank` — the same, with the rank
  of the middle term given rather than derived.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-! ### The two products agree -/

/-- **The product of Stacks 0B7E is the product of Stacks 0B75.** On homogeneous classes
`a ∈ A^p(Y)` and `b ∈ A^q(Y)`, the multiplication of the ring `A^*(Y)` and the product
`Stacks.Chow.BivariantClass.mulId` of the ring of total classes give the same class of
`A^{p+q}(Y)`: both cap as `a ∩ (b ∩ -)` on every test scheme. -/
theorem chowCohomologyMul_eq_mulId {p q : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    chowCohomologyMulOfInvertible C sY p q a b = a.mulId C sY b := by
  rw [← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact BivariantClass.eq_of_idRule_eq C sY _ _ _ fun g _ k α ↦ eq_of_heq <|
    (chowCohomologyMul_toIdentityCapRule_heq C _ sY
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C) a b g k α).trans
        (BivariantClass.idRule_mulId C sY a b g k α).symm

/-- The product `0 · b` of Stacks 0B75 vanishes. -/
theorem BivariantClass.zero_mulId {p q : ℤ}
    (b : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) :
    (0 : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p).mulId C sY b = 0 := by
  rw [← chowCohomologyMul_eq_mulId, ← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact chowCohomologyZero_mul C _ sY _ b

/-- The product `a · 0` of Stacks 0B75 vanishes. -/
theorem BivariantClass.mulId_zero {p q : ℤ}
    (a : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    a.mulId C sY (0 : chowCohomologyComponent C (gysinSystemOfInvertible C) sY q) = 0 := by
  rw [← chowCohomologyMul_eq_mulId, ← chowCohomologyRingMul_gysinSystemOfInvertible]
  exact chowCohomologyMul_zero C _ sY _ a

/-- A homogeneous class placed in `A^*(Y)` does not see a transport of its degree. -/
theorem of_bivariantClassDegreeCongr {p p' : ℤ} (h : p = p')
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) :
    DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p) p'
        (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) h c) =
      DirectSum.of _ p c := by
  subst h
  rfl

/-! ### Truncation of total classes -/

namespace TotalChowClass

/-- **The truncation of a total class.** The element `∑_{p < N} c_p` of the Chow cohomology
`A^*(Y) = ⨁_p A^p(Y)` of Stacks 0B7E. For a class vanishing in degrees `≥ N` this is the class
itself, read in the direct sum. -/
def toChowCohomology (N : ℕ) (c : TotalChowClass C sY) :
    chowCohomology C (gysinSystemOfInvertible C) sY :=
  ∑ m ∈ range N, DirectSum.of _ (m : ℤ) (c m)

variable {C sY}

/-- The truncation of `0` is `0`. -/
@[simp]
theorem toChowCohomology_zero (N : ℕ) : toChowCohomology C sY N 0 = 0 := by
  simp [toChowCohomology]

/-- The truncation of `c d` is a sum over the pairs `(m, j)` with `j ≤ m < N`. -/
private theorem toChowCohomology_mul_eq_sum_sigma (c d : TotalChowClass C sY) (N : ℕ) :
    toChowCohomology C sY N (c * d) =
      ∑ x ∈ (range N).sigma (fun m ↦ range (m + 1)),
        DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
          (x.1 : ℤ) (mulTerm c d x.1 x.2) := by
  rw [toChowCohomology, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [mul_apply, map_sum]

/-- **Truncation is multiplicative on classes of bounded degree.** If `c` vanishes above degree
`a` and `d` vanishes above degree `b`, then `c d` vanishes above degree `a + b` and its truncation
is the product in `A^*(Y)` of the truncations of `c` and `d`. -/
theorem toChowCohomology_mul (c d : TotalChowClass C sY) (a b : ℕ)
    (hc : ∀ i, a < i → c i = 0) (hd : ∀ j, b < j → d j = 0) :
    letI := chowCohomologyRingOfInvertible C sY
    toChowCohomology C sY (a + b + 1) (c * d) =
      toChowCohomology C sY (a + 1) c * toChowCohomology C sY (b + 1) d := by
  let := chowCohomologyGRingOfInvertible C sY
  -- the summand `c_i d_j ∈ A^{i+j}(Y)` placed in `A^*(Y)`
  let F : ℕ × ℕ → chowCohomology C (gysinSystemOfInvertible C) sY := fun x ↦
    DirectSum.of _ ((x.1 : ℤ) + (x.2 : ℤ)) ((c x.1).mulId C sY (d x.2))
  have hF : ∀ i i' j : ℕ, i' = i →
      DirectSum.of (fun p ↦ chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
        ((i' : ℤ) + (j : ℤ)) ((c i').mulId C sY (d j)) = F (i, j) := by
    rintro i i' j rfl
    rfl
  -- the right-hand side is the sum of the `F (i, j)` over `i ≤ a`, `j ≤ b`
  have hR : toChowCohomology C sY (a + 1) c * toChowCohomology C sY (b + 1) d =
      ∑ x ∈ range (a + 1) ×ˢ range (b + 1), F x := by
    rw [toChowCohomology, toChowCohomology, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [DirectSum.of_mul_of]
    exact congrArg (DirectSum.of _ _) (chowCohomologyMul_eq_mulId C sY (c i) (d j))
  rw [toChowCohomology_mul_eq_sum_sigma, hR]
  symm
  refine Finset.sum_of_injOn (fun x ↦ ⟨x.1 + x.2, x.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    ext <;> simp <;> omega
  · rintro ⟨i, j⟩ hx
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hx
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_range]
    omega
  · rintro ⟨m, j⟩ hx hn
    simp only [mem_sigma, mem_range] at hx
    have hjm : j ≤ m := by omega
    rw [mulTerm, dite_eq_left hjm, of_bivariantClassDegreeCongr]
    by_cases hi : a < m - j
    · rw [hc _ hi, BivariantClass.zero_mulId, map_zero]
    by_cases hj : b < j
    · rw [hd _ hj, BivariantClass.mulId_zero, map_zero]
    refine absurd ⟨(m - j, j), ?_, ?_⟩ hn
    · simp only [coe_product, Set.mem_prod, mem_coe, mem_range]
      omega
    · simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      omega
  · rintro ⟨i, j⟩ _
    rw [mulTerm, dite_eq_left (Nat.le_add_left j i), of_bivariantClassDegreeCongr]
    exact (hF i (i + j - j) j (Nat.add_sub_cancel i j)).symm

end TotalChowClass

/-! ### The total Chern class in `A^*(X)` -/

variable (F : Y.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- **The total Chern class** `c(ℱ) = c_0(ℱ) + c_1(ℱ) + ⋯ + c_r(ℱ)` of a finite locally free
module of rank `r`, as an element of the Chow cohomology ring `A^*(Y) = ⨁_p A^p(Y)` of
Stacks 0B7E: the sum of the bivariant Chern classes `c_j(ℱ) ∈ A^j(Y)` of Stacks 0B7H. -/
def totalChernClassCohomology : chowCohomology C (gysinSystemOfInvertible C) sY :=
  ∑ j : Fin (r + 1), DirectSum.of _ (j : ℤ) (GenuineChern.chernClass C sY F r j)

/-- The total Chern class in `A^*(Y)` is the truncation of the total Chern class in
`∏_{p ≥ 0} A^p(Y)` to the degrees `≤ r`. -/
theorem totalChernClassCohomology_eq_toChowCohomology :
    totalChernClassCohomology C sY F r =
      TotalChowClass.toChowCohomology C sY (r + 1) (totalChern C sY F r) := by
  rw [totalChernClassCohomology, TotalChowClass.toChowCohomology,
    ← Fin.sum_univ_eq_sum_range (fun m ↦ DirectSum.of _ (m : ℤ) (totalChern C sY F r m))]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [totalChern_apply]

/-- **Stacks 02UI, the Whitney sum formula.** Let `X` be locally of finite type over the base and
let `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` be a short exact sequence of `𝒪_X`-modules with `ℰ₁`, `ℰ₂` finite
locally free of ranks `r₁`, `r₂`; then `ℰ` is finite locally free of rank `r₁ + r₂`
(`Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact`), and the total Chern classes
satisfy

  `c(ℰ) = c(ℰ₁) c(ℰ₂)`   in `A^*(X)`. -/
@[stacks 02UI "c(E) = c(E₁) c(E₂) in the Chow cohomology ring A^*(X) of Stacks 0B7E, for a short \
  exact sequence 0 -> E₁ -> E -> E₂ -> 0 on X locally of finite type over the base with E₁, E₂ \
  finite locally free of ranks r₁, r₂ (E is then finite locally free of rank r₁ + r₂); c(F) is \
  the sum in A^*(X) of the bivariant Chern classes c_j(F) of Stacks 0B7H"]
theorem totalChernClassCohomology_eq_mul_of_shortExact (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] :
    letI := chowCohomologyRingOfInvertible C sY
    haveI := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ ‹_› ‹_›
    totalChernClassCohomology C sY S.X₂ (r₁ + r₂) =
      totalChernClassCohomology C sY S.X₁ r₁ * totalChernClassCohomology C sY S.X₃ r₂ := by
  have := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ ‹_› ‹_›
  rw [totalChernClassCohomology_eq_toChowCohomology, totalChernClassCohomology_eq_toChowCohomology,
    totalChernClassCohomology_eq_toChowCohomology, totalChern_eq_mul_of_shortExact C sY S hS r₁ r₂]
  exact TotalChowClass.toChowCohomology_mul _ _ r₁ r₂
    (fun _ hi ↦ totalChern_apply_of_lt C sY S.X₁ r₁ hi)
    (fun _ hj ↦ totalChern_apply_of_lt C sY S.X₃ r₂ hj)

/-- **Stacks 02UI, with the middle term carrying its own rank.** On a nonempty scheme that rank
is forced to be `r₁ + r₂`; on the empty scheme both sides vanish. For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules `ℰ₁`, `ℰ`, `ℰ₂` of ranks `r₁`, `r`, `r₂`,
the total Chern classes satisfy `c(ℰ) = c(ℰ₁) c(ℰ₂)` in `A^*(X)`. -/
theorem totalChernClassCohomology_eq_mul_of_shortExact_of_rank (S : ShortComplex Y.Modules)
    (hS : S.ShortExact) (r₁ r r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] :
    letI := chowCohomologyRingOfInvertible C sY
    totalChernClassCohomology C sY S.X₂ r =
      totalChernClassCohomology C sY S.X₁ r₁ * totalChernClassCohomology C sY S.X₃ r₂ := by
  let := chowCohomologyRingOfInvertible C sY
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y⟩⟩
  · have h0 : ∀ (G : Y.Modules) (s : ℕ)
        [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G s],
        totalChernClassCohomology C sY G s = 0 := fun G s _ ↦ by
      rw [totalChernClassCohomology_eq_toChowCohomology,
        (TotalChowClass.subsingleton_of_isEmpty (C := C) sY).elim (totalChern C sY G s) 0,
        TotalChowClass.toChowCohomology_zero]
    rw [h0, h0, h0, zero_mul]
  · have h₂ := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ ‹_› ‹_›
    have hr : r = r₁ + r₂ := Scheme.Modules.isFiniteLocallyFreeOfRank_unique S.X₂ ‹_› h₂ y
    subst hr
    convert totalChernClassCohomology_eq_mul_of_shortExact C sY S hS r₁ r₂ using 2

end Stacks.Chow

end
