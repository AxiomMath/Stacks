module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleComm
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernFamily
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTensorExact
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern roots of a filtered module, and of a tensor product

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let `X`
be locally of finite type over `S`. The total Chern class of a finite locally free module of
rank `r`, `c(ℱ) = 1 + c₁(ℱ) + ⋯ + c_r(ℱ)`, is an element
`Stacks.Chow.GenuineChern.chernFamily C sX ℱ r` of the ring
`Stacks.Chow.GradedCapFamily (Stacks.Chow.chowGroup C sX)` of graded cap families on the Chow
groups of `X`. This file computes it for a module presented by a filtration with invertible
successive quotients, and for a tensor product of two such modules:

  `c(ℰ) = ∏_i (1 + c₁(ℒ_i))`                     (Stacks 02UJ),

  `c(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∏_i ∏_j (1 + c₁(𝒩_j) + c₁(ℒ_i))`,

so that the Chern roots of a tensor product are the sums `x_i + y_j` of the Chern roots of the
factors. **Everything here is proved with nothing carried.**

The second identity is the content that the source of Stacks 0FA6 and of Stacks 0F9D hides behind
"ordering pairs `(i, j)` lexicographically we obtain a filtration with successive quotients
`ℒ_i ⊗ 𝒩_j`", and that
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses` and
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsDischarge` carry as the
hypothesis `hquot`.

## The lexicographic filtration is assembled in two stages, not interpolated

The source's filtration of `ℰ₁ ⊗ ℰ₂` interpolates the stages
`ℰ_i ⊗ ℱ_j + ℰ_{i-1} ⊗ ℱ` between `ℰ_{i-1} ⊗ ℱ` and `ℰ_i ⊗ ℱ`, a sum of subobjects which this
repository has no declaration for. It is not needed. Tensoring the filtration of `ℰ₁` by `ℰ₂`
gives `c(ℰ₁ ⊗ ℰ₂) = ∏_i c(ℒ_i ⊗ ℰ₂)` (`Stacks.Chow.chernFamily_tensorObj_eq_prod`), because
tensoring by a finite locally free module is exact and the Whitney relation of Stacks 02UI
multiplies the factors; and tensoring the filtration of `ℰ₂` by the invertible `ℒ_i` gives
`c(ℰ₂ ⊗ ℒ_i) = ∏_j (1 + c₁(𝒩_j) + c₁(ℒ_i))`
(`Stacks.Chow.chernFamily_tensorObj_invertible_eq_prod`). Composing the two — through the braiding
`Stacks.Chow.tensorObjSwap`, which exchanges `ℒ_i ⊗ ℰ₂` with `ℰ₂ ⊗ ℒ_i` — is the lexicographic
filtration's Chern class without ever naming the lexicographic filtration.

## Why the ring of graded cap families, and not `A^*(X)`

`Stacks.Chow.GradedCapFamily` carries a `Ring` instance
(`Stacks.Chow.instRingGradedCapFamily`), the Whitney relation of Stacks 02UI holds in it with
nothing carried (`Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact`), flat pullback
intertwines total Chern classes there by Stacks 02U8
(`Stacks.Chow.GenuineChern.intertwines_chernFamily`), and an injective intertwiner descends
identities (`Stacks.Chow.eq_of_intertwines`). That is exactly the package the splitting
principle needs, and it is the reason the computation is done here rather than in the cycle-level
vocabulary of `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity`, where
Stacks 02UJ is stated with four carried inputs.

The ring is **not** commutative. The products above are therefore ordered, written as
`List.prod` of a `List.ofFn`; `Stacks.Chow.commute_chernFamily` — Stacks 02UA with nothing
carried — says the factors commute, and is what the inductions use to reorder them.

## Main definitions

* `Stacks.Chow.firstChernElem` — `c₁(ℒ)` for a module of rank one, as an element of the ring of
  graded cap families: the index-`1` homogeneous component of its total Chern class.
* `Stacks.Chow.HasQuotients` — a filtration with prescribed successive quotients, recursively on
  the length. This is `Stacks.WeilCohomology.HasInvertibleFiltration` with the quotients named.
* `Stacks.Chow.tensorObjSwap` — the braiding `A ⊗_{𝒪_X} B ≅ B ⊗_{𝒪_X} A`.

## Main results

* `Stacks.Chow.comm_apply_chernFamily`, `Stacks.Chow.commute_chernFamily` — **Stacks 02UA** at
  each pair of indices and in the ring of graded cap families.
* `Stacks.Chow.firstChernElem_tensorObj` — **Stacks 02SP** there: `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)`.
* `Stacks.Chow.chernFamily_rank_one_eq` — `c(ℒ) = 1 + c₁(ℒ)` in rank one.
* `Stacks.Chow.exists_hasQuotients_of_hasInvertibleFiltration` — the filtration Stacks 02UL
  delivers, with its quotients named. The elimination out of the inductive `Prop` is legitimate
  because the target is a `Prop`.
* `Stacks.Chow.chernFamily_eq_prod_of_hasQuotients` — **Stacks 02UJ** in the ring of graded cap
  families, with nothing carried.
* `Stacks.Chow.hasQuotients_tensorObj_invertible`,
  `Stacks.Chow.chernFamily_tensorObj_invertible_eq_prod` — the twist of a filtered module by an
  invertible module, and its Chern roots `y_j + c₁(ℒ)`.
* `Stacks.Chow.chernFamily_tensorObj_eq_prod` — the outer stage: `c(ℰ ⊗ ℱ) = ∏_i c(ℒ_i ⊗ ℱ)`.
* `Stacks.Chow.chernFamily_tensorObj_eq_prod_prod` — **the Chern roots of a tensor product are
  the sums of the Chern roots.**

## What comes next

Two steps carry these identities to the constant-rank form of Stacks 0F9D, and both are taken in
the two files built on this one:

1. the **power sums**. `P_p` of Stacks 0F9B is available as a polynomial
   (`AlgebraicGeometry.powerSumChernPolynomial`), its evaluation at a family of Chern classes
   that split is identified with `∑ x_i^p` in a *commutative* ring
   (`AlgebraicGeometry.powerSumOfChernClasses_eq_powerSumOfRoots`), and the binomial convolution
   for the roots `x_i + y_j` is `AlgebraicGeometry.powerSumOfRoots_tensorRoots`. The commutative
   ring is the subring the Chern classes generate — every pair of which commutes, by
   `Stacks.Chow.commute_homComponent_chernFamily`, Stacks 02UA read componentwise. That is
   `Stacks.Chow.chernSubring` of
   `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumElem`, where
   `Stacks.Chow.powerSumChernElem` is `P_p` of the Chern classes of a module and the identities
   above are read coefficientwise as `AlgebraicGeometry.HasChernRoots`;
2. the **descent along `π^*`**. The identities above hold on the `P` of Stacks 02UL, where the
   filtrations live. Carrying them down to `X` is `Stacks.Chow.eq_of_intertwines` with
   `Stacks.Chow.GenuineChern.intertwines_chernFamily` for Stacks 02U8 and
   `Stacks.Chow.SplittingMorphism.injective_pullbackChow` for the injectivity of `π^*`; that the
   power sums intertwine as well is `Stacks.Chow.intertwines_powerSumChernElem` of
   `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumDescent`.

That constant-rank form is `Stacks.Chow.powerSumChernElem_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsTotal`. Stacks 0F9D itself
is `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum`, the same
identity between bivariant classes in the ring `A^*(X)` = `Stacks.Chow.TotalChowClass` and with
no hypothesis on the ranks; the constant-rank form read on every test scheme is what makes it.

## References

* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0FA6](https://stacks.math.columbia.edu/tag/0FA6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### Commutation in the ring of graded cap families -/

section Algebra

universe v

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- Two graded cap families whose components commute termwise, up to the transport comparing
`k - i - j` with `k - j - i`, commute in the ring of graded cap families. -/
theorem commute_of_comm_apply {a b : GradedCapFamily G}
    (h : ∀ (k : ℤ) (i j : ℕ) (x : G k),
      a (k - (j : ℤ)) i (b k j x) =
        gradedDegreeCast G (show k - (i : ℤ) - (j : ℤ) = k - (j : ℤ) - (i : ℤ) by ring)
          (b (k - (i : ℤ)) j (a k i x))) :
    Commute a b := by
  have key : ∀ (k : ℤ) (m j : ℕ), j ≤ m → ∀ x : G k,
      convolveTerm a b k m j x = convolveTerm b a k m (m - j) x := by
    intro k m j hj x
    rw [convolveTerm_of_le a b k hj, convolveTerm_of_le b a k (show m - j ≤ m by omega),
      capTo_congr_index b (show m - (m - j) = j by omega), capTo_def, capTo_def,
      h k (m - j) j x, gradedDegreeCast_gradedDegreeCast]
  funext k m
  refine AddMonoidHom.ext fun x => ?_
  rw [gradedCap_mul_def, gradedCap_mul_def, convolve_apply, convolve_apply]
  calc ∑ j ∈ range (m + 1), convolveTerm a b k m j x
      = ∑ j ∈ range (m + 1), convolveTerm b a k m (m + 1 - 1 - j) x := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simpa using key k m j (Nat.lt_succ_iff.mp (mem_range.mp hj)) x
    _ = ∑ j ∈ range (m + 1), convolveTerm b a k m j x :=
        Finset.sum_range_reflect (fun j => convolveTerm b a k m j x) (m + 1)

end Algebra

/-! ### The total Chern classes of two modules commute -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The transport of degrees of a graded cap family on the Chow groups is the transport of Chow
groups: both are `AddEquiv.cast`. -/
theorem gradedDegreeCast_chowGroup {k l : ℤ} (h : k = l) (x : chowGroup C sX k) :
    gradedDegreeCast (chowGroup C sX) h x = chowGroupCast C sX h x := rfl

/-- **Stacks 02UA before the indices are quantified.** The cap product with `c_i(ℰ)` and the cap
product with `c_j(ℱ)` commute in every degree and at every pair of indices, up to the transport
comparing `k - i - j` with `k - j - i`. Above the rank both operations vanish, so only the range
`i ≤ r`, `j ≤ s` uses `Stacks.Chow.GenuineChern.chernCap_chernCap_comm`. -/
theorem comm_apply_chernFamily (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (F : X.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
    (k : ℤ) (i j : ℕ) (x : chowGroup C sX k) :
    GenuineChern.chernFamily C sX E r (k - (j : ℤ)) i
        (GenuineChern.chernFamily C sX F s k j x)
      = gradedDegreeCast (chowGroup C sX)
          (show k - (i : ℤ) - (j : ℤ) = k - (j : ℤ) - (i : ℤ) by ring)
          (GenuineChern.chernFamily C sX F s (k - (i : ℤ)) j
            (GenuineChern.chernFamily C sX E r k i x)) := by
  dsimp only [GenuineChern.chernFamily]
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ s
    · rw [chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX F s k hj,
        chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX E r _ hi,
        chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX E r k hi,
        chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX F s _ hj,
        gradedDegreeCast_chowGroup]
      exact GenuineChern.chernCap_chernCap_comm C sX E r F s k
        ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩ x
    · rw [chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX F s k hj,
        chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX F s _ hj]
      simp
  · rw [chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX E r _ hi,
      chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX E r k hi]
    simp

/-- **Stacks 02UA in the ring of graded cap families.** The total Chern classes of two finite
locally free modules commute: componentwise this is
`Stacks.Chow.GenuineChern.chernCap_chernCap_comm`, which is
`Stacks.Chow.comm_apply_chernFamily`. -/
theorem commute_chernFamily (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (F : X.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    Commute (GenuineChern.chernFamily C sX E r) (GenuineChern.chernFamily C sX F s) :=
  commute_of_comm_apply fun k i j x => comm_apply_chernFamily C sX E r F s k i j x

/-! ### The first Chern class of an invertible module as a ring element -/

attribute [local instance] isFiniteLocallyFreeOfRank_one_of_isInvertible

/-- **The first Chern class of a module of rank one as an element of the ring of graded cap
families**: the index-`1` homogeneous component of its total Chern class. -/
def firstChernElem (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    GradedCapFamily (chowGroup C sX) :=
  homComponent 1 (GenuineChern.chernFamily C sX L 1)

section RankOne

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]

/-- The first Chern class is homogeneous of index one. -/
theorem isHomogeneous_firstChernElem :
    (firstChernElem C sX L).IsHomogeneous 1 :=
  isHomogeneous_homComponent 1 _

/-- The index-`1` component of the first Chern class is the Chern class cap product. -/
theorem firstChernElem_apply_one (k : ℤ) :
    firstChernElem C sX L k 1 = GenuineChern.chernCap C 1 sX L k 1 := by
  rw [firstChernElem, homComponent_apply_self]
  exact chernCapFamilyOnChow_of_le C (GenuineChern.chernCap C) sX L 1 k le_rfl

/-- **`c(ℒ) = 1 + c₁(ℒ)` for a module of rank one.** -/
theorem chernFamily_rank_one_eq :
    GenuineChern.chernFamily C sX L 1 = 1 + firstChernElem C sX L := by
  funext k i
  match i with
  | 0 =>
      rw [GenuineChern.chernFamily_apply_zero]
      have : firstChernElem C sX L k 0 = 0 :=
        homComponent_apply_of_ne (by omega) _ _
      simp [this]
  | 1 =>
      have h1 : (1 : GradedCapFamily (chowGroup C sX)) k 1 = 0 := gradedCap_one_of_ne one_ne_zero k
      have : firstChernElem C sX L k 1 = GenuineChern.chernFamily C sX L 1 k 1 :=
        homComponent_apply_self 1 _ _
      simp [this, h1]
  | (n + 2) =>
      have h0 : GenuineChern.chernFamily C sX L 1 k (n + 2) = 0 :=
        chernCapFamilyOnChow_of_gt C (GenuineChern.chernCap C) sX L 1 k (by omega)
      have h1 : (1 : GradedCapFamily (chowGroup C sX)) k (n + 2) = 0 :=
        gradedCap_one_of_ne (by omega) k
      have h2 : firstChernElem C sX L k (n + 2) = 0 :=
        homComponent_apply_of_ne (by omega) _ _
      simp [h0, h1, h2]

end RankOne

/-! ### Stacks 02SP: the first Chern class is additive in a tensor product -/

section Tensor

variable (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The cap operator of an invertible module acts by `Stacks.Chow.firstChernClassCapChow`. -/
theorem invCap_capOnChow_eq (k : ℤ) (y : chowGroup C sX (k + 1)) :
    (invCap C sX L).capOnChow C sX k y = firstChernClassCapChow C k sX L y := rfl

/-- **Stacks 02SP in the ring of graded cap families**: `c₁(ℒ ⊗ 𝒩) = c₁(ℒ) + c₁(𝒩)`. -/
theorem firstChernElem_tensorObj :
    firstChernElem C sX (Scheme.Modules.tensorObj L N) =
      firstChernElem C sX L + firstChernElem C sX N := by
  funext k i
  match i with
  | 0 =>
      simp [firstChernElem, homComponent_apply_of_ne (show (0 : ℕ) ≠ 1 by omega)]
  | 1 =>
      rw [firstChernElem_apply_one]
      refine AddMonoidHom.ext fun α => ?_
      have hsum : (firstChernElem C sX L + firstChernElem C sX N) k 1 α =
          firstChernElem C sX L k 1 α + firstChernElem C sX N k 1 α := rfl
      rw [hsum, firstChernElem_apply_one, firstChernElem_apply_one,
        GenuineChern.chernCap_one_eq_invCap, GenuineChern.chernCap_one_eq_invCap,
        GenuineChern.chernCap_one_eq_invCap, invCap_capOnChow_eq, invCap_capOnChow_eq,
        invCap_capOnChow_eq]
      exact (firstChernClassCapChow_tensorObj C sX (k - 1) L N _).symm
  | (n + 2) =>
      simp [firstChernElem, homComponent_apply_of_ne (show n + 2 ≠ 1 by omega)]

end Tensor

/-! ### Stacks 02UJ: the total Chern class of a filtered module -/

section Filtration

/-- **A filtration with prescribed successive quotients.** `HasQuotients X r E L` says that `E`
carries a filtration `0 = ℱ_0 ⊆ ℱ_1 ⊆ ⋯ ⊆ ℱ_r = E` of length `r` whose `i`-th successive
quotient is `L i`, each stage being finite locally free of its own rank. The quotients are not
required to be invertible here; that is an instance hypothesis of the statements that use it. -/
def HasQuotients (X : Scheme.{u}) : (r : ℕ) → X.Modules → (Fin r → X.Modules) → Prop
  | 0, E, _ => CategoryTheory.Limits.IsZero E
  | (r + 1), E, L => ∃ (F : X.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
      (f : F ⟶ E) (g : E ⟶ L 0) (w : f ≫ g = 0),
      (CategoryTheory.ShortComplex.mk f g w).ShortExact ∧
        HasQuotients X r F (fun i => L i.succ)

/-- A module carrying a filtration with `r` quotients is finite locally free of rank `r` as soon
as the quotients are. -/
theorem isFiniteLocallyFreeOfRank_of_hasQuotients :
    ∀ (r : ℕ) (E : X.Modules) (L : Fin r → X.Modules)
      [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1],
      HasQuotients X r E L →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r := by
  intro r
  induction r with
  | zero => intro E L _ h; exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero h
  | succ r _ =>
      intro E L _ h
      obtain ⟨F, hF, f, g, w, hS, _⟩ := h
      exact GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
        (CategoryTheory.ShortComplex.mk f g w) hS r 1 hF inferInstance

/-- A product built by peeling off the first factor of a family: `a = b * c` with `b` and `c`
commuting, `b` the product of the tail and `c` the head. -/
private theorem eq_prod_ofFn_succ_of_mul {R : Type*} [Monoid R] {n : ℕ} {a b c : R}
    {f : Fin (n + 1) → R} (h : a = b * c) (hc : Commute b c)
    (hb : b = (List.ofFn fun i => f i.succ).prod) (h0 : c = f 0) :
    a = (List.ofFn f).prod := by
  rw [h, hc.eq, hb, h0, List.ofFn_succ, List.prod_cons]

/-- **Stacks 02UJ in the ring of graded cap families**: if `ℰ` carries a filtration of length `r`
whose successive quotients are the invertible modules `ℒ_i`, then

  `c(ℰ) = ∏_{i} (1 + c₁(ℒ_i))`, the product taken in the given order

in the ring of graded cap families on the Chow groups of `X`. No hypothesis is carried: the
Whitney relation `Stacks.Chow.GenuineChern.chernFamily_eq_mul_of_shortExact` of Stacks 02UI is
unconditional, and the rank-one factor is `Stacks.Chow.chernFamily_rank_one_eq`. -/
theorem chernFamily_eq_prod_of_hasQuotients :
    ∀ (r : ℕ) (E : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      (L : Fin r → X.Modules)
      [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1],
      HasQuotients X r E L →
      GenuineChern.chernFamily C sX E r =
        (List.ofFn fun i => 1 + firstChernElem C sX (L i)).prod := by
  intro r
  induction r with
  | zero =>
      intro E _ L _ _
      rw [GenuineChern.chernFamily_of_rank_zero]
      simp
  | succ r ih =>
      intro E _ L _ h
      obtain ⟨F, hF, f, g, w, hS, hrec⟩ := h
      have := hF
      exact eq_prod_ofFn_succ_of_mul
        (GenuineChern.chernFamily_eq_mul_of_shortExact C sX
          (CategoryTheory.ShortComplex.mk f g w) hS r 1)
        (commute_chernFamily C sX F r (L 0) 1) (ih F (fun i => L i.succ) hrec)
        (chernFamily_rank_one_eq C sX (L 0))

/-- **The filtration Stacks 02UL delivers, with its quotients named.** The inductive
`Stacks.WeilCohomology.HasInvertibleFiltration` eliminates into the existence of a family of
invertible modules which are the successive quotients of a filtration in the sense of
`Stacks.Chow.HasQuotients`: the elimination is allowed because the target is a `Prop`. -/
theorem exists_hasQuotients_of_hasInvertibleFiltration :
    ∀ {E : X.Modules} {r : ℕ}, Stacks.WeilCohomology.HasInvertibleFiltration X E r →
      ∃ L : Fin r → X.Modules,
        (∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
          (L i)) ∧ HasQuotients X r E L := by
  intro E r h
  induction h with
  | nil E hE => exact ⟨Fin.elim0, fun i => i.elim0, hE⟩
  | @step E F L r f g w hS hL hE hF ih =>
      obtain ⟨Lq, hLq, hq⟩ := ih
      have : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
          X.ringCatSheaf.property (Lq i) := hLq
      refine ⟨Fin.cons L Lq, ?_, ⟨F, ?_, f, g, w, hS, hq⟩⟩
      · refine Fin.cases ?_ ?_
        · exact hL
        · exact hLq
      · exact isFiniteLocallyFreeOfRank_of_hasQuotients r F Lq hq

/-! ### Twisting a filtration by an invertible module -/

/-- **The braiding** `A ⊗_{𝒪_X} B ≅ B ⊗_{𝒪_X} A` of `𝒪_X`-modules on a scheme, Stacks 01CA. -/
def tensorObjSwap (A B : X.Modules) :
    Scheme.Modules.tensorObj A B ≅ Scheme.Modules.tensorObj B A :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace A B

/-- **The rank of a twist by a module of rank one.** This is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf` at `s * 1 = s`, read at
the spelling `AlgebraicGeometry.Scheme.Modules.tensorObj`. -/
theorem isFiniteLocallyFreeOfRank_tensorObj_rankOne (E L : X.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj E L) s := by
  have h1 := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E L s 1
  rw [mul_one] at h1
  exact h1

attribute [local instance] isFiniteLocallyFreeOfRank_tensorObj_rankOne

/-- **The rank of a tensor product with a module of rank one on the left.** -/
theorem isFiniteLocallyFreeOfRank_tensorObj_rankOneLeft (L E : X.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj L E) s := by
  have h1 := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X L E 1 s
  rw [one_mul] at h1
  exact h1

/-- **The rank of a tensor product**, Stacks 02U9, read at the spelling
`AlgebraicGeometry.Scheme.Modules.tensorObj`. -/
theorem isFiniteLocallyFreeOfRank_tensorObj_mul (E F : X.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj E F) (r * s) :=
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E F r s

attribute [local instance] isFiniteLocallyFreeOfRank_tensorObj_rankOneLeft
  isFiniteLocallyFreeOfRank_tensorObj_mul

/-- **Twisting a filtration by an invertible module.** If `ℰ` carries a filtration of length `s`
with successive quotients `𝒩_j`, then `ℰ ⊗_{𝒪_X} ℒ` carries one of the same length with
successive quotients `𝒩_j ⊗ ℒ`: tensoring by an invertible — hence flat — module is exact
(`Stacks.Chow.exists_shortExact_tensorModules`), and the ranks are multiplied by one. -/
theorem hasQuotients_tensorObj_invertible (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    ∀ (s : ℕ) (E : X.Modules) (N : Fin s → X.Modules)
      [∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (N j) 1],
      HasQuotients X s E N →
      HasQuotients X s (Scheme.Modules.tensorObj E L)
        (fun j => Scheme.Modules.tensorObj (N j) L) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (h := hL) L
  intro s
  induction s with
  | zero =>
      intro E N _ h
      have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero h
      exact isZero_of_isFiniteLocallyFreeOfRank_zero (Scheme.Modules.tensorObj E L)
  | succ s ih =>
      intro E N _ h
      obtain ⟨F, hF, f, g, w, hS, hrec⟩ := h
      have := hF
      obtain ⟨f', g', w', hS'⟩ := exists_shortExact_tensorModules L hL f g w hS
      exact ⟨Scheme.Modules.tensorObj F L, inferInstance, f', g', w', hS',
        ih F (fun j => N j.succ) hrec⟩

/-- **The Chern roots of an invertible twist.** If `ℰ` is filtered with invertible successive
quotients `𝒩_j`, `j < s`, and `ℒ` is invertible, then

  `c(ℰ ⊗ ℒ) = ∏_j (1 + c₁(𝒩_j) + c₁(ℒ))`

in the ring of graded cap families: the Chern roots of `ℰ ⊗ ℒ` are the `y_j + c₁(ℒ)`. Nothing is
carried: the filtration of the twist is `Stacks.Chow.hasQuotients_tensorObj_invertible`, the
product formula is `Stacks.Chow.chernFamily_eq_prod_of_hasQuotients` (Stacks 02UJ) and the
additivity of the first Chern class is `Stacks.Chow.firstChernElem_tensorObj` (Stacks 02SP). -/
theorem chernFamily_tensorObj_invertible_eq_prod (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (s : ℕ) (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E s]
    (N : Fin s → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (N j)] (h : HasQuotients X s E N) :
    haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible (h := hL) L
    GenuineChern.chernFamily C sX (Scheme.Modules.tensorObj E L) s =
      (List.ofFn fun j =>
        1 + (firstChernElem C sX (N j) + firstChernElem C sX L)).prod := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (h := hL) L
  have : ∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj (N j) L) := fun j => isInvertible_tensorObj (N j) L
  have hfun : (fun j : Fin s => 1 + firstChernElem C sX (Scheme.Modules.tensorObj (N j) L))
      = fun j : Fin s => 1 + (firstChernElem C sX (N j) + firstChernElem C sX L) := by
    funext j
    rw [firstChernElem_tensorObj]
  rw [chernFamily_eq_prod_of_hasQuotients C sX s (Scheme.Modules.tensorObj E L)
    (fun j => Scheme.Modules.tensorObj (N j) L)
    (hasQuotients_tensorObj_invertible L hL s E N h), hfun]

/-! ### Tensoring a filtration by a finite locally free module -/

/-- **The outer half of the lexicographic filtration of Stacks 0FA6 and Stacks 0F9D.** If `ℰ`
carries a filtration of length `r` with invertible successive quotients `ℒ_i` and `ℱ` is finite
locally free of rank `s`, then

  `c(ℰ ⊗ ℱ) = ∏_i c(ℒ_i ⊗ ℱ)`

in the ring of graded cap families. The filtration of `ℰ` tensored by `ℱ` is short exact at every
stage because `ℱ` is flat (`Stacks.Chow.exists_shortExact_tensorModules_of_isFiniteLocallyFree`),
and the Whitney relation of Stacks 02UI multiplies the factors. The rank of the tensor product is
`r · s`, carried through the induction as the hypothesis `ht`. -/
theorem chernFamily_tensorObj_eq_prod :
    ∀ (r : ℕ) (E : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      (L : Fin r → X.Modules)
      [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1],
      HasQuotients X r E L →
      ∀ (s t : ℕ) (F : X.Modules)
        [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s]
        [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (Scheme.Modules.tensorObj E F) t],
        t = r * s →
        GenuineChern.chernFamily C sX (Scheme.Modules.tensorObj E F) t =
          (List.ofFn fun i =>
            GenuineChern.chernFamily C sX (Scheme.Modules.tensorObj (L i) F) s).prod := by
  intro r
  induction r with
  | zero =>
      intro E _ L _ _ s t F _ _ ht
      have ht' : t = 0 := by simpa using ht
      subst ht'
      rw [GenuineChern.chernFamily_of_rank_zero]
      simp
  | succ r ih =>
      intro E _ L _ h s t F _ _ ht
      have ht' : t = r * s + s := by rw [ht]; ring
      subst ht'
      obtain ⟨Fst, hFst, f, g, w, hS, hrec⟩ := h
      have := hFst
      obtain ⟨f', g', w', hS'⟩ := exists_shortExact_tensorModules_of_isFiniteLocallyFree F
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F s)
        f g w hS
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (CategoryTheory.ShortComplex.mk f' g' w').X₁ (r * s) :=
        isFiniteLocallyFreeOfRank_tensorObj_mul Fst F r s
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (CategoryTheory.ShortComplex.mk f' g' w').X₃ s :=
        isFiniteLocallyFreeOfRank_tensorObj_rankOneLeft (L 0) F s
      exact eq_prod_ofFn_succ_of_mul
        (GenuineChern.chernFamily_eq_mul_of_shortExact C sX
          (CategoryTheory.ShortComplex.mk f' g' w') hS' (r * s) s)
        (commute_chernFamily C sX (Scheme.Modules.tensorObj Fst F) (r * s)
          (Scheme.Modules.tensorObj (L 0) F) s)
        (ih Fst (fun i => L i.succ) hrec s (r * s) F rfl) rfl

/-! ### The Chern roots of a tensor product -/

/-- **The Chern roots of a tensor product are the sums of the Chern roots**, which is the content
the source of Stacks 0FA6 and Stacks 0F9D hides behind the lexicographic filtration. If `ℰ₁`
carries a filtration of length `r` with invertible successive quotients `ℒ_i` and `ℰ₂` one of
length `s` with invertible successive quotients `𝒩_j`, then

  `c(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∏_i ∏_j (1 + c₁(𝒩_j) + c₁(ℒ_i))`

in the ring of graded cap families on the Chow groups of `X`, so that the Chern roots of
`ℰ₁ ⊗ ℰ₂` are the `r · s` classes `x_i + y_j`. **Nothing is carried**: the two filtrations are
what Stacks 02UL delivers (`Stacks.Chow.exists_hasQuotients_of_hasInvertibleFiltration`), the
lexicographic filtration is assembled in two stages by
`Stacks.Chow.chernFamily_tensorObj_eq_prod` and
`Stacks.Chow.chernFamily_tensorObj_invertible_eq_prod`, and the braiding
`Stacks.Chow.tensorObjSwap` exchanges the two factors between the stages. -/
theorem chernFamily_tensorObj_eq_prod_prod (r s t : ℕ) (E₁ E₂ : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₂ s]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj E₁ E₂) t]
    (L : Fin r → X.Modules)
    [hL : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (L i)]
    (N : Fin s → X.Modules)
    [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (N j)]
    (h₁ : HasQuotients X r E₁ L) (h₂ : HasQuotients X s E₂ N) (ht : t = r * s) :
    GenuineChern.chernFamily C sX (Scheme.Modules.tensorObj E₁ E₂) t =
      (List.ofFn fun i => (List.ofFn fun j =>
        1 + (firstChernElem C sX (N j) + firstChernElem C sX (L i))).prod).prod := by
  have : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1 :=
    fun i => isFiniteLocallyFreeOfRank_one_of_isInvertible (h := hL i) (L i)
  have hfun : (fun i : Fin r =>
        GenuineChern.chernFamily C sX (Scheme.Modules.tensorObj (L i) E₂) s)
      = fun i : Fin r => (List.ofFn fun j =>
        1 + (firstChernElem C sX (N j) + firstChernElem C sX (L i))).prod := by
    funext i
    rw [GenuineChern.chernFamily_congr C sX (Scheme.Modules.tensorObj E₂ (L i)) s
      (tensorObjSwap (L i) E₂) rfl]
    exact chernFamily_tensorObj_invertible_eq_prod C sX (L i) (hL i) s E₂ N h₂
  rw [chernFamily_tensorObj_eq_prod C sX r E₁ L h₁ s t E₂ ht, hfun]

end Filtration

end Stacks.Chow

end
