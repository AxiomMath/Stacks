module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ChowCohomologySeriesRingConstruction
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.AlternatingSubsetSums
public import StacksCore.Tactic.StacksAttribute

/-!
# The alternating product of the Chern classes of the exterior powers

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ` be a locally free `𝒪_X`-module of rank `r ≥ 1`.
[Stacks, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE) is the statement

  `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ} = 1 - (r-1)! c_r(ℰ) + …`

in the completed Chow cohomology ring `A^*(X)^∧`.

## What the `+ …` is, and what is proved

The trailing `+ …` is not a term: the source's own proof ends "hence we see that the first
nonzero term in our Chern class is in degree `r` and equal to the predicted value", so the
assertion is about the components of the alternating product in degrees `≤ r` and says nothing at
all about the higher ones. That is exactly what is proved here:

* the component in each degree `n` with `1 ≤ n < r` vanishes, and
* the component in degree `r` is `-(r-1)! c_r(ℰ)`.

Nothing is claimed in degrees above `r`. The component in degree `0` is `1` because the
alternating product is a product of series with constant term `1`, which is how the group it is
formed in is defined.

## Where the inverses live

The product has genuine inverses in it, so it needs a ring in which a total Chern class is a
unit. This repository has one, carried rather than constructed:
`Stacks.Chow.ChowCohomologySeriesRing` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup` is the ring
`A^*(X)^∧ = ∏_{i ≥ 0} A^i(X)` of Stacks 0FE0 as a datum — a degreewise product with the three
laws — and `Stacks.Chow.ChowCohomologySeriesRing.UnitalSeries`, the series with constant term
`1`, is a commutative **group** under the Cauchy product, with
`Stacks.Chow.ChowCohomologySeriesRing.formalInverse` providing the inverse. So
`c(⋀ⁿ ℰ)^{(-1)ⁿ}` is an honest `zpow` in that group and the alternating product is an honest
`Finset.prod`. The degreewise statements of the neighbouring tags —
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses` for Stacks 0FA5 and
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses` for Stacks 0FA6 — are
written against cap products on Chow groups instead, where no such inverse exists; this tag
cannot be stated that way, which is why the carried ring is used.

## Main definitions

* `Stacks.Chow.seriesCommRing` — the carried datum `Stacks.Chow.ChowCohomologySeriesRing` read as
  a `CommRing` structure on `∏_{i ≥ 0} A^i(X)`. Only the distributive laws are proved here; the
  rest are its fields.
* `Stacks.Chow.IsConcentrated` — a series has all components but the degree-`n` one equal to `0`.
* `Stacks.Chow.oneAddDegreeOne` — the unital series `1 + a` of a class `a ∈ A^1(X)`; the total
  Chern class of an invertible module, in the shape the splitting principle produces it.
* `Stacks.Chow.rootTotalChern` — `∏_{I ∈ p} (1 + ∑_{i ∈ I} x_i)`, the total Chern class the
  splitting principle predicts from Chern roots `x_1, …, x_r` for a collection `p` of subsets.
* `Stacks.Chow.altExteriorChernProduct` — the alternating product
  `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}`.

## Main results

* `Stacks.Chow.altExteriorChernProduct_apply` — **Stacks 0FEE.**

## What is carried, and why

The source proves the lemma "by the splitting principle" — it refers to the section Stacks 02UK —
and the only input it takes from there is the Chern roots: the identity
`c(⋀ⁿ ℰ) = ∏_{i_1 < … < i_n} (1 + x_{i_1} + … + x_{i_n})`, which its proof merely observes and
attaches no tag of its own to. That identity is the hypothesis `hwedge` below, together with the
corresponding `hE` for `ℰ` itself; both are products of
`Stacks.Chow.oneAddDegreeOne`, so the hypothesis is literally the display of the source proof.

Three facts make it an input here rather than a consequence.

* Stacks 02UK is a section, and nothing in this repository formalizes it.
* The filtration that Stacks 02UL delivers here, `Stacks.Chow.exists_splittingMorphism`,
  produces `Stacks.WeilCohomology.HasInvertibleFiltration`, an inductive `Prop` out of which the
  tower of modules and maps that Stacks 02UJ consumes cannot be eliminated, and nothing in this
  repository states that the Chern classes commute with flat pullback, so injectivity of `π^*`
  has nothing to be applied to. Both obstructions are already recorded by
  `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses` for Stacks 0FA5.
* Stacks 02UJ is proved in this repository, as
  `Stacks.Chow.chernClassCapExt_eq_elemSymmChernCap` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.FilteredAdditivity`, but only componentwise as
  an identity between cap products on Chow groups: its `@[stacks 02UJ]` clause records that the
  product `c(ℰ) = ∏ (1 + x_i)` in `A^*(X)` is **not** stated there and cannot be in that
  vocabulary. The hypotheses here are exactly that product form, in the carried ring, so the
  library's Stacks 02UJ does not supply them.

Everything after that display is proved, and it is the whole mathematical content of the lemma:
the alternating product of those explicit products is computed, in every degree up to `r`.

## The computation that replaces the source's logarithm

The source takes logarithms and recognises `∏ (1 - e^{-x_i})`. The same cancellation is
available without any denominators, and that is the route taken, in
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.AlternatingSubsetSums`: writing
`s_I = ∑_{i ∈ I} x_i`, the alternating product regrouped over all subsets `I ⊆ {1, …, r}` is
`(∏_{#I even} (1 + s_I)) · (∏_{#I odd} (1 + s_I))^{-1}`, the two factors expand into the
elementary symmetric functions of the two families `(s_I)`, and
`∑_{I} (-1)^{#I} s_I^d`, the `r`-fold finite difference of `y ↦ y^d`, vanishes for `d < r` and is
`(-1)^r r! x_1 ⋯ x_r` for `d = r`. Newton's identities turn that into the equality of the two
families' elementary symmetric functions below degree `r` and the value `-(r-1)! x_1 ⋯ x_r` of
their difference in degree `r`. Because the degree-`k` elementary symmetric function of degree-one
classes is concentrated in degree `k`, reading that off degreewise gives the lemma.

## References

* [Stacks Project, Tag 0FEE](https://stacks.math.columbia.edu/tag/0FEE)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02UK](https://stacks.math.columbia.edu/tag/02UK)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

open ChowCohomologySeriesRing

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {R : ChowCohomologySeriesRing C G sX}

/-! ### The series ring -/

/-- The degreewise product of anything with `0` is `0`. -/
theorem ChowCohomologySeriesRing.gradedMul_zero_right' (R : ChowCohomologySeriesRing C G sX)
    (i j n : ℕ) (h : i + j = n) (y : chowCohomologyComponent C G sX (i : ℤ)) :
    R.gradedMul i j n h y 0 = 0 :=
  GradedChowProductRule.IsAddRight.zero_right R.gradedMul_add_right i j n h y

/-- A term of the Cauchy product with `0` on the left vanishes. -/
theorem chowSeriesTerm_zero_left (R : ChowCohomologySeriesRing C G sX)
    (a : chowCohomologySeries C G sX) (n : ℕ) (p : ℕ × ℕ) :
    chowSeriesTerm R.gradedMul 0 a n p = 0 :=
  chowSeriesTerm_zero_left_of R.gradedMul_add_left a n p

/-- The Cauchy product with `0` on the left is `0`. -/
theorem chowSeriesMul_zero_left (R : ChowCohomologySeriesRing C G sX)
    (a : chowCohomologySeries C G sX) : chowSeriesMul R.gradedMul 0 a = 0 :=
  chowSeriesMul_zero_left_of R.gradedMul_add_left a

/-- The Cauchy product is additive in its second variable. -/
theorem chowSeriesMul_add_right (R : ChowCohomologySeriesRing C G sX)
    (a b c : chowCohomologySeries C G sX) :
    chowSeriesMul R.gradedMul a (b + c)
      = chowSeriesMul R.gradedMul a b + chowSeriesMul R.gradedMul a c :=
  chowSeriesMul_add_right_of R.gradedMul_add_right a b c

/-- The Cauchy product is additive in its first variable. -/
theorem chowSeriesMul_add_left (R : ChowCohomologySeriesRing C G sX)
    (a b c : chowCohomologySeries C G sX) :
    chowSeriesMul R.gradedMul (a + b) c
      = chowSeriesMul R.gradedMul a c + chowSeriesMul R.gradedMul b c :=
  chowSeriesMul_add_left_of R.gradedMul_add_left a b c

/-- The Cauchy product with `0` on the right is `0`. -/
theorem chowSeriesMul_zero_right (R : ChowCohomologySeriesRing C G sX)
    (a : chowCohomologySeries C G sX) : chowSeriesMul R.gradedMul a 0 = 0 :=
  chowSeriesMul_zero_right_of R.gradedMul_add_right a

/-- The unit series is a right unit for the Cauchy product. -/
theorem chowSeriesMul_one_right (R : ChowCohomologySeriesRing C G sX)
    (a : chowCohomologySeries C G sX) : chowSeriesMul R.gradedMul a R.one = a :=
  (R.mul_comm a R.one).trans (R.one_mul a)

/-- **The ring `A^*(X)^∧ = ∏_{i ≥ 0} A^i(X)` of Stacks 0FE0 as a commutative ring**, assembled
from the degreewise product, the unit series and the laws carried by
`Stacks.Chow.ChowCohomologySeriesRing`. The additive structure is the pointwise one. -/
@[instance_reducible]
def seriesCommRing (R : ChowCohomologySeriesRing C G sX) :
    CommRing (chowCohomologySeries C G sX) :=
  { (inferInstance : AddCommGroup (chowCohomologySeries C G sX)) with
    mul := chowSeriesMul R.gradedMul
    one := R.one
    mul_assoc := R.mul_assoc
    mul_comm := R.mul_comm
    one_mul := R.one_mul
    mul_one := chowSeriesMul_one_right R
    zero_mul := chowSeriesMul_zero_left R
    mul_zero := chowSeriesMul_zero_right R
    left_distrib := chowSeriesMul_add_right R
    right_distrib := chowSeriesMul_add_left R }

/-! ### Series concentrated in one degree -/

/-- A series of Chow cohomology classes is concentrated in degree `n` when all its components in
other degrees vanish. -/
def IsConcentrated (n : ℕ) (a : chowCohomologySeries C G sX) : Prop := ∀ m, m ≠ n → a m = 0

/-- The zero series is concentrated in every degree. -/
theorem isConcentrated_zero (n : ℕ) :
    IsConcentrated n (0 : chowCohomologySeries C G sX) := fun _ _ => rfl

/-- The unit series is concentrated in degree `0`. -/
theorem isConcentrated_one (R : ChowCohomologySeriesRing C G sX) :
    IsConcentrated 0 R.one := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  exact R.one_apply_succ k

/-- A sum of series concentrated in degree `n` is concentrated in degree `n`. -/
theorem IsConcentrated.add {n : ℕ} {a b : chowCohomologySeries C G sX}
    (ha : IsConcentrated n a) (hb : IsConcentrated n b) : IsConcentrated n (a + b) := by
  intro m hm
  rw [Pi.add_apply, ha m hm, hb m hm, add_zero]

/-- The negative of a series concentrated in degree `n` is concentrated in degree `n`. -/
theorem IsConcentrated.neg {n : ℕ} {a : chowCohomologySeries C G sX}
    (ha : IsConcentrated n a) : IsConcentrated n (-a) := by
  intro m hm
  rw [Pi.neg_apply, ha m hm, neg_zero]

/-- A difference of series concentrated in degree `n` is concentrated in degree `n`. -/
theorem IsConcentrated.sub {n : ℕ} {a b : chowCohomologySeries C G sX}
    (ha : IsConcentrated n a) (hb : IsConcentrated n b) : IsConcentrated n (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- A natural multiple of a series concentrated in degree `n` is concentrated in degree `n`. -/
theorem IsConcentrated.nsmul {n : ℕ} {a : chowCohomologySeries C G sX} (k : ℕ)
    (ha : IsConcentrated n a) : IsConcentrated n (k • a) := by
  intro m hm
  rw [Pi.smul_apply, ha m hm, smul_zero]

/-- The Cauchy product of series concentrated in degrees `i` and `j` is concentrated in degree
`i + j`. -/
theorem IsConcentrated.chowSeriesMul (R : ChowCohomologySeriesRing C G sX) {i j : ℕ}
    {a b : chowCohomologySeries C G sX} (ha : IsConcentrated i a) (hb : IsConcentrated j b) :
    IsConcentrated (i + j) (chowSeriesMul R.gradedMul a b) := by
  intro m hm
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨p1, p2⟩ := p
  have hadd : p1 + p2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [chowSeriesTerm_of_add R.gradedMul a b hadd]
  rcases eq_or_ne p1 i with h1 | h1
  · rw [hb p2 (by omega), R.gradedMul_zero_right']
  · rw [ha p1 h1, R.gradedMul_zero_left]

/-! ### Chern roots and the alternating product -/

/-- The unital series `1 + a` of a degree-one Chow cohomology class `a`: the total Chern class
of an invertible module with `c_1 = a`, in the shape the splitting principle produces it. -/
def oneAddDegreeOne (R : ChowCohomologySeriesRing C G sX)
    (a : chowCohomologyComponent C G sX 1) : UnitalSeries R :=
  ⟨R.one + Function.update (0 : chowCohomologySeries C G sX) 1 a, by
    have h : Function.update (0 : chowCohomologySeries C G sX) 1 a 0 = 0 := by simp
    rw [Pi.add_apply, h, add_zero]⟩

/-- A degree-one class, viewed as a series, is concentrated in degree one. -/
theorem isConcentrated_update_one (a : chowCohomologyComponent C G sX 1) :
    IsConcentrated 1 (Function.update (0 : chowCohomologySeries C G sX) 1 a) := by
  intro m hm
  simp [Function.update, hm]

/-- The degree-one part of a sum of degree-one classes, viewed as a series, is additive. -/
theorem update_one_sum {ι : Type*} (s : Finset ι)
    (t : ι → chowCohomologyComponent C G sX 1) :
    Function.update (0 : chowCohomologySeries C G sX) 1 (∑ i ∈ s, t i)
      = ∑ i ∈ s, Function.update (0 : chowCohomologySeries C G sX) 1 (t i) := by
  funext n
  rw [Finset.sum_apply]
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [hn]

/-- The total Chern class `∏_{I ∈ p} (1 + ∑_{i ∈ I} x_i)` that the splitting principle predicts
from Chern roots `x_1, …, x_r`, for a collection `p` of subsets of `Fin r`. -/
def rootTotalChern (R : ChowCohomologySeriesRing C G sX) {r : ℕ}
    (t : Fin r → chowCohomologyComponent C G sX 1) (p : Finset (Finset (Fin r))) :
    UnitalSeries R :=
  ∏ I ∈ p, oneAddDegreeOne R (∑ i ∈ I, t i)

/-- The alternating product `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}` of the total Chern classes of the
exterior powers of a sheaf of modules, in the group of series with constant term `1`. -/
def altExteriorChernProduct (D : TotalChernClassSeries C G sX R) (E : X.Modules) (r : ℕ) :
    UnitalSeries R :=
  ∏ n ∈ Finset.range (r + 1),
    (⟨D.ch (Scheme.Modules.exteriorPower E (n : ℤ)),
        D.ch_apply_zero (Scheme.Modules.exteriorPower E (n : ℤ))⟩ : UnitalSeries R) ^ ((-1 : ℤ) ^ n)

/-! ### Stacks 0FEE -/

/-- **Stacks 0FEE.** For `ℰ` locally free of rank `r ≥ 1` with Chern roots `t`, the alternating
product `∏_{n = 0}^{r} c(⋀ⁿ ℰ)^{(-1)ⁿ}` has vanishing components in the degrees `1, …, r-1` and
the component `-(r-1)! c_r(ℰ)` in degree `r`; nothing is asserted in higher degrees, which is the
`+ …` of the source. -/
@[stacks 0FEE "the whole lemma, in the carried ring A^*(X)^∧ of Stacks 0FE0 where the inverses \
  c(E)^{-1} exist. CARRIED: the Chern roots, i.e. the display c(wedge^n E) = prod_{i_1 < ... < \
  i_n} (1 + x_{i_1} + ... + x_{i_n}) of the source proof, i.e. the splitting principle: Stacks \
  02UK, 02UL and the product form of 02UJ; see the module doc. The computation is proved"]
theorem altExteriorChernProduct_apply (D : TotalChernClassSeries C G sX R) (E : X.Modules)
    {r : ℕ} [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hr : r ≠ 0) (t : Fin r → chowCohomologyComponent C G sX 1)
    (hE : D.ch E = (∏ i, oneAddDegreeOne R (t i) : UnitalSeries R).1)
    (hwedge : ∀ n ≤ r, D.ch (Scheme.Modules.exteriorPower E (n : ℤ))
      = (rootTotalChern R t ((Finset.univ : Finset (Fin r)).powersetCard n)).1) :
    (∀ n, 0 < n → n < r → (altExteriorChernProduct D E r).1 n = 0) ∧
      (altExteriorChernProduct D E r).1 r
        = -(Nat.factorial (r - 1) • D.ch E r) := by
  classical
  let _ : CommRing (chowCohomologySeries C G sX) := seriesCommRing R
  -- the Chern roots as series concentrated in degree one
  set v : Fin r → chowCohomologySeries C G sX :=
    fun i => Function.update (0 : chowCohomologySeries C G sX) 1 (t i) with hv
  have hvconc : ∀ i, IsConcentrated 1 (v i) := fun i => isConcentrated_update_one (t i)
  have hvsum : ∀ I : Finset (Fin r), IsConcentrated 1 (∑ i ∈ I, v i) := by
    intro I
    induction I using Finset.induction_on with
    | empty => exact isConcentrated_zero 1
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hvconc a).add ih
  have honeAdd : ∀ I : Finset (Fin r),
      (oneAddDegreeOne R (∑ i ∈ I, t i)).1 = 1 + ∑ i ∈ I, v i := by
    intro I
    rw [oneAddDegreeOne, hv, ← update_one_sum]
    rfl
  -- the value of a product of unital series
  have hvalProd : ∀ {κ : Type} (q : Finset κ) (f : κ → UnitalSeries R),
      (∏ k ∈ q, f k).1 = ∏ k ∈ q, (f k).1 := by
    intro κ q f
    exact map_prod (⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ : UnitalSeries R →* _) f q
  -- a product of `#T` series concentrated in degree one is concentrated in degree `#T`
  have hconcProd : ∀ {κ : Type} (T : Finset κ) (y : κ → chowCohomologySeries C G sX),
      (∀ k, IsConcentrated 1 (y k)) → IsConcentrated #T (∏ k ∈ T, y k) := by
    intro κ T y hy
    induction T using Finset.induction_on with
    | empty => exact isConcentrated_one R
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_comm]
        exact IsConcentrated.chowSeriesMul R (hy a) ih
  -- a sum of elementary symmetric functions of degree-one series is concentrated
  have hconcEsymm : ∀ {κ : Type} (q : Finset κ) (y : κ → chowCohomologySeries C G sX),
      (∀ k, IsConcentrated 1 (y k)) → ∀ j : ℕ,
        IsConcentrated j (∑ T ∈ q.powersetCard j, ∏ k ∈ T, y k) := by
    intro κ q y hy j
    refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) (isConcentrated_zero j) ?_
    intro T hT
    have := hconcProd T y hy
    rwa [(Finset.mem_powersetCard.mp hT).2] at this
  -- the expansion of a product `∏ (1 + y k)` into elementary symmetric functions
  have hexpand : ∀ {κ : Type} (q : Finset κ) (y : κ → chowCohomologySeries C G sX) (M : ℕ),
      #q ≤ M → (∏ k ∈ q, (1 + y k))
        = ∑ j ∈ Finset.range (M + 1), ∑ T ∈ q.powersetCard j, ∏ k ∈ T, y k := by
    intro κ q y M hM
    have h1 : (∏ k ∈ q, (1 + y k)) = ∑ T ∈ q.powerset, ∏ k ∈ T, y k := by
      rw [Finset.prod_congr rfl fun k _ => add_comm (1 : chowCohomologySeries C G sX) (y k),
        Finset.prod_add y (fun _ => (1 : chowCohomologySeries C G sX)) q]
      exact Finset.sum_congr rfl fun T _ => by rw [Finset.prod_const_one, mul_one]
    rw [h1, Finset.sum_powerset]
    refine Finset.sum_subset (fun j hj =>
      Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)) ?_
    intro j _ hj
    have hlt : #q < j := by
      have : ¬ (j < #q + 1) := fun h => hj (Finset.mem_range.mpr h)
      omega
    rw [Finset.powersetCard_eq_empty.mpr hlt, Finset.sum_empty]
  -- the two halves of the alternating product
  set Qe : UnitalSeries R := rootTotalChern R t (evenCardSubsets r) with hQe
  set Qo : UnitalSeries R := rootTotalChern R t (oddCardSubsets r) with hQo
  have hzpowProd : ∀ (z : ℤ) {κ : Type} (q : Finset κ) (f : κ → UnitalSeries R),
      (∏ k ∈ q, f k) ^ z = ∏ k ∈ q, f k ^ z := fun z κ q f =>
    map_prod (zpowGroupHom z) f q
  have hcu : #(Finset.univ : Finset (Fin r)) = r := by simp
  -- regrouping the alternating product over all subsets
  have hregroup : altExteriorChernProduct D E r = Qe * Qo⁻¹ := by
    have hfac : ∀ n ∈ Finset.range (r + 1),
        (⟨D.ch (Scheme.Modules.exteriorPower E (n : ℤ)),
            D.ch_apply_zero (Scheme.Modules.exteriorPower E (n : ℤ))⟩ : UnitalSeries R)
              ^ ((-1 : ℤ) ^ n)
          = ∏ I ∈ (Finset.univ : Finset (Fin r)).powersetCard n,
              oneAddDegreeOne R (∑ i ∈ I, t i) ^ ((-1 : ℤ) ^ #I) := by
      intro n hn
      have hn' : n ≤ r := by have := Finset.mem_range.mp hn; omega
      rw [show (⟨D.ch (Scheme.Modules.exteriorPower E (n : ℤ)),
            D.ch_apply_zero (Scheme.Modules.exteriorPower E (n : ℤ))⟩ : UnitalSeries R)
          = rootTotalChern R t ((Finset.univ : Finset (Fin r)).powersetCard n) from
        Subtype.ext (hwedge n hn'), rootTotalChern, hzpowProd]
      refine Finset.prod_congr rfl fun I hI => ?_
      rw [(Finset.mem_powersetCard.mp hI).2]
    have hpow : ∀ g : Finset (Fin r) → UnitalSeries R,
        ∏ n ∈ Finset.range (r + 1), ∏ I ∈ (Finset.univ : Finset (Fin r)).powersetCard n, g I
          = ∏ I ∈ (Finset.univ : Finset (Finset (Fin r))), g I := by
      intro g
      have h := Finset.prod_powerset (Finset.univ : Finset (Fin r)) g
      rw [hcu] at h
      rw [← h, Finset.powerset_univ]
    have heven : ∏ I ∈ Finset.univ.filter (fun I : Finset (Fin r) => Even #I),
        oneAddDegreeOne R (∑ i ∈ I, t i) ^ ((-1 : ℤ) ^ #I) = Qe := by
      rw [hQe, rootTotalChern, evenCardSubsets]
      refine Finset.prod_congr rfl fun I hI => ?_
      rw [Even.neg_one_pow (Finset.mem_filter.mp hI).2, zpow_one]
    have hodd : ∏ I ∈ Finset.univ.filter (fun I : Finset (Fin r) => ¬ Even #I),
        oneAddDegreeOne R (∑ i ∈ I, t i) ^ ((-1 : ℤ) ^ #I) = Qo⁻¹ := by
      rw [hQo, rootTotalChern, oddCardSubsets, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun I hI => ?_
      rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hI).2), zpow_neg_one]
    rw [altExteriorChernProduct, Finset.prod_congr rfl hfac, hpow,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Finset (Fin r)))
        (fun I => Even #I) (fun I => oneAddDegreeOne R (∑ i ∈ I, t i) ^ ((-1 : ℤ) ^ #I)),
      heven, hodd]
  -- the two halves, expanded degreewise
  have hbound : ∀ p : Finset (Finset (Fin r)), #p ≤ 2 ^ r := by
    intro p
    calc #p ≤ #(Finset.univ : Finset (Finset (Fin r))) := Finset.card_le_card (Finset.subset_univ p)
      _ = 2 ^ r := by simp
  have hhalf : ∀ p : Finset (Finset (Fin r)), (rootTotalChern R t p).1
      = ∑ j ∈ Finset.range (2 ^ r + 1), subsetSumEsymm v p j := by
    intro p
    rw [rootTotalChern, hvalProd, Finset.prod_congr rfl fun I _ => honeAdd I,
      hexpand p (fun I => ∑ i ∈ I, v i) (2 ^ r) (hbound p)]
    exact Finset.sum_congr rfl fun j _ => rfl
  -- the difference of the two halves, degreewise
  set Δ : chowCohomologySeries C G sX := Qe.1 - Qo.1 with hΔdef
  have hΔsum : Δ = ∑ j ∈ Finset.range (2 ^ r + 1),
      (subsetSumEsymm v (evenCardSubsets r) j - subsetSumEsymm v (oddCardSubsets r) j) := by
    rw [hΔdef, hQe, hQo, hhalf, hhalf, ← Finset.sum_sub_distrib]
  have hrM : r < 2 ^ r + 1 := by have := Nat.lt_two_pow_self (n := r); omega
  have hΔapply : ∀ n ≤ r, Δ n
      = (subsetSumEsymm v (evenCardSubsets r) n - subsetSumEsymm v (oddCardSubsets r) n) n := by
    intro n hn
    rw [hΔsum, Finset.sum_apply,
      Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr (by omega))]
    intro b _ hb
    exact ((hconcEsymm (evenCardSubsets r) (fun I => ∑ i ∈ I, v i) hvsum b).sub
      (hconcEsymm (oddCardSubsets r) (fun I => ∑ i ∈ I, v i) hvsum b)) n (Ne.symm hb)
  have hΔzero : ∀ n < r, Δ n = 0 := by
    intro n hn
    rw [hΔapply n hn.le, subsetSumEsymm_even_eq_odd v hn, sub_self]
    rfl
  -- the degree-`r` Chern class, from the roots
  have hcr : D.ch E r = (∏ i, v i) r := by
    have h1 : D.ch E = ∑ j ∈ Finset.range (2 ^ r + 1),
        ∑ T ∈ (Finset.univ : Finset (Fin r)).powersetCard j, ∏ i ∈ T, v i := by
      rw [hE, hvalProd, Finset.prod_congr rfl fun i _ => (by simpa using honeAdd {i}),
        hexpand (Finset.univ : Finset (Fin r)) v (2 ^ r)
          (by rw [hcu]; exact Nat.lt_two_pow_self.le)]
    have hps : (Finset.univ : Finset (Fin r)).powersetCard r = {Finset.univ} := by
      have h := Finset.powersetCard_self (Finset.univ : Finset (Fin r))
      rwa [hcu] at h
    rw [h1, Finset.sum_apply, Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hrM)]
    · rw [hps, Finset.sum_singleton]
    · intro b _ hb
      exact hconcEsymm (Finset.univ : Finset (Fin r)) v hvconc b r (Ne.symm hb)
  have hΔtop : Δ r = -(Nat.factorial (r - 1) • D.ch E r) := by
    rw [hΔapply r le_rfl, subsetSumEsymm_even_sub_odd v hr, Pi.neg_apply, Pi.smul_apply, hcr]
  -- transporting the difference to the alternating product
  set W : chowCohomologySeries C G sX := (altExteriorChernProduct D E r).1 - 1 with hW
  have hprodEq : Δ = chowSeriesMul R.gradedMul Qo.1 W := by
    have hQ : Qe.1 = chowSeriesMul R.gradedMul (altExteriorChernProduct D E r).1 Qo.1 := by
      rw [← UnitalSeries.val_mul, hregroup, inv_mul_cancel_right]
    rw [hΔdef, hW]
    change Qe.1 - Qo.1 = Qo.1 * ((altExteriorChernProduct D E r).1 - 1)
    rw [show chowSeriesMul R.gradedMul (altExteriorChernProduct D E r).1 Qo.1
        = (altExteriorChernProduct D E r).1 * Qo.1 from rfl] at hQ
    rw [hQ]
    ring
  have hWeq : ∀ n, n ≤ r → W n = Δ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hWj : ∀ j, j < n → W j = 0 := by
        intro j hj
        rw [ih j hj (by omega), hΔzero j (by omega)]
      refine (?_ : Δ n = W n).symm
      rw [hprodEq]
      show chowSeriesMul R.gradedMul Qo.1 W n = W n
      rw [chowSeriesMul,
        Finset.sum_eq_single_of_mem (0, n)
          (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.zero_add n))]
      · rw [chowSeriesTerm_of_add R.gradedMul Qo.1 W (Nat.zero_add n), Qo.2]
        exact R.gradedMul_one_apply_zero n (W n)
      · rintro ⟨b1, b2⟩ hb hne
        have hadd : b1 + b2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
        have hb2 : b2 < n := by
          rcases Nat.eq_zero_or_pos b1 with h | h
          · exact absurd (by rw [h, ← hadd, h, Nat.zero_add] : ((b1, b2) : ℕ × ℕ) = (0, n)) hne
          · omega
        rw [chowSeriesTerm_of_add R.gradedMul Qo.1 W hadd, hWj b2 hb2, R.gradedMul_zero_right']
  have hval : ∀ k, k + 1 ≤ r → (altExteriorChernProduct D E r).1 (k + 1) = Δ (k + 1) := by
    intro k hk
    rw [← hWeq _ hk, hW, Pi.sub_apply]
    change (altExteriorChernProduct D E r).1 (k + 1)
      = (altExteriorChernProduct D E r).1 (k + 1) - R.one (k + 1)
    rw [R.one_apply_succ, sub_zero]
  refine ⟨fun n hn0 hnr => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0.ne'
    rw [hval k hnr.le, hΔzero _ hnr]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    rw [hval k le_rfl, hΔtop]

end Stacks.Chow

end
