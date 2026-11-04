module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes and the Chern character of the second Adams operation

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be a
scheme locally of finite type over `S`, let `ψ²` be the second Adams operation of Stacks 0FEJ on
`K_0(Vect(X))` and let `c` and `ch` be the Chern class map of Stacks 0FEL and the Chern character
of Stacks 0FEM. Stacks 0FEN says that for every `α ∈ K_0(Vect(X))`

  `c_i(ψ²(α)) = 2^i c_i(α)`  and  `ch_i(ψ²(α)) = 2^i ch_i(α)`.

Both equations are proved here, the second from the first.

## Main definitions

* `Stacks.Chow.chowSeriesScale` — the endomorphism of `∏_{i ≥ 0} A^i(X)` scaling `A^i(X)` by
  `2^i`. It is the map the source's proof introduces.
* `Stacks.Chow.InvertibleChernClassData` — the facts about the Chern classes of an invertible
  module that the base case of the source's proof uses: Stacks 02U0, Stacks 02SZ and
  Stacks 01CT (1).
* `Stacks.Chow.SecondAdamsSplittingAt`, `Stacks.Chow.SecondAdamsSplitting` and
  `Stacks.Chow.HasSecondAdamsSplitting` — the splitting principle of Stacks 02UL in the shape
  the source's proof uses it, together with the functoriality of Chow cohomology and of
  `K_0(Vect(-))` that reading the conclusion back at `X` requires.
* `Stacks.Chow.NewtonPowerSums` — the power sums `P_p(c_1, …, c_p)` as a function of the total
  Chern class series, with the two properties of those universal polynomials the Chern character
  needs.
* `Stacks.Chow.chernCharacterKGroup` — the Chern character `ch_p(α) = P_p(c_1(α), …, c_p(α))/p!`
  of Stacks 0FEM, on `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`.

## Main results

* `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesScale_one` and
  `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesScale_mul` — **the scaling map is a ring
  endomorphism of `∏_{i ≥ 0} A^i(X)`**, the source's first step and what makes the reduction to
  additive generators of `K_0(Vect(X))` possible.
* `Stacks.Chow.ch_tensorSelf_eq_chowSeriesScale` — **the base case**: for an invertible module
  `ℒ`, the series `c(ℒ ⊗ ℒ) = 1 + 2c_1(ℒ)` is the scaling of `c(ℒ) = 1 + c_1(ℒ)`.
* `Stacks.Chow.chernClassKGroup_secondAdams_sum` — the source's steps 4 and 5: on a sum of
  classes of invertible modules `c(ψ²(α))` is the scaling of `c(α)`, because `ψ²` sends `[ℒ]` to
  `[ℒ ⊗ ℒ]` and the scaling map is multiplicative. In the source's notation
  `c(α) = ∏ (1 + x_j)` becomes `c(ψ²(α)) = ∏ (1 + 2x_j)`.
* `Stacks.Chow.chernClassKGroup_pullback` — the Chern class map commutes with a pullback of Chow
  cohomology; this is what makes the identity descend from the splitting space to `X`.
* `Stacks.Chow.chernClassKGroup_secondAdams` — **Stacks 0FEN, the first equation**:
  `c_i(ψ²(α)) = 2^i c_i(α)`.
* `Stacks.Chow.chernCharacterKGroup_secondAdams` — **Stacks 0FEN, the second equation**:
  `ch_i(ψ²(α)) = 2^i ch_i(α)`.

## The dictionary

`K_0(Vect(X))` is `AlgebraicGeometry.VectorBundleKZero` of Stacks 0FDK, `ψ²` is
`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom` of Stacks 0FEJ, `A^i(X)` is
`Stacks.Chow.chowCohomologyComponent` of Stacks 0B7E, `∏_{i ≥ 0} A^i(X)` is
`Stacks.Chow.chowCohomologySeries`, and `c` is `Stacks.Chow.chernClassKGroup` of Stacks 0FEL.
The parameters `R`, `D` and `hX` below are exactly the data those already carry; see the
attributes on `Stacks.Chow.chernClassKGroup` and
`AlgebraicGeometry.VectorBundleKZero.exists_secondAdamsOperator`.

## What is carried here, and why

Beyond the data Stacks 0FEL and Stacks 0FEJ already carry, the geometric input of the source's
own proof is carried:

* **The splitting principle, Stacks 02UL**, which this repository does not have. The source
  chooses a projective smooth `p : P ⟶ X` with `A^*(X) ⟶ A^*(P)` injective and `p^*ℰ` filtered
  with invertible graded pieces `ℒ_j`. Descending the identity needs the functoriality of Chow
  cohomology and of `K_0(Vect(-))`; the latter is not constructed in this repository either, as
  the implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator` already
  record, and the former is only the additive restriction map of Stacks 0B7F, whose
  multiplicativity for the composition product of Stacks 0FE0 the library explicitly does not
  formalize. All of it is `Stacks.Chow.SecondAdamsSplittingAt`.
* **Stacks 02U0 and Stacks 02SZ**, the vanishing of `c_j(ℒ)` above the rank of `ℒ` and the
  additivity `c_1(ℒ ⊗ ℒ) = 2c_1(ℒ)` of the first Chern class, with Stacks 01CT (1), collected in
  `Stacks.Chow.InvertibleChernClassData`. The bivariant Chern classes these are statements about
  are themselves only characterized in this repository, by `Stacks.Chow.IsChernClassBivariant`
  of Stacks 0B7H, and `Stacks.Chow.TotalChernClassSeries` carries them; so these are properties
  of a carried datum and are carried in turn.
* **Two universal properties of the Newton power-sum polynomials**, in
  `Stacks.Chow.NewtonPowerSums`: that `P_p` is additive for the Cauchy product — which is why
  the Chern character is additive, Stacks 0F9C — and that it is weighted homogeneous of degree
  `p`, so that substituting `2^j c_j` for `c_j` multiplies it by `2^p`. The power sums are not
  constructed here: `Stacks.Chow.powerSumClassArbitraryRank` of Stacks 0ESX assembles them over
  the rank loci from a quantified family, so there is no polynomial expression to read either
  property off. The second is combinatorial, with no geometry in it, and it is what makes the
  lemma's second equation a consequence of its first.

Everything else is proved. The scaling map is not assumed to be a ring map; the value
`ψ²([ℒ]) = [ℒ ⊗ ℒ]` is not assumed, being
`AlgebraicGeometry.VectorBundleKZero.secondAdamsAddHom_classOf_isInvertible`; the base case
`c(ℒ ⊗ ℒ) = 1 + 2c_1(ℒ)` is proved from Stacks 02U0 and Stacks 02SZ; the value of `ψ²` on a sum
of invertible classes is computed, not assumed; the descent along the pullback is proved; and
the second equation of the lemma is deduced from the first.

## Implementation notes

**Where the reduction to generators happens.** The source's first step is that the scaling map is
a ring endomorphism of `∏_{i ≥ 0} A^i(X)`. Then `α ↦ c(ψ²(α))` and `α ↦ 2^• c(α)` are both
homomorphisms from `K_0(Vect(X))`, written additively, to the group of series with constant term
`1`, written multiplicatively, so they may be compared on the classes of finite locally free
modules by `AlgebraicGeometry.VectorBundleKZero.addHom_ext`. That is how
`Stacks.Chow.chernClassKGroup_secondAdams_eq_chowSeriesScale` is organised. Multiplicativity of
the scaling map, `Stacks.Chow.ChowCohomologySeriesRing.chowSeriesScale_mul`, is the identity
`2^i · 2^j = 2^n` on the terms `i + j = n` of a Cauchy product.

**Why the splitting data is a family and not a single morphism.** Stacks 02UL splits a module of
*constant* rank `r` into `r` invertible pieces; a finite locally free module of non-constant rank
never becomes a sum of a fixed number of invertible classes after a pullback, because invertible
modules have rank one. The source therefore reduces to constant rank first, over the rank loci of
`ℰ` (Stacks 0ESW). The reduction and the splitting are the same kind of step — pull back along
morphisms that are *jointly* injective on Chow cohomology — so they are carried together:
`Stacks.Chow.SecondAdamsSplitting` asks for a family of morphisms `p_r : P_r ⟶ X`, jointly
injective on each `A^i(X)`, along each of which `ℰ` splits. Composing the rank loci of `ℰ` with
the splitting spaces of Stacks 02UL over them gives exactly such a family for every finite
locally free `ℰ`, so nothing is assumed away; a single morphism would have restricted the lemma
to the modules of constant rank.

**Why the pullback of Chow cohomology is a field rather than Stacks 0B7F.** The library has the
restriction map `f^* : A^i(Y) ⟶ A^i(Y')` of Stacks 0B7F as
`Stacks.Chow.chowCohomologyRestriction`, but none of the three properties of it that this proof
uses is formalized there — multiplicativity for the composition product is explicitly not
(it needs Stacks 0FE0, hence Stacks 0B6Y), compatibility with Chern classes is not, and
injectivity is Stacks 02UL. Since all three have to be carried in any case, the map is carried
with them. Doing so only *weakens* the hypothesis: the real `f^*` is one such map, so a
splitting datum built from Stacks 0B7F satisfies this statement, and the statement also covers
any other map with those properties.

**The second equation.** `ch_p` is `P_p(c_1, …, c_p)/p!`, a function of the total Chern class
series, so the second equation follows from the first *as an equality of series*, together with
the weighted homogeneity of `P_p`; no second splitting argument is needed. That is why
`Stacks.Chow.chernClassKGroup_secondAdams_eq_chowSeriesScale` is stated for series and the
degreewise form is a corollary. The target `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` is written out as
`∀ p : ℕ, TensorProduct ℤ ℚ (chowCohomologyComponent C G sX p)`, which is the library's
`Stacks.Chow.fullRationalChowCohomology`; the module defining that abbreviation is not imported,
only to keep this file off the rank-locus assembly of Stacks 0ESX.

**Natural-number multiples.** `2^i c_i(α)` is a natural-number multiple in the abelian group
`A^i(X)`, and `2^p ch_p(α)` one in `A^p(X) ⊗ 𝐐`; the source writes both as multiplication by the
integer `2^i`, and in an abelian group the two agree.

## References

* [Stacks Project, Tag 0FEN](https://stacks.math.columbia.edu/tag/0FEN)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02SZ](https://stacks.math.columbia.edu/tag/02SZ)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.VectorBundleKZero
open Stacks.FiniteLocallyFree
open scoped TensorProduct

universe u

namespace Stacks.Chow

open ChowCohomologySeriesRing

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX]

/-! ### The endomorphism scaling `A^i(X)` by `2^i` -/

/-- The endomorphism of `∏_{i ≥ 0} A^i(X)` which scales `A^i(X)` by `2^i`. -/
def chowSeriesScale (a : chowCohomologySeries C G sX) : chowCohomologySeries C G sX :=
  fun i => ((2 : ℕ) ^ i) • a i

/-- The degree-`i` coefficient of `chowSeriesScale a` is `2^i • a i`. -/
@[simp] theorem chowSeriesScale_apply (a : chowCohomologySeries C G sX) (i : ℕ) :
    chowSeriesScale a i = ((2 : ℕ) ^ i) • a i := rfl

namespace ChowCohomologySeriesRing

variable (R : ChowCohomologySeriesRing C G sX)

/-- The degreewise product of anything with `0` is `0`. -/
theorem gradedMul_zero_right (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) : R.gradedMul i j n h x 0 = 0 := by
  have h0 := R.gradedMul_add_right i j n h x 0 0
  rw [add_zero] at h0
  simpa using h0.symm

/-- The degreewise product is compatible with natural-number multiples in its first variable. -/
theorem gradedMul_nsmul_left (i j n : ℕ) (h : i + j = n) (k : ℕ)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    R.gradedMul i j n h (k • x) y = k • R.gradedMul i j n h x y := by
  exact map_nsmul (AddMonoidHom.mk' (R.gradedMul i j n h · y)
    fun a b => R.gradedMul_add_left i j n h a b y) k x

/-- The degreewise product is compatible with natural-number multiples in its second variable. -/
theorem gradedMul_nsmul_right (i j n : ℕ) (h : i + j = n) (k : ℕ)
    (x : chowCohomologyComponent C G sX (i : ℤ))
    (y : chowCohomologyComponent C G sX (j : ℤ)) :
    R.gradedMul i j n h x (k • y) = k • R.gradedMul i j n h x y := by
  exact map_nsmul (AddMonoidHom.mk' (R.gradedMul i j n h x)
    fun a b => R.gradedMul_add_right i j n h x a b) k y

/-- **The scaling map fixes the unit series.** The unit series is concentrated in degree `0`,
where the factor is `2^0 = 1`. -/
theorem chowSeriesScale_one : chowSeriesScale R.one = R.one := by
  funext n
  cases n with
  | zero => rw [chowSeriesScale_apply, pow_zero, one_smul]
  | succ m => rw [chowSeriesScale_apply, R.one_apply_succ m, smul_zero]

/-- **The scaling map is multiplicative for the Cauchy product.** The degree-`n` coefficient of a
product is a sum over the antidiagonal of `n`, and on the term indexed by `(i, j)` the two
factors contribute `2^i · 2^j = 2^n`. -/
theorem chowSeriesScale_mul (a b : chowCohomologySeries C G sX) :
    chowSeriesScale (chowSeriesMul R.gradedMul a b) =
      chowSeriesMul R.gradedMul (chowSeriesScale a) (chowSeriesScale b) := by
  funext n
  rw [chowSeriesScale_apply, chowSeriesMul, chowSeriesMul, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hmem
  rw [Finset.mem_antidiagonal] at hmem
  rw [chowSeriesTerm_of_add R.gradedMul a b hmem,
    chowSeriesTerm_of_add R.gradedMul (chowSeriesScale a) (chowSeriesScale b) hmem,
    chowSeriesScale_apply, chowSeriesScale_apply, R.gradedMul_nsmul_left,
    R.gradedMul_nsmul_right, smul_smul, ← pow_add, hmem]

/-- **The scaling map as an endomorphism of the group of series with constant term `1`.** The
constant term is multiplied by `2^0 = 1`, hence unchanged, and the Cauchy product is preserved,
so this is a homomorphism of the commutative group of unital series. -/
def unitalSeriesScale : UnitalSeries R →* UnitalSeries R :=
  MonoidHom.mk' (fun a : UnitalSeries R => ⟨chowSeriesScale a.1, by
      change ((2 : ℕ) ^ 0) • a.1 0 = R.one 0
      rw [pow_zero, one_smul]
      exact a.2⟩)
    fun a b => Subtype.ext (R.chowSeriesScale_mul a.1 b.1)

/-- The underlying series of `R.unitalSeriesScale a` is `chowSeriesScale a.1`. -/
@[simp] theorem unitalSeriesScale_val (a : UnitalSeries R) :
    (R.unitalSeriesScale a).1 = chowSeriesScale a.1 := rfl

/-- The scaling map read on `Additive` of the group of unital series. -/
theorem toAdditive_unitalSeriesScale_ofMul (a : UnitalSeries R) :
    MonoidHom.toAdditive R.unitalSeriesScale (Additive.ofMul a) =
      Additive.ofMul (R.unitalSeriesScale a) := rfl

end ChowCohomologySeriesRing

/-! ### Two values of the Chern class map -/

variable {R : ChowCohomologySeriesRing C G sX}

/-- The constant term of the Chern class of any class in `K_0(Vect(X))` is `1`. -/
theorem chernClassKGroup_apply_zero (D : TotalChernClassSeries C G sX R)
    (α : VectorBundleKZero X) : chernClassKGroup D α 0 = R.one 0 :=
  (Additive.toMul (chernClassKGroupHom D α) : UnitalSeries R).2

/-- The Chern class map is the underlying series of the Chern class homomorphism. -/
theorem chernClassKGroup_eq_val (D : TotalChernClassSeries C G sX R) (α : VectorBundleKZero X) :
    chernClassKGroup D α = (Additive.toMul (chernClassKGroupHom D α) : UnitalSeries R).1 := rfl

/-- The Chern class homomorphisms of `a` and `b` are related by the scaling map exactly when
the Chern class series are. -/
private theorem chernClassKGroupHom_eq_iff {D : TotalChernClassSeries C G sX R}
    {a b : VectorBundleKZero X} :
    chernClassKGroupHom D a = MonoidHom.toAdditive R.unitalSeriesScale (chernClassKGroupHom D b) ↔
      chernClassKGroup D a = chowSeriesScale (chernClassKGroup D b) :=
  ⟨fun h => congrArg Subtype.val (congrArg Additive.toMul h),
    fun h => congrArg Additive.ofMul (Subtype.ext h)⟩

/-! ### The Chern classes of an invertible module -/

/-- **The facts about the Chern classes of an invertible module that the base case of the
source's proof of Stacks 0FEN uses.** For an invertible module `ℒ` on `X`:

* its tensor square is invertible, Stacks 01CT (1);
* `c_j(ℒ) = 0` for `j ≥ 2`, the vanishing of the Chern classes above the rank, Stacks 02U0;
* `c_1(ℒ ⊗ ℒ) = 2c_1(ℒ)`, the additivity of the first Chern class, Stacks 02SZ.

None of the three is formalized in this repository. The bivariant Chern classes the last two are
statements about are themselves only characterized here, by `Stacks.Chow.IsChernClassBivariant`
of Stacks 0B7H, and `Stacks.Chow.TotalChernClassSeries` carries them; so these are properties of
a carried datum and are carried in turn. Stacks 01CT (1) is available in the library for the
tensor product `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, but `K_0(Vect(X))` is
built over `AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace` and the comparison of the two
constructions is not available. -/
structure InvertibleChernClassData (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (R : ChowCohomologySeriesRing C G sX)
    (D : TotalChernClassSeries C G sX R) : Prop where
  /-- **Stacks 01CT (1).** The tensor square of an invertible module is invertible. -/
  isInvertible_tensorSelf : ∀ L : X.Modules,
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
      Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (Scheme.Modules.tensorObjRingedSpace X L L)
  /-- **Stacks 02U0.** The Chern classes of an invertible module vanish above degree `1`. -/
  ch_apply_of_two_le : ∀ L : X.Modules,
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
      ∀ n : ℕ, 2 ≤ n → D.ch L n = 0
  /-- **Stacks 02SZ.** The first Chern class of a tensor square is twice the first Chern
  class. -/
  ch_tensorSelf_apply_one : ∀ L : X.Modules,
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L →
      D.ch (Scheme.Modules.tensorObjRingedSpace X L L) 1 = (2 : ℕ) • D.ch L 1

/-- **The base case of the source's proof.** For an invertible module `ℒ` the total Chern class
of its tensor square is the `2^i`-scaling of its total Chern class: both series are concentrated
in degrees `0` and `1` with constant term `1`, and their degree-`1` coefficients differ by the
factor `2` of Stacks 02SZ. -/
theorem ch_tensorSelf_eq_chowSeriesScale {D : TotalChernClassSeries C G sX R}
    (N : InvertibleChernClassData C G sX R D) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    D.ch (Scheme.Modules.tensorObjRingedSpace X L L) = chowSeriesScale (D.ch L) := by
  funext n
  match n with
  | 0 => rw [chowSeriesScale_apply, pow_zero, one_smul, D.ch_apply_zero, D.ch_apply_zero]
  | 1 => rw [chowSeriesScale_apply, pow_one, N.ch_tensorSelf_apply_one L hL]
  | (m + 2) =>
    rw [chowSeriesScale_apply,
      N.ch_apply_of_two_le _ (N.isInvertible_tensorSelf L hL) (m + 2) (by omega),
      N.ch_apply_of_two_le L hL (m + 2) (by omega), smul_zero]

/-- **The Chern class of the second Adams operation on the class of an invertible module.** The
base case read on `K_0(Vect(X))`: `ψ²([ℒ]) = [ℒ ⊗ ℒ]` by Stacks 0FEJ, where it is proved and not
assumed, and `c(ℒ ⊗ ℒ)` is the scaling of `c(ℒ)`. -/
theorem chernClassKGroupHom_secondAdams_classOf_isInvertible
    {D : TotalChernClassSeries C G sX R} (N : InvertibleChernClassData C G sX R D)
    (h : SquarePowersData X) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    chernClassKGroupHom D (secondAdamsAddHom h (classOf X L)) =
      MonoidHom.toAdditive R.unitalSeriesScale (chernClassKGroupHom D (classOf X L)) := by
  have := hL
  rw [secondAdamsAddHom_classOf_isInvertible h L, chernClassKGroupHom_eq_iff,
    chernClassKGroup_classOf, chernClassKGroup_classOf]
  exact ch_tensorSelf_eq_chowSeriesScale N L hL

/-- **The source's steps 4 and 5.** On a sum of classes of invertible modules the Chern class of
the second Adams operation is the `2^i`-scaling of the Chern class: `ψ²` is additive and sends
`[ℒ_j]` to `[ℒ_j ⊗ ℒ_j]`, the Chern class map turns a sum into a Cauchy product, and the scaling
map is multiplicative. In the source's notation, `c(α) = ∏ (1 + x_j)` becomes
`c(ψ²(α)) = ∏ (1 + 2x_j)`. -/
theorem chernClassKGroupHom_secondAdams_sum {D : TotalChernClassSeries C G sX R}
    (N : InvertibleChernClassData C G sX R D) (h : SquarePowersData X) {m : ℕ}
    (L : Fin m → X.Modules)
    (hL : ∀ j, Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)) :
    chernClassKGroupHom D (secondAdamsAddHom h (∑ j, classOf X (L j))) =
      MonoidHom.toAdditive R.unitalSeriesScale
        (chernClassKGroupHom D (∑ j, classOf X (L j))) := by
  rw [map_sum (secondAdamsAddHom h), map_sum (chernClassKGroupHom D),
    map_sum (chernClassKGroupHom D), map_sum (MonoidHom.toAdditive R.unitalSeriesScale)]
  exact Finset.sum_congr rfl fun j _ =>
    chernClassKGroupHom_secondAdams_classOf_isInvertible N h (L j) (hL j)

/-- The series form of `Stacks.Chow.chernClassKGroupHom_secondAdams_sum`. -/
theorem chernClassKGroup_secondAdams_sum {D : TotalChernClassSeries C G sX R}
    (N : InvertibleChernClassData C G sX R D) (h : SquarePowersData X) {m : ℕ}
    (L : Fin m → X.Modules)
    (hL : ∀ j, Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)) :
    chernClassKGroup D (secondAdamsAddHom h (∑ j, classOf X (L j))) =
      chowSeriesScale (chernClassKGroup D (∑ j, classOf X (L j))) :=
  chernClassKGroupHom_eq_iff.1 (chernClassKGroupHom_secondAdams_sum N h L hL)

/-! ### Descent along a pullback of Chow cohomology -/

/-- **The Chern class map commutes with a pullback of Chow cohomology.** A degreewise pullback
which is a ring map for the product of `A^*(X)^∧` and carries total Chern classes of modules to
total Chern classes of their pullbacks carries `c(α)` to `c(p(α))` for every
`α ∈ K_0(Vect(X))`: both sides are homomorphisms from `K_0(Vect(X))` to the group of unital
series on `P`, so they agree as soon as they agree on the classes of finite locally free
modules. -/
theorem chernClassKGroup_pullback {P : Scheme.{u}} {sP : P ⟶ C.S} [LocallyOfFiniteType sP]
    {RP : ChowCohomologySeriesRing C G sP} {D : TotalChernClassSeries C G sX R}
    {DP : TotalChernClassSeries C G sP RP} {f : P ⟶ X}
    (pb : ∀ i : ℕ,
      chowCohomologyComponent C G sX (i : ℤ) →+ chowCohomologyComponent C G sP (i : ℤ))
    (pbOne : ∀ i : ℕ, pb i (R.one i) = RP.one i)
    (pbGradedMul : ∀ (i j n : ℕ) (h : i + j = n)
      (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ)),
      pb n (R.gradedMul i j n h x y) = RP.gradedMul i j n h (pb i x) (pb j y))
    (pK : VectorBundleKZero X →+* VectorBundleKZero P)
    (pbCh : ∀ E' : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E' →
      ∀ i : ℕ, pb i (D.ch E' i) = DP.ch ((Scheme.Modules.pullback f).obj E') i)
    (pKClassOf : ∀ E' : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E' →
      pK (classOf X E') = classOf P ((Scheme.Modules.pullback f).obj E'))
    (β : VectorBundleKZero X) (i : ℕ) :
    pb i (chernClassKGroup D β i) = chernClassKGroup DP (pK β) i := by
  let pbHom : UnitalSeries R →* UnitalSeries RP :=
    MonoidHom.mk' (fun a : UnitalSeries R => ⟨fun n => pb n (a.1 n), by
        show pb 0 (a.1 0) = RP.one 0
        rw [a.2]
        exact pbOne 0⟩)
      (fun a b => Subtype.ext (by
        funext n
        show pb n (chowSeriesMul R.gradedMul a.1 b.1 n) =
          chowSeriesMul RP.gradedMul (fun k => pb k (a.1 k)) (fun k => pb k (b.1 k)) n
        rw [chowSeriesMul, chowSeriesMul, map_sum]
        refine Finset.sum_congr rfl ?_
        rintro ⟨k, l⟩ hmem
        rw [Finset.mem_antidiagonal] at hmem
        rw [chowSeriesTerm_of_add R.gradedMul a.1 b.1 hmem,
          chowSeriesTerm_of_add RP.gradedMul (fun k => pb k (a.1 k)) (fun k => pb k (b.1 k))
            hmem, pbGradedMul]))
  have key : (MonoidHom.toAdditive pbHom).comp (chernClassKGroupHom D) =
      (chernClassKGroupHom DP).comp
        (pK : VectorBundleKZero X →+ VectorBundleKZero P) := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E' hE' => ?_
    show MonoidHom.toAdditive pbHom (chernClassKGroupHom D (classOf X E')) =
      chernClassKGroupHom DP (pK (classOf X E'))
    rw [chernClassKGroupHom_classOf, pKClassOf E' hE', chernClassKGroupHom_classOf]
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    funext n
    exact pbCh E' hE' n
  have hβ := congrArg
    (fun φ : VectorBundleKZero X →+ Additive (UnitalSeries RP) => φ β) key
  exact congrFun (congrArg Subtype.val (congrArg Additive.toMul hβ)) i

/-! ### The splitting principle -/

/-- **One member of the splitting data of Stacks 02UL for a module `ℰ` on `X`**, carried along a
morphism `f : P ⟶ X`.

The source chooses `f` projective and smooth so that `A^*(X) ⟶ A^*(P)` is injective and `f^*ℰ`
has a filtration with invertible graded pieces. Neither Stacks 02UL, nor the multiplicativity of
the restriction map of Stacks 0B7F, nor the functoriality of `K_0(Vect(-))` is available in this
repository, so all of that is collected here. Every field is a property of the real situation:

* `RP`, `DP`, `hP` and `invP` are the data Stacks 0FEL, Stacks 0FEJ and the base case already
  carry at `X`, carried again at `P`;
* `pb` is the restriction map `f^* : A^i(X) ⟶ A^i(P)` of Stacks 0B7F, and `pbOne`,
  `pbGradedMul` and `pbCh` say that it is a ring map of `A^*(X)^∧` and carries the total Chern
  class of a module to that of its pullback;
* `pK`, `pKClassOf` and `pKIsFiniteLocallyFree` are the pullback ring map of Grothendieck
  rings, already carried as a hypothesis by
  `AlgebraicGeometry.VectorBundleKZero.secondAdamsAddHom_pullback`, which is the form in which
  Stacks 0FEJ proves the compatibility of `ψ²` with pullback;
* `rank`, `pieces`, `piecesIsInvertible` and `pKClassOfEqSum` are the filtration of `f^*ℰ` with
  invertible graded pieces, read as the relation `[f^*ℰ] = ∑_j [ℒ_j]` in `K_0(Vect(P))` that the
  defining relation of the Grothendieck group turns it into.

Injectivity of `pb` is *not* a field here; it is asked of the whole family in
`Stacks.Chow.SecondAdamsSplitting`, which is what lets a module of non-constant rank be
handled. -/
structure SecondAdamsSplittingAt (C : ChowSituation.{u}) (G : GysinSystem C)
    {X P : Scheme.{u}} (sX : X ⟶ C.S) (sP : P ⟶ C.S)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sP]
    (R : ChowCohomologySeriesRing C G sX) (D : TotalChernClassSeries C G sX R)
    (hX : SquarePowersData X) (f : P ⟶ X) (E : X.Modules) where
  /-- The ring `A^*(P)^∧` of Stacks 0FE0, as Stacks 0FEL carries it. -/
  RP : ChowCohomologySeriesRing C G sP
  /-- The total Chern class on `P`, as Stacks 0FEL carries it. -/
  DP : TotalChernClassSeries C G sP RP
  /-- The geometric input of Stacks 0FEJ on `P`. -/
  hP : SquarePowersData P
  /-- Stacks 01CT (1), Stacks 02U0 and Stacks 02SZ on `P`. -/
  invP : InvertibleChernClassData C G sP RP DP
  /-- The restriction map `f^* : A^i(X) ⟶ A^i(P)` of Stacks 0B7F. -/
  pb : ∀ i : ℕ,
    chowCohomologyComponent C G sX (i : ℤ) →+ chowCohomologyComponent C G sP (i : ℤ)
  /-- The restriction map preserves the unit of `A^*(X)^∧`. -/
  pbOne : ∀ i : ℕ, pb i (R.one i) = RP.one i
  /-- The restriction map is multiplicative for the degreewise product of `A^*(X)^∧`. -/
  pbGradedMul : ∀ (i j n : ℕ) (h : i + j = n)
    (x : chowCohomologyComponent C G sX (i : ℤ)) (y : chowCohomologyComponent C G sX (j : ℤ)),
    pb n (R.gradedMul i j n h x y) = RP.gradedMul i j n h (pb i x) (pb j y)
  /-- The restriction map carries the total Chern class of a finite locally free module to the
  total Chern class of its pullback. -/
  pbCh : ∀ E' : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E' →
    ∀ i : ℕ, pb i (D.ch E' i) = DP.ch ((Scheme.Modules.pullback f).obj E') i
  /-- The pullback ring map of Grothendieck rings. -/
  pK : VectorBundleKZero X →+* VectorBundleKZero P
  /-- The pullback ring map sends `[ℰ']` to `[f^*ℰ']`. -/
  pKClassOf : ∀ E' : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E' →
    pK (classOf X E') = classOf P ((Scheme.Modules.pullback f).obj E')
  /-- Pullback preserves finite local freeness. -/
  pKIsFiniteLocallyFree : ∀ E' : X.Modules,
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E' →
      IsFiniteLocallyFree.{u, u, u} (R := P.ringCatSheaf)
        ((Scheme.Modules.pullback f).obj E')
  /-- The length of the filtration of `f^*ℰ`. -/
  rank : ℕ
  /-- The invertible graded pieces `ℒ_j` of the filtration of `f^*ℰ`. -/
  pieces : Fin rank → P.Modules
  /-- The graded pieces are invertible. -/
  piecesIsInvertible : ∀ j,
    Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property (pieces j)
  /-- **Stacks 02UL.** The filtration gives `[f^*ℰ] = ∑_j [ℒ_j]` in `K_0(Vect(P))`. -/
  pKClassOfEqSum : pK (classOf X E) = ∑ j, classOf P (pieces j)

/-- **The splitting principle of Stacks 02UL for a module `ℰ` on `X`, in the shape the source's
proof of Stacks 0FEN uses it.** A family of morphisms `p_r : P_r ⟶ X`, indexed by the possible
ranks, each carrying `Stacks.Chow.SecondAdamsSplittingAt` data for `ℰ`, such that the
restrictions are *jointly* injective on each `A^i(X)`.

A family and not a single morphism: Stacks 02UL splits a module of constant rank `r` into `r`
invertible pieces, and a module of non-constant rank never becomes a sum of a fixed number of
invertible classes after a pullback, invertible modules having rank one. The source therefore
reduces to constant rank first, over the rank loci of `ℰ` (Stacks 0ESW). Composing the rank loci
of `ℰ` with the splitting spaces of Stacks 02UL over them gives such a family for every finite
locally free `ℰ`, the joint injectivity being the injectivity of
`A^i(X) ⟶ ∏_r A^i(X_r)` followed by the injectivity Stacks 02UL provides on each rank locus. A
single morphism would have restricted the lemma to the modules of constant rank. -/
structure SecondAdamsSplitting (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [instX : LocallyOfFiniteType sX] (R : ChowCohomologySeriesRing C G sX)
    (D : TotalChernClassSeries C G sX R) (hX : SquarePowersData X) (E : X.Modules) where
  /-- The splitting spaces, one for each rank occurring on `X`. -/
  space : ℕ → Scheme.{u}
  /-- Their structure morphisms to the base. -/
  structureMorphism : ∀ r : ℕ, space r ⟶ C.S
  /-- The structure morphisms are locally of finite type. -/
  structureMorphismFiniteType : ∀ r : ℕ, LocallyOfFiniteType (structureMorphism r)
  /-- The morphisms down to `X`. -/
  proj : ∀ r : ℕ, space r ⟶ X
  /-- The splitting data along each member of the family. -/
  member : ∀ r : ℕ, @SecondAdamsSplittingAt C G X (space r) sX (structureMorphism r) instX
    (structureMorphismFiniteType r) R D hX (proj r) E
  /-- **Stacks 02UL and Stacks 0ESW.** The restrictions are jointly injective on `A^i(X)`. -/
  jointInjective : ∀ (i : ℕ) (x y : chowCohomologyComponent C G sX (i : ℤ)),
    (∀ r : ℕ, (member r).pb i x = (member r).pb i y) → x = y

/-- **The splitting principle of Stacks 02UL holds for `ℰ`**: there is a
`Stacks.Chow.SecondAdamsSplitting` for it. -/
def HasSecondAdamsSplitting (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (R : ChowCohomologySeriesRing C G sX)
    (D : TotalChernClassSeries C G sX R) (hX : SquarePowersData X) (E : X.Modules) : Prop :=
  Nonempty (SecondAdamsSplitting C G sX R D hX E)

/-- **The generator case of Stacks 0FEN.** For a finite locally free module `ℰ` with the
splitting data of Stacks 02UL, `c(ψ²([ℰ]))` is the `2^i`-scaling of `c([ℰ])`. The identity is
proved on each splitting space, where the pullback of `[ℰ]` is a sum of classes of invertible
modules, and descends because the restrictions are jointly injective; `ψ²` commutes with the
pullback of Grothendieck rings by Stacks 0FEJ. -/
theorem chernClassKGroup_secondAdams_classOf {D : TotalChernClassSeries C G sX R}
    {hX : SquarePowersData X} {E : X.Modules}
    (hs : HasSecondAdamsSplitting C G sX R D hX E) :
    chernClassKGroup D (secondAdamsAddHom hX (classOf X E)) =
      chowSeriesScale (chernClassKGroup D (classOf X E)) := by
  obtain ⟨S⟩ := hs
  funext i
  refine S.jointInjective i _ _ fun r => ?_
  have := S.structureMorphismFiniteType r
  have hpb := chernClassKGroup_pullback (S.member r).pb (S.member r).pbOne
    (S.member r).pbGradedMul (S.member r).pK (S.member r).pbCh (S.member r).pKClassOf
  rw [hpb, chowSeriesScale_apply, map_nsmul, hpb,
    ← secondAdamsAddHom_pullback (S.proj r) (S.member r).hP hX (S.member r).pK
      (S.member r).pKClassOf (S.member r).pKIsFiniteLocallyFree,
    (S.member r).pKClassOfEqSum,
    chernClassKGroup_secondAdams_sum (S.member r).invP (S.member r).hP (S.member r).pieces
      (S.member r).piecesIsInvertible,
    chowSeriesScale_apply]

/-- **Stacks 0FEN, the first equation, as an equality of series.** The identity
`c(ψ²(α)) = 2^• c(α)` in `∏_{i ≥ 0} A^i(X)`. Both sides are homomorphisms from `K_0(Vect(X))`,
written additively, to the group of unital series, written multiplicatively — for the right-hand
side that is exactly the observation that the scaling map is a ring endomorphism, the first step
of the source's proof — so it suffices to compare them on the classes of finite locally free
modules, which is `Stacks.Chow.chernClassKGroup_secondAdams_classOf`. -/
theorem chernClassKGroup_secondAdams_eq_chowSeriesScale
    {D : TotalChernClassSeries C G sX R} (hX : SquarePowersData X)
    (hsplit : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      HasSecondAdamsSplitting C G sX R D hX E)
    (α : VectorBundleKZero X) :
    chernClassKGroup D (secondAdamsRingHom hX α) =
      chowSeriesScale (chernClassKGroup D α) := by
  have key : (chernClassKGroupHom D).comp (secondAdamsAddHom hX) =
      (MonoidHom.toAdditive R.unitalSeriesScale).comp (chernClassKGroupHom D) := by
    refine AlgebraicGeometry.VectorBundleKZero.addHom_ext fun E hE => ?_
    exact chernClassKGroupHom_eq_iff.2 (chernClassKGroup_secondAdams_classOf (hsplit E hE))
  have hα := congrArg
    (fun φ : VectorBundleKZero X →+ Additive (UnitalSeries R) => φ α) key
  rw [secondAdamsRingHom_apply]
  exact chernClassKGroupHom_eq_iff.1 hα

/-- **Stacks Project, Tag 0FEN, the first equation.** Let `(S, δ)` be as in Stacks 02QL, let `X`
be locally of finite type over `S`, let `ψ²` be the second Adams operation of Stacks 0FEJ and let
`c` be the Chern class map of Stacks 0FEL. Then

  `c_i(ψ²(α)) = 2^i c_i(α)`

for every `α ∈ K_0(Vect(X))` and every `i ≥ 0`.

The parameters `R`, `D` and `hX` are the data Stacks 0FEL and Stacks 0FEJ already carry; `hsplit`
is the splitting principle of Stacks 02UL, which the source's proof uses and which this
repository does not have, in the shape `Stacks.Chow.SecondAdamsSplitting` records. The scaling
map is not assumed to be a ring map, the base case is not assumed, and the descent is proved. -/
@[stacks 0FEN "the first equation, c_i(psi^2(alpha)) = 2^i c_i(alpha), for every alpha in \
  K_0(Vect(X)); psi^2 is AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom of Stacks 0FEJ \
  and c is Stacks.Chow.chernClassKGroup of Stacks 0FEL, so the parameters R, D and hX are the \
  data those two already carry. CARRIED in addition: (1) the splitting principle of Stacks \
  02UL, not formalized in this repository, as Stacks.Chow.HasSecondAdamsSplitting -- a family \
  of morphisms p_r : P_r -> X, jointly injective on each A^i(X), along each of which [E] \
  becomes a sum of classes of invertible modules, together with the restriction map of Stacks \
  0B7F and its multiplicativity and Chern class compatibility (which Stacks 0B7F does not \
  formalize, needing the composition product of Stacks 0FE0) and the functoriality of \
  K_0(Vect(-)) (which this repository does not construct, as the notes of \
  StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator record); the family rather than a \
  single morphism is what keeps modules of non-constant rank in scope, since the source reduces \
  to constant rank over the rank loci (Stacks 0ESW) before applying Stacks 02UL; and (2) Stacks \
  02U0 and Stacks 02SZ, the vanishing of c_j of an invertible module above degree 1 and the \
  additivity c_1(L tensor L) = 2 c_1(L), with Stacks 01CT (1), as \
  Stacks.Chow.InvertibleChernClassData -- properties of the bivariant Chern classes of Stacks \
  0B7H, which this repository characterizes but does not construct. NOT carried, and proved \
  here: that the 2^i-scaling of A^i(X) is a ring endomorphism of the product (the source's \
  first step, which is what reduces the lemma to additive generators), the base case \
  c(L tensor L) = 1 + 2 c_1(L), the value psi^2([L]) = [L tensor L] (proved in Stacks 0FEJ), \
  the computation of c(psi^2(alpha)) on a sum of classes of invertible modules, and the descent \
  along the pullback"]
theorem chernClassKGroup_secondAdams {D : TotalChernClassSeries C G sX R}
    (hX : SquarePowersData X)
    (hsplit : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      HasSecondAdamsSplitting C G sX R D hX E)
    (α : VectorBundleKZero X) (i : ℕ) :
    chernClassKGroup D (secondAdamsRingHom hX α) i =
      ((2 : ℕ) ^ i) • chernClassKGroup D α i := by
  rw [chernClassKGroup_secondAdams_eq_chowSeriesScale hX hsplit α, chowSeriesScale_apply]

/-! ### The Chern character -/

/-- **The power sums of the Chern classes, as a datum.** For each `p` the class
`P_p(c_1, …, c_p) ∈ A^p(X)` as a function of the total Chern class series, with the two
properties of the universal Newton polynomial `P_p` that are used below:

* it is additive for the Cauchy product of unital series, which is why the Chern character is
  additive on short exact sequences, Stacks 0F9C;
* it is weighted homogeneous of degree `p`, so substituting `2^j c_j` for `c_j` multiplies it by
  `2^p`.

The power sums are not constructed in this repository:
`Stacks.Chow.powerSumClassArbitraryRank` of Stacks 0ESX assembles them over the rank loci from a
quantified family of constant-rank power sums, so there is no polynomial expression off which
either property could be read, and both are carried. The second is a purely combinatorial
property of `P_p`, with no geometry in it, and it is what makes the second equation of
Stacks 0FEN a consequence of the first. -/
structure NewtonPowerSums (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (R : ChowCohomologySeriesRing C G sX) where
  /-- The power sum `P_p(c_1, …, c_p) ∈ A^p(X)` of a total Chern class series. -/
  powerSum : ∀ p : ℕ, chowCohomologySeries C G sX → chowCohomologyComponent C G sX (p : ℤ)
  /-- The power sums are additive for the Cauchy product of series with constant term `1`. -/
  powerSum_mul : ∀ (p : ℕ) (a b : chowCohomologySeries C G sX),
    a 0 = R.one 0 → b 0 = R.one 0 →
      powerSum p (chowSeriesMul R.gradedMul a b) = powerSum p a + powerSum p b
  /-- The power sum `P_p` is weighted homogeneous of degree `p`. -/
  powerSum_chowSeriesScale : ∀ (p : ℕ) (a : chowCohomologySeries C G sX),
    powerSum p (chowSeriesScale a) = ((2 : ℕ) ^ p) • powerSum p a

/-- **The Chern character of Stacks 0FEM.** The degree-`p` component

  `ch_p(α) = P_p(c_1(α), …, c_p(α))/p! ∈ A^p(X) ⊗ 𝐐`

of the Chern character of `α ∈ K_0(Vect(X))`, the target being `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)`. On a
generator `[ℰ]` this is the source's formula for `ch(ℰ)`, and it is additive by
`Stacks.Chow.chernCharacterKGroup_add`, which is the content Stacks 0FEM extends to
`K_0(Vect(X))`. -/
def chernCharacterKGroup {D : TotalChernClassSeries C G sX R} (N : NewtonPowerSums C G sX R)
    (α : VectorBundleKZero X) (p : ℕ) :
    TensorProduct ℤ ℚ (chowCohomologyComponent C G sX (p : ℤ)) :=
  ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] N.powerSum p (chernClassKGroup D α)

/-- **The Chern character is additive on `K_0(Vect(X))`.** The Chern class map turns a sum into a
Cauchy product, and the power sums are additive for it. -/
theorem chernCharacterKGroup_add {D : TotalChernClassSeries C G sX R}
    (N : NewtonPowerSums C G sX R) (α β : VectorBundleKZero X) (p : ℕ) :
    chernCharacterKGroup (D := D) N (α + β) p =
      chernCharacterKGroup (D := D) N α p + chernCharacterKGroup (D := D) N β p := by
  rw [chernCharacterKGroup, chernCharacterKGroup, chernCharacterKGroup,
    chernClassKGroup_add D α β,
    N.powerSum_mul p _ _ (chernClassKGroup_apply_zero D α) (chernClassKGroup_apply_zero D β),
    TensorProduct.tmul_add]

/-- **Stacks Project, Tag 0FEN, the second equation.** In the situation of
`Stacks.Chow.chernClassKGroup_secondAdams`, with `ch` the Chern character of Stacks 0FEM,

  `ch_i(ψ²(α)) = 2^i ch_i(α)`

for every `α ∈ K_0(Vect(X))` and every `i ≥ 0`.

This is deduced from the first equation in its series form,
`Stacks.Chow.chernClassKGroup_secondAdams_eq_chowSeriesScale`, together with the weighted
homogeneity of the Newton power sums: `ch_i` is `P_i(c_1, …, c_i)/i!` and `P_i` is weighted
homogeneous of degree `i`. No second splitting argument is needed. -/
@[stacks 0FEN "the second equation, ch_i(psi^2(alpha)) = 2^i ch_i(alpha), for every alpha in \
  K_0(Vect(X)); ch is Stacks.Chow.chernCharacterKGroup, the Chern character of Stacks 0FEM \
  written out as ch_p(alpha) = P_p(c_1(alpha), ..., c_p(alpha))/p! in the product over p >= 0 \
  of A^p(X) tensor Q, which is the library's Stacks.Chow.fullRationalChowCohomology. It is \
  deduced from the first equation rather than proved by a second splitting argument. CARRIED in \
  addition to what the first equation carries: the power sums P_p themselves, as \
  Stacks.Chow.NewtonPowerSums, with their additivity for the Cauchy product (Stacks 0F9C) and \
  their weighted homogeneity of degree p -- Stacks.Chow.powerSumClassArbitraryRank of Stacks \
  0ESX assembles the power sums over the rank loci from a quantified family rather than from a \
  polynomial expression, so neither property can be read off here. The weighted homogeneity is \
  a combinatorial property of P_p alone, with no geometry in it"]
theorem chernCharacterKGroup_secondAdams {D : TotalChernClassSeries C G sX R}
    (N : NewtonPowerSums C G sX R) (hX : SquarePowersData X)
    (hsplit : ∀ E : X.Modules, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E →
      HasSecondAdamsSplitting C G sX R D hX E)
    (α : VectorBundleKZero X) (i : ℕ) :
    chernCharacterKGroup (D := D) N (secondAdamsRingHom hX α) i =
      ((2 : ℕ) ^ i) • chernCharacterKGroup (D := D) N α i := by
  have hns : ∀ (k : ℕ) (q : ℚ) (x : chowCohomologyComponent C G sX (i : ℤ)),
      q ⊗ₜ[ℤ] (k • x) = k • (q ⊗ₜ[ℤ] x) := fun k q x =>
    map_nsmul (TensorProduct.mk ℤ ℚ (chowCohomologyComponent C G sX (i : ℤ)) q) k x
  rw [chernCharacterKGroup, chernCharacterKGroup,
    chernClassKGroup_secondAdams_eq_chowSeriesScale hX hsplit α,
    N.powerSum_chowSeriesScale, hns]

end Stacks.Chow

end
