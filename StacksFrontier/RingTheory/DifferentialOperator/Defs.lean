module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Differential operators of finite order

Let `R → S` be a ring map and let `M`, `N` be `S`-modules. Following the source, a
*differential operator of order `k`* from `M` to `N` relative to `R → S` is defined by induction
on `k`: for `k = 0` it is an `S`-linear map, and for `k + 1` it is an `R`-linear map `D` such that
for every `g ∈ S` the commutator `m ↦ D (g • m) - g • D m` is a differential operator of order
`k`. The commutator of an `S`-linear map with `g` vanishes, so a differential operator of order
`k` is also one of order `k + 1`, and the source records the resulting chain
`Diff⁰(M, N) ⊆ Diff¹(M, N) ⊆ Diff²(M, N) ⊆ …`: the integer `k` is an upper bound for the order,
not the order itself, and the definition is named accordingly here. Unwinding the induction, `D`
has order at most `k` exactly when every `(k + 1)`-fold iterated commutator of `D` with elements
of `S` vanishes.

The `S`-linear maps are the operators of order at most `0`. For `R` a commutative ring,
`S = M = N = R[X]`, the derivative `d/dX` has order at most `1` and not `0`: its commutator with
`X` is the identity, which is `R[X]`-linear, while `d/dX` itself is not `R[X]`-linear.

## Main definitions

* `LinearMap.IsDifferentialOperatorOfOrderLE`: the predicate on an `R`-linear map `D : M → N`
  between `S`-modules saying that `D` is a differential operator of order at most `k` relative
  to `R → S`.
* `LinearMap.commSMul`: the commutator `m ↦ D (g • m) - g • D m` of `D` with the multiplication
  by `g : S`, the operator whose order drops by one in the induction.

## Implementation notes

`R`-linearity is carried by the type `M →ₗ[R] N` in both branches of the induction rather than
being stated as a side condition on an additive map, and the `R`-module structures on `M` and `N`
are pinned to the restrictions along `R → S` by `IsScalarTower R S M` and `IsScalarTower R S N`.
At order `0` this adds nothing: an `S`-linear map between such modules is `R`-linear. The
commutator with `g` is the difference of the two composites of `D` with multiplication by `g`,
`Algebra.lsmul R R M g : Module.End R M`; multiplication by `g` is `R`-linear because the image
of `R` in `S` is central, so this is available for an arbitrary, not necessarily commutative,
`R`-algebra `S`.

Only `N` is required to be a group, since only the values of `D` are subtracted, and `S` is
required to be no more than an `R`-algebra: commutativity of `S` enters not in this definition but
in the assertion, made in the source immediately after it, that the differential operators of
order at most `k` form an `S`-submodule `Diffᵏ_{S/R}(M, N)` of `M →ₗ[R] N`.

## References

* [Stacks 09CI](https://stacks.math.columbia.edu/tag/09CI), Definition 10.133.1, in the section
  "Finite order differential operators" (Tag 09CH).
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- Let `R → S` be a ring map, let `M` and `N` be `S`-modules, and let `k : ℕ`.
`D.IsDifferentialOperatorOfOrderLE S k` says that the `R`-linear map `D : M → N` is a
*differential operator of order at most `k`* relative to `R → S`. By induction on `k`: order at
most `0` means `S`-linear, and order at most `k + 1` means that for every `g : S` the commutator
`m ↦ D (g • m) - g • D m` is a differential operator of order at most `k`. -/
@[stacks 09CI "The source's `k` bounds the order: `Diff⁰ ⊆ Diff¹ ⊆ …`, whence `LE` in the name.
The commutator `m ↦ D (g • m) - g • D m` is the difference of the two composites of `D` with
`Algebra.lsmul R R _ g`, multiplication by `g`. The `S`-module `Diffᵏ_{S/R}(M, N)` of the
paragraph following the definition is a separate statement. See the module docstring.",
  ega "IV 16.8.1" "affine (module) case",
  sga "3 VIIA 1.4" "affine case",
  sga "6 II AppII.1.2.2" "Diff^n, affine case", sga "3 VIIA 1.1.1" "partial"]
public def IsDifferentialOperatorOfOrderLE (S : Type*) [Semiring S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] [Module S N] [IsScalarTower R S N] : ℕ → (M →ₗ[R] N) → Prop
  | 0, D => ∀ (g : S) (m : M), D (g • m) = g • D m
  | k + 1, D => ∀ g : S, IsDifferentialOperatorOfOrderLE S k
      (D ∘ₗ Algebra.lsmul R R M g - Algebra.lsmul R R N g ∘ₗ D)

/-! ### The commutator of an operator with a scalar -/

section Comm

variable {N₂ S : Type*} [Semiring S] [Algebra R S] [Module S M] [IsScalarTower R S M]
  [Module S N] [IsScalarTower R S N]

/-- The commutator `m ↦ D (g • m) - g • D m` of an `R`-linear map `D : M → N` with the
multiplication by `g : S`. -/
@[ega "IV 16.8.8"]
public def commSMul (D : M →ₗ[R] N) (g : S) : M →ₗ[R] N :=
  D ∘ₗ Algebra.lsmul R R M g - Algebra.lsmul R R N g ∘ₗ D

/-- The commutator `commSMul D g` sends `m` to `D (g • m) - g • D m`. -/
public lemma commSMul_apply (D : M →ₗ[R] N) (g : S) (m : M) :
    commSMul D g m = D (g • m) - g • D m := rfl

/-- The commutators of the zero operator vanish. -/
public lemma commSMul_zero_left (g : S) : commSMul (0 : M →ₗ[R] N) g = 0 := by
  ext m; simp [commSMul_apply]

/-- The commutator with `g` is additive in the operator. -/
public lemma commSMul_add_left (D E : M →ₗ[R] N) (g : S) :
    commSMul (D + E) g = commSMul D g + commSMul E g := by
  ext m
  simp only [commSMul_apply, add_apply, smul_add]
  abel

/-- The commutator with `g` is subtractive in the operator. -/
public lemma commSMul_sub_left (D E : M →ₗ[R] N) (g : S) :
    commSMul (D - E) g = commSMul D g - commSMul E g := by
  ext m
  simp only [commSMul_apply, sub_apply, smul_sub]
  abel

/-- The commutator with the scalar `0` vanishes. -/
public lemma commSMul_zero_right (D : M →ₗ[R] N) : commSMul D (0 : S) = 0 := by
  ext m; simp [commSMul_apply]

/-- The commutator of `D` is additive in the scalar. -/
public lemma commSMul_add_right (D : M →ₗ[R] N) (g h : S) :
    commSMul D (g + h) = commSMul D g + commSMul D h := by
  ext m
  simp only [commSMul_apply, add_apply, add_smul, map_add]
  abel

/-- The Leibniz rule for the commutator: `[D, b * c] = [D, b] ∘ c + b • [D, c]`. -/
public lemma commSMul_mul_apply (D : M →ₗ[R] N) (b c : S) (m : M) :
    commSMul D (b * c) m = commSMul D b (c • m) + b • commSMul D c m := by
  simp only [commSMul_apply, mul_smul, smul_sub]
  abel

/-- The Leibniz rule for the commutator: `[D, b * c] = [D, b] ∘ c + b • [D, c]`. -/
public lemma commSMul_mul (D : M →ₗ[R] N) (b c : S) :
    commSMul D (b * c)
      = commSMul D b ∘ₗ Algebra.lsmul R R M c + Algebra.lsmul R R N b ∘ₗ commSMul D c :=
  LinearMap.ext fun m => commSMul_mul_apply D b c m

/-- Commutators with two elements of `S` commute with each other. -/
public lemma commSMul_comm [SMulCommClass S S M] [SMulCommClass S S N] (D : M →ₗ[R] N) (b c : S) :
    commSMul (commSMul D b) c = commSMul (commSMul D c) b := by
  ext m
  simp only [commSMul_apply, smul_sub]
  rw [smul_comm b c m, smul_comm b c (D m)]
  abel

/-- Order at most `0` is `S`-linearity, by definitional unfolding. -/
public lemma isDifferentialOperatorOfOrderLE_zero_iff {D : M →ₗ[R] N} :
    D.IsDifferentialOperatorOfOrderLE S 0 ↔ ∀ (g : S) (m : M), D (g • m) = g • D m := Iff.rfl

/-- Order at most `0` says that every commutator with a scalar vanishes. -/
@[ega "IV 16.8.8" "special case", sga "3 VIIA 1.1.1" "partial"]
public lemma isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero {D : M →ₗ[R] N} :
    D.IsDifferentialOperatorOfOrderLE S 0 ↔ ∀ g : S, commSMul D g = 0 :=
  forall_congr' fun _ => by simp [LinearMap.ext_iff, commSMul_apply, sub_eq_zero]

/-- Order at most `k + 1` says that every commutator with a scalar has order at most `k`. -/
public lemma isDifferentialOperatorOfOrderLE_succ_iff {k : ℕ} {D : M →ₗ[R] N} :
    D.IsDifferentialOperatorOfOrderLE S (k + 1) ↔
      ∀ g : S, (commSMul D g).IsDifferentialOperatorOfOrderLE S k := Iff.rfl

/-- The zero operator has order at most `k` for every `k`. -/
public lemma zero_isDifferentialOperatorOfOrderLE (k : ℕ) :
    (0 : M →ₗ[R] N).IsDifferentialOperatorOfOrderLE S k := by
  induction k with
  | zero => exact isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mpr commSMul_zero_left
  | succ k ih =>
    exact isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => by
      rw [commSMul_zero_left]; exact ih

/-- A sum of two operators of order at most `k` has order at most `k`. -/
public lemma isDifferentialOperatorOfOrderLE_add {k : ℕ} {D E : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (hE : E.IsDifferentialOperatorOfOrderLE S k) :
    (D + E).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D E with
  | zero =>
    refine isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mpr fun g => ?_
    rw [commSMul_add_left, isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD g,
      isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hE g, add_zero]
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => ?_
    rw [commSMul_add_left]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)
      (isDifferentialOperatorOfOrderLE_succ_iff.mp hE g)

/-- A difference of two operators of order at most `k` has order at most `k`. -/
public lemma isDifferentialOperatorOfOrderLE_sub {k : ℕ} {D E : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (hE : E.IsDifferentialOperatorOfOrderLE S k) :
    (D - E).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D E with
  | zero =>
    refine isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mpr fun g => ?_
    rw [commSMul_sub_left, isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD g,
      isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hE g, sub_zero]
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => ?_
    rw [commSMul_sub_left]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)
      (isDifferentialOperatorOfOrderLE_succ_iff.mp hE g)

/-- The negative of an operator of order at most `k` has order at most `k`. -/
public lemma isDifferentialOperatorOfOrderLE_neg {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    (-D).IsDifferentialOperatorOfOrderLE S k := by
  simpa using isDifferentialOperatorOfOrderLE_sub (zero_isDifferentialOperatorOfOrderLE k) hD

/-- An operator of order at most `k` has order at most `k + 1`. -/
public lemma isDifferentialOperatorOfOrderLE_succ {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    D.IsDifferentialOperatorOfOrderLE S (k + 1) := by
  induction k generalizing D with
  | zero =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => ?_
    rw [isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD g]
    exact zero_isDifferentialOperatorOfOrderLE 0
  | succ k ih =>
    exact isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g =>
      ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)

/-- The commutator of an operator of order at most `k` has order at most `k`. -/
public lemma isDifferentialOperatorOfOrderLE_commSMul {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (g : S) :
    (commSMul D g).IsDifferentialOperatorOfOrderLE S k := by
  cases k with
  | zero =>
    rw [isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD g]
    exact zero_isDifferentialOperatorOfOrderLE 0
  | succ k =>
    exact isDifferentialOperatorOfOrderLE_succ (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)

variable [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower R S N₂]

/-- Postcomposition with an `S`-linear map commutes with taking commutators. -/
public lemma commSMul_comp (L : N →ₗ[S] N₂) (D : M →ₗ[R] N) (g : S) :
    commSMul (L.restrictScalars R ∘ₗ D) g = L.restrictScalars R ∘ₗ commSMul D g := by
  ext m; simp [commSMul_apply]

/-- Postcomposition with an `S`-linear map preserves the order of a differential operator. -/
public lemma isDifferentialOperatorOfOrderLE_postcomp (L : N →ₗ[S] N₂) {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    (L.restrictScalars R ∘ₗ D).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero =>
    refine isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mpr fun g => ?_
    rw [commSMul_comp, isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero.mp hD g,
      comp_zero]
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => ?_
    rw [commSMul_comp]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)

end Comm

end LinearMap

end



/-!
## The module of principal parts

Let `R → S` be a ring map, let `M` be an `S`-module and let `k : ℕ`. Lemma 09CK produces an
`S`-module representing the functor `N ↦ Diffᵏ_{S/R}(M, N)` of differential operators of order at
most `k` out of `M` (Definition 09CI), and Definition 09CL names it the *module of principal parts
of order `k`* of `M`, written `Pᵏ_{S/R}(M)`. Via the Yoneda lemma, as the source records right
after Lemma 09CK, the representation is the datum of a *universal* differential operator
`D : M → Pᵏ_{S/R}(M)` of order at most `k`: one through which every differential operator
`M → N` of order at most `k` factors as `α ∘ D` for a unique `S`-linear `α`. The pair
`(Pᵏ_{S/R}(M), D)` is determined by that property up to unique isomorphism, and it is that
property which is defined here. Thus `D.IsUniversalDifferentialOperatorOfOrderLE S k`, for an
`R`-linear map `D : M → P` into an `S`-module `P`, says that `P` together with `D` *is* a module
of principal parts of order `k` of `M`.

Lemma 09CK says that such a `D` exists; Example 09CM computes that `Ω[S⁄R] × S` with
`b ↦ (d b, b)` is one for `M = S` and `k = 1`, and the sequence of principal parts (Lemma 09CN)
holds for every one of them.

### Main definitions

* `LinearMap.IsUniversalDifferentialOperatorOfOrderLE`: the property of an `R`-linear map
  `D : M → P` between `S`-modules of exhibiting `P` as the module of principal parts of order `k`
  of `M`, with `D` as its universal differential operator.

### Implementation notes

The source names an object, `Pᵏ_{S/R}(M)`, which it has just constructed by generators and
relations; what is defined here is instead the property of a pair `(P, D)` of being such an
object. The two carry the same mathematics, because a representing object is unique up to unique
isomorphism, and a statement made for an arbitrary `(P, D)` with this property applies to each
construction, including the source's quotient of `⨁_{m ∈ M} S[m]` and the base change `S ⊗[R] M`
modulo the submodule generated by the iterated commutators. This is the choice Mathlib makes for
base change (`IsBaseChange`) and localization of modules (`IsLocalizedModule`). Existence of a
pair with this property is Lemma 09CK, not a consequence of this definition.

Both clauses are content. The factorisation clause quantifies only over the operators of order at
most `k` and asks each to factor uniquely through `D`; it does not assert that the composites
`α ∘ D` are again of that order, which is what the first clause supplies — given it, they are, by
Lemma 09CJ at orders `k` and `0`. In the other direction the first clause alone holds for `D = 0`.

Following `IsBaseChange`, the test modules `N` are taken in the single universe `max v w x`
containing `S`, `M` and `P`, rather than the definition carrying a universe parameter of its own;
that universe contains the quotients of `P`, the module `Ω[S⁄R] ⊗[S] M` and the free `S`-modules
on `M`. A pair with the property for test modules in one universe has it in every universe, since
the property forces `P` to be generated over `S` by the image of `D`.

Lemma 09CK is phrased there as injectivity of `α ↦ α ∘ D` together with the computation of its
range; the unique-factorisation form used here is the same statement rearranged, a map being
injective with range `s` exactly when each element of `s` has a unique preimage. The
factorisation is written pointwise, `∀ m, α (D m) = E m`, as `IsBaseChange` writes its own.

The hypotheses are the weakest the definition needs, and are those of Definition 09CI: `S` is only
an `R`-algebra, not assumed commutative, and `M` only an additive monoid, while `P` and the test
modules are groups because the commutators defining the order subtract values. Commutativity of
`S` and the ring structure that Lemma 09CK needs for its construction are hypotheses of that
lemma, not of this definition. The `R`-module structures on `M`, `P` and `N` are pinned to the
restrictions along `R → S` by `IsScalarTower`, as in Definition 09CI.

For every `R → S` and every `S`-module `M` the pair `(M, id)` has the property at `k = 0`, the
operators of order at most `0` being exactly the `S`-linear maps, whereas at `k = 1` it does not,
already for `R = ℤ` and `M = S = ℤ[X]`, since `d/dX` has order at most `1` and is not `S`-linear.

### References

* [Stacks 09CL](https://stacks.math.columbia.edu/tag/09CL), Definition 10.133.4, in the section
  "Finite order differential operators" (Tag 09CH). Definition 09CI is
  `LinearMap.IsDifferentialOperatorOfOrderLE` and Lemma 09CK is
  `LinearMap.exists_universal_isDifferentialOperatorOfOrderLE`.
-/

@[expose] public section

universe u v w x

namespace LinearMap

variable {R : Type u} {M : Type w} {P : Type x} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- Let `R → S` be a ring map, let `M` be an `S`-module and let `k : ℕ`. For an
`R`-linear map `D : M → P` into an `S`-module `P`, the property
`D.IsUniversalDifferentialOperatorOfOrderLE S k` says that `D` is a differential operator of order
at most `k` relative to `R → S` and that every differential operator `E : M → N` of order at most
`k` into an `S`-module factors as `E = α ∘ D` for a unique `S`-linear map `α : P → N`. Equivalently
`α ↦ α ∘ D` is the canonical isomorphism `Hom_S(P, N) = Diffᵏ_{S/R}(M, N)` of Lemma 09CK: that is,
`P` is a *module of principal parts of order `k`* of `M`, written `Pᵏ_{S/R}(M)`, and `D` is its
universal differential operator. Such a pair is unique up to unique isomorphism. -/
@[stacks 09CL "The source names the module `Pᵏ_{S/R}(M)` it has just constructed; defined here is
the property of a pair `(P, D)` of being one, which determines it up to unique isomorphism and so
applies to every construction. Existence of such a pair is Lemma 09CK. See the module docstring.",
  sga "6 II AppII.1.2.2" "affine case"]
public def IsUniversalDifferentialOperatorOfOrderLE (S : Type v) [Semiring S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] [Module S P] [IsScalarTower R S P] (k : ℕ)
    (D : M →ₗ[R] P) : Prop :=
  D.IsDifferentialOperatorOfOrderLE S k ∧
    ∀ ⦃N : Type (max v w x)⦄ [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
      (E : M →ₗ[R] N), E.IsDifferentialOperatorOfOrderLE S k →
        ∃! α : P →ₗ[S] N, ∀ m : M, α (D m) = E m

end LinearMap

end

end

/-!
## Composition of differential operators

Let `R → S` be a ring map and let `M, N` be `S`-modules, regarded as `R`-modules by
restriction of scalars along `R → S`. For `k : ℕ` one defines by induction on `k` what it
means for an `R`-linear map `D : M → N` to be a *differential operator of order `k`*:

* for `k = 0`, that `D` is `S`-linear;
* for `k ≥ 1`, that for every `g ∈ S` the bracket `[D, g] : m ↦ D (g • m) - g • D m` is a
  differential operator of order `k - 1`.

The main result is that composition adds orders: if `D : L → M` has order `k` and
`D' : M → N` has order `k'`, then `D' ∘ D : L → N` has order `k + k'`.

The ring map `R → S` is modelled as a commutative `R`-algebra `S`. The `S`-modules `M, N`
are simultaneously `R`-modules via restriction of scalars, expressed by `Module R _`
together with `IsScalarTower R S _`, i.e. `r • x = algebraMap R S r • x`.
-/

@[expose] public section

variable {R S M N : Type*}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The bracket `[D, g]` of an `R`-linear map `D : M → N` with an element `g ∈ S`,
i.e. the `R`-linear map `m ↦ D (g • m) - g • D m`. -/
@[ega "IV 16.8.8"]
noncomputable def diffBracket (g : S) (D : M →ₗ[R] N) : M →ₗ[R] N :=
  D ∘ₗ DistribSMul.toLinearMap R M g - DistribSMul.toLinearMap R N g ∘ₗ D

/-- The bracket `[D, g]` evaluated at `m` is `D (g • m) - g • D m`. -/
@[simp]
theorem diffBracket_apply (g : S) (D : M →ₗ[R] N) (m : M) :
    diffBracket g D m = D (g • m) - g • D m :=
  rfl

/-- `IsDiffOpOfOrder S k D` says that the `R`-linear map `D : M → N` is a differential
operator of order `k` with respect to `R → S`.  Defined by induction on `k`:
order `0` means `S`-linearity, and order `k+1` means that `[D, g]` has order `k` for
every `g ∈ S`. -/
@[ega "IV 16.8.1" "affine module case",
  sga "3 VIIA 1.1.1" "partial",
  sga "3 VIIA 1.4" "special case"]
def IsDiffOpOfOrder (S : Type*) [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N] :
    ℕ → (M →ₗ[R] N) → Prop
  | 0, D => ∀ (g : S) (m : M), D (g • m) = g • D m
  | (k + 1), D => ∀ g : S, IsDiffOpOfOrder S k (diffBracket g D)

/-- The composition of a differential operator of order `k` with one of order `k'` is a
differential operator of order `k + k'`. -/
@[stacks 09CJ,
  ega "IV 16.8.9" "affine case",
  sga "3 VIIA 1.2" "affine, deviations of id",
  sga "3 VIIA 1.4" "partial"]
theorem isDiffOpOfOrder_comp
    {L : Type*} [AddCommGroup L] [Module S L] [Module R L] [IsScalarTower R S L]
    (k k' : ℕ) (D : L →ₗ[R] M) (D' : M →ₗ[R] N)
    (hD : IsDiffOpOfOrder S k D) (hD' : IsDiffOpOfOrder S k' D') :
    IsDiffOpOfOrder S (k + k') (D'.comp D) := by
  have diffBracket_add :
      ∀ (g : S) (D₁ D₂ : L →ₗ[R] N),
        diffBracket g (D₁ + D₂) = diffBracket g D₁ + diffBracket g D₂ := by
    intro g D₁ D₂
    ext m
    simp only [LinearMap.add_apply, diffBracket_apply, smul_add]
    abel
  have diffBracket_comp :
      ∀ (g : S) (E : L →ₗ[R] M) (E' : M →ₗ[R] N),
        diffBracket g (E'.comp E)
          = (diffBracket g E').comp E + E'.comp (diffBracket g E) := by
    intro g E E'
    ext m
    simp only [LinearMap.add_apply, LinearMap.comp_apply, diffBracket_apply, map_sub]
    abel
  have zero_op : ∀ (j : ℕ), IsDiffOpOfOrder S j (0 : L →ₗ[R] N) := by
    intro j
    induction j with
    | zero =>
      intro g m
      simp
    | succ j ih =>
      intro g
      have hz : diffBracket g (0 : L →ₗ[R] N) = 0 := by
        ext m
        simp
      rw [hz]
      exact ih
  have add_op :
      ∀ (j : ℕ) (D₁ D₂ : L →ₗ[R] N),
        IsDiffOpOfOrder S j D₁ → IsDiffOpOfOrder S j D₂ →
        IsDiffOpOfOrder S j (D₁ + D₂) := by
    intro j
    induction j with
    | zero =>
      intro D₁ D₂ hD₁ hD₂ g m
      show (D₁ + D₂) (g • m) = g • (D₁ + D₂) m
      simp only [LinearMap.add_apply]
      rw [hD₁ g m, hD₂ g m, smul_add]
    | succ j ih =>
      intro D₁ D₂ hD₁ hD₂ g
      rw [diffBracket_add]
      exact ih _ _ (hD₁ g) (hD₂ g)
  match k, hD with
  | 0, hD =>
    match k', hD' with
    | 0, hD' =>
      intro g m
      show D' (D (g • m)) = g • D' (D m)
      rw [hD g m, hD' g (D m)]
    | (n + 1), hD' =>
      show IsDiffOpOfOrder S ((0 + n) + 1) (D'.comp D)
      intro g
      rw [diffBracket_comp]
      have hzero : diffBracket g D = 0 := LinearMap.ext fun m => sub_eq_zero.2 (hD g m)
      rw [hzero, LinearMap.comp_zero, add_zero]
      exact isDiffOpOfOrder_comp 0 n D (diffBracket g D') hD (hD' g)
  | (n + 1), hD =>
    rw [Nat.succ_add]
    intro g
    rw [diffBracket_comp]
    apply add_op
    · match k', hD' with
      | 0, hD' =>
        have hzero : diffBracket g D' = 0 := LinearMap.ext fun m => sub_eq_zero.2 (hD' g m)
        rw [hzero, LinearMap.zero_comp]
        exact zero_op (n + 0)
      | (m + 1), hD' =>
        have heq : n + (m + 1) = (n + 1) + m := by omega
        rw [heq]
        exact isDiffOpOfOrder_comp (n + 1) m D (diffBracket g D') hD (hD' g)
    · exact isDiffOpOfOrder_comp n k' (diffBracket g D) D' (hD g) hD'
termination_by k + k'
decreasing_by
  all_goals (simp_wf; try omega)

end

/-!
## Checking the order of a differential operator on algebra generators

Fix a ring map `A → B` (a homomorphism of commutative rings), and let `M, N` be
`B`-modules. All maps between modules are additive maps unless stated otherwise.

For a ring element `g ∈ B` and a `B`-module `L`, write `g : L → L` for the
multiplication-by-`g` endomorphism `m ↦ g • m`. For an additive map `D : M → N`
between `B`-modules and `g ∈ B`, the "commutator" is the additive map
`m ↦ D (g • m) - g • D m`.

### Differential operators of order `≤ k`
By induction on `k`:
- Base `k = 0`: `D` is a differential operator of order `≤ 0` iff `D` is `B`-linear.
- Step `k ≥ 1`: `D` is a differential operator of order `≤ k` iff `D` is `A`-linear
  and, for every `g ∈ B`, the commutator `m ↦ D (g • m) - g • D m` is a
  differential operator of order `≤ k - 1`.

### Generators of `B` as an `A`-algebra
A family `(g i)` generates `B` as an `A`-algebra if the smallest subring of `B`
containing the image of `A → B` and every `g i` is all of `B`. In Mathlib terms,
`Algebra.adjoin A (Set.range g) = ⊤`.

### Main results

Let `A → B` be a ring map, `(g i)` generate `B` as an `A`-algebra, `M, N` be
`B`-modules, and `D : M → N` an `A`-linear map. Fix `k ≥ 1`. If for every `i` the
commutator `m ↦ D (g i • m) - g i • D m` is a differential operator of order
`≤ k - 1`, then `D` is a differential operator of order `≤ k`.
-/

@[expose] public section
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The "commutator" additive map `m ↦ D (g • m) - g • D m`, for an additive map
`D : M →+ N` between `B`-modules and a ring element `g ∈ B`. -/
@[ega "IV 16.8.8"]
def diffOpComm {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (g : B) (D : M →+ N) : M →+ N where
  toFun m := D (g • m) - g • D m
  map_zero' := by simp
  map_add' x y := by
    simp only [smul_add, map_add]
    abel

/-- A predicate expressing that an additive map `D : M →+ N` is `A`-linear, i.e.
commutes with the `A`-action. The `A`-action on a `B`-module is given through the
algebra map `A → B`. -/
def IsALinear (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (D : M →+ N) : Prop :=
  ∀ (a : A) (m : M), D ((algebraMap A B a) • m) = (algebraMap A B a) • D m

/-- A predicate expressing that an additive map `D : M →+ N` is `B`-linear, i.e.
commutes with the `B`-action. -/
def IsBLinear (B : Type*) [CommRing B]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (D : M →+ N) : Prop :=
  ∀ (b : B) (m : M), D (b • m) = b • D m


/-- Precomposition of an additive map with multiplication by `b`. -/
def precompSmul {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M]
    (b : B) (E : M →+ N) : M →+ N where
  toFun m := E (b • m)
  map_zero' := by simp
  map_add' x y := by simp [smul_add]

/-- `precompSmul b E` sends `m` to `E (b • m)`. -/
@[simp] lemma precompSmul_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] (b : B) (E : M →+ N) (m : M) :
    precompSmul b E m = E (b • m) := rfl

/-! ### Commutator identities -/

/-- The commutator `diffOpComm g D` sends `m` to `D (g • m) - g • D m`. -/
@[simp] lemma diffOpComm_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g : B) (D : M →+ N) (m : M) :
    diffOpComm g D m = D (g • m) - g • D m := rfl

/-- The commutator of the zero map is zero. -/
@[simp] lemma diffOpComm_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g : B) :
    diffOpComm g (0 : M →+ N) = 0 := by
  ext m; simp

/-- The commutator is additive in the operator. -/
@[simp] lemma diffOpComm_add {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g : B) (E F : M →+ N) :
    diffOpComm g (E + F) = diffOpComm g E + diffOpComm g F := by
  ext m
  simp only [diffOpComm_apply, AddMonoidHom.add_apply, smul_add]
  abel

/-- The commutator commutes with precomposition by multiplication. -/
lemma diffOpComm_precompSmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g b : B) (E : M →+ N) :
    diffOpComm g (precompSmul b E) = precompSmul b (diffOpComm g E) := by
  ext m
  simp only [diffOpComm_apply, precompSmul_apply]
  rw [smul_comm b g m]

/-- The commutator commutes with postcomposition by multiplication. -/
lemma diffOpComm_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g b : B) (E : M →+ N) :
    diffOpComm g (b • E) = b • diffOpComm g E := by
  ext m
  simp only [diffOpComm_apply, AddMonoidHom.smul_apply, smul_sub, smul_comm b g]

/-! ### Closure properties of `IsBLinear` -/

/-- The zero map is `B`-linear. -/
lemma isBLinear_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] : IsBLinear B (0 : M →+ N) := by
  intro b m; simp

/-- A sum of `B`-linear maps is `B`-linear. -/
lemma isBLinear_add {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] {E F : M →+ N}
    (hE : IsBLinear B E) (hF : IsBLinear B F) : IsBLinear B (E + F) := by
  intro b m
  simp only [AddMonoidHom.add_apply]
  rw [hE, hF, smul_add]

/-- Precomposing a `B`-linear map with multiplication by `c` keeps it `B`-linear. -/
lemma isBLinear_precompSmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (c : B) {E : M →+ N}
    (hE : IsBLinear B E) : IsBLinear B (precompSmul c E) := by
  intro b m
  simp only [precompSmul_apply]
  rw [smul_comm c b m, hE]

/-- Postcomposing a `B`-linear map with multiplication by `c` keeps it `B`-linear. -/
lemma isBLinear_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (c : B) {E : M →+ N}
    (hE : IsBLinear B E) : IsBLinear B (c • E) := by
  intro b m
  simp only [AddMonoidHom.smul_apply]
  rw [hE, smul_comm c b]

/-! ### Closure properties of `IsALinear` -/

/-- The zero map is `A`-linear. -/
lemma isALinear_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] : IsALinear A B (0 : M →+ N) := by
  intro a m; simp

/-- A sum of `A`-linear maps is `A`-linear. -/
lemma isALinear_add {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] {E F : M →+ N}
    (hE : IsALinear A B E) (hF : IsALinear A B F) : IsALinear A B (E + F) := by
  intro a m
  simp only [AddMonoidHom.add_apply]
  rw [hE, hF, smul_add]

/-- Precomposing an `A`-linear map with multiplication by `c` keeps it `A`-linear. -/
lemma isALinear_precompSmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (c : B) {E : M →+ N}
    (hE : IsALinear A B E) : IsALinear A B (precompSmul c E) := by
  intro a m
  simp only [precompSmul_apply]
  rw [smul_comm c (algebraMap A B a) m, hE]

/-- Postcomposing an `A`-linear map with multiplication by `c` keeps it `A`-linear. -/
lemma isALinear_smul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (c : B) {E : M →+ N}
    (hE : IsALinear A B E) : IsALinear A B (c • E) := by
  intro a m
  simp only [AddMonoidHom.smul_apply]
  rw [hE, smul_comm c (algebraMap A B a)]

/-! ### Linearity of the commutator in the ring element -/

/-- The commutator is additive in the ring element. -/
lemma diffOpComm_add_left {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g g' : B) (D : M →+ N) :
    diffOpComm (g + g') D = diffOpComm g D + diffOpComm g' D := by
  ext m
  simp only [diffOpComm_apply, AddMonoidHom.add_apply, add_smul, map_add]
  abel

/-- The Leibniz rule: the commutator of a product is the sum of the two
"partial" commutators, precomposed and postcomposed with multiplication by `g'` and `g`. -/
lemma diffOpComm_mul_left {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (g g' : B) (D : M →+ N) :
    diffOpComm (g * g') D
      = precompSmul g' (diffOpComm g D) + g • diffOpComm g' D := by
  ext m
  simp only [diffOpComm_apply, AddMonoidHom.add_apply, precompSmul_apply,
    AddMonoidHom.smul_apply, smul_sub, mul_smul, mul_comm g g']
  rw [smul_comm g' g (D m), smul_comm g' g m]
  abel

/-- For an `A`-linear `D`, the commutator with the image of a scalar `r : A`
vanishes. -/
lemma diffOpComm_algebraMap {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module B M] [Module B N] (r : A) {D : M →+ N} (hD : IsALinear A B D) :
    diffOpComm (algebraMap A B r) D = 0 := by
  ext m
  simp only [diffOpComm_apply, AddMonoidHom.zero_apply, hD r m, sub_self]

/-- `IsDiffOpLE A k D` holds when `D : M →+ N` is a differential
operator of order `≤ k` relative to `A → B`, defined by induction on `k`.

* Base case (`k = 0`): `D` is `B`-linear.
* Inductive step (`k+1`): `D` is `A`-linear and for every `g ∈ B`, the commutator
  `diffOpComm g D` is a differential operator of order `≤ k`. -/
@[ega "IV 16.8.1" "affine module case",
  sga "3 VIIA 1.1.1" "partial",
  sga "3 VIIA 1.4" "special case"]
def IsDiffOpLE (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N] :
    ℕ → (M →+ N) → Prop
  | 0, D => IsBLinear B D
  | (k + 1), D => IsALinear A B D ∧ ∀ g : B, IsDiffOpLE A B k (diffOpComm g D)

/-- Let `A → B` be a ring map, let `(g i)`
generate `B` as an `A`-algebra, let `M, N` be `B`-modules and `D : M →+ N` an
`A`-linear map. Fix `k ≥ 1` (written `k + 1` here). If for every `i` the commutator
`diffOpComm (g i) D` is a differential operator of order `≤ k`, then `D` is a
differential operator of order `≤ k + 1`. -/
@[stacks 0G35]
theorem isDiffOpLE_succ_of_comm_isDiffOpLE_on_generators
    {ι : Type*} (g : ι → B)
    (hgen : Algebra.adjoin A (Set.range g) = ⊤)
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (D : M →+ N) (hD : IsALinear A B D) (k : ℕ)
    (hcomm : ∀ i : ι, IsDiffOpLE A B k (diffOpComm (g i) D)) :
    IsDiffOpLE A B (k + 1) D := by
  have diffOp_zero : ∀ j : ℕ, IsDiffOpLE A B j (0 : M →+ N) := by
    intro j
    induction j with
    | zero => exact isBLinear_zero
    | succ n ih => exact ⟨isALinear_zero, fun g => by rw [diffOpComm_zero]; exact ih⟩
  have diffOp_add : ∀ (j : ℕ) (E F : M →+ N),
      IsDiffOpLE A B j E → IsDiffOpLE A B j F → IsDiffOpLE A B j (E + F) := by
    intro j
    induction j with
    | zero => exact fun E F hE hF => isBLinear_add hE hF
    | succ n ih =>
      refine fun E F hE hF => ⟨isALinear_add hE.1 hF.1, fun g => ?_⟩
      rw [diffOpComm_add]
      exact ih _ _ (hE.2 g) (hF.2 g)
  have diffOp_map : ∀ T : B → (M →+ N) → (M →+ N),
      (∀ (c : B) (E : M →+ N), IsBLinear B E → IsBLinear B (T c E)) →
      (∀ (c : B) (E : M →+ N), IsALinear A B E → IsALinear A B (T c E)) →
      (∀ (g c : B) (E : M →+ N), diffOpComm g (T c E) = T c (diffOpComm g E)) →
      ∀ (j : ℕ) (c : B) (E : M →+ N), IsDiffOpLE A B j E → IsDiffOpLE A B j (T c E) := by
    intro T hB hA hT j
    induction j with
    | zero => exact hB
    | succ n ih =>
      refine fun c E hE => ⟨hA c E hE.1, fun g => ?_⟩
      rw [hT]
      exact ih c _ (hE.2 g)
  refine ⟨hD, fun b => ?_⟩
  have hb : b ∈ Algebra.adjoin A (Set.range g) := by rw [hgen]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hcomm i
  | algebraMap r =>
    rw [diffOpComm_algebraMap r hD]
    exact diffOp_zero k
  | add x y _ _ ihx ihy =>
    rw [diffOpComm_add_left]
    exact diffOp_add k _ _ ihx ihy
  | mul x y _ _ ihx ihy =>
    rw [diffOpComm_mul_left]
    exact diffOp_add k _ _
      (diffOp_map _ isBLinear_precompSmul isALinear_precompSmul diffOpComm_precompSmul k y _ ihx)
      (diffOp_map (fun c E => c • E) isBLinear_smul isALinear_smul diffOpComm_smul k x _ ihy)

end
