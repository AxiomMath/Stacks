module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseTensorComparison

/-!
# The Veronese part of a tensor product is not the tensor product of the Veronese parts

The proof of [Stacks, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J) asserts, of a graded
ring `S`, an integer `d ≥ 1` and graded `S`-modules `M` and `N` with `M' = M^{(d)}` and
`N' = N^{(d)}` the Veronese parts over `S' = S^{(d)}`, that

`M' ⊗_{S'} N' = (M ⊗_S N)^{(d)} = (M ⊗_S N)'`

"as can be verified directly from the definitions", and then draws the compatibility diagram of
its trailing clause with `i^*((M' ⊗_{S'} N')~)` in the bottom right corner. **That identity is
false.** This file is the counterexample.

Take `S = k[x, y]`, `d = 2`, `M = N = S(1)`. In degree zero the canonical map
`M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` is the multiplication

`S₁ ⊗_k S₁ ⟶ S₂`

of the homogeneous components of degree one into the component of degree two — on the left
`M'₀ ⊗_{S'₀} N'₀ = S₁ ⊗_k S₁`, which is `4`-dimensional, on the right
`((M ⊗_S N)')₀ = S(2)₀ = S₂`, which is `3`-dimensional. `multiplicationDegreeOne` below is that
map, and `not_injective_multiplicationDegreeOne` is the refutation: `x ⊗ y - y ⊗ x` is a nonzero
element of the kernel, nonzero because the functional `coeffDegreeOne` separating `x` from `y`
in each factor takes the value `1` on it, and in the kernel because multiplication in `S` is
commutative.

The same computation is carried out on the comparison map itself, not only on that model of
its degree-zero part. `not_injective_veroneseTensorMap` proves that
`Stacks.Veronese.veroneseTensorMap`, the map `c : M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` along the lower
edge of the compatibility square of `Stacks.Veronese.tag0B5J`, is not injective at
`S = k[x, y]` (the grading `MvPolynomial.homogeneousSubmodule`), `d = 2` and `M = N = S(1)`
(the grading `Stacks.Veronese.twistGradingAddSubgroup _ 1`). The element is again
`x ⊗ y - y ⊗ x`, now in `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`, where `x` and `y` lie in degree zero of
`S(1)⁽²⁾`. Its image `x ⊗ y - y ⊗ x` in `S(1) ⊗_S S(1)` is zero, because there
`x ⊗ y = 1 ⊗ xy = y ⊗ x`. It is not zero itself: the functional sending `m ⊗ n` to the
coefficient of `x` in `m` times the coefficient of `y` in `n` is `S⁽²⁾`-balanced for the action
of `S⁽²⁾` on `k` through the constant coefficient, because an element of `S⁽²⁾` has no terms
of degree one, and it takes the value `1` on that element.

**What this does and does not refute.** It refutes the *displayed identity*, hence the source's
proof of the trailing clause as written. It does **not** refute the clause itself: the clause is
true and is proved in this library (`Stacks.Veronese.veroneseTensorCompatibility`), with the
source's equality replaced by the canonical multiplication `c : M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` along
the lower edge of the square. The square commutes because over every standard open
`D₊(f) = i⁻¹ D₊(f ᵈ)` both of its composites send `m / f^(pd) ⊗ n / f^(qd)` to
`c(m ⊗ n) / (f ᵈ)^(p+q)`. Nothing here says that `c` becomes an isomorphism after passing to
associated sheaves, and in general it does not: for `S = k[f, z]` with `deg f = 2`, `deg z = 1`,
`d = 2` and `M = N = S(1)`, the map `c` is multiplication by `z²` from `S'` to `S'(1)`, so the
induced map of sheaves on `Proj S' = ℙ¹` is the section `z²` of `𝒪(1)`, which is not surjective
on `D₊(f)`. The whole of Tag 0B5J is `Stacks.Veronese.tag0B5J` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjVeroneseStatement.lean`, which holds the
library's `0B5J` attribute; this file is the erratum and carries none.

## Main definitions

* `Stacks.Veronese.coeffDegreeOne`: the `k`-linear functional on `S₁` reading off the
  coefficient of the variable `i`.
* `Stacks.Veronese.multiplicationDegreeOne`: the multiplication `S₁ ⊗_k S₁ ⟶ S₂`, the
  degree-zero component of the canonical map `M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` at the data above.
* `Stacks.Veronese.separatingFunctional`: the functional `S₁ ⊗_k S₁ ⟶ k` sending `a ⊗ b` to the
  coefficient of `x` in `a` times the coefficient of `y` in `b`, which detects
  `x ⊗ y - y ⊗ x ≠ 0`.
* `Stacks.Veronese.veroneseSeparatingFunctional`: its counterpart on
  `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`, an `S⁽²⁾`-linear functional to `k` with `S⁽²⁾` acting through the
  constant coefficient (`Stacks.Veronese.veroneseConstantAlgebra`).

## Main results

* `Stacks.Veronese.multiplicationDegreeOne_antisymmetrizer`: the antisymmetrizer
  `x ⊗ y - y ⊗ x` is in the kernel of the multiplication.
* `Stacks.Veronese.antisymmetrizer_ne_zero`: it is not zero.
* `Stacks.Veronese.not_injective_multiplicationDegreeOne`: **the counterexample**, on the
  multiplication `S₁ ⊗_k S₁ ⟶ S₂`.
* `Stacks.Veronese.veroneseAntisymmetrizer_mem_tensorGrading_zero`,
  `Stacks.Veronese.veroneseAntisymmetrizer_ne_zero` and
  `Stacks.Veronese.veroneseTensorMap_veroneseAntisymmetrizer`: `x ⊗ y - y ⊗ x` is a nonzero
  element of degree zero of `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾` which the comparison sends to zero.
* `Stacks.Veronese.not_injective_veroneseTensorMap`: **the counterexample on the comparison map
  `Stacks.Veronese.veroneseTensorMap` itself**, for any decomposition of the tensor grading, and
  `Stacks.Veronese.not_injective_veroneseTensorMap_tensorGrading` at the library's
  decomposition `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition`.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace Stacks.Veronese

universe u

variable (k : Type u) [CommRing k]

/-- The degree-one homogeneous component of `k[x, y]`. -/
public abbrev degOne : Submodule k (MvPolynomial (Fin 2) k) :=
  homogeneousSubmodule (Fin 2) k 1

/-- The degree-two homogeneous component of `k[x, y]`. -/
public abbrev degTwo : Submodule k (MvPolynomial (Fin 2) k) :=
  homogeneousSubmodule (Fin 2) k 2

/-- The product of two degree-one homogeneous polynomials is homogeneous of degree two. -/
public theorem mul_mem_degTwo (a b : degOne k) : (a : MvPolynomial (Fin 2) k) * b ∈ degTwo k :=
  homogeneousSubmodule_mul (σ := Fin 2) (R := k) 1 1 (Submodule.mul_mem_mul a.2 b.2)

/-- **The multiplication `S₁ ⊗_k S₁ ⟶ S₂`** for `S = k[x, y]`: the degree-zero component of the
canonical map `M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` of [Stacks, Tag 0B5J]'s proof at `d = 2` and
`M = N = S(1)`. -/
public def multiplicationDegreeOne : degOne k ⊗[k] degOne k →ₗ[k] degTwo k :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => ⟨(a : MvPolynomial (Fin 2) k) * b, mul_mem_degTwo k a b⟩
          map_add' := fun b c => Subtype.ext (by simpa using mul_add _ _ _)
          map_smul' := fun r b => Subtype.ext (by simp) }
      map_add' := fun a b => LinearMap.ext fun c => Subtype.ext (by simpa using add_mul _ _ _)
      map_smul' := fun r a => LinearMap.ext fun c => Subtype.ext
        (by simp) }

/-- The multiplication `S₁ ⊗_k S₁ ⟶ S₂` sends `a ⊗ b` to the product `a * b`. -/
@[simp] public theorem multiplicationDegreeOne_tmul (a b : degOne k) :
    (multiplicationDegreeOne k (a ⊗ₜ[k] b) : MvPolynomial (Fin 2) k) =
      (a : MvPolynomial (Fin 2) k) * b :=
  rfl

/-- The `k`-linear functional on `S₁` reading off the coefficient of the variable `i`. -/
public def coeffDegreeOne (i : Fin 2) : degOne k →ₗ[k] k :=
  (MvPolynomial.lcoeff k (Finsupp.single i 1)).comp (degOne k).subtype

/-- `coeffDegreeOne k i a` is the coefficient of the variable `i` in `a`. -/
@[simp] public theorem coeffDegreeOne_apply (i : Fin 2) (a : degOne k) :
    coeffDegreeOne k i a = (a : MvPolynomial (Fin 2) k).coeff (Finsupp.single i 1) :=
  rfl

/-- The functional on `S₁ ⊗_k S₁` sending `a ⊗ b` to the coefficient of `x` in `a` times the
coefficient of `y` in `b`. It takes the value `1` on `x ⊗ y` and `0` on `y ⊗ x`, so it separates
the antisymmetrizer from zero. -/
public def separatingFunctional : degOne k ⊗[k] degOne k →ₗ[k] k :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun a b => coeffDegreeOne k 0 a * coeffDegreeOne k 1 b)
    (fun a b c => by rw [map_add, add_mul])
    (fun r a b => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun a b c => by rw [map_add, mul_add])
    (fun r a b => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm])

/-- `separatingFunctional` sends `a ⊗ b` to the coefficient of `x` in `a` times the coefficient
of `y` in `b`. -/
@[simp] public theorem separatingFunctional_tmul (a b : degOne k) :
    separatingFunctional k (a ⊗ₜ[k] b) = coeffDegreeOne k 0 a * coeffDegreeOne k 1 b :=
  rfl

/-- The variable `x` as an element of `S₁`. -/
public def xDegOne : degOne k := ⟨X 0, isHomogeneous_X k 0⟩

/-- The variable `y` as an element of `S₁`. -/
public def yDegOne : degOne k := ⟨X 1, isHomogeneous_X k 1⟩

/-- The antisymmetrizer `x ⊗ y - y ⊗ x` of `S₁ ⊗_k S₁`. -/
public def antisymmetrizer : degOne k ⊗[k] degOne k :=
  xDegOne k ⊗ₜ[k] yDegOne k - yDegOne k ⊗ₜ[k] xDegOne k

/-- **The antisymmetrizer is in the kernel of the multiplication**, because multiplication in
`k[x, y]` is commutative. -/
public theorem multiplicationDegreeOne_antisymmetrizer :
    multiplicationDegreeOne k (antisymmetrizer k) = 0 := by
  refine Subtype.ext ?_
  rw [antisymmetrizer, map_sub]
  change (multiplicationDegreeOne k (xDegOne k ⊗ₜ[k] yDegOne k) : MvPolynomial (Fin 2) k) -
    (multiplicationDegreeOne k (yDegOne k ⊗ₜ[k] xDegOne k) : MvPolynomial (Fin 2) k) = 0
  rw [multiplicationDegreeOne_tmul, multiplicationDegreeOne_tmul]
  change (X 0 : MvPolynomial (Fin 2) k) * X 1 - (X 1 : MvPolynomial (Fin 2) k) * X 0 = 0
  rw [mul_comm, sub_self]

/-- The two degree-one monomial exponents are different. -/
public theorem single_zero_ne_single_one :
    (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have h0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 =
      (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 := by rw [h]
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide)] at h0
  exact one_ne_zero h0

/-- **The antisymmetrizer is not zero**: `separatingFunctional` takes the value `1` on it. -/
public theorem antisymmetrizer_ne_zero [Nontrivial k] : antisymmetrizer k ≠ 0 := by
  intro h
  have hne := single_zero_ne_single_one
  have h1 : separatingFunctional k (antisymmetrizer k) = (1 : k) := by
    simp [antisymmetrizer, xDegOne, yDegOne, coeff_X, hne, hne.symm]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **Stacks Project, Tag 0B5J: a counterexample to the identity its proof asserts.**

The proof of Tag 0B5J asserts `M' ⊗_{S'} N' = (M ⊗_S N)^{(d)}` for the Veronese parts over
`S' = S^{(d)}`. For `S = k[x, y]`, `d = 2` and `M = N = S(1)` the canonical map between those two
graded modules is, in degree zero, the multiplication `S₁ ⊗_k S₁ ⟶ S₂`, and it is **not
injective**: `x ⊗ y - y ⊗ x` is a nonzero element of its kernel. So the two graded modules are not
canonically identified, the displayed equality is false, and the tag's trailing clause cannot be
stated the way its proof states it.

The clause itself is not refuted, and is proved in this library
(`Stacks.Veronese.veroneseTensorCompatibility`) with the canonical multiplication in place of
the asserted equality: the failure is killed by the degree-zero localization at a
positive-degree homogeneous element, and hence by sheafification. See the module docstring. -/
public theorem not_injective_multiplicationDegreeOne [Nontrivial k] :
    ¬ Function.Injective (multiplicationDegreeOne k) := fun h =>
  antisymmetrizer_ne_zero k
    (h ((multiplicationDegreeOne_antisymmetrizer k).trans (map_zero _).symm))

/-! ### The comparison `veroneseTensorMap` itself is not injective -/

section VeroneseTensorMap

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.GradedModule (tensorGrading)

/-- The standard grading of `S = k[x, y]` by total degree. -/
public abbrev polyGrading : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  homogeneousSubmodule (Fin 2) k

/-- The grading of the twist `S(1)` of `S = k[x, y]`: its degree-`i` piece is `S_{i+1}`. -/
public abbrev twistOneGrading : ℤ → AddSubgroup (MvPolynomial (Fin 2) k) :=
  twistGradingAddSubgroup (polyGrading k) 1

/-- The coefficient of a degree-one monomial in a product. -/
public theorem coeff_single_one_mul (i : Fin 2) (p q : MvPolynomial (Fin 2) k) :
    (p * q).coeff (Finsupp.single i 1) =
      p.coeff 0 * q.coeff (Finsupp.single i 1) + p.coeff (Finsupp.single i 1) * q.coeff 0 := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]
  simp

/-- An element of the Veronese subring `S⁽²⁾` has no degree-one terms. -/
public theorem coeff_single_one_eq_zero_of_mem_veroneseSubring (i : Fin 2)
    {s : MvPolynomial (Fin 2) k} (hs : s ∈ veroneseSubring (polyGrading k) 2) :
    s.coeff (Finsupp.single i 1) = 0 := by
  rw [mem_veroneseSubring_iff] at hs
  induction hs using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    refine IsHomogeneous.coeff_eq_zero hn ?_
    rw [Finsupp.degree_single]
    omega
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => rw [coeff_neg, hx, neg_zero]

/-- The variables of `k[x, y]` lie in degree zero of `S(1)`. -/
public theorem X_mem_twistOneGrading_zero (i : Fin 2) :
    (X i : MvPolynomial (Fin 2) k) ∈ twistOneGrading k (0 * ((2 : ℕ) : ℤ)) := by
  simp only [twistOneGrading, twistGradingAddSubgroup,
    Submodule.mem_toAddSubgroup, AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading_apply]
  rw [show (0 : ℤ) * ((2 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by norm_num,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast]
  exact isHomogeneous_X k i

/-- The variables of `k[x, y]` lie in the Veronese part `S(1)⁽²⁾`. -/
public theorem X_mem_veroneseSubmodule_twistOne (i : Fin 2) :
    (X i : MvPolynomial (Fin 2) k) ∈ veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨0, X_mem_twistOneGrading_zero k i⟩)

/-- `k` as an algebra over the Veronese subring `S⁽²⁾` of `k[x, y]`, through the constant
coefficient. -/
@[instance_reducible]
public def veroneseConstantAlgebra : Algebra (veroneseSubring (polyGrading k) 2) k :=
  (constantCoeff.comp (veroneseSubring (polyGrading k) 2).subtype).toAlgebra

attribute [local instance] veroneseConstantAlgebra

/-- The `S⁽²⁾`-linear functional on `S(1)⁽²⁾` reading off the coefficient of the variable `i`.
It is `S⁽²⁾`-linear for the action of `S⁽²⁾` on `k` through the constant coefficient because an
element of `S⁽²⁾` has no degree-one terms. -/
public def veroneseCoeff (i : Fin 2) :
    veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 →ₗ[veroneseSubring (polyGrading k) 2]
      k where
  toFun m := (m : MvPolynomial (Fin 2) k).coeff (Finsupp.single i 1)
  map_add' m n := by simp
  map_smul' s m := by
    change ((s : MvPolynomial (Fin 2) k) * (m : MvPolynomial (Fin 2) k)).coeff
        (Finsupp.single i 1) =
      constantCoeff (s : MvPolynomial (Fin 2) k) *
        (m : MvPolynomial (Fin 2) k).coeff (Finsupp.single i 1)
    rw [coeff_single_one_mul, coeff_single_one_eq_zero_of_mem_veroneseSubring k i s.2, zero_mul,
      add_zero, constantCoeff_eq]

/-- `veroneseCoeff k i m` is the coefficient of the variable `i` in `m`. -/
@[simp] public theorem veroneseCoeff_apply (i : Fin 2)
    (m : veroneseSubmodule (polyGrading k) (twistOneGrading k) 2) :
    veroneseCoeff k i m = (m : MvPolynomial (Fin 2) k).coeff (Finsupp.single i 1) :=
  rfl

/-- The `S⁽²⁾`-balanced functional on `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾` sending `m ⊗ n` to the
coefficient of `x` in `m` times the coefficient of `y` in `n`. -/
public def veroneseSeparatingFunctional :
    veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 ⊗[veroneseSubring (polyGrading k) 2]
        veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 →ₗ[
          veroneseSubring (polyGrading k) 2] k :=
  TensorProduct.lift <|
    (LinearMap.mul (veroneseSubring (polyGrading k) 2) k).compl₁₂
      (veroneseCoeff k 0) (veroneseCoeff k 1)

/-- `veroneseSeparatingFunctional` sends `m ⊗ n` to the coefficient of `x` in `m` times the
coefficient of `y` in `n`. -/
@[simp] public theorem veroneseSeparatingFunctional_tmul
    (m n : veroneseSubmodule (polyGrading k) (twistOneGrading k) 2) :
    veroneseSeparatingFunctional k (m ⊗ₜ[veroneseSubring (polyGrading k) 2] n) =
      (m : MvPolynomial (Fin 2) k).coeff (Finsupp.single 0 1) *
        (n : MvPolynomial (Fin 2) k).coeff (Finsupp.single 1 1) :=
  rfl

/-- The variable `x`, as an element of degree zero of `S(1)⁽²⁾`. -/
public def xVeronese : veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 :=
  ⟨X 0, X_mem_veroneseSubmodule_twistOne k 0⟩

/-- The variable `y`, as an element of degree zero of `S(1)⁽²⁾`. -/
public def yVeronese : veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 :=
  ⟨X 1, X_mem_veroneseSubmodule_twistOne k 1⟩

/-- The antisymmetrizer `x ⊗ y - y ⊗ x` of `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`. -/
public def veroneseAntisymmetrizer :
    veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 ⊗[veroneseSubring (polyGrading k) 2]
      veroneseSubmodule (polyGrading k) (twistOneGrading k) 2 :=
  xVeronese k ⊗ₜ yVeronese k - yVeronese k ⊗ₜ xVeronese k

/-- The antisymmetrizer is homogeneous of degree zero for the tensor grading of
`S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`. -/
public theorem veroneseAntisymmetrizer_mem_tensorGrading_zero :
    veroneseAntisymmetrizer k ∈ tensorGrading (S := veroneseSubring (polyGrading k) 2)
      (veroneseModuleGrading (polyGrading k) (twistOneGrading k) 2)
      (veroneseModuleGrading (polyGrading k) (twistOneGrading k) 2) 0 := by
  have hx : xVeronese k ∈ veroneseModuleGrading (polyGrading k) (twistOneGrading k) 2 0 :=
    (mem_veroneseModuleGrading _ _).mpr (X_mem_twistOneGrading_zero k 0)
  have hy : yVeronese k ∈ veroneseModuleGrading (polyGrading k) (twistOneGrading k) 2 0 :=
    (mem_veroneseModuleGrading _ _).mpr (X_mem_twistOneGrading_zero k 1)
  exact sub_mem (Stacks.GradedModule.tmul_mem_tensorGrading _ _ (add_zero 0) hx hy)
    (Stacks.GradedModule.tmul_mem_tensorGrading _ _ (add_zero 0) hy hx)

/-- **The antisymmetrizer is not zero** in `S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`:
`veroneseSeparatingFunctional` takes the value `1` on it. -/
public theorem veroneseAntisymmetrizer_ne_zero [Nontrivial k] : veroneseAntisymmetrizer k ≠ 0 := by
  intro h
  have hne := single_zero_ne_single_one
  have h1 := congrArg (veroneseSeparatingFunctional k) h
  rw [map_zero, veroneseAntisymmetrizer, map_sub, veroneseSeparatingFunctional_tmul,
    veroneseSeparatingFunctional_tmul] at h1
  simp only [xVeronese, yVeronese, coeff_X, ite_eq_right hne, ite_eq_right hne.symm] at h1
  simp at h1

/-- **The antisymmetrizer is in the kernel of the comparison** `veroneseTensorMap`: its image
`x ⊗ y - y ⊗ x` in `S(1) ⊗_S S(1)` vanishes, since `x ⊗ y = 1 ⊗ xy = y ⊗ x` there. -/
public theorem veroneseTensorMap_veroneseAntisymmetrizer :
    veroneseTensorMap (polyGrading k) (twistOneGrading k) (twistOneGrading k) 2
      (veroneseAntisymmetrizer k) = 0 := by
  apply Subtype.ext
  rw [veroneseAntisymmetrizer, map_sub, Submodule.coe_sub, veroneseTensorMap_tmul,
    veroneseTensorMap_tmul, ZeroMemClass.coe_zero]
  apply (TensorProduct.lid (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k)).injective
  simp [xVeronese, yVeronese, mul_comm]

/-- **Stacks Project, Tag 0B5J: the canonical comparison `M' ⊗_{S'} N' ⟶ (M ⊗_S N)'` is not
injective.**

For `S = k[x, y]` with its standard grading, `d = 2` and `M = N = S(1)`, the comparison
`Stacks.Veronese.veroneseTensorMap` — the very map along the lower edge of the compatibility
square of `Stacks.Veronese.tag0B5J` — kills the nonzero element `x ⊗ y - y ⊗ x` of
`S(1)⁽²⁾ ⊗_{S⁽²⁾} S(1)⁽²⁾`. So it is not an isomorphism, and the identity
`M' ⊗_{S'} N' = (M ⊗_S N)'` asserted in the source's proof is false. This holds for every
choice of the decomposition of the tensor grading that the map's statement carries; the
library's own is `not_injective_veroneseTensorMap_tensorGrading`. -/
public theorem not_injective_veroneseTensorMap [Nontrivial k] :
    ¬ Function.Injective
      (veroneseTensorMap (polyGrading k) (twistOneGrading k) (twistOneGrading k) 2) := fun h =>
  veroneseAntisymmetrizer_ne_zero k
    (h ((veroneseTensorMap_veroneseAntisymmetrizer k).trans (map_zero _).symm))

/-- `not_injective_veroneseTensorMap` at the decomposition of the tensor grading that the
library uses everywhere,
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition`:
`veroneseTensorMap` for `S = k[x, y]`, `d = 2`, `M = N = S(1)` is not injective. -/
public theorem not_injective_veroneseTensorMap_tensorGrading [Nontrivial k] :
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
      (polyGrading k) (twistOneGrading k) (twistOneGrading k)
    letI := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
      (polyGrading k) (twistOneGrading k) (twistOneGrading k)
    ¬ Function.Injective
      (veroneseTensorMap (polyGrading k) (twistOneGrading k) (twistOneGrading k) 2) :=
  let := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition
    (polyGrading k) (twistOneGrading k) (twistOneGrading k)
  let := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul
    (polyGrading k) (twistOneGrading k) (twistOneGrading k)
  not_injective_veroneseTensorMap k

end VeroneseTensorMap

end Stacks.Veronese

end
