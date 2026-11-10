module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardTorsion
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffinePositiveDegree
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.RingBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of the structure sheaf on the two fibres of a regular model

Let `S` be the standing situation of [Stacks, Tag 0C61]: a discrete valuation ring `R` with a
chosen uniformizer `π`, fraction field `K` and residue field `k`, a smooth projective curve `C`
over `K`, and a regular proper model `X ⟶ Spec R` whose generic fibre is `C`. This file proves
that the Euler characteristic of the structure sheaf is the same on the two fibres,

`χ(C, 𝒪_C) = χ(X_k, 𝒪_{X_k})`.

## Main results

All in the namespace `Stacks.Models`:

* `RegularProperModelSituation.eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre`:
  the comparison itself.
* `RegularProperModelSituation.specialBetti_eq`: the degreewise form,
  `dim_k Hⁿ(X_k, 𝒪_{X_k}) = dim_K Hⁿ(C, 𝒪_C) + t n + t (n+1)` with `t n = dim_k Hⁿ(X, 𝒪_X)[π]`.
* `RegularProperModelSituation.genericBetti_eq`: flat base change along `R ⟶ K`,
  `dim_K Hⁿ(C, 𝒪_C) = rank_R Hⁿ(X, 𝒪_X)`.
* `DVRArith.finrank_tensorResidue_eq`: the arithmetic of finite modules over a
  discrete valuation ring, `dim_k(M/πM) = rank_R M + dim_k(M[π])`.
* `ExactCount.finrank_eq_add_finrank_tensorTorsionBy`: the dimension count for the
  middle term of a five-term exact sequence `M --π--> M ⟶ V ⟶ M' --π--> M'`.
* `finsum_alternating_eq_of_shift`: the alternating sums of `a` and of
  `n ↦ a n + c n + c (n+1)` agree when `c 0 = 0` and both families are eventually zero.

## Implementation notes

**Why this is not [Stacks, Tag 0B9T].** The source deduces the statement from the perfection of
`Rf_*ℱ` ([Stacks, Tag 0B91] clause 2) together with the comparison of `Hⁱ(Rf_*ℱ ⊗^L κ(s))` with
`Hⁱ(X_s, ℱ_s)`; neither is carried in this library, and the tag is therefore available here only
with those two as hypotheses (see
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFibreEulerCharacteristic.lean`). Over a discrete
valuation ring the statement is instead provable from unconditional results of the library, and that
is the route taken: no tag attribute is attached to anything in this file.

**The proof.** Write `Mⁿ = Hⁿ(X, 𝒪_X)`, a finite `R`-module by [Stacks, Tag 02O6]
(`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`, unconditional) which
vanishes in large degrees. Flat base change in every degree
(`AlgebraicGeometry.nonempty_cohomologyBaseChangeIso`) applied to the localization `R ⟶ K`
identifies `dim_K Hⁿ(C, 𝒪_C)` with `rank_R Mⁿ`. The uniformizer gives a regular global section of
`𝒪_X` whose zero scheme is the special fibre, hence a short exact sequence
`0 ⟶ 𝒪_X --π--> 𝒪_X ⟶ i_*𝒪_{X_k} ⟶ 0` ([Stacks, Tag 0C6K]); its long exact sequence of
global-sections cohomology, taken from the `δ`-functor
`Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor`, and the invariance of cohomology
along the closed immersion `i` give
`dim_k Hⁿ(X_k, 𝒪_{X_k}) = dim_k(Mⁿ/πMⁿ) + dim_k(Mⁿ⁺¹[π])`. The arithmetic of finite modules over
a discrete valuation ring turns `dim_k(Mⁿ/πMⁿ)` into `rank_R Mⁿ + dim_k(Mⁿ[π])`, and the two
shifted copies of `dim_k(Mⁿ[π])` telescope out of the alternating sum because `π` acts injectively
on `H⁰`.

**That the map induced on cohomology by multiplication by `π` is multiplication by `π`** is
`AlgebraicGeometry.Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply`, which is what makes the
kernel and image of that map the `π`-torsion and the `π`-multiples of `Mⁿ`.

**Scalars.** `k ⊗[R] N` is used throughout as the model of the reduction of an `R`-module modulo
`π`, so that every dimension in sight is the dimension of an honest `k`-module and no `k`-module
structure has to be installed on a subquotient by hand. The cohomology of the special fibre
carries both the residue-field action and the action of `R` through the model; that these are
compatible is `Stacks.Models.appTop_modelBaseMap`, which is
`Stacks.Models.RegularProperModelSituation.fibreSubschemeResidueMap_comp` read at `⊤`.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

universe u

/-! ## DVR arithmetic over a discrete valuation ring -/

section

open TensorProduct

namespace Stacks.Models.DVRArith

section Transfer

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]

/-- The residual dimension `dim_k (k ⊗[R] ·)` is invariant under `R`-linear equivalences,
because the `R`-linear equivalence it induces on base changes is automatically `k`-linear
when `R → k` is surjective. -/
theorem finrank_tensor_congr (hsurj : Function.Surjective (algebraMap R k))
    {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) :
    Module.finrank k (k ⊗[R] A) = Module.finrank k (k ⊗[R] B) :=
  ((LinearEquiv.lTensor k e).extendScalarsOfSurjective hsurj).finrank_eq

/-- Base change of a trivial module is trivial. -/
instance subsingleton_tensor {A : Type u} [AddCommGroup A] [Module R A] [Subsingleton A] :
    Subsingleton (k ⊗[R] A) :=
  ⟨fun x y => by
    have h : ∀ z : k ⊗[R] A, z = 0 := fun z => by
      induction z with
      | tmul c a => rw [Subsingleton.elim a 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h x, h y]⟩

/-- The residual dimension of a trivial module is zero. -/
theorem finrank_tensor_eq_zero_of_subsingleton {A : Type u} [AddCommGroup A] [Module R A]
    [Subsingleton A] : Module.finrank k (k ⊗[R] A) = 0 :=
  Module.finrank_zero_of_subsingleton

/-- Base change turns a binary product into a binary product of `k`-vector spaces. -/
theorem finrank_tensor_prod {A B : Type u} [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] :
    Module.finrank k (k ⊗[R] (A × B)) =
      Module.finrank k (k ⊗[R] A) + Module.finrank k (k ⊗[R] B) := by
  rw [(TensorProduct.prodRight R k k A B).finrank_eq, Module.finrank_prod]

/-- Base change turns a finite product into a finite product of `k`-vector spaces. -/
theorem finrank_tensor_pi {ι : Type*} [Fintype ι] (N : ι → Type u)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Finite R (N i)] :
    Module.finrank k (k ⊗[R] (∀ i, N i)) = ∑ i, Module.finrank k (k ⊗[R] N i) := by
  classical
  rw [(TensorProduct.piRight R k k N).finrank_eq, Module.finrank_pi_fintype]

end Transfer

section Torsion

variable {R : Type u} [CommRing R]

/-- An `R`-linear equivalence restricts to an equivalence of `a`-torsion submodules. -/
def torsionByCongr {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (a : R) :
    Submodule.torsionBy R A a ≃ₗ[R] Submodule.torsionBy R B a :=
  LinearEquiv.ofEq _ _ (by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_torsionBy_iff, LinearEquiv.coe_coe,
      ← map_smul, e.map_eq_zero_iff]) ≪≫ₗ
    LinearEquiv.ofSubmodule' e (Submodule.torsionBy R B a)

/-- An `R`-linear equivalence restricts to an equivalence of `a`-torsion submodules, for modules
in arbitrary universes.

This is `Stacks.Models.DVRArith.torsionByCongr` with the two modules allowed to live in
different universes: the `a`-torsion of the Picard group of a scheme is compared this way with
the `a`-torsion of a group of rational points, and those sit one universe apart.  See
`StacksFrontier/AlgebraicGeometry/Picard/TorsionSmoothProjectiveCurve.lean`. -/
def torsionByCongr' {A : Type*} {B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] (e : A ≃ₗ[R] B) (a : R) :
    Submodule.torsionBy R A a ≃ₗ[R] Submodule.torsionBy R B a :=
  LinearEquiv.ofEq _ _ (by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_torsionBy_iff, LinearEquiv.coe_coe,
      ← map_smul, e.map_eq_zero_iff]) ≪≫ₗ
    LinearEquiv.ofSubmodule' e (Submodule.torsionBy R B a)

/-- `a`-torsion of a binary product is the product of the `a`-torsions. -/
def torsionByProdEquiv {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (a : R) :
    Submodule.torsionBy R (A × B) a ≃ₗ[R]
      Submodule.torsionBy R A a × Submodule.torsionBy R B a where
  toFun x :=
    (⟨(x : A × B).1, by
        have h := (Submodule.mem_torsionBy_iff a (x : A × B)).mp x.2
        rw [Submodule.mem_torsionBy_iff, ← Prod.smul_fst, h, Prod.fst_zero]⟩,
      ⟨(x : A × B).2, by
        have h := (Submodule.mem_torsionBy_iff a (x : A × B)).mp x.2
        rw [Submodule.mem_torsionBy_iff, ← Prod.smul_snd, h, Prod.snd_zero]⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y :=
    ⟨((y.1 : A), (y.2 : B)), by
      rw [Submodule.mem_torsionBy_iff, Prod.smul_mk, Submodule.smul_coe_torsionBy,
        Submodule.smul_coe_torsionBy, Prod.mk_zero_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `a`-torsion of a product of modules is the product of the `a`-torsions. -/
def torsionByPiEquiv {ι : Type*} (N : ι → Type u) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (a : R) :
    Submodule.torsionBy R (∀ i, N i) a ≃ₗ[R] ∀ i, Submodule.torsionBy R (N i) a where
  toFun x i :=
    ⟨(x : ∀ j, N j) i, by
      have h := (Submodule.mem_torsionBy_iff a _).mp x.2
      simpa using congrFun h i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y :=
    ⟨fun i => (y i : N i), by
      rw [Submodule.mem_torsionBy_iff]
      funext i
      exact Submodule.smul_coe_torsionBy a (y i)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A torsion factor does not contribute to the generic rank of a product. -/
theorem finrank_prod_of_isTorsion {A B : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (hB : Module.IsTorsion R B) :
    Module.finrank R (A × B) = Module.finrank R A := by
  have hker : LinearMap.ker (LinearMap.fst R A B) ≤ Submodule.torsion R (A × B) := by
    intro x hx
    obtain ⟨c, hc⟩ := @hB x.2
    refine (Submodule.mem_torsion_iff x).mpr ⟨c, ?_⟩
    have hx1 : x.1 = 0 := LinearMap.mem_ker.mp hx
    rw [show x = (x.1, x.2) from rfl, Prod.smul_mk, hx1, smul_zero, hc, Prod.mk_zero_zero]
  rw [← finrank_quotient_eq_of_le_torsion hker,
    (LinearMap.quotKerEquivOfSurjective (LinearMap.fst R A B)
      (LinearMap.fst_surjective)).finrank_eq]

end Torsion

section Residue

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]

/-- If every element of `I` dies in `k`, then `I` annihilates `k`. -/
theorem smul_top_eq_bot_of_mapsTo_zero {I : Ideal R}
    (hI : ∀ x ∈ I, algebraMap R k x = 0) : I • (⊤ : Submodule R k) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun r hr c _ => ?_
  rw [Algebra.smul_def, hI r hr, zero_mul]
  exact Submodule.zero_mem _

/-- If the ideal `I` dies in `k`, then `k ⊗[R] (R ⧸ I)` is just `k`. -/
def tensorQuotEquivBase (I : Ideal R) (hI : ∀ x ∈ I, algebraMap R k x = 0) :
    k ⊗[R] (R ⧸ I) ≃ₗ[R] k :=
  TensorProduct.tensorQuotEquivQuotSMul k I ≪≫ₗ
    Submodule.quotEquivOfEqBot _ (smul_top_eq_bot_of_mapsTo_zero hI)

/-- If the ideal `I` dies in `k`, the residual dimension of `R ⧸ I` is one. -/
theorem finrank_tensor_quot_eq_one (hsurj : Function.Surjective (algebraMap R k))
    (I : Ideal R) (hI : ∀ x ∈ I, algebraMap R k x = 0) :
    Module.finrank k (k ⊗[R] (R ⧸ I)) = 1 := by
  rw [((tensorQuotEquivBase I hI).extendScalarsOfSurjective hsurj).finrank_eq,
    Module.finrank_self]

end Residue

section Cyclic

variable {R : Type u} [CommRing R] [IsDomain R]

/-- For `e = d + 1`, multiplication by `π ^ d` presents the `π`-torsion submodule of
`R ⧸ (π ^ e)` as the quotient `R ⧸ (π)`. -/
def quotSpanEquivTorsionBy {π : R} (hπ0 : π ≠ 0) (d : ℕ) :
    (R ⧸ Ideal.span {π}) ≃ₗ[R]
      Submodule.torsionBy R (R ⧸ Ideal.span {π ^ (d + 1)}) π := by
  have hmem : ∀ r : R,
      r • (Submodule.Quotient.mk (π ^ d) : R ⧸ Ideal.span {π ^ (d + 1)}) ∈
        Submodule.torsionBy R (R ⧸ Ideal.span {π ^ (d + 1)}) π := by
    intro r
    rw [Submodule.mem_torsionBy_iff, smul_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
    exact ⟨r, by ring⟩
  set g : R →ₗ[R] Submodule.torsionBy R (R ⧸ Ideal.span {π ^ (d + 1)}) π :=
    LinearMap.codRestrict _
      (LinearMap.toSpanSingleton R (R ⧸ Ideal.span {π ^ (d + 1)}) (Submodule.Quotient.mk (π ^ d)))
      hmem
  have hgapp : ∀ r : R, (g r : R ⧸ Ideal.span {π ^ (d + 1)}) =
      Submodule.Quotient.mk (r * π ^ d) := by
    intro r
    change r • (Submodule.Quotient.mk (π ^ d) : R ⧸ Ideal.span {π ^ (d + 1)}) = _
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul]
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (Ideal.span {π ^ (d + 1)}) (t : _)
    have ht : (π : R) • (t : R ⧸ Ideal.span {π ^ (d + 1)}) = 0 :=
      (Submodule.mem_torsionBy_iff π _).mp t.2
    rw [← hx, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton] at ht
    obtain ⟨y, hy⟩ := ht
    have hxy : x = π ^ d * y := by
      have : π * x = π * (π ^ d * y) := by rw [hy]; ring
      exact mul_left_cancel₀ hπ0 this
    refine ⟨y, Subtype.ext ?_⟩
    rw [hgapp, ← hx, hxy]
    congr 1
    ring
  have hker : LinearMap.ker g = Ideal.span {π} := by
    apply le_antisymm
    · intro r hr
      have h0 : (g r : R ⧸ Ideal.span {π ^ (d + 1)}) = 0 := by
        rw [LinearMap.mem_ker.mp hr]; rfl
      rw [hgapp, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at h0
      obtain ⟨y, hy⟩ := h0
      rw [Ideal.mem_span_singleton]
      refine ⟨y, mul_right_cancel₀ (pow_ne_zero d hπ0) ?_⟩
      rw [hy]; ring
    · intro r hr
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨y, hy⟩ := hr
      refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
      rw [ZeroMemClass.coe_zero, hgapp, hy, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton]
      exact ⟨y, by ring⟩
  exact Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ LinearMap.quotKerEquivOfSurjective g hg

end Cyclic

section Pieces

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]

/-- The residual dimension of `R` itself is one. -/
theorem finrank_tensor_base (hsurj : Function.Surjective (algebraMap R k)) :
    Module.finrank k (k ⊗[R] R) = 1 := by
  rw [((TensorProduct.rid R k).extendScalarsOfSurjective hsurj).finrank_eq, Module.finrank_self]

/-- The residual dimension of a finite free module equals its rank. -/
theorem finrank_tensor_fun (hsurj : Function.Surjective (algebraMap R k)) (n : ℕ) :
    Module.finrank k (k ⊗[R] (Fin n → R)) = n := by
  rw [finrank_tensor_pi (fun _ : Fin n => R)]
  simp [finrank_tensor_base hsurj]

/-- A finite free module over a domain has no `a`-torsion for `a ≠ 0`. -/
theorem subsingleton_torsionBy_fun [IsDomain R] (n : ℕ) {a : R} (ha : a ≠ 0) :
    Subsingleton (Submodule.torsionBy R (Fin n → R) a) :=
  ⟨fun x y => Subtype.ext (by
    funext i
    have hx : a * (x : Fin n → R) i = 0 := by
      simpa using congrFun (Submodule.smul_coe_torsionBy a x) i
    have hy : a * (y : Fin n → R) i = 0 := by
      simpa using congrFun (Submodule.smul_coe_torsionBy a y) i
    rw [(mul_eq_zero.mp hx).resolve_left ha, (mul_eq_zero.mp hy).resolve_left ha])⟩

/-- Every element of a submodule of a trivial module is trivial. -/
theorem subsingleton_submodule {A : Type u} [AddCommGroup A] [Module R A] [Subsingleton A]
    (p : Submodule R A) : Subsingleton p :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

end Pieces

section Combine

variable {R : Type u} [CommRing R] [IsDomain R] {k : Type u} [Field k] [Algebra R k]

omit [IsDomain R] in
/-- A power of `π` dies in `k` as soon as the exponent is positive. -/
theorem mapsTo_zero_span_pow {π : R} (hπ0 : algebraMap R k π = 0) {e : ℕ} (he : e ≠ 0)
    (x : R) (hx : x ∈ Ideal.span ({π ^ e} : Set R)) : algebraMap R k x = 0 := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [map_mul, map_pow, hπ0, zero_pow he, zero_mul]

/-- For a uniformizer `π` of `R` with residue field `k`, the cyclic module `R ⧸ (π ^ e)` has
the same residual dimension as its `π`-torsion submodule: both are `1` for `e ≥ 1` and both
are `0` for `e = 0`. -/
theorem finrank_tensor_cyclic_eq (hsurj : Function.Surjective (algebraMap R k)) {π : R}
    (hπ0 : algebraMap R k π = 0) (hπne : π ≠ 0) (e : ℕ) :
    Module.finrank k (k ⊗[R] (R ⧸ Ideal.span ({π ^ e} : Set R))) =
      Module.finrank k
        (k ⊗[R] Submodule.torsionBy R (R ⧸ Ideal.span ({π ^ e} : Set R)) π) := by
  match e with
  | 0 =>
    have : Subsingleton (R ⧸ Ideal.span ({π ^ 0} : Set R)) :=
      Submodule.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    have := subsingleton_submodule (Submodule.torsionBy R (R ⧸ Ideal.span ({π ^ 0} : Set R)) π)
    rw [finrank_tensor_eq_zero_of_subsingleton, finrank_tensor_eq_zero_of_subsingleton]
  | d + 1 =>
    rw [finrank_tensor_quot_eq_one hsurj _ (mapsTo_zero_span_pow hπ0 (Nat.succ_ne_zero d)),
      ← finrank_tensor_congr hsurj (quotSpanEquivTorsionBy hπne d),
      finrank_tensor_quot_eq_one hsurj _ (fun x hx => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
        rw [map_mul, hπ0, zero_mul])]

/-- A finite product of cyclic modules `R ⧸ (q i)` with every `q i` nonzero is torsion. -/
theorem isTorsion_pi_quot {ι : Type u} [Finite ι] (q : ι → R) (hq : ∀ i, q i ≠ 0) :
    Module.IsTorsion R (∀ i, R ⧸ Ideal.span ({q i} : Set R)) := by
  classical
  have := Fintype.ofFinite ι
  intro x
  refine ⟨⟨∏ i, q i, mem_nonZeroDivisors_of_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ => hq i)⟩, ?_⟩
  rw [Submonoid.smul_def]
  funext i
  obtain ⟨c, hc⟩ : q i ∣ ∏ j, q j := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (Ideal.span ({q i} : Set R)) (x i)
  simp only [Pi.smul_apply, Pi.zero_apply]
  rw [← hy, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_span_singleton]
  exact ⟨c * y, by rw [hc]; ring⟩

end Combine

/-- For a discrete valuation ring `R` with uniformizer `π` and residue field `k`, and a
finitely generated `R`-module `M`, the dimension of the residual fibre `M/πM = k ⊗[R] M`
is the generic rank of `M` plus the dimension of the `π`-torsion `M[π]` after base change. -/
@[ega "III 7.6.5" "partial"]
theorem finrank_tensorResidue_eq (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (k : Type u) [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k)) {π : R} (hπ : Irreducible π)
    (hπ0 : algebraMap R k π = 0) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.finrank k (k ⊗[R] M) =
      Module.finrank R M + Module.finrank k (k ⊗[R] (Submodule.torsionBy R M π)) := by
  classical
  have hπne : π ≠ 0 := hπ.ne_zero
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R M
  have hassoc : ∀ i, (R ∙ p i ^ e i) = Ideal.span ({π ^ e i} : Set R) := fun i => by
    rw [Ideal.span_singleton_eq_span_singleton]
    exact (IsDiscreteValuationRing.associated_of_irreducible R (hp i) hπ).pow_pow
  have g : M ≃ₗ[R] (Fin n → R) × (∀ i, R ⧸ Ideal.span ({π ^ e i} : Set R)) :=
    f ≪≫ₗ LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite R R (Fin n))
      (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ (R ∙ p i ^ e i)) ≪≫ₗ
        LinearEquiv.piCongrRight fun i => Submodule.quotEquivOfEq _ _ (hassoc i))
  have : Subsingleton (Submodule.torsionBy R (Fin n → R) π) :=
    subsingleton_torsionBy_fun n hπne
  have hTors : Module.IsTorsion R (∀ i, R ⧸ Ideal.span ({π ^ e i} : Set R)) :=
    isTorsion_pi_quot _ fun i => pow_ne_zero _ hπne
  have hL : Module.finrank k (k ⊗[R] M) =
      n + ∑ i, Module.finrank k (k ⊗[R] (R ⧸ Ideal.span ({π ^ e i} : Set R))) := by
    rw [finrank_tensor_congr hsurj g, finrank_tensor_prod, finrank_tensor_fun hsurj,
      finrank_tensor_pi]
  have hR : Module.finrank R M = n := by
    rw [g.finrank_eq, finrank_prod_of_isTorsion hTors, Module.finrank_pi R, Fintype.card_fin]
  have hT : Module.finrank k (k ⊗[R] (Submodule.torsionBy R M π)) =
      ∑ i, Module.finrank k
        (k ⊗[R] Submodule.torsionBy R (R ⧸ Ideal.span ({π ^ e i} : Set R)) π) := by
    rw [finrank_tensor_congr hsurj (torsionByCongr g π),
      finrank_tensor_congr hsurj (torsionByProdEquiv π), finrank_tensor_prod,
      finrank_tensor_eq_zero_of_subsingleton, zero_add,
      finrank_tensor_congr hsurj (torsionByPiEquiv _ π), finrank_tensor_pi]
  rw [hL, hR, hT,
    Finset.sum_congr rfl fun i _ => finrank_tensor_cyclic_eq hsurj hπ0 hπne (e i)]

end Stacks.Models.DVRArith

end

/-! ## Counting the dimension of the middle term of a five-term exact sequence -/

section

open TensorProduct

namespace Stacks.Models.ExactCount

/-- Two `k`-modules whose `R`-module structures factor through a surjection `R → k` have the
same `k`-dimension as soon as they are `R`-linearly isomorphic: the `R`-linear isomorphism is
automatically `k`-linear. -/
theorem finrank_eq_of_rLinearEquiv {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k))
    {A B : Type u} [AddCommGroup A] [Module k A] [Module R A] [IsScalarTower R k A]
    [AddCommGroup B] [Module k B] [Module R B] [IsScalarTower R k B]
    (e : A ≃ₗ[R] B) : Module.finrank k A = Module.finrank k B :=
  (e.extendScalarsOfSurjective hsurj).finrank_eq

/-- `k ⊗[R] W ≃ W` for a `k`-module `W` on which `R` acts through the surjection `R → k`. -/
def tensorEquivSelf {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k))
    (W : Type u) [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower R k W] :
    k ⊗[R] W ≃ₗ[R] W := by
  refine LinearEquiv.ofLinearMap (TensorProduct.lift
    { toFun := fun c => (LinearMap.lsmul k W c).restrictScalars R
      map_add' := by intro c c'; ext v; simp
      map_smul' := by intro r c; ext v; exact smul_assoc r c v })
    (TensorProduct.mk R k W 1) ?_ ?_
  · refine LinearMap.ext fun v => ?_
    change (1 : k) • v = v
    exact one_smul k v
  · ext c v
    change (1 : k) ⊗ₜ[R] (c • v) = c ⊗ₜ[R] v
    obtain ⟨r, rfl⟩ := hsurj c
    rw [IsScalarTower.algebraMap_smul (A := k) (R := R) r v, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

/-- An element of `R` that maps to `0` in `k` acts as `0` on any `k`-module whose `R`-module
structure factors through `R → k`. -/
theorem smul_eq_zero_of_algebraMap_eq_zero {R : Type u} [CommRing R] {k : Type u} [Field k]
    [Algebra R k] {π : R} (hπ0 : algebraMap R k π = 0)
    {W : Type u} [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower R k W] (w : W) :
    π • w = 0 := by
  rw [← IsScalarTower.algebraMap_smul k π w, hπ0, zero_smul]

section Main

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]
  {M M' V : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]

/-- The image of an `R`-linear map into a `k`-module is a `k`-subspace, provided `R → k` is
surjective: the `k`-action on the image is the `R`-action pushed along the surjection. -/
def rangeSubmodule (hsurj : Function.Surjective (algebraMap R k)) (φ : M →ₗ[R] V) :
    Submodule k V where
  carrier := Set.range φ
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨m, rfl⟩
    obtain ⟨r, rfl⟩ := hsurj c
    exact ⟨r • m, by rw [map_smul, IsScalarTower.algebraMap_smul]⟩

/-- An element of `V` lies in `rangeSubmodule hsurj φ` if and only if it lies in the image of
`φ`. -/
@[simp]
theorem mem_rangeSubmodule {hsurj : Function.Surjective (algebraMap R k)} {φ : M →ₗ[R] V} {x : V} :
    x ∈ rangeSubmodule hsurj φ ↔ ∃ m, φ m = x := Iff.rfl

/-- The corestriction of `φ : M →ₗ[R] V` to its image, viewed as a `k`-subspace of `V`. -/
def toRangeSubmodule (hsurj : Function.Surjective (algebraMap R k)) (φ : M →ₗ[R] V) :
    M →ₗ[R] rangeSubmodule hsurj φ where
  toFun m := ⟨φ m, ⟨m, rfl⟩⟩
  map_add' m m' := by ext; simp
  map_smul' r m := by ext; simp

/-- The image of `m` under `toRangeSubmodule hsurj φ`, viewed in `V`, is `φ m`. -/
@[simp]
theorem coe_toRangeSubmodule (hsurj : Function.Surjective (algebraMap R k)) (φ : M →ₗ[R] V)
    (m : M) : ((toRangeSubmodule hsurj φ m : rangeSubmodule hsurj φ) : V) = φ m := rfl

/-- `φ` corestricted to its image is surjective. -/
theorem toRangeSubmodule_surjective (hsurj : Function.Surjective (algebraMap R k))
    (φ : M →ₗ[R] V) : Function.Surjective (toRangeSubmodule hsurj φ) := by
  rintro ⟨x, m, rfl⟩
  exact ⟨m, rfl⟩

/-- Corestricting to the image does not change the kernel. -/
theorem toRangeSubmodule_eq_zero_iff (hsurj : Function.Surjective (algebraMap R k))
    (φ : M →ₗ[R] V) (m : M) : toRangeSubmodule hsurj φ m = 0 ↔ φ m = 0 := by
  rw [← Submodule.coe_eq_zero, coe_toRangeSubmodule]

/-- Step (B1): the image of `φ` has the same `k`-dimension as the reduction `k ⊗[R] M`, as soon
as `ker φ = π • M` and `π` dies in `k`. This is right-exactness of the tensor product applied to
`M --π--> M --φ--> im φ --> 0`. -/
theorem finrank_tensor_eq_finrank_rangeSubmodule
    (hsurj : Function.Surjective (algebraMap R k)) {π : R} (hπ0 : algebraMap R k π = 0)
    (φ : M →ₗ[R] V) (h1 : Function.Exact (π • (LinearMap.id : M →ₗ[R] M)) φ) :
    Module.finrank k (k ⊗[R] M) = Module.finrank k (rangeSubmodule hsurj φ) := by
  set A := rangeSubmodule hsurj φ
  set φ' := toRangeSubmodule hsurj φ
  have hsurj' : Function.Surjective φ' := toRangeSubmodule_surjective hsurj φ
  have h1' : Function.Exact (π • (LinearMap.id : M →ₗ[R] M)) φ' := fun m => by
    rw [toRangeSubmodule_eq_zero_iff]; exact h1 m
  have hex := _root_.lTensor_exact (R := R) k h1' hsurj'
  have hzero : LinearMap.lTensor k (π • (LinearMap.id : M →ₗ[R] M)) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    change c ⊗ₜ[R] (π • m) = 0
    rw [TensorProduct.tmul_smul]
    exact smul_eq_zero_of_algebraMap_eq_zero hπ0 _
  have hinj : Function.Injective (LinearMap.lTensor k φ') := by
    rw [← LinearMap.ker_eq_bot, hex.linearMap_ker_eq, hzero, LinearMap.range_zero]
  have e1 : (k ⊗[R] M) ≃ₗ[R] (k ⊗[R] A) :=
    LinearEquiv.ofBijective (LinearMap.lTensor k φ') ⟨hinj, LinearMap.lTensor_surjective k hsurj'⟩
  exact finrank_eq_of_rLinearEquiv hsurj (e1.trans (tensorEquivSelf hsurj A))

/-- The corestriction of `ψ : V →ₗ[R] M'` to the `π`-torsion of `M'`, available whenever the
image of `ψ` consists of `π`-torsion elements. -/
def toTorsionBy {π : R} (ψ : V →ₗ[R] M')
    (h3 : Function.Exact ψ (π • (LinearMap.id : M' →ₗ[R] M'))) :
    V →ₗ[R] Submodule.torsionBy R M' π where
  toFun v := ⟨ψ v, (h3 (ψ v)).mpr ⟨v, rfl⟩⟩
  map_add' v v' := by ext; simp
  map_smul' r v := by ext; simp

/-- The image of `v` under `toTorsionBy ψ h3`, viewed in `M'`, is `ψ v`. -/
@[simp]
theorem coe_toTorsionBy {π : R} (ψ : V →ₗ[R] M')
    (h3 : Function.Exact ψ (π • (LinearMap.id : M' →ₗ[R] M'))) (v : V) :
    ((toTorsionBy ψ h3 v : Submodule.torsionBy R M' π) : M') = ψ v := rfl

/-- `ψ` corestricted to the `π`-torsion of `M'` is surjective, because its image is exactly the
`π`-torsion. -/
theorem toTorsionBy_surjective {π : R} (ψ : V →ₗ[R] M')
    (h3 : Function.Exact ψ (π • (LinearMap.id : M' →ₗ[R] M'))) :
    Function.Surjective (toTorsionBy ψ h3) := by
  rintro ⟨y, hy⟩
  obtain ⟨v, rfl⟩ := (h3 y).mp hy
  exact ⟨v, rfl⟩

/-- Step (B2): the quotient of `V` by the image of `φ` has the same `k`-dimension as the
reduction `k ⊗[R] M'[π]` of the `π`-torsion of `M'`. -/
theorem finrank_quotient_eq_finrank_tensorTorsionBy
    (hsurj : Function.Surjective (algebraMap R k)) {π : R}
    (φ : M →ₗ[R] V) (ψ : V →ₗ[R] M')
    (h2 : Function.Exact φ ψ)
    (h3 : Function.Exact ψ (π • (LinearMap.id : M' →ₗ[R] M'))) :
    Module.finrank k (V ⧸ rangeSubmodule hsurj φ) =
      Module.finrank k (k ⊗[R] (Submodule.torsionBy R M' π)) := by
  set A := rangeSubmodule hsurj φ
  set ψ' := toTorsionBy ψ h3
  have hker : LinearMap.ker ψ' = A.restrictScalars R := by
    refine Submodule.ext fun v => ?_
    rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero, coe_toTorsionBy,
      Submodule.restrictScalars_mem]
    exact h2 v
  have e2 : (V ⧸ A) ≃ₗ[R] (Submodule.torsionBy R M' π) :=
    (Submodule.Quotient.restrictScalarsEquiv R A).symm.trans
      (hker ▸ LinearMap.quotKerEquivOfSurjective ψ' (toTorsionBy_surjective ψ h3))
  refine finrank_eq_of_rLinearEquiv hsurj
    ((tensorEquivSelf hsurj (V ⧸ A)).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R k) e2))

/-- The dimension of the middle term of an exact sequence
`M --π--> M --φ--> V --ψ--> M' --π--> M'` over a ring `R` surjecting onto a field `k` which
kills `π`: it is the sum of the dimension of the reduction `k ⊗[R] M` and the dimension of the
reduction `k ⊗[R] M'[π]` of the `π`-torsion of `M'`. -/
theorem finrank_eq_add_finrank_tensorTorsionBy
    {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k]
    (hsurj : Function.Surjective (algebraMap R k)) {π : R} (hπ0 : algebraMap R k π = 0)
    {M M' V : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V] [FiniteDimensional k V]
    (φ : M →ₗ[R] V) (ψ : V →ₗ[R] M')
    (h1 : Function.Exact (π • (LinearMap.id : M →ₗ[R] M)) φ)
    (h2 : Function.Exact φ ψ)
    (h3 : Function.Exact ψ (π • (LinearMap.id : M' →ₗ[R] M'))) :
    Module.finrank k V =
      Module.finrank k (k ⊗[R] M) +
        Module.finrank k (k ⊗[R] (Submodule.torsionBy R M' π)) := by
  have hrn := Submodule.finrank_quotient_add_finrank (rangeSubmodule hsurj φ)
  rw [finrank_quotient_eq_finrank_tensorTorsionBy hsurj φ ψ h2 h3,
    ← finrank_tensor_eq_finrank_rangeSubmodule hsurj hπ0 φ h1] at hrn
  omega

end Main

end Stacks.Models.ExactCount

end

/-! ## Flat base change onto the generic fibre -/

section

open AlgebraicGeometry CategoryTheory Limits Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange (baseRestrictScalars baseExtendScalars
  le_preimage_top)
open scoped TensorProduct

namespace Stacks.Models.GenericBaseChange

/-! ### Dimension under change of rings -/

/-- **Being a fraction ring transports along a pair of ring isomorphisms.** If `B` is the fraction
ring of `A` after `A` and `B` are renamed to `R` and `K` by ring isomorphisms carrying `φ` to
`algebraMap R K`, then `B` is the fraction ring of `A` along `φ`. The nonzerodivisors of `A` are
the image of those of `R`, so each of the three clauses of `isLocalization_iff` is the
corresponding clause downstairs, transported. -/
private theorem isFractionRing_of_ringEquivs {R K A B : Type u} [CommRing R] [CommRing K]
    [CommRing A] [CommRing B] [Algebra R K] [IsFractionRing R K]
    (eR : R ≃+* A) (eK : K ≃+* B) (φ : A →+* B)
    (h : ∀ x : R, φ (eR x) = eK (algebraMap R K x)) :
    letI := φ.toAlgebra
    IsFractionRing A B := by
  let := φ.toAlgebra
  have hmap : ∀ x : A, algebraMap A B x = φ x := fun _ => rfl
  have hR : Submonoid.map (eR : R ≃* A) (nonZeroDivisors R) = nonZeroDivisors A :=
    MulEquivClass.map_nonZeroDivisors eR
  refine (isLocalization_iff (nonZeroDivisors A) B).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hR] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change IsUnit (algebraMap A B (eR x))
    rw [hmap, h x]
    exact (IsLocalization.map_units (M := nonZeroDivisors R) K ⟨x, hx⟩).map eK
  · intro z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := nonZeroDivisors R) (S := K) (eK.symm z)
    refine ⟨⟨eR a, eR s, hR ▸ Submonoid.mem_map_of_mem _ s.2⟩, ?_⟩
    have h2 := congrArg eK hs
    rw [map_mul, eK.apply_symm_apply] at h2
    simpa [hmap, h] using h2
  · intro x y hxy
    rw [hmap, hmap, ← eR.apply_symm_apply x, ← eR.apply_symm_apply y, h, h] at hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := nonZeroDivisors R) (eK.injective hxy)
    refine ⟨⟨eR c, hR ▸ Submonoid.mem_map_of_mem _ c.2⟩, ?_⟩
    have h3 := congrArg eR hc
    rwa [map_mul, map_mul, eR.apply_symm_apply, eR.apply_symm_apply] at h3

/-- **Extension of scalars to a fraction ring does not change the dimension**, with no freeness
hypothesis: `B ⊗[A] M` is the localization of `M` at the nonzerodivisors of `A`, so its dimension
over `A` is that of `M`, and over `B` it is the same because `B` is a localization of `A`. -/
private theorem finrank_extendScalars_of_isFractionRing {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hfr : letI := φ.toAlgebra; IsFractionRing A B) (M : ModuleCat.{u} A) :
    Module.finrank B ((ModuleCat.extendScalars.{u, u, u} φ).obj M) = Module.finrank A M := by
  let := φ.toAlgebra
  have := hfr
  have h1 : Module.finrank B (B ⊗[A] M) = Module.finrank A (B ⊗[A] M) :=
    IsLocalization.finrank_eq B (nonZeroDivisors A) le_rfl
  have h2 : Module.finrank A (B ⊗[A] M) = Module.finrank A M :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors A) (TensorProduct.mk A B M 1) le_rfl
  exact h1.trans h2

/-- **The dimension over the base ring is the dimension over the global functions of the base.**
The one-step restriction of scalars along `A ⟶ Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)` used by
`AlgebraicGeometry.cohomologyOverField` and by `Stacks.LocalCohomology.cohomologyOverBase` is the
restriction along `Γ(Spec A, ⊤) ⟶ Γ(X, ⊤)` followed by the restriction along the ring isomorphism
`A ≅ Γ(Spec A, ⊤)`, which preserves dimension. -/
private theorem finrank_eq_finrank_baseRestrictScalars (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (M : ModuleCat.{u} Γ(X, ⊤)) :
    Module.finrank A
        ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom).obj M) =
      Module.finrank Γ(Spec (.of A), ⊤) ((baseRestrictScalars f).obj M) := by
  have hfr : ∀ {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (N : ModuleCat.{u} S),
      Module.finrank R ((ModuleCat.restrictScalars e.toRingHom).obj N) = Module.finrank S N :=
    fun e N => congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv e (AddEquiv.refl N) e.bijective fun _ _ => rfl)
  rw [← hfr (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    ((baseRestrictScalars f).obj M)]
  exact (ModuleCat.restrictScalarsComp'App
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toRingHom
    (f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom
    (by ext x; rfl) M).toLinearEquiv.finrank_eq

/-! ### Flat base change to the fraction field -/

/-- **The cohomology of the structure sheaf of the base change to a fraction field has the rank of
the cohomology of the structure sheaf downstairs.** For `X` separated and quasi-compact over
`Spec(R)` and `K` a fraction field of `R`,

`dim_K Hⁿ(X_K, 𝒪_{X_K}) = rank_R Hⁿ(X, 𝒪_X)`

in every degree, `X_K` being the pullback of `X` along `Spec(K) ⟶ Spec(R)` with its second
projection as structure morphism. -/
private theorem finrank_cohomologyOverField_pullback_snd_unit (R K : Type u) [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}} (iX : X ⟶ Spec (.of R))
    [IsSeparated iX] [QuasiCompact iX] (n : ℕ) :
    Module.finrank K
        (cohomologyOverField K
          (pullback.snd iX (Spec.map (CommRingCat.ofHom (algebraMap R K))))
          (SheafOfModules.unit
            (pullback iX (Spec.map (CommRingCat.ofHom (algebraMap R K)))).ringCatSheaf) n) =
      Module.finrank R
        (Stacks.LocalCohomology.cohomologyOverBase.{u, u} R iX
          (SheafOfModules.unit X.ringCatSheaf) n) := by
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    AlgebraicGeometry.Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  obtain ⟨e⟩ := AlgebraicGeometry.nonempty_cohomologyBaseChangeIso
    (IsPullback.of_hasPullback iX (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (SheafOfModules.unit X.ringCatSheaf) n
  have hnat : ∀ x : R,
      ((Spec.map (CommRingCat.ofHom (algebraMap R K))).appLE ⊤ ⊤
          (le_preimage_top (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⊤)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv x) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (algebraMap R K x) := by
    intro x
    rw [Scheme.Hom.appLE_top_top]
    exact (congrArg (fun m : CommRingCat.of R ⟶ Γ(Spec (CommRingCat.of K), ⊤) => m.hom x)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))).symm
  have eu := Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso
    (pullback.fst iX (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  have ebc := e ≪≫ (baseRestrictScalars
      (pullback.snd iX (Spec.map (CommRingCat.ofHom (algebraMap R K))))).mapIso
    (((_root_.SheafOfModules.evaluation _ (op ⊤)).rightDerived n).mapIso eu)
  refine Eq.trans (finrank_eq_finrank_baseRestrictScalars K
    (pullback.snd iX (Spec.map (CommRingCat.ofHom (algebraMap R K)))) _) ?_
  refine Eq.trans ?_ (finrank_eq_finrank_baseRestrictScalars R iX _).symm
  exact ebc.toLinearEquiv.finrank_eq.symm.trans
    (finrank_extendScalars_of_isFractionRing _ (isFractionRing_of_ringEquivs _ _ _ hnat) _)

/-! ### The cohomology of the generic fibre -/

/-- **The cohomology of the structure sheaf of the generic fibre of a regular proper model has the
rank of the cohomology of the structure sheaf of the model**:
`dim_K Hⁿ(C, 𝒪_C) = rank_R Hⁿ(X, 𝒪_X)` in every degree.

The curve `C` is identified with the categorical generic fibre over `Spec(K)` by the data of the
situation, and the two cohomologies of the generic fibre and of the model are then compared by
flat base change along the localization `R ⟶ K`. -/
theorem finrank_cohomologyOverField_genericFibre
    (S : Stacks.Models.RegularProperModelSituation.{u}) (n : ℕ) :
    Module.finrank S.K
        (AlgebraicGeometry.cohomologyOverField S.K S.C_to_K
          (SheafOfModules.unit S.C.ringCatSheaf) n) =
      Module.finrank S.R
        (Stacks.LocalCohomology.cohomologyOverBase.{u, u} S.R S.X_to_R
          (SheafOfModules.unit S.X.ringCatSheaf) n) := by
  rw [← S.genericFiberIso_over_K,
    AlgebraicGeometry.finrank_cohomologyOverField_unit_pushforward S.K S.genericFiberIso.hom
      (pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) n]
  exact finrank_cohomologyOverField_pullback_snd_unit S.R S.K S.X_to_R n

end Stacks.Models.GenericBaseChange

end

/-! ## The uniformizer sequence and the special fibre -/

section

open AlgebraicGeometry CategoryTheory Limits Opposite TensorProduct

namespace Stacks.Models

section ExactTransport

/-- Exactness survives postcomposition with an injective map sending zero to zero. -/
theorem exact_postcomp_injective {α β γ δ : Type*} [Zero γ] [Zero δ] {f : α → β} {g : β → γ}
    {v : γ → δ} (h : Function.Exact f g) (hv : Function.Injective v) (hv0 : v 0 = 0) :
    Function.Exact f (v ∘ g) := fun b => by
  refine Iff.trans ?_ (h b)
  exact ⟨fun hb => hv (by rw [hv0]; exact hb), fun hb => by
    change v (g b) = 0
    rw [hb, hv0]⟩

/-- Exactness survives precomposition with a surjection. -/
theorem exact_precomp_surjective {α α' β γ : Type*} [Zero γ] {f : α → β} {g : β → γ}
    {v : α' → α} (h : Function.Exact f g) (hv : Function.Surjective v) :
    Function.Exact (f ∘ v) g := fun b => by
  refine (h b).trans ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    obtain ⟨a', rfl⟩ := hv a
    exact ⟨a', ha⟩
  · rintro ⟨a', ha⟩
    exact ⟨v a', ha⟩

/-- Exactness is transported by a bijection of the middle term. -/
theorem exact_congr_middle_of_equiv {α β β' γ : Type*} [Zero γ] {f : α → β} {g : β → γ} (e : β ≃ β')
    (h : Function.Exact f g) : Function.Exact (e ∘ f) (g ∘ e.symm) := fun y => by
  refine (h (e.symm y)).trans ⟨?_, ?_⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [Function.comp_apply, hz, Equiv.apply_symm_apply]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz, Function.comp_apply, Equiv.symm_apply_apply]⟩

end ExactTransport

section Uniformizer

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (r : R)

/-- Multiplication by an element of the base ring on the structure sheaf. -/
theorem unitHomEquiv_symm_uniformizerSection :
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
        (Stacks.Models.uniformizerSection f r) =
      (Scheme.smulEnd X (AlgebraicGeometry.baseSection X f r)).asHom.app
        (SheafOfModules.unit X.ringCatSheaf) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  obtain ⟨V⟩ := U
  refine LinearMap.ext fun x => ?_
  have h1 := Scheme.Modules.unitHomEquiv_symm_app_apply
    (SheafOfModules.unit X.ringCatSheaf) (Stacks.Models.uniformizerSection f r) V x
  rw [h1, Scheme.Modules.map_eval_top (SheafOfModules.unit X.ringCatSheaf)
    (Stacks.Models.uniformizerSection f r) V]
  exact mul_comm (G := Γ(X, V)) x _

/-- The map induced on cohomology by multiplication by `r` is multiplication by `r`. -/
theorem rightDerived_map_uniformizerSection_apply (n : ℕ)
    (x : ((AlgebraicGeometry.moduleGlobalSections X).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :
    (((AlgebraicGeometry.moduleGlobalSections X).rightDerived n).map
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          (Stacks.Models.uniformizerSection f r))).hom x =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom r • x := by
  rw [unitHomEquiv_symm_uniformizerSection]
  have hbr : AlgebraicGeometry.baseSection X f r =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom r := by
    rw [AlgebraicGeometry.appLE_top_top_eq_appTop f (by simp)]
    rfl
  exact (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X
    (AlgebraicGeometry.baseSection X f r) n (SheafOfModules.unit X.ringCatSheaf) x).trans
    (by rw [hbr]; rfl)

end Uniformizer

section Model

open Stacks.Models

variable (S : RegularProperModelSituation.{u})

/-- The ring map through which the residue field acts on the cohomology of the special fibre. -/
abbrev specialFibreResidueMap : S.k →+* Γ(S.specialFiberIdeal.subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.k)).inv ≫
    (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl).appLE ⊤ ⊤ (by simp)).hom

/-- The ring map through which the base ring acts on the cohomology of the model. -/
abbrev modelBaseMap : S.R →+* Γ(S.X, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.X_to_R.appLE ⊤ ⊤ (by simp)).hom

/-- Compatibility: the residue field acts through the base ring. -/
theorem appTop_modelBaseMap (x : S.R) :
    (S.specialFiberIdeal.subschemeι.appTop).hom (modelBaseMap S x) =
      specialFibreResidueMap S (algebraMap S.R S.k x) := by
  have hres : specialFibreResidueMap S = S.fibreSubschemeResidueMap S.specialFiberIdeal le_rfl := by
    change ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl).appLE ⊤ ⊤ (by simp)).hom = _
    rw [AlgebraicGeometry.appLE_top_top_eq_appTop
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl) (by simp)]
    rfl
  have hbase : (S.specialFiberIdeal.subschemeι.appTop).hom (modelBaseMap S x) =
      S.fibreSubschemeBaseMap S.specialFiberIdeal x := by
    change _ = ((Scheme.ΓSpecIso (.of S.R)).inv ≫
      (S.specialFiberIdeal.subschemeι ≫ S.X_to_R).appTop).hom x
    rw [Scheme.Hom.comp_appTop]
    change (S.specialFiberIdeal.subschemeι.appTop).hom
      (((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.X_to_R.appLE ⊤ ⊤ (by simp)).hom x) = _
    rw [AlgebraicGeometry.appLE_top_top_eq_appTop S.X_to_R (by simp)]
    rfl
  rw [hres, hbase, ← S.fibreSubschemeResidueMap_comp S.specialFiberIdeal le_rfl]
  rfl

/-- The structure sheaf of the model restricted to the special fibre. -/
abbrev specialFibreStructureSheaf : S.specialFiberIdeal.subscheme.Modules :=
  (Scheme.Modules.pullback S.specialFiberIdeal.subschemeι).obj
    (SheafOfModules.unit S.X.ringCatSheaf)

/-- `Hⁿ(X, 𝒪_X)` as a module over the global functions of the model. -/
abbrev modelSectionsCohomology (n : ℕ) : ModuleCat.{u} Γ(S.X, ⊤) :=
  ((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).obj
    (SheafOfModules.unit S.X.ringCatSheaf)

/-- The `R`-module `Hⁿ(X, 𝒪_X)`. -/
abbrev modelCohomology (n : ℕ) : ModuleCat.{u} S.R :=
  (ModuleCat.restrictScalars (modelBaseMap S)).obj (modelSectionsCohomology S n)

/-- `Hⁿ(X_k, 𝒪_{X_k})` as a module over the global functions of the special fibre. -/
abbrev specialFibreCohomology (n : ℕ) : ModuleCat.{u} Γ(S.specialFiberIdeal.subscheme, ⊤) :=
  ((AlgebraicGeometry.moduleGlobalSections S.specialFiberIdeal.subscheme).rightDerived n).obj
    (specialFibreStructureSheaf S)

/-- The residue field acts on the cohomology of the special fibre. -/
instance module_residueField_specialFibreCohomology (n : ℕ) :
    Module S.k ↥(specialFibreCohomology S n) :=
  inferInstanceAs (Module S.k ↥(cohomologyOverField S.k
    (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl) (specialFibreStructureSheaf S) n))

/-- The base ring acts on the cohomology of the special fibre through the model. -/
instance module_base_specialFibreCohomology (n : ℕ) : Module S.R ↥(specialFibreCohomology S n) :=
  inferInstanceAs (Module S.R ↥((ModuleCat.restrictScalars (modelBaseMap S)).obj
    ((ModuleCat.restrictScalars S.specialFiberIdeal.subschemeι.appTop.hom).obj
      (specialFibreCohomology S n))))

/-- The base ring acts through the residue field. -/
instance isScalarTower_specialFibreCohomology (n : ℕ) :
    IsScalarTower S.R S.k ↥(specialFibreCohomology S n) :=
  IsScalarTower.of_algebraMap_smul fun r y => by
    change specialFibreResidueMap S (algebraMap S.R S.k r) • y =
      (S.specialFiberIdeal.subschemeι.appTop).hom (modelBaseMap S r) • y
    rw [appTop_modelBaseMap]

/-- The quotient map of the uniformizer sequence. -/
abbrev specialFibreQuotientMap : SheafOfModules.unit S.X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward S.specialFiberIdeal.subschemeι).obj
      (specialFibreStructureSheaf S) :=
  (Scheme.Modules.pullbackPushforwardAdjunction S.specialFiberIdeal.subschemeι).unit.app
    (SheafOfModules.unit S.X.ringCatSheaf)

/-- Cohomology does not change along the closed immersion of the special fibre. -/
abbrev specialFibreCohomologyIso (n : ℕ) :
    ((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).obj
        ((Scheme.Modules.pushforward S.specialFiberIdeal.subschemeι).obj
          (specialFibreStructureSheaf S)) ≅
      (ModuleCat.restrictScalars S.specialFiberIdeal.subschemeι.appTop.hom).obj
        (specialFibreCohomology S n) :=
  Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward
    S.specialFiberIdeal.subschemeι (specialFibreStructureSheaf S) n

/-- The map `Hⁿ(X, 𝒪_X) ⟶ Hⁿ(X_k, 𝒪_{X_k})` of the uniformizer sequence. -/
def specialFibreCohomologyMap (n : ℕ) :
    ↥(modelCohomology S n) →ₗ[S.R] ↥(specialFibreCohomology S n) :=
  ((ModuleCat.restrictScalars (modelBaseMap S)).map
    (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).map (specialFibreQuotientMap S) ≫
      (specialFibreCohomologyIso S n).hom)).hom

/-- A uniformizer dies in the residue field. -/
theorem algebraMap_pi_eq_zero : algebraMap S.R S.k S.π = 0 :=
  (S.algebraMap_eq_zero_iff S.π).mpr
    (by rw [S.maximalIdeal_eq_span_pi]; exact Ideal.mem_span_singleton_self _)

/-- The cohomology of the special fibre is finite dimensional over the residue field. -/
instance finiteDimensional_specialFibreCohomology (n : ℕ) :
    FiniteDimensional S.k ↥(specialFibreCohomology S n) :=
  haveI : FiniteDimensional S.k ↥(cohomologyOverField S.k
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
      (SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf) n) :=
    AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper S.k
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl) _
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
        (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)) n
  (AlgebraicGeometry.cohomologyOverFieldIso S.k
    (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
    (Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso
      S.specialFiberIdeal.subschemeι) n).toLinearEquiv.symm.finiteDimensional

/-- **The uniformizer sequence** `0 ⟶ 𝒪_X --π--> 𝒪_X ⟶ i_*𝒪_{X_k} ⟶ 0` is short exact. -/
private theorem shortExact_uniformizer_sequence :
    ∃ h, (ShortComplex.mk ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
      (uniformizerSection S.X_to_R S.π)) (specialFibreQuotientMap S) h).ShortExact := by
  have hs := AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection S.X
    (SheafOfModules.unit S.X.ringCatSheaf) (uniformizerSection S.X_to_R S.π)
    (isRegularSection_uniformizerSection (k := S.k) S.residueEquiv S.X_to_R S.uniformizer)
  dsimp only at hs
  rw [zeroScheme_uniformizer_eq_specialFiberIdeal S] at hs
  exact hs

/-- **The special fibre count, from the exactness of the uniformizer sequence.** -/
theorem specialBetti_count_of_exact (n : ℕ)
    (d : ↥(specialFibreCohomology S n) →ₗ[S.R] ↥(modelCohomology S (n + 1)))
    (h1 : Function.Exact
      (S.π • (LinearMap.id : ↥(modelCohomology S n) →ₗ[S.R] ↥(modelCohomology S n)))
      (specialFibreCohomologyMap S n))
    (h2 : Function.Exact (specialFibreCohomologyMap S n) d)
    (h3 : Function.Exact d
      (S.π • (LinearMap.id : ↥(modelCohomology S (n + 1)) →ₗ[S.R] ↥(modelCohomology S (n + 1))))) :
    Module.finrank S.k ↥(specialFibreCohomology S n) =
      Module.finrank S.k (S.k ⊗[S.R] ↥(modelCohomology S n)) +
        Module.finrank S.k
          (S.k ⊗[S.R] ↥(Submodule.torsionBy S.R ↥(modelCohomology S (n + 1)) S.π)) :=
  Stacks.Models.ExactCount.finrank_eq_add_finrank_tensorTorsionBy
    S.surjective_algebraMap (algebraMap_pi_eq_zero S) (specialFibreCohomologyMap S n) d h1 h2 h3

/-- **The special fibre count.** -/
theorem specialBetti_count (n : ℕ) :
    Module.finrank S.k ↥(specialFibreCohomology S n) =
      Module.finrank S.k (S.k ⊗[S.R] ↥(modelCohomology S n)) +
        Module.finrank S.k
          (S.k ⊗[S.R] ↥(Submodule.torsionBy S.R ↥(modelCohomology S (n + 1)) S.π)) := by
  obtain ⟨hz, hse⟩ := shortExact_uniformizer_sequence S
  have hex1 : Function.Exact
      ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).map
        ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
          (uniformizerSection S.X_to_R S.π))).hom)
      ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).map
        (specialFibreQuotientMap S)).hom) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).exact_map hse n)
  have hex2 : Function.Exact
      ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).map
        (specialFibreQuotientMap S)).hom)
      (((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).δ hse n).hom) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).exact_δ₁ hse n)
  have hex3 : Function.Exact
      (((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).δ hse n).hom)
      ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived (n + 1)).map
        ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
          (uniformizerSection S.X_to_R S.π))).hom) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).exact_δ₂ hse n)
  have hR : ∀ (m : ℕ) (b : ↥(modelCohomology S m)),
      (b ∈ Set.range ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived m).map
          ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
            (uniformizerSection S.X_to_R S.π))).hom)) ↔
        b ∈ Set.range
          (S.π • (LinearMap.id : ↥(modelCohomology S m) →ₗ[S.R] ↥(modelCohomology S m))) :=
    fun m _ =>
      ⟨fun ⟨z, hz⟩ =>
          ⟨z, (rightDerived_map_uniformizerSection_apply S.X_to_R S.π m z).symm.trans hz⟩,
        fun ⟨z, hz⟩ => ⟨z, (rightDerived_map_uniformizerSection_apply S.X_to_R S.π m z).trans hz⟩⟩
  refine specialBetti_count_of_exact S n
    (((ModuleCat.restrictScalars (modelBaseMap S)).map ((specialFibreCohomologyIso S n).inv ≫
      (Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).δ hse n)).hom)
    (fun b => ?_) ?_ (fun b => ?_)
  · exact (exact_postcomp_injective hex1 (specialFibreCohomologyIso S n).toLinearEquiv.injective
      (map_zero _) b).trans (hR n b)
  · exact exact_congr_middle_of_equiv (specialFibreCohomologyIso S n).toLinearEquiv.toEquiv hex2
  · refine Iff.trans ?_ (exact_precomp_surjective hex3
      (specialFibreCohomologyIso S n).toLinearEquiv.symm.surjective b)
    rw [rightDerived_map_uniformizerSection_apply S.X_to_R S.π (n + 1) b]
    exact Iff.rfl

/-- The count is the Betti number of the special fibre: the pullback of the structure sheaf of
the model to the special fibre is the structure sheaf of the special fibre. -/
theorem finrank_specialFibreCohomology_eq_specialBetti (n : ℕ) :
    Module.finrank S.k ↥(specialFibreCohomology S n) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
        (SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf) n) :=
  AlgebraicGeometry.finrank_cohomologyOverField_eq_of_iso S.k
    (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
    (Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso
      S.specialFiberIdeal.subschemeι) n

/-- **A uniformizer acts injectively on `H⁰(X, 𝒪_X)`**: the uniformizer sequence begins with a
monomorphism and global sections is left exact. -/
theorem torsionBy_modelCohomology_zero :
    Submodule.torsionBy S.R ↥(modelCohomology S 0) S.π = ⊥ := by
  obtain ⟨hz, hse⟩ := shortExact_uniformizer_sequence S
  have hmono : Function.Injective
      ((((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived 0).map
        ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
          (uniformizerSection S.X_to_R S.π))).hom) :=
    (ModuleCat.mono_iff_injective _).1
      ((Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor S.X).mono_map_f hse)
  refine le_antisymm (fun x hx => ?_) bot_le
  have h0 : (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived 0).map
      ((SheafOfModules.unit S.X.ringCatSheaf).unitHomEquiv.symm
        (uniformizerSection S.X_to_R S.π))).hom x = 0 :=
    (rightDerived_map_uniformizerSection_apply S.X_to_R S.π 0 x).trans
      ((Submodule.mem_torsionBy_iff S.π x).1 hx)
  exact (Submodule.mem_bot S.R).2 (hmono (h0.trans (map_zero _).symm))

end Model

end Stacks.Models

end


/-! ## The comparison of the Euler characteristics of the two fibres -/

section

open AlgebraicGeometry CategoryTheory Limits Opposite TensorProduct

namespace Stacks.Models

/-- The telescoping sum `∑_{n<m} (-1)ⁿ (c n + c (n+1)) = c 0 - (-1)ᵐ c m`. -/
theorem sum_range_alternating_add_succ (c : ℕ → ℕ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * ((c n : ℤ) + (c (n + 1) : ℤ)) =
      (c 0 : ℤ) - (-1) ^ m * (c m : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- **The bookkeeping behind the comparison of the two fibres.** If `b n = a n + c n + c (n+1)`
for every `n`, if `c 0 = 0`, and if `a` and `c` vanish from `N` on, then the alternating sums of
`a` and of `b` agree: the two shifted copies of `c` telescope away. -/
theorem finsum_alternating_eq_of_shift (a b c : ℕ → ℕ) (N : ℕ)
    (hb : ∀ n, b n = a n + c n + c (n + 1)) (hc0 : c 0 = 0) (ha : ∀ n, N ≤ n → a n = 0)
    (hc : ∀ n, N ≤ n → c n = 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (b n : ℤ)) = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (a n : ℤ) := by
  have hbz : ∀ n, N ≤ n → b n = 0 := fun n hn => by
    rw [hb n, ha n hn, hc n hn, hc (n + 1) (le_trans hn (Nat.le_succ n))]
  have hfin : ∀ f : ℕ → ℕ, (∀ n, N ≤ n → f n = 0) →
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (f n : ℤ)) = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (f n : ℤ) :=
    fun f hf => finsum_eq_sum_of_support_subset _ fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      exact hn (by simp [hf n (not_lt.mp hcon)])
  rw [hfin a ha, hfin b hbz]
  have key : ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (b n : ℤ) =
      (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (a n : ℤ)) +
        ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * ((c n : ℤ) + (c (n + 1) : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hb n]
    push_cast
    ring
  rw [key, sum_range_alternating_add_succ c N, hc0, hc N le_rfl]
  simp

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- `dim_K Hⁿ(C, 𝒪_C)`, the `n`-th Betti number of the generic fibre. -/
abbrev genericBetti (n : ℕ) : ℕ :=
  Module.finrank S.K (cohomologyOverField S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) n)

/-- `dim_k Hⁿ(X_k, 𝒪_{X_k})`, the `n`-th Betti number of the special fibre. -/
abbrev specialBetti (n : ℕ) : ℕ :=
  Module.finrank S.k (cohomologyOverField S.k (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
    (SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf) n)

/-- The correction term `dim_k Hⁿ(X, 𝒪_X)[π]` measuring the `π`-torsion in degree `n`. -/
abbrev torsionBetti (n : ℕ) : ℕ :=
  Module.finrank S.k (S.k ⊗[S.R] ↥(Submodule.torsionBy S.R ↥(modelCohomology S n) S.π))

/-- **The cohomology of the structure sheaf of the model vanishes in large degrees.** The model
is proper over the affine base `Spec R`, so there is a single degree beyond which the cohomology
of every quasi-coherent module vanishes. -/
theorem exists_isZero_modelCohomology : ∃ N : ℕ, ∀ n, N ≤ n → IsZero (modelCohomology S n) := by
  obtain ⟨N, hN⟩ :=
    AlgebraicGeometry.exists_isZero_rightDerived_moduleGlobalSections_of_isProper S.R S.X_to_R
  exact ⟨N, fun n hn =>
    Functor.map_isZero _ (hN (SheafOfModules.unit S.X.ringCatSheaf) inferInstance n hn)⟩

/-- **[Stacks, Tag 02O6] for the model.** `Hⁿ(X, 𝒪_X)` is a finite `R`-module. -/
theorem moduleFinite_modelCohomology (n : ℕ) : Module.Finite S.R ↥(modelCohomology S n) := by
  have : IsLocallyNoetherian (Spec (CommRingCat.of S.R)) := inferInstance
  have hln : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.X_to_R
  have : (SheafOfModules.unit S.X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := S.X)
  have h := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology S.X_to_R
    (SheafOfModules.unit S.X.ringCatSheaf) n
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).2
  have h2 := Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom hsurj
    ((ModuleCat.restrictScalars (Scheme.Hom.appTop S.X_to_R).hom).obj
      (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).obj
        (SheafOfModules.unit S.X.ringCatSheaf)))
  change Module.Finite S.R
    ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of S.R)).inv ≫
        S.X_to_R.appLE ⊤ ⊤ (by simp)).hom).obj
      (((AlgebraicGeometry.moduleGlobalSections S.X).rightDerived n).obj
        (SheafOfModules.unit S.X.ringCatSheaf)))
  rw [AlgebraicGeometry.appLE_top_top_eq_appTop S.X_to_R (by simp)]
  exact h2

/-- **The generic Betti number is the rank of the cohomology of the model**, by flat base change
along the localization `R ⟶ K`. -/
theorem genericBetti_eq (n : ℕ) : genericBetti S n = Module.finrank S.R ↥(modelCohomology S n) :=
  Stacks.Models.GenericBaseChange.finrank_cohomologyOverField_genericFibre S n

/-- The torsion correction vanishes in degree zero. -/
theorem torsionBetti_zero : torsionBetti S 0 = 0 := by
  have h := torsionBy_modelCohomology_zero S
  have : Subsingleton ↥(Submodule.torsionBy S.R ↥(modelCohomology S 0) S.π) := by
    rw [h]; infer_instance
  exact Stacks.Models.DVRArith.finrank_tensor_eq_zero_of_subsingleton

/-- **The special Betti number splits as the reduction plus the torsion of the next degree.** -/
theorem specialBetti_eq (n : ℕ) :
    specialBetti S n = genericBetti S n + torsionBetti S n + torsionBetti S (n + 1) := by
  have := moduleFinite_modelCohomology S n
  calc specialBetti S n
      = Module.finrank S.k ↥(specialFibreCohomology S n) :=
        (finrank_specialFibreCohomology_eq_specialBetti S n).symm
    _ = Module.finrank S.k (S.k ⊗[S.R] ↥(modelCohomology S n)) + torsionBetti S (n + 1) :=
        specialBetti_count S n
    _ = Module.finrank S.R ↥(modelCohomology S n) + torsionBetti S n + torsionBetti S (n + 1) := by
        rw [Stacks.Models.DVRArith.finrank_tensorResidue_eq S.R S.k S.surjective_algebraMap
          S.uniformizer (algebraMap_pi_eq_zero S) ↥(modelCohomology S n)]
    _ = genericBetti S n + torsionBetti S n + torsionBetti S (n + 1) := by
        rw [genericBetti_eq S n]

/-- **The Euler characteristic of the structure sheaf is the same on the generic fibre and on
the special fibre of a regular proper model.** -/
@[sga "6 X 7.5" "special case"]
theorem eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre
    [IsProper S.C_to_K] [(SheafOfModules.unit S.C.ringCatSheaf).IsCoherent]
    [(SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf).IsCoherent] :
    eulerCharacteristic S.K S.C_to_K (SheafOfModules.unit S.C.ringCatSheaf) =
      eulerCharacteristic S.k (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
        (SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf) := by
  obtain ⟨N, hN⟩ := exists_isZero_modelCohomology S
  refine (eulerCharacteristic_eq_finsum S.K S.C_to_K _).trans
    (Eq.trans ?_ (eulerCharacteristic_eq_finsum S.k
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl) _).symm)
  refine (finsum_alternating_eq_of_shift (genericBetti S) (specialBetti S) (torsionBetti S) N
    (specialBetti_eq S) (torsionBetti_zero S) (fun n hn => ?_) (fun n hn => ?_)).symm
  · rw [genericBetti_eq S n]
    have := ModuleCat.subsingleton_of_isZero (hN n hn)
    exact Module.finrank_zero_of_subsingleton
  · have := ModuleCat.subsingleton_of_isZero (hN n hn)
    have := Stacks.Models.DVRArith.subsingleton_submodule
      (Submodule.torsionBy S.R ↥(modelCohomology S n) S.π)
    exact Stacks.Models.DVRArith.finrank_tensor_eq_zero_of_subsingleton

end RegularProperModelSituation

end Stacks.Models

end

end
