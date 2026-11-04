module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroLevelwise
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTaylorHorizontal
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsHorizontal

/-!
# The coface `⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is horizontal when it is a Taylor series

`Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_of_horizontal` reduces the
compatibility of the base-change connections of a cosimplicial module `M(•)` with every transition
map to one statement: the transition `M(0) ⟶ M(1)` along `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` carries `∇` to the
base-change connection `∇₁` of `M(1)`.  This module proves that statement as soon as the
transition is the Taylor series of `∇`:

`M(δ)(m) = ∑_K ξ^{[K]} · M(σ)(θ_K m)`,      `ξ_i = δ(x_i) - σ(x_i)`,

where `σ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 0` is the coprojection, `θ_i` are the coordinate operators of `∇` in the
coordinates `d x_i` and `θ_K` their composites.  This is the horizontality of the stratification of
a crystal, which in the proof of [Stacks, Lemma 60.17.3, Tag 07JG] is how the connection is
defined from the crystal; here it is the last input of the double complex of
[Stacks, Proposition 60.21.3, Tag 07LG].

The argument is the one of `Crystalline.taylorDeriv_eq_sum`, run at each level `pⁿ`: there only
finitely many `θ_K m` survive, all below one multi-index `L`, and both sides become finite sums
over the box `K ≤ L` and the support of `L`.

## Main results

* `Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_delta_of_taylor` — **the coface
  `δ` is horizontal**, given the Taylor expansion of `M(δ)`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Simplicial DividedPowers
open scoped TensorProduct

namespace Crystalline

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

/-- The universal differential of a cosimplicial degree kills the powers of `p`. -/
theorem differential_natCast_pow (b n : ℕ) :
    E.differential p b ((p : E.completedRing p b) ^ n) = 0 := by
  rw [← Nat.cast_pow]
  induction p ^ n with
  | zero => simpa using E.differential_add p b 0 0
  | succ k ih => rw [Nat.cast_succ, E.differential_add, ih, E.differential_one, add_zero]

/-- A semilinear map carries `pⁿ` multiples to `pⁿ` multiples. -/
theorem map_mem_pPowSmul_of_semilinear {R R' : Type*} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R' Y]
    (g : X →ₛₗ[σ] Y) {n : ℕ} {y : X} (hy : y ∈ pPowSmul p R X n) : g y ∈ pPowSmul p R' Y n := by
  obtain ⟨z, rfl⟩ := (mem_pPowSmul_iff p R X).mp hy
  refine (mem_pPowSmul_iff p R' Y).mpr ⟨g z, ?_⟩
  rw [g.map_smulₛₗ, map_pow, map_natCast]

/-- A pure tensor whose left factor is a scalar multiple of an element of `pⁿ M` vanishes at the
level `n`. -/
theorem toCompletedTensor_smul_tmul_val_eq_zero {R : Type*} [CommRing R] {X Ω : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Ω] [Module R Ω] (n : ℕ) (b : R) {y : X}
    (hy : y ∈ pPowSmul p R X n) (ω : Ω) :
    (toCompletedTensor p R Ω X ((b • y) ⊗ₜ[R] ω)).val n = 0 :=
  CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul p R Ω X n ω
    (Submodule.smul_mem _ b hy)

/-- **The base-change connection of degree one is local at the levels**: it carries `pⁿ M(1)`
into elements vanishing at the level `n`, `p` being killed by the universal differential. -/
theorem baseChangeConnection_one_val_eq_zero (n : ℕ) {y : V.carrier 1}
    (hy : y ∈ pPowSmul p (E.completedRing p 1) (V.carrier 1) n) :
    (V.baseChangeConnection nabla beta 1 y).val n = 0 :=
  (V.baseChangeConnection nabla beta 1).val_eq_zero_of_mem_pPowSmul p
    (differential_natCast_pow (E := E) 1) n hy

/-- The base-change connection of degree one, at the level `n`, depends only on its argument
modulo `pⁿ`. -/
theorem baseChangeConnection_one_val_congr (n : ℕ) {y y' : V.carrier 1}
    (h : y - y' ∈ pPowSmul p (E.completedRing p 1) (V.carrier 1) n) :
    (V.baseChangeConnection nabla beta 1 y).val n =
      (V.baseChangeConnection nabla beta 1 y').val n :=
  (V.baseChangeConnection nabla beta 1).val_congr_of_sub_mem p
    (differential_natCast_pow (E := E) 1) n h

/-! ### The Taylor expansion and the horizontality of the coface -/

section Taylor

variable {ι : Type u} [DecidableEq ι] (x : ι → E.carrier 0)
  (theta : (ι →₀ ℕ) → V.carrier 0 →+ V.carrier 0)

/-- The divided power ring of the cosimplicial degree `1`. -/
abbrev degreeOneDPRing : DividedPowerRing.{u} :=
  DividedPowerRing.of (E.carrier 1) (E.ideal 1) (E.dividedPowers 1)

/-- The coordinate differences `ξ_i = σ(x_i) - δ(x_i)` in the cosimplicial degree `1`, that is
`x_i ⊗ 1 - 1 ⊗ x_i`, as in [Stacks, Tag 07JG]. -/
def coordinateDifference (i : ι) : E.carrier 1 :=
  E.map (CosimplicialDPAlgebra.coprojection 1) (x i) - E.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (x i)

/-- The completed divided power monomials `ξ^{[K]}` of the coordinate differences. -/
def taylorCoefficient (K : ι →₀ ℕ) : E.completedRing p 1 :=
  AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
    (taylorMonomial (degreeOneDPRing (E := E)) (coordinateDifference x) K)

omit [DecidableEq ι] in
/-- **The derivative of a divided power monomial of the coordinate differences**:
`d(ξ^{[K]}) = ∑_{i} ξ^{[K - e_i]} d(ξ_i)`, the divided power chain rule
(`Crystalline.dividedPowerDerivation_taylorMonomial`) for the universal differential of the
completion. -/
theorem differential_taylorCoefficient (hξ : ∀ i, coordinateDifference x i ∈ E.ideal 1)
    (K : ι →₀ ℕ) :
    E.differential p 1 (taylorCoefficient (p := p) x K) =
      ∑ i ∈ K.support, taylorCoefficient (p := p) x (K - Finsupp.single i 1) •
        E.differential p 1
          (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
            (coordinateDifference x i)) := by
  have h := dividedPowerDerivation_taylorMonomial
    (completedFormsDPDerivation p A (E.dividedPowers 1)) (xi := coordinateDifference x) hξ K
  simp only at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  exact (adicCompletion_algebraMap_smul p A (E.dividedPowers 1) _ _).symm

/-- The universal differential of the completed degree `b` is additive. -/
theorem differential_sub' (b : ℕ) (y z : E.completedRing p b) :
    E.differential p b (y - z) = E.differential p b y - E.differential p b z := by
  have h := E.differential_add p b (y - z) z
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

omit [DecidableEq ι] in
/-- **The differential of `δ(x_i)`** is the differential of `σ(x_i)` minus the differential of the
coordinate difference `ξ_i`. -/
theorem differential_map_delta_eq (i : ι) :
    E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
        (E.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (x i))) =
      E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
          (E.map (CosimplicialDPAlgebra.coprojection 1) (x i))) -
        E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
          (coordinateDifference x i)) := by
  rw [← differential_sub', ← map_sub, coordinateDifference, sub_sub_cancel]

/-- **A coface carries the coordinate differential `d x_i` to `d φ(x_i)`**, on pure tensors of
the double complex. -/
theorem tensorMap_tmul_differential_of (φ : ⦋0⦌ ⟶ ⦋1⦌) (z : V.carrier 0) (y : E.carrier 0) :
    V.tensorMap φ 1 (toCompletedTensor p (E.completedRing p 0) (E.forms p 1 0) (V.carrier 0)
        (z ⊗ₜ[E.completedRing p 0] E.differential p 0
          (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p) (E.carrier 0) y))) =
      toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        (V.map φ z ⊗ₜ[E.completedRing p 1] E.differential p 1
          (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1) (E.map φ y))) := by
  rw [V.tensorMap_of_tmul φ 1 z, E.formsMap_differential p φ]
  congr 3

/-- A scalar crosses into the left factor of a pure tensor of a completed tensor product. -/
theorem smul_toCompletedTensor_tmul {R : Type*} [CommRing R] {X Ω : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Ω] [Module R Ω] (c : R) (y : X) (ω : Ω) :
    c • toCompletedTensor p R Ω X (y ⊗ₜ[R] ω) = toCompletedTensor p R Ω X ((c • y) ⊗ₜ[R] ω) := by
  rw [← map_smul, TensorProduct.smul_tmul']

/-- A pure tensor at the level `n` depends only on its left factor modulo `pⁿ`. -/
theorem toCompletedTensor_tmul_val_congr {R : Type*} [CommRing R] {X Ω : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Ω] [Module R Ω] (n : ℕ) {y y' : X} (h : y - y' ∈ pPowSmul p R X n)
    (ω : Ω) :
    (toCompletedTensor p R Ω X (y ⊗ₜ[R] ω)).val n =
      (toCompletedTensor p R Ω X (y' ⊗ₜ[R] ω)).val n := by
  have h0 := CompletedDeRham.toCompletedTensor_tmul_val_eq_zero_of_mem_pPowSmul p R Ω X n ω h
  rwa [TensorProduct.sub_tmul, map_sub, AdicCompletion.val_sub_apply, sub_eq_zero] at h0

/-- A pure tensor with left factor `b • g(-z)` is minus the one with left factor `b • g z`. -/
private theorem toCompletedTensor_smul_map_neg_tmul {R R' : Type*} [CommRing R] [CommRing R']
    {σ : R →+* R'} {X Y Ω : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R' Y]
    [AddCommGroup Ω] [Module R' Ω] (g : X →ₛₗ[σ] Y) (b : R') (z : X) (ω : Ω) :
    toCompletedTensor p R' Ω Y ((b • g (-z)) ⊗ₜ[R'] ω) =
      -toCompletedTensor p R' Ω Y ((b • g z) ⊗ₜ[R'] ω) := by
  rw [g.map_neg, smul_neg, TensorProduct.neg_tmul, map_neg]

/-- The level-`n` value of `(b • g(-z)) ⊗ ω` is minus that of `(b • g z) ⊗ ω`. -/
theorem toCompletedTensor_smul_map_neg_tmul_val {R R' : Type*} [CommRing R] [CommRing R']
    {σ : R →+* R'} {X Y Ω : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R' Y]
    [AddCommGroup Ω] [Module R' Ω] (g : X →ₛₗ[σ] Y) (n : ℕ) (b : R') (z : X) (ω : Ω) :
    (toCompletedTensor p R' Ω Y ((b • g (-z)) ⊗ₜ[R'] ω)).val n =
      -(toCompletedTensor p R' Ω Y ((b • g z) ⊗ₜ[R'] ω)).val n := by
  rw [toCompletedTensor_smul_map_neg_tmul, AdicCompletion.val_neg_apply]

/-- `(b • g(-z)) ⊗ (ω - η) = (b • g(-z)) ⊗ ω + (b • g z) ⊗ η`. -/
theorem toCompletedTensor_smul_map_neg_tmul_sub {R R' : Type*} [CommRing R] [CommRing R']
    {σ : R →+* R'} {X Y Ω : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R' Y]
    [AddCommGroup Ω] [Module R' Ω] (g : X →ₛₗ[σ] Y) (b : R') (z : X) (ω η : Ω) :
    toCompletedTensor p R' Ω Y ((b • g (-z)) ⊗ₜ[R'] (ω - η)) =
      toCompletedTensor p R' Ω Y ((b • g (-z)) ⊗ₜ[R'] ω) +
        toCompletedTensor p R' Ω Y ((b • g z) ⊗ₜ[R'] η) := by
  rw [TensorProduct.tmul_sub, map_sub, sub_eq_add_neg, toCompletedTensor_smul_map_neg_tmul _ _ _ η,
    neg_neg]

/-- The level-`n` value of a pure tensor is additive in the right factor. -/
theorem toCompletedTensor_tmul_sub_val {R : Type*} [CommRing R] {Y Ω : Type*} [AddCommGroup Y]
    [Module R Y] [AddCommGroup Ω] [Module R Ω] (n : ℕ) (y : Y) (ω η : Ω) :
    (toCompletedTensor p R Ω Y (y ⊗ₜ[R] (ω - η))).val n =
      (toCompletedTensor p R Ω Y (y ⊗ₜ[R] ω)).val n -
        (toCompletedTensor p R Ω Y (y ⊗ₜ[R] η)).val n := by
  rw [TensorProduct.tmul_sub, (toCompletedTensor p R Ω Y).map_sub, AdicCompletion.val_sub_apply]

section Expansions

variable (hθ : ∀ (K L : ι →₀ ℕ) (m : V.carrier 0), theta L (theta K m) = theta (K + L) m)

/-- The coordinate differential `d σ(x_i)` of the degree `1`. -/
abbrev sigmaDx (i : ι) : E.forms p 1 1 :=
  E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
    (E.map (CosimplicialDPAlgebra.coprojection 1) (x i)))

/-- The differential `d ξ_i` of a coordinate difference. -/
abbrev xiDx (i : ι) : E.forms p 1 1 :=
  E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
    (coordinateDifference x i))

omit [DecidableEq ι] in
include hθ in
/-- **The coprojection on a coordinate expansion of `∇ (θ_K m)`**, multiplied by a scalar. -/
theorem smul_tensorMap_coprojection_expansion (c : E.completedRing p 1) (K : ι →₀ ℕ)
    (m : V.carrier 0) (t : Finset ι) :
    c • V.tensorMap (CosimplicialDPAlgebra.coprojection 1) 1
        (∑ i ∈ t, toCompletedTensor p (E.completedRing p 0) (E.forms p 1 0) (V.carrier 0)
          ((-theta (Finsupp.single i 1) (theta K m)) ⊗ₜ[E.completedRing p 0]
            E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
              (E.carrier 0) (x i)))) =
      ∑ i ∈ t, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        ((c • V.map (CosimplicialDPAlgebra.coprojection 1)
          (-theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1] sigmaDx (p := p) x i) := by
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tensorMap_tmul_differential_of, smul_toCompletedTensor_tmul, hθ]

omit [DecidableEq ι] in
/-- **The coface `δ` on a coordinate expansion of `∇ m`.** -/
theorem tensorMap_delta_expansion (m : V.carrier 0) (t : Finset ι) :
    V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1
        (∑ i ∈ t, toCompletedTensor p (E.completedRing p 0) (E.forms p 1 0) (V.carrier 0)
          ((-theta (Finsupp.single i 1) m) ⊗ₜ[E.completedRing p 0]
            E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
              (E.carrier 0) (x i)))) =
      ∑ i ∈ t, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (-theta (Finsupp.single i 1) m)
          ⊗ₜ[E.completedRing p 1] E.differential p 1
            (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
              (E.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (x i)))) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => tensorMap_tmul_differential_of V _ _ _

omit [DecidableEq ι] in
include hθ in
/-- **The Taylor series of `δ(-θ_i m)` tensored with `d δ(x_i)`**, split along
`d δ(x_i) = d σ(x_i) - d ξ_i`. -/
theorem taylorSum_tmul_differential_delta (S : Finset (ι →₀ ℕ)) (m : V.carrier 0) (i : ι) :
    toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        ((∑ K ∈ S, taylorCoefficient (p := p) x K •
            V.map (CosimplicialDPAlgebra.coprojection 1)
              (theta K (-theta (Finsupp.single i 1) m))) ⊗ₜ[E.completedRing p 1]
          E.differential p 1 (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
            (E.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (x i)))) =
      ∑ K ∈ S, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
          ((taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1)
            (-theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1]
              sigmaDx (p := p) x i) +
        ∑ K ∈ S, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
          ((taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1)
            (theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1] xiDx (p := p) x i) := by
  rw [differential_map_delta_eq, TensorProduct.sum_tmul, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [(theta K).map_neg, hθ, add_comm (Finsupp.single i 1) K]
  exact toCompletedTensor_smul_map_neg_tmul_sub _ _ _ _ _

/-- **The differentiated Taylor series at the level `n`**:
`∑_{K ≤ L} σ(θ_K m) ⊗ d(ξ^{[K]}) = ∑_{i ∈ t} ∑_{K ≤ L} ξ^{[K]} σ(θ_{K + e_i} m) ⊗ d ξ_i`
at the level
`n`, when the `θ_K m` outside the box `K ≤ L` lie in `pⁿ M(0)`. -/
theorem taylorDeriv_sum_val (hξ : ∀ i, coordinateDifference x i ∈ E.ideal 1) (m : V.carrier 0)
    (n : ℕ) (L : ι →₀ ℕ) (t : Finset ι) (ht : L.support ⊆ t)
    (hvan : ∀ K, ¬ K ≤ L → theta K m ∈ pPowSmul p (E.completedRing p 0) (V.carrier 0) n) :
    (∑ K ∈ Finset.Iic L, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        (V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m) ⊗ₜ[E.completedRing p 1]
          E.differential p 1 (taylorCoefficient (p := p) x K))).val n =
      (∑ i ∈ t, ∑ K ∈ Finset.Iic L,
        toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
          ((taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1)
            (theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1]
              xiDx (p := p) x i)).val n :=
  taylorDeriv_toCompletedTensor_val p n (taylorCoefficient (p := p) x)
    (E.differential p 1)
    (fun i => AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
      (coordinateDifference x i))
    (differential_taylorCoefficient x hξ)
    (fun K => V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m)) L
    (fun K hK => map_mem_pPowSmul_of_semilinear (V.map (CosimplicialDPAlgebra.coprojection 1))
      (hvan K hK)) t ht

omit [DecidableEq ι] in
include hbeta in
/-- **The base-change connection on a Taylor sum**, by the Leibniz rule term by term. -/
theorem baseChangeConnection_one_taylorSum (m : V.carrier 0) (S : Finset (ι →₀ ℕ)) :
    V.baseChangeConnection nabla beta 1 (∑ K ∈ S,
        taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m)) =
      ∑ K ∈ S, (taylorCoefficient (p := p) x K •
          V.tensorMap (CosimplicialDPAlgebra.coprojection 1) 1 (nabla (theta K m)) +
        toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
          (V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m) ⊗ₜ[E.completedRing p 1]
            E.differential p 1 (taylorCoefficient (p := p) x K))) :=
  (map_sum (AddMonoidHom.mk' (fun y => V.baseChangeConnection nabla beta 1 y)
    fun a b => (V.baseChangeConnection nabla beta 1).map_add a b) _ _).trans
    (Finset.sum_congr rfl fun K _ => ((V.baseChangeConnection nabla beta 1).leibniz
      (taylorCoefficient (p := p) x K)
      (V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m))).trans (by
        rw [V.baseChangeConnection_map_coprojection nabla beta hbeta 1 (theta K m)]))

omit [DecidableEq ι] in
include hθ in
/-- **The coprojection on a level-`n` coordinate expansion of `∇ (θ_K m)`**, multiplied by
`ξ^{[K]}`, at the level `n`. -/
theorem smul_tensorMap_coprojection_val (n : ℕ) (K : ι →₀ ℕ) (m : V.carrier 0) (t : Finset ι)
    (hexp : CompletedDeRham.IsLevelExpansionAt p (E.completedRing p 0) (E.forms p 1 0)
      (fun i => E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
        (E.carrier 0) (x i))) nabla (fun i m => -theta (Finsupp.single i 1) m) n t
      (theta K m)) :
    (taylorCoefficient (p := p) x K •
        V.tensorMap (CosimplicialDPAlgebra.coprojection 1) 1 (nabla (theta K m))).val n =
      (∑ i ∈ t, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        ((taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1)
          (-theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1]
            sigmaDx (p := p) x i)).val n :=
  (addMonoidHom_val_congr p (AddMonoidHom.mk' (fun X => taylorCoefficient (p := p) x K •
      V.tensorMap (CosimplicialDPAlgebra.coprojection 1) 1 X) fun X Y => by
        rw [map_add, smul_add]) n hexp).trans
    (congrArg (fun X => X.val n) (smul_tensorMap_coprojection_expansion V x theta hθ _ K m t))

omit [DecidableEq ι] in
include hθ in
/-- **The Taylor series of `δ(-θ_i m)` tensored with `d δ(x_i)`, at the level `n`**, given that
the Taylor sum over `S` agrees with `δ(-θ_i m)` modulo `pⁿ`. -/
theorem taylorSum_tmul_differential_delta_val (n : ℕ) (S : Finset (ι →₀ ℕ)) (m : V.carrier 0)
    (i : ι) (h : V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (-theta (Finsupp.single i 1) m) -
        ∑ K ∈ S, taylorCoefficient (p := p) x K • V.map (CosimplicialDPAlgebra.coprojection 1)
          (theta K (-theta (Finsupp.single i 1) m)) ∈
      pPowSmul p (E.completedRing p 1) (V.carrier 1) n) :
    (toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1) (V.carrier 1)
        (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (-theta (Finsupp.single i 1) m)
          ⊗ₜ[E.completedRing p 1] E.differential p 1
            (AdicCompletion.of (pAdicIdeal (A := E.carrier 1) p) (E.carrier 1)
              (E.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) (x i))))).val n =
      (∑ K ∈ S, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1)
          (V.carrier 1) ((taylorCoefficient (p := p) x K •
            V.map (CosimplicialDPAlgebra.coprojection 1)
              (-theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1]
                sigmaDx (p := p) x i) +
        ∑ K ∈ S, toCompletedTensor p (E.completedRing p 1) (E.forms p 1 1)
          (V.carrier 1) ((taylorCoefficient (p := p) x K •
            V.map (CosimplicialDPAlgebra.coprojection 1)
              (theta (K + Finsupp.single i 1) m)) ⊗ₜ[E.completedRing p 1]
                xiDx (p := p) x i)).val n :=
  (toCompletedTensor_tmul_val_congr n h _).trans
    (congrArg (fun X => X.val n) (taylorSum_tmul_differential_delta V x theta hθ S m i))

end Expansions

include hbeta in
/-- **The coface `δ : ⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` is horizontal for the base-change connections, given the
Taylor expansion of `M(δ)`.**

The data: coordinates `x_i` of `D(0)`, with differences `ξ_i = σ(x_i) - δ(x_i)` in the divided
power ideal of `D(1)`, and operators `θ_K` on `M(0)` with `θ_L ∘ θ_K = θ_{K + L}` (`hθ`), such that
`∇ m = ∑_i (-θ_{e_i} m) ⊗ d x_i` (`hco`), only finitely many `θ_K m` survive at each level
(`hfin`), and `M(δ)(m) = ∑_K ξ^{[K]} · M(σ)(θ_K m)` modulo `pⁿ` as soon as the sum runs over the
multi-indices surviving at a level `k` depending on `n` (`htaylor`).  This is the situation of
the source's proof of [Stacks, Lemma 60.17.3, Tag 07JG], where `δ`, `σ` are the two projections
`p₁`, `p₀`. -/
theorem baseChangeConnection_map_delta_of_taylor
    (hθ : ∀ (K L : ι →₀ ℕ) (m : V.carrier 0), theta L (theta K m) = theta (K + L) m)
    (hco : IsCoordinateExpansion p (E.completedRing p 0) (E.forms p 1 0)
      (fun i => E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
        (E.carrier 0) (x i))) nabla (fun i m => -theta (Finsupp.single i 1) m))
    (hfin : ∀ (m : V.carrier 0) (n : ℕ),
      {K | theta K m ∉ pPowSmul p (E.completedRing p 0) (V.carrier 0) n}.Finite)
    (hξ : ∀ i, coordinateDifference x i ∈ E.ideal 1)
    (htaylor : ∀ n : ℕ, ∃ k : ℕ, ∀ (m : V.carrier 0) (S : Finset (ι →₀ ℕ)),
      (∀ K, theta K m ∉ pPowSmul p (E.completedRing p 0) (V.carrier 0) k → K ∈ S) →
      V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m -
          ∑ K ∈ S, taylorCoefficient (p := p) x K •
            V.map (CosimplicialDPAlgebra.coprojection 1) (theta K m) ∈
        pPowSmul p (E.completedRing p 1) (V.carrier 1) n)
    (m : V.carrier 0) :
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla m) := by
  classical
  refine AdicCompletion.ext fun n => ?_
  refine (htaylor n).elim fun k hk => ?_
  have hF := hfin m (max k n)
  refine (⟨_, rfl⟩ : ∃ L : ι →₀ ℕ, L = hF.toFinset.sup id).elim fun L hL => ?_
  have hle : ∀ (a : ℕ) (K : ι →₀ ℕ), a ≤ max k n →
      theta K m ∉ pPowSmul p (E.completedRing p 0) (V.carrier 0) a → K ≤ L := by
    intro a K ha hK
    rw [hL]
    exact Finset.le_sup (f := id) (hF.mem_toFinset.mpr fun h => hK
      (Submodule.smul_mono (Ideal.pow_le_pow_right ha) le_rfl h))
  have hvan : ∀ K, ¬ K ≤ L → theta K m ∈ pPowSmul p (E.completedRing p 0) (V.carrier 0) n :=
    fun K hK => by_contra fun h => hK (hle n K (le_max_right _ _) h)
  have hsupp : ∀ (K : ι →₀ ℕ) (i : ι),
      theta (K + Finsupp.single i 1) m ∉ pPowSmul p (E.completedRing p 0) (V.carrier 0) n →
      i ∈ L.support := by
    intro K i h
    have h2 := Finsupp.le_def.mp (hle n _ (le_max_right _ _) h) i
    rw [Finsupp.add_apply, Finsupp.single_eq_same] at h2
    rw [Finsupp.mem_support_iff]
    omega
  have hexp : ∀ K : ι →₀ ℕ, CompletedDeRham.IsLevelExpansionAt p (E.completedRing p 0)
      (E.forms p 1 0)
      (fun i => E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
        (E.carrier 0) (x i))) nabla (fun i m => -theta (Finsupp.single i 1) m) n L.support
      (theta K m) := fun K =>
    isLevelExpansionAt_of_support_subset p _ _ _ hco (theta K m) n L.support fun i hi =>
      hsupp K i fun h => hi (by rw [hθ]; exact Submodule.neg_mem _ h)
  have hexp0 : CompletedDeRham.IsLevelExpansionAt p (E.completedRing p 0) (E.forms p 1 0)
      (fun i => E.differential p 0 (AdicCompletion.of (pAdicIdeal (A := E.carrier 0) p)
        (E.carrier 0) (x i))) nabla (fun i m => -theta (Finsupp.single i 1) m) n L.support m :=
    isLevelExpansionAt_of_support_subset p _ _ _ hco m n L.support fun i hi =>
      hsupp 0 i fun h => hi (Submodule.neg_mem _ (by rwa [zero_add] at h))
  have hA1 := V.baseChangeConnection_one_val_congr nabla beta n
    (hk m (Finset.Iic L) fun K hK => Finset.mem_Iic.mpr (hle k K (le_max_left _ _) hK))
  have hA2 := V.baseChangeConnection_one_taylorSum nabla beta hbeta x theta m (Finset.Iic L)
  have hB1 := addMonoidHom_val_congr p
    (V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1).toAddMonoidHom n hexp0
  refine hA1.trans ((congrArg (fun X => X.val n) hA2).trans (Eq.trans ?_ hB1.symm))
  refine Eq.trans ?_ (congrArg (fun X => X.val n)
    (tensorMap_delta_expansion V x theta m L.support)).symm
  exact sum_add_val_eq_of_level n (Finset.Iic L) L.support _ _ _ _ _
    (fun K => V.smul_tensorMap_coprojection_val nabla x theta hθ n K m L.support (hexp K))
    (taylorDeriv_sum_val V x theta hξ m n L L.support subset_rfl hvan) fun i =>
      V.taylorSum_tmul_differential_delta_val x theta hθ n (Finset.Iic L) m i
        (hk (-theta (Finsupp.single i 1) m) (Finset.Iic L) fun K hK =>
          Finset.mem_Iic.mpr (le_trans le_add_self (hle k _ (le_max_left _ _) fun h => hK (by
            rw [(theta K).map_neg, hθ]
            exact Submodule.neg_mem _ h))))

end Taylor

end CosimplicialCompletedModule

end Crystalline

end
