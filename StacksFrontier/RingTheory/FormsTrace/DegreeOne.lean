module

public import StacksFrontier.RingTheory.FormsTrace.Differential

/-!
# The degree-one compatibility of trace maps with `d`

Let `A → B` be finite free with a nice element `h` (`Stacks.FormsTrace.IsNiceElement`), and let
`Θ^p : Ω^p_B → Ω^p_A` have property (1) of Stacks, Lemma 0FLB. This file proves

`Θ¹(d b) = d (Trace_{B/A}(b))`,

which, with `Stacks.FormsTrace.IsFormsTrace.commutesWithD_of_isNiceElement`, shows that `Θ` is a
map of de Rham complexes.

## The argument

Let `μ : B ⊗_A Ω_A → Ω_B` be the canonical map and `e` a basis of `B` over `A`, with coordinate
functions `cᵢ`. Since `h^N` kills `Ω_{B/A}`, every `h^N d z` has a preimage `λ(z)` under `μ`. The
coordinate maps `πᵢ : B ⊗_A Ω_A → Ω_A`, `b ⊗ ω ↦ cᵢ(b) ω`, vanish on `ker μ`, which is
`h`-power torsion while `h` is a nonzerodivisor on `Ω_A`. Comparing the two expressions of
`∑ᵢ πᵢ(λ(x eᵢ))` obtained from `x eᵢ = ∑ⱼ cⱼ(x eᵢ) eⱼ` and from the Leibniz rule, the terms
`∑ᵢⱼ cⱼ(x eᵢ) πᵢ(λ eⱼ)` and `∑ᵢⱼ cᵢ(x eⱼ) πⱼ(λ eᵢ)` cancel (the identity `tr(MP) = tr(PM)`), and
what is left is `h^N d Trace(x) = τ(λ x)`, where `τ(b ⊗ ω) = Trace(b) ω`. Property (1) says that
`Θ¹ ∘ μ = τ`, and `h` is a nonzerodivisor on `Ω¹_A`.

## Main results

* `Stacks.FormsTrace.IsFormsTrace.degreeOneD_of_isNiceElement`: `Θ¹(d b) = d Trace(b)`.
* `Stacks.FormsTrace.IsFormsTrace.commutesWithD_of_isNiceElement_of_free`: `Θ` commutes with `d`.

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open KaehlerDifferential

universe u

namespace Stacks.FormsTrace

/-- A vector of `M`, as an element of the first exterior power. -/
def oneForm (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    M →ₗ[R] ⋀[R]^1 M :=
  LinearMap.codRestrict _ (ExteriorAlgebra.ι R) exteriorPower.ι_mem_degreeOne

/-- `oneForm R M m` is `ExteriorAlgebra.ι R m`, as an element of the first exterior power. -/
@[simp]
theorem oneForm_apply (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (m : M) : oneForm R M m = ⟨ExteriorAlgebra.ι R m, exteriorPower.ι_mem_degreeOne m⟩ :=
  rfl

/-- `oneForm` is injective. -/
theorem oneForm_injective (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective (oneForm R M) := fun m m' h =>
  (ExteriorAlgebra.ι_inj R m m').mp (congrArg Subtype.val h)

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A nice element is a nonzerodivisor on the Kähler differentials of `A`. -/
theorem IsNiceElement.regular_kaehler {h : A} (hh : IsNiceElement A B h) :
    IsSMulRegular Ω[A⁄ℤ] h := by
  intro ω ω' hω
  apply oneForm_injective A Ω[A⁄ℤ]
  refine hh.regular 1 ?_
  show h • oneForm A _ ω = h • oneForm A _ ω'
  rw [← map_smul, ← map_smul]
  exact congrArg _ hω

variable (A B) in
/-- The `i`-th coordinate map `B ⊗_A Ω_A → Ω_A`, `b ⊗ ω ↦ cᵢ(b) ω`, for a basis of `B`. -/
def coordTensor {ι : Type*} (e : Module.Basis ι A B) (i : ι) : B ⊗[A] Ω[A⁄ℤ] →ₗ[A] Ω[A⁄ℤ] :=
  (TensorProduct.lid A Ω[A⁄ℤ]).toLinearMap ∘ₗ (e.coord i).rTensor Ω[A⁄ℤ]

/-- The `i`-th coordinate map sends `b ⊗ ω` to `e.repr b i • ω`. -/
@[simp]
theorem coordTensor_tmul {ι : Type*} (e : Module.Basis ι A B) (i : ι) (b : B) (ω : Ω[A⁄ℤ]) :
    coordTensor A B e i (b ⊗ₜ ω) = e.repr b i • ω := by
  simp [coordTensor]

/-- The coordinate maps on `B ⊗_A Ω_A` against the action of `B`:
`πᵢ(x · t) = ∑ⱼ cᵢ(x eⱼ) πⱼ(t)`. -/
theorem coordTensor_smul {ι : Type*} [Fintype ι] (e : Module.Basis ι A B) (i : ι) (x : B)
    (t : B ⊗[A] Ω[A⁄ℤ]) :
    coordTensor A B e i (x • t) = ∑ j, e.repr (x * e j) i • coordTensor A B e j t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b ω =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, coordTensor_tmul]
    simp only [coordTensor_tmul, smul_smul, ← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← e.sum_repr b, Finset.mul_sum]
    simp only [mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  | add s t hs ht =>
    rw [smul_add, map_add, hs, ht, ← Finset.sum_add_distrib]
    simp only [map_add, smul_add]

/-- The trace in coordinates: `Trace(x) = ∑ᵢ cᵢ(x eᵢ)`. -/
theorem trace_eq_sum_repr {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι A B)
    [Module.Finite A B] [Module.Projective A B] (x : B) :
    trace A B x = ∑ i, e.repr (x * e i) i := by
  have : Module.Free A B := Module.Free.of_basis e
  rw [trace, LinearMap.comp_apply, Stacks.Discriminant.finiteProjectiveTrace_eq_trace,
    LinearMap.trace_eq_matrix_trace A e, Matrix.trace]
  simp [LinearMap.toMatrix_apply]

/-- The trace contraction `τ : B ⊗_A Ω_A → Ω_A`, `b ⊗ ω ↦ Trace(b) ω`, as `∑ᵢ πᵢ(eᵢ · -)`. -/
theorem sum_coordTensor_basis_smul_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι A B) [Module.Finite A B] [Module.Projective A B] (b : B) (ω : Ω[A⁄ℤ]) :
    ∑ i, coordTensor A B e i (e i • (b ⊗ₜ ω)) = trace A B b • ω := by
  rw [trace_eq_sum_repr e, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, coordTensor_tmul, mul_comm]

/-- **The coordinate maps kill the kernel of `B ⊗_A Ω_A → Ω_B`** over a nice element. -/
theorem IsNiceElement.coordTensor_eq_zero_of_mem_ker {h : A} (hh : IsNiceElement A B h)
    {ι : Type*} (e : Module.Basis ι A B) (i : ι) {t : B ⊗[A] Ω[A⁄ℤ]}
    (ht : t ∈ LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ A B)) :
    coordTensor A B e i t = 0 := by
  obtain ⟨n, hn⟩ := hh.ker_torsion t ht
  refine (hh.regular_kaehler.pow n) ?_
  show h ^ n • coordTensor A B e i t = h ^ n • 0
  rw [← map_smul, hn, map_zero, smul_zero]

/-- Over a nice element, `h^N d z` lifts to `B ⊗_A Ω_A`. -/
theorem exists_mapBaseChange_eq_pow_smul_D {h : A} {N : ℕ} (hN : ∀ x : Ω[B⁄A], h ^ N • x = 0)
    (z : B) : ∃ t : B ⊗[A] Ω[A⁄ℤ],
      KaehlerDifferential.mapBaseChange ℤ A B t = h ^ N • D ℤ B z := by
  have hx : h ^ N • D ℤ B z ∈ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ A B) := by
    rw [(KaehlerDifferential.exact_mapBaseChange_map ℤ A B).linearMap_ker_eq.symm,
      LinearMap.mem_ker, ← algebraMap_smul B, map_smul, algebraMap_smul]
    exact hN _
  exact hx

/-- The derivative of `c · z` for a scalar `c ∈ A`:
`d(c z) = c d z + z · f^*(d c)`. -/
theorem D_smul_eq (c : A) (z : B) :
    D ℤ B (c • z) = c • D ℤ B z + z • KaehlerDifferential.map ℤ ℤ A B (D ℤ A c) := by
  rw [Algebra.smul_def, Derivation.leibniz, KaehlerDifferential.map_D, algebraMap_smul]

/-- `Θ¹ ∘ μ = τ`: property (1) of Lemma 0FLB in degree one, read on `B ⊗_A Ω_A`. -/
theorem IsFormsTrace.apply_oneForm_mapBaseChange {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι A B) [Module.Finite A B] [Module.Projective A B]
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ)
    (t : B ⊗[A] Ω[A⁄ℤ]) :
    Θ 1 (oneForm B _ (KaehlerDifferential.mapBaseChange ℤ A B t)) =
      oneForm A _ (∑ i, coordTensor A B e i (e i • t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero, Finset.sum_const_zero]
  | tmul b ω =>
    rw [sum_coordTensor_basis_smul_tmul, KaehlerDifferential.mapBaseChange_tmul, map_smul]
    have : oneForm B Ω[B⁄ℤ] (KaehlerDifferential.map ℤ ℤ A B ω) =
        formsMap A B 1 (oneForm A _ ω) := by
      rw [oneForm_apply, oneForm_apply, formsMap_one_ι]
    rw [this, hΘ, map_smul]
  | add s t hs ht =>
    simp only [map_add, smul_add, Finset.sum_add_distrib, hs, ht]

/-- **The degree-one compatibility** `Θ¹(d b) = d Trace(b)` over a nice element, for a finite
free algebra. -/
theorem IsFormsTrace.degreeOneD_of_isNiceElement {ι : Type*} [Fintype ι]
    (e : Module.Basis ι A B) [Module.Finite A B] [Module.Projective A B] {h : A}
    (hh : IsNiceElement A B h) {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]}
    (hΘ : IsFormsTrace A B Θ) : DegreeOneD Θ := by
  classical
  obtain ⟨N, hN⟩ := hh.pow_smul_kaehler
  choose lam hlam using exists_mapBaseChange_eq_pow_smul_D hN
  set μ := KaehlerDifferential.mapBaseChange ℤ A B
  set π := coordTensor A B e
  have hker : ∀ t s, μ t = μ s → ∀ i, π i t = π i s := fun t s hts i => by
    rw [← sub_eq_zero, ← map_sub]
    exact hh.coordTensor_eq_zero_of_mem_ker e i (by rw [LinearMap.mem_ker, map_sub, hts, sub_self])
  -- the expansion of `x eᵢ` in the basis
  have keyA : ∀ (x : B) (i : ι), π i (lam (x * e i)) =
      ∑ j, e.repr (x * e i) j • π i (lam (e j)) + h ^ N • D ℤ A (e.repr (x * e i) i) := by
    intro x i
    set c := e.repr (x * e i)
    let T : B ⊗[A] Ω[A⁄ℤ] := ∑ j, (c j • lam (e j) + e j ⊗ₜ (h ^ N • D ℤ A (c j)))
    have hT' : μ T = h ^ N • D ℤ B (x * e i) := by
      conv_rhs => rw [← e.sum_repr (x * e i)]
      simp only [T, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show μ (c j • lam (e j) + _) = h ^ N • D ℤ B (c j • e j)
      rw [map_add, μ.map_smul_of_tower, hlam, KaehlerDifferential.mapBaseChange_tmul, map_smul,
        D_smul_eq, smul_add, smul_comm (h ^ N) (c j), smul_comm (h ^ N) (e j)]
    have := hker (lam (x * e i)) T (by rw [hlam, hT']) i
    rw [this, map_sum]
    simp only [map_add, map_smul, Finset.sum_add_distrib]
    congr 1
    show ∑ j, coordTensor A B e i (e j ⊗ₜ (h ^ N • D ℤ A (c j))) = _
    simp only [coordTensor_tmul, e.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- the Leibniz rule for `x eᵢ`
  have keyB : ∀ (x : B) (i : ι), π i (lam (x * e i)) =
      ∑ j, e.repr (x * e j) i • π j (lam (e i)) + π i (e i • lam x) := by
    intro x i
    have := hker (lam (x * e i)) (x • lam (e i) + e i • lam x) (by
      rw [map_add, map_smul, map_smul, hlam, hlam, hlam, Derivation.leibniz, smul_add,
        smul_comm (h ^ N) x, smul_comm (h ^ N) (e i), add_comm]) i
    rw [this, map_add]
    exact congrArg (· + _) (coordTensor_smul e i x (lam (e i)))
  intro x
  have hi : ∀ i, π i (e i • lam x) = (∑ j, e.repr (x * e i) j • π i (lam (e j))) +
      h ^ N • D ℤ A (e.repr (x * e i) i) - ∑ j, e.repr (x * e j) i • π j (lam (e i)) := by
    intro i
    rw [← keyA, keyB]
    abel
  have hτ : ∑ i, π i (e i • lam x) = h ^ N • D ℤ A (trace A B x) := by
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_comm (f := fun i j => e.repr (x * e j) i • π j (lam (e i))),
      trace_eq_sum_repr e, map_sum, Finset.smul_sum]
    abel
  refine ((hh.regular 1).pow N) ?_
  show h ^ N • Θ 1 (oneForm B _ (D ℤ B x)) = h ^ N • oneForm A _ (D ℤ A (trace A B x))
  rw [← map_smul (Θ 1), ← LinearMap.map_smul_of_tower (oneForm B _), ← hlam,
    hΘ.apply_oneForm_mapBaseChange e, hτ, map_smul]

/-- **Trace maps on forms commute with the de Rham differential over a nice element**, for a
finite free algebra: a family with property (1) of Stacks, Lemma 0FLB is a map of de Rham
complexes. -/
theorem IsFormsTrace.commutesWithD_of_isNiceElement_of_free [Module.Finite A B]
    [Module.Free A B] {h : A} (hh : IsNiceElement A B h)
    {Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ]} (hΘ : IsFormsTrace A B Θ) :
    CommutesWithD A B Θ :=
  hΘ.commutesWithD_of_isNiceElement hh (hΘ.isWedgeLinear_of_isNiceElement hh)
    (hΘ.degreeOneD_of_isNiceElement (Module.Free.chooseBasis A B) hh)

end Stacks.FormsTrace

end
