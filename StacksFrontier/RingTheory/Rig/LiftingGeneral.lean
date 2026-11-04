module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Lifting

/-!
# Lifting maps into a quotient of a complete algebra, for an arbitrary ideal (Stacks 0GAP)

Let `A` be a Noetherian ring, `I` an ideal of `A`, `B` an `I`-adically complete `A`-algebra of
finite type modulo `I` presented as `B = A⟨x₁, …, x_r⟩ / J`, and `C` an `I`-adically complete
`A`-algebra. Given an `A`-algebra map `ψₙ : B → C / IⁿC`, Stacks 0GAP attaches to it an
obstruction class

`o(ψₙ) ∈ Ext¹_B(NL^∧_{B/A}, IⁿC / I²ⁿC)`

and asserts that if `o(ψₙ)` maps to zero in `Ext¹_B(NL^∧_{B/A}, I^{n'}C / I^{2n'}C)` then `ψₙ`
lifts to an `A`-algebra map `ψ'_{2n'} : B → C / I^{2n'}C` agreeing with `ψₙ` into `C / I^{n'}C`.

This file carries out that argument for an **arbitrary** ideal `I`, with no regularity
assumption on `C` and no annihilation hypothesis on the Ext groups. The special case
`I = (a)` principal, `a` a nonzerodivisor on `C`, and `Ext¹` annihilated by `a ^ c` is
`Rig.exists_perturbed_continuousAlgHom` and `Rig.exists_algHom_lift_of_isRegular` in
`StacksFrontier/RingTheory/Rig/Lifting.lean`; it is what Stacks 0AK6 needs, and it is strictly
less than the remark asserts.

## The obstruction class, read on representatives

The remark builds `o(ψₙ)` by choosing a presentation and a lift `ψ : A⟨x₁, …, x_r⟩ → C` of
`ψₙ`. Then `ψ(J) ⊆ IⁿC`, hence `ψ(J²) ⊆ I²ⁿC`, and `g ↦ ψ(g)` is a well-defined `B`-linear map

`o(ψ) : J / J² → IⁿC / I²ⁿC`.

The class `o(ψₙ)` is the image of `o(ψ)` in
`Coker (Hom_B(⨁ i, B dxᵢ, IⁿC/I²ⁿC) → Hom_B(J/J², IⁿC/I²ⁿC))`, which Stacks 0ALN part (1)
identifies with `Ext¹_B(NL^∧_{B/A}, IⁿC/I²ⁿC)`.

Everything here is phrased on representatives, so no quotient module is built: `o(ψ)` is
recorded by `Rig.map_mem_pow_two_mul_of_mem_sq` (its well-definedness, i.e. `ψ(J²) ⊆ I²ⁿC`),
the statement that `o(ψ)` lies in the image of `Hom_B(⨁ i, B dxᵢ, -)` is the existence of
`δ₁, …, δ_r ∈ I^{n'}C` with

`ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I^{2n'}C`  for every `g ∈ J`,

and the `δᵢ` are exactly the representatives `h(dxᵢ)` of the map `h : ⨁ i, B dxᵢ → I^{n'}C /
I^{2n'}C` the remark produces from the vanishing of `o(ψₙ)`.

## Main results

* `Rig.map_mem_pow_two_mul_of_mem_sq` and `Rig.sub_mem_pow_two_mul_of_sub_mem_sq`:
  `ψ(J) ⊆ IⁿC` implies `ψ(J²) ⊆ I²ⁿC`, so `o(ψ) : J/J² → IⁿC/I²ⁿC` is well defined.
  **Stacks 0GAP**, the construction of the obstruction map.
* `Rig.exists_obstruction_difference_of_lifts`: two continuous lifts of `ψₙ` have obstruction
  maps differing by a map that factors through the differential, so the class `o(ψₙ)` does not
  depend on the chosen lift. **Stacks 0GAP**, the well-definedness of the class.
* `Rig.obstruction_factors_of_lift_change`: consequently the vanishing hypothesis, read on
  representatives, holds for one continuous lift exactly when it holds for every one.
* `Rig.exists_perturbed_algHom_of_obstruction_factors`: the perturbation `xᵢ ↦ ψ(xᵢ) - δᵢ` has
  `ψ'(J) ⊆ I^{2n'}C` and differs from `ψ` by `I^{n'}C`. **Stacks 0GAP**, the power-series
  computation.
* `Rig.exists_algHom_quotient_of_obstruction_factors` and
  `Rig.exists_algHom_quotient_of_obstruction_vanishes`: the claim of the remark — an
  `A`-algebra map `ψ'_{2n'} : B → C/I^{2n'}C` agreeing with `ψₙ` as maps into `C/I^{n'}C`.
* `Rig.exists_obstruction_factors_of_exists_algHom_quotient` and
  `Rig.obstruction_factors_iff_exists_algHom_quotient`: the converse, and hence the headline
  sentence of the remark — `o(ψₙ)` *is* the obstruction to lifting `ψₙ` to `C/I²ⁿC`.

## Implementation notes

No relation between `n` and `n'` is needed for the perturbation step; the source's
`n > n' > n/2` is what makes `2n' > n`, i.e. what makes the conclusion an improvement on the
hypothesis, and `n' ≤ n` is what makes the comparison of `ψ'_{2n'}` with `ψₙ` into
`C/I^{n'}C` meaningful. Only `n' ≤ n` is assumed, in
`Rig.exists_algHom_quotient_of_obstruction_factors`.

The first-order expansion of the perturbed map is Stacks 0AK3, in the form
`Rig.eval_add_variables_eq_linear_add_error`, so the whole file lives on the
restricted-power-series side of
`RestrictedPowerSeries.adicCompletionAlgEquiv`, as `StacksFrontier/RingTheory/Rig/Lifting.lean`
does.

## References

* [Stacks Project, Tag 0GAP](https://stacks.math.columbia.edu/tag/0GAP)
* [Stacks Project, Tag 0AK3](https://stacks.math.columbia.edu/tag/0AK3)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open RestrictedPowerSeries

namespace Rig

universe u v w

section Obstruction

variable {A : Type u} [CommRing A] {Rs : Type v} [CommRing Rs] [Algebra A Rs]
  {C : Type w} [CommRing C] [Algebra A C]

/-- **Stacks 0GAP**, the construction of the obstruction map. If an `A`-algebra map `ψ` carries
the ideal `J` into `IⁿC`, then it carries `J²` into `I²ⁿC`. -/
public theorem map_mem_pow_two_mul_of_mem_sq (JC : Ideal C) (Jid : Ideal Rs) (n : ℕ)
    (ψ : Rs →ₐ[A] C) (hψJ : ∀ g ∈ Jid, ψ g ∈ JC ^ n) :
    ∀ g ∈ Jid ^ 2, ψ g ∈ JC ^ (2 * n) := by
  intro g hg
  have hmapJ : Ideal.map (ψ : Rs →+* C) Jid ≤ JC ^ n := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun x hx => hψJ x hx
  have h1 : ψ g ∈ Ideal.map (ψ : Rs →+* C) (Jid ^ 2) := Ideal.mem_map_of_mem _ hg
  rw [Ideal.map_pow] at h1
  have h2 := pow_le_pow_left' hmapJ 2 h1
  rwa [← pow_mul, mul_comm n 2] at h2

/-- **Stacks 0GAP**, the well-definedness of the obstruction map. Representatives of one class
in `J / J²` have the same image in `IⁿC / I²ⁿC`, so `o(ψ) : J/J² → IⁿC/I²ⁿC`, `g ↦ ψ(g)`, is
well defined. -/
@[stacks 0GAP "the obstruction map o(ψ) is well defined"]
public theorem sub_mem_pow_two_mul_of_sub_mem_sq (JC : Ideal C) (Jid : Ideal Rs) (n : ℕ)
    (ψ : Rs →ₐ[A] C) (hψJ : ∀ g ∈ Jid, ψ g ∈ JC ^ n) (g g' : Rs) (h : g - g' ∈ Jid ^ 2) :
    ψ g - ψ g' ∈ JC ^ (2 * n) := by
  rw [← map_sub]
  exact map_mem_pow_two_mul_of_mem_sq JC Jid n ψ hψJ _ h

end Obstruction

section LiftIndependence

variable {A : Type u} [CommRing A]

/-- The first-order comparison of two continuous `A`-algebra maps out of `A⟨x₁, …, x_r⟩` whose
increments `εᵢ` on the variables lie in `IⁿC`: the quadratic error of Stacks 0AK3 lies in
`I²ⁿC`. -/
private theorem sub_sub_sum_mem_pow_two_mul (I : Ideal A) (hI : I.FG)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {r : ℕ} (n : ℕ)
    (ψ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψ'c : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ')
    (ε : Fin r → C) (hε : ∀ i, ε i ∈ (I.map (algebraMap A C)) ^ n)
    (hvar : ∀ i, ψ' (polynomialAlgHom I (Fin r) (MvPolynomial.X i))
      = ψ (polynomialAlgHom I (Fin r) (MvPolynomial.X i)) + ε i) :
    ∀ g, ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i
      ∈ (I.map (algebraMap A C)) ^ (2 * n) := by
  intro g
  obtain ⟨ξ, hξmem, hξ⟩ :=
    eval_add_variables_eq_linear_add_error I hI ψ ψ' hψc hψ'c ε hvar g
  have hξJ : ξ ∈ (I.map (algebraMap A C)) ^ (2 * n) := by
    refine (Ideal.span_le.mpr ?_) hξmem
    rintro x ⟨ij, rfl⟩
    simp only [SetLike.mem_coe]
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul (hε ij.1) (hε ij.2)
  rw [show ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i = ξ by rw [hξ]; ring]
  exact hξJ

/-- **Stacks 0GAP**, the independence of the obstruction class of the chosen lift. Two
continuous `A`-algebra maps `ψ, ψ' : A⟨x₁, …, x_r⟩ → C` that reduce to the same map modulo
`IⁿC` satisfy

`ψ'(g) - ψ(g) - ∑ i, ψ(∂g/∂xᵢ) εᵢ ∈ I²ⁿC`  for every `g`,

with `εᵢ = ψ'(xᵢ) - ψ(xᵢ) ∈ IⁿC`. So the obstruction maps `o(ψ')` and `o(ψ)` differ by the
composite of the differential of `NL^∧_{B/A}` with `dxᵢ ↦ εᵢ`, and therefore define the same
class in `Ext¹_B(NL^∧_{B/A}, IⁿC/I²ⁿC)`. -/
@[stacks 0GAP "o(ψₙ) does not depend on the chosen lift"]
public theorem exists_obstruction_difference_of_lifts (I : Ideal A) (hI : I.FG)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {r : ℕ} (n : ℕ)
    (ψ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψ'c : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ')
    (hsame : ∀ g, ψ' g - ψ g ∈ (I.map (algebraMap A C)) ^ n) :
    ∃ ε : Fin r → C, (∀ i, ε i ∈ (I.map (algebraMap A C)) ^ n) ∧
      ∀ g, ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i
        ∈ (I.map (algebraMap A C)) ^ (2 * n) :=
  ⟨fun i => ψ' (polynomialAlgHom I (Fin r) (MvPolynomial.X i)) -
      ψ (polynomialAlgHom I (Fin r) (MvPolynomial.X i)), fun i => hsame _,
    sub_sub_sum_mem_pow_two_mul I hI n ψ ψ' hψc hψ'c _ (fun i => hsame _)
      (fun i => by ring)⟩

/-- The vanishing of the obstruction class, read on representatives, is a condition on `ψₙ`
alone: if one continuous lift `ψ` of `ψₙ` admits increments `δᵢ ∈ I^{n'}C` witnessing it, then
so does every other continuous lift `ψ'`, for `n' ≤ n`. -/
public theorem obstruction_factors_of_lift_change (I : Ideal A) (hI : I.FG)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {r : ℕ} (Jid : Ideal (RestrictedPowerSeries I (Fin r))) (n n' : ℕ) (hn' : n' ≤ n)
    (ψ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψ'c : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ')
    (hsame : ∀ g, ψ' g - ψ g ∈ (I.map (algebraMap A C)) ^ n)
    (δ : Fin r → C) (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (hfac : ∀ g ∈ Jid, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
      ∈ (I.map (algebraMap A C)) ^ (2 * n')) :
    ∃ δ' : Fin r → C, (∀ i, δ' i ∈ (I.map (algebraMap A C)) ^ n') ∧
      ∀ g ∈ Jid, ψ' g - ∑ i, ψ' (partialDerivative I i g) * δ' i
        ∈ (I.map (algebraMap A C)) ^ (2 * n') := by
  classical
  set JC : Ideal C := I.map (algebraMap A C) with hJC
  obtain ⟨ε, hε, hexp⟩ :=
    exists_obstruction_difference_of_lifts I hI n ψ ψ' hψc hψ'c hsame
  refine ⟨fun i => δ i + ε i, fun i => Ideal.add_mem _ (hδ i)
    (Ideal.pow_le_pow_right (by omega) (hε i)), ?_⟩
  intro g hg
  have hsplit : ∑ i, (ψ' (partialDerivative I i g) - ψ (partialDerivative I i g)) * (δ i + ε i)
      = ∑ i, ψ' (partialDerivative I i g) * (δ i + ε i)
        - ∑ i, ψ (partialDerivative I i g) * δ i
        - ∑ i, ψ (partialDerivative I i g) * ε i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : ψ' g - ∑ i, ψ' (partialDerivative I i g) * (δ i + ε i)
      = (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i)
        + (ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i)
        - ∑ i, (ψ' (partialDerivative I i g) - ψ (partialDerivative I i g)) * (δ i + ε i) := by
    rw [hsplit]; ring
  have h1 : ψ g - ∑ i, ψ (partialDerivative I i g) * δ i ∈ JC ^ (2 * n') := hfac g hg
  have h2 : ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i ∈ JC ^ (2 * n') :=
    Ideal.pow_le_pow_right (by omega) (hexp g)
  have h3 : ∑ i, (ψ' (partialDerivative I i g) - ψ (partialDerivative I i g)) * (δ i + ε i)
      ∈ JC ^ (2 * n') := by
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [two_mul, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_le_pow_right hn' (hsame _))
      (Ideal.add_mem _ (hδ i) (Ideal.pow_le_pow_right (by omega) (hε i)))
  rw [key]
  exact Ideal.sub_mem _ (Ideal.add_mem _ h1 h2) h3

end LiftIndependence

section Perturbation

variable {A : Type u} [CommRing A]

/-- **Stacks 0GAP**, the power-series computation, for an arbitrary ideal `I`.

Let `C` be an `I`-adically complete `A`-algebra, `J` an ideal of `A⟨x₁, …, x_r⟩`, and
`ψ : A⟨x₁, …, x_r⟩ → C` a continuous `A`-algebra map. Suppose there are `δ₁, …, δ_r ∈ I^{n'}C`
with

`ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I^{2n'}C`  for every `g ∈ J`,

which is the statement that the obstruction map of `ψ` agrees with `h ∘ d` into
`I^{n'}C / I^{2n'}C`, for `h : ⨁ i, B dxᵢ → I^{n'}C / I^{2n'}C` the map sending `dxᵢ` to the
class of `δᵢ`. Then `ψ' : xᵢ ↦ ψ(xᵢ) - δᵢ` is a continuous `A`-algebra map with
`ψ'(J) ⊆ I^{2n'}C`, and `ψ' - ψ` takes values in `I^{n'}C`.

No principality of `I`, no regularity on `C` and no relation between `n'` and the precision of
`ψ` are used; the two conclusions are the first-order expansion of Stacks 0AK3 applied to the
perturbation. -/
@[stacks 0GAP "the lifting claim, arbitrary ideal"]
public theorem exists_perturbed_algHom_of_obstruction_factors (I : Ideal A) (hI : I.FG)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    {r : ℕ} (Jid : Ideal (RestrictedPowerSeries I (Fin r))) (n' : ℕ)
    (ψ : RestrictedPowerSeries I (Fin r) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin r))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (δ : Fin r → C) (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (hfac : ∀ g ∈ Jid, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
      ∈ (I.map (algebraMap A C)) ^ (2 * n')) :
    ∃ ψ' : RestrictedPowerSeries I (Fin r) →ₐ[A] C,
      (@Continuous _ _ (limitTopology I (Fin r))
        ((I.map (algebraMap A C)).adicTopology) ψ') ∧
      (∀ g ∈ Jid, ψ' g ∈ (I.map (algebraMap A C)) ^ (2 * n')) ∧
      (∀ g, ψ' g - ψ g ∈ (I.map (algebraMap A C)) ^ n') := by
  classical
  set JC : Ideal C := I.map (algebraMap A C) with hJC
  obtain ⟨ψ', ⟨hψ'c, hψ'var⟩, -⟩ :=
    exists_continuousAlgHom_add_variables I hI ψ hψc (fun i => -δ i)
  have hexp : ∀ g : RestrictedPowerSeries I (Fin r),
      ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i) ∈ JC ^ (2 * n') := by
    intro g
    have h := sub_sub_sum_mem_pow_two_mul I hI n' ψ ψ' hψc hψ'c (fun i => -δ i)
      (fun i => Submodule.neg_mem _ (hδ i)) hψ'var g
    rwa [show ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i)
      = ψ' g - ψ g - ∑ i, ψ (partialDerivative I i g) * -δ i by
        simp only [mul_neg, Finset.sum_neg_distrib]; ring]
  refine ⟨ψ', hψ'c, ?_, ?_⟩
  · intro g hg
    have hsum := Ideal.add_mem (JC ^ (2 * n')) (hexp g) (hfac g hg)
    simpa using hsum
  · intro g
    have h1 : (∑ i, ψ (partialDerivative I i g) * δ i) ∈ JC ^ n' :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hδ i)
    have h2 := Ideal.sub_mem (JC ^ n')
      (Ideal.pow_le_pow_right (by omega : n' ≤ 2 * n') (hexp g)) h1
    rw [show ψ' g - ψ g
        = (ψ' g - (ψ g - ∑ i, ψ (partialDerivative I i g) * δ i))
          - (∑ i, ψ (partialDerivative I i g) * δ i) by ring]
    exact h2

end Perturbation

section Claim

variable {A : Type u} [CommRing A]

/-- **Stacks 0GAP**, the claim of the remark, for an arbitrary ideal `I`.

Let `A` be a ring with a finitely generated ideal `I`, let `B` be an `I`-adically complete
`A`-algebra of finite type modulo `I` with a completed polynomial presentation
`B = A⟨x₁, …, x_r⟩ / J`, and let `C` be an `I`-adically complete `A`-algebra. Let
`ψₙ : B → C / IⁿC` be an `A`-algebra map and `ψ : A⟨x₁, …, x_r⟩ → C` a continuous lift of it.

If the obstruction map of `ψ` maps to zero in
`Ext¹_B(NL^∧_{B/A}, I^{n'}C / I^{2n'}C)` for some `n' ≤ n` — that is, if there are
`δ₁, …, δ_r ∈ I^{n'}C` with `ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I^{2n'}C` for every `g ∈ J` — then
there is an `A`-algebra homomorphism `ψ'_{2n'} : B → C / I^{2n'}C` which agrees with `ψₙ` as
maps into `C / I^{n'}C`.

Neither principality of `I` nor regularity of anything on `C` is assumed, and no Cramer
relation on `J` is hypothesised: the only input is the vanishing of the obstruction class. -/
@[stacks 0GAP "the claim"]
public theorem exists_algHom_quotient_of_obstruction_factors
    {I : Ideal A} (hI : I.FG) {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    (n n' : ℕ) (hn' : n' ≤ n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin P.variableCount))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψred : ∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)
      = ψn (P.restrictedToAlgHom g))
    (δ : Fin P.variableCount → C) (hδ : ∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n')
    (hfac : ∀ g ∈ P.restrictedKer, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
      ∈ (I.map (algebraMap A C)) ^ (2 * n')) :
    ∃ ψ₂ : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (by omega : n' ≤ 2 * n'))).comp ψ₂
        = (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn')).comp ψn := by
  classical
  obtain ⟨ψ', hψ'c, hψ'J, hψ'diff⟩ := exists_perturbed_algHom_of_obstruction_factors I hI
    P.restrictedKer n' ψ hψc δ hδ hfac
  have hFker : RingHom.ker P.restrictedToAlgHom.toRingHom ≤
      RingHom.ker
        ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp ψ').toRingHom := by
    intro x hx
    rw [RingHom.mem_ker]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hψ'J x hx)
  refine ⟨AlgHom.liftOfSurjective P.restrictedToAlgHom P.restrictedToAlgHom_surjective
    ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp ψ') hFker,
    AlgHom.ext fun b => ?_⟩
  obtain ⟨y, rfl⟩ := P.restrictedToAlgHom_surjective b
  have hLHS : (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (show n' ≤ 2 * n' by omega))).comp
          (AlgHom.liftOfSurjective P.restrictedToAlgHom P.restrictedToAlgHom_surjective
            ((Ideal.Quotient.mkₐ A ((I.map (algebraMap A C)) ^ (2 * n'))).comp ψ') hFker)
          (P.restrictedToAlgHom y)
      = Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n') (ψ' y) := by
    rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]
    rfl
  have hRHS : (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn')).comp ψn
        (P.restrictedToAlgHom y)
      = Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n') (ψ y) := by
    rw [AlgHom.comp_apply, ← hψred y]
    rfl
  rw [hLHS, hRHS, Ideal.Quotient.eq]
  exact hψ'diff y

/-- **Stacks 0GAP**, the claim of the remark with the lift of `ψₙ` produced internally.

For a Noetherian `A`, an `A`-algebra map `ψₙ : B → C/IⁿC` whose obstruction class vanishes in
`Ext¹_B(NL^∧_{B/A}, I^{n'}C/I^{2n'}C)` — the vanishing being witnessed, as in the source, on
*some* continuous lift `ψ` of `ψₙ`, which by `Rig.obstruction_factors_of_lift_change` is the
same as on every one — lifts to `ψ'_{2n'} : B → C/I^{2n'}C` agreeing with `ψₙ` into
`C/I^{n'}C`. -/
@[stacks 0GAP "the claim, with the lift chosen internally"]
public theorem exists_algHom_quotient_of_obstruction_vanishes
    {I : Ideal A} (hI : I.FG) {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    (n n' : ℕ) (hn' : n' ≤ n)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (hvanish : ∀ ψ : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C,
      @Continuous _ _ (limitTopology I (Fin P.variableCount))
        ((I.map (algebraMap A C)).adicTopology) ψ →
      (∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)
        = ψn (P.restrictedToAlgHom g)) →
      ∃ δ : Fin P.variableCount → C, (∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n') ∧
        ∀ g ∈ P.restrictedKer, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
          ∈ (I.map (algebraMap A C)) ^ (2 * n')) :
    ∃ ψ₂ : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n'),
      (Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (by omega : n' ≤ 2 * n'))).comp ψ₂
        = (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hn')).comp ψn := by
  obtain ⟨ψ, hψc, hψred⟩ := exists_continuousAlgHom_lift_quotient hI P n ψn
  obtain ⟨δ, hδ, hfac⟩ := hvanish ψ hψc hψred
  exact exists_algHom_quotient_of_obstruction_factors hI P n n' hn' ψn ψ hψc hψred δ hδ hfac

/-- **Stacks 0GAP**, the converse of the claim: `o(ψₙ)` is *the* obstruction, not merely an
obstruction. If `ψₙ : B → C/IⁿC` does lift to an `A`-algebra map `ψ₂ : B → C/I²ⁿC`, then the
obstruction map of any continuous lift `ψ` of `ψₙ` already factors through the differential of
`NL^∧_{B/A}`, i.e. `o(ψₙ) = 0` in `Ext¹_B(NL^∧_{B/A}, IⁿC/I²ⁿC)`.

The proof is the independence of the obstruction class of the chosen lift: a continuous lift
`χ` of `ψ₂` is in particular a lift of `ψₙ` with `χ(J) ⊆ I²ⁿC`, so `o(χ) = 0`, and
`o(ψ) = o(χ) - h ∘ d` for `h : dxᵢ ↦ χ(xᵢ) - ψ(xᵢ)`. -/
@[stacks 0GAP "o(ψₙ) is the obstruction: the converse"]
public theorem exists_obstruction_factors_of_exists_algHom_quotient
    {I : Ideal A} (hI : I.FG) {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    (n : ℕ)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin P.variableCount))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψred : ∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)
      = ψn (P.restrictedToAlgHom g))
    (ψ₂ : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n))
    (hψ₂ : (Ideal.Quotient.factorₐ A
        (Ideal.pow_le_pow_right (show n ≤ 2 * n by omega))).comp ψ₂ = ψn) :
    ∃ δ : Fin P.variableCount → C, (∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n) ∧
      ∀ g ∈ P.restrictedKer, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
        ∈ (I.map (algebraMap A C)) ^ (2 * n) := by
  classical
  obtain ⟨χ, hχc, hχred⟩ := exists_continuousAlgHom_lift_quotient hI P (2 * n) ψ₂
  have hsame : ∀ g, χ g - ψ g ∈ (I.map (algebraMap A C)) ^ n := by
    intro g
    rw [← Ideal.Quotient.eq]
    have h1 : Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (χ g)
        = (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (show n ≤ 2 * n by omega)))
          (Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ (2 * n)) (χ g)) := rfl
    have h2 := congrArg (fun F : B.carrier →ₐ[A] _ => F (P.restrictedToAlgHom g)) hψ₂
    simp only [AlgHom.comp_apply] at h2
    rw [h1, hχred g, h2, ← hψred g]
  obtain ⟨ε, hε, hdiff⟩ := exists_obstruction_difference_of_lifts I hI n ψ χ hψc hχc hsame
  refine ⟨fun i => -ε i, fun i => Submodule.neg_mem _ (hε i), ?_⟩
  intro g hg
  have hχJ : χ g ∈ (I.map (algebraMap A C)) ^ (2 * n) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hχred g,
      show P.restrictedToAlgHom g = 0 from hg, map_zero]
  have hneg : ∑ i, ψ (partialDerivative I i g) * (-ε i)
      = -∑ i, ψ (partialDerivative I i g) * ε i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : ψ g - ∑ i, ψ (partialDerivative I i g) * (-ε i)
      = χ g - (χ g - ψ g - ∑ i, ψ (partialDerivative I i g) * ε i) := by
    rw [hneg]; ring
  rw [key]
  exact Ideal.sub_mem _ hχJ (hdiff g)

/-- **Stacks 0GAP**, the headline sentence of the remark: the obstruction to lifting
`ψₙ : B → C/IⁿC` to `C/I²ⁿC` *is* the class `o(ψₙ)`. Reading the class through the cokernel
description of `Ext¹_B(NL^∧_{B/A}, IⁿC/I²ⁿC)` of Stacks 0ALN part (1), its vanishing says
that the obstruction map of a continuous lift `ψ` of `ψₙ` is `h ∘ d` for some
`h : ⨁ i, B dxᵢ → IⁿC/I²ⁿC`, i.e. that there are `δ₁, …, δ_r ∈ IⁿC` with
`ψ(g) - ∑ i, ψ(∂g/∂xᵢ) δᵢ ∈ I²ⁿC` for every `g ∈ J`. -/
@[stacks 0GAP "o(ψₙ) is the obstruction to lifting ψₙ to C/I²ⁿC"]
public theorem obstruction_factors_iff_exists_algHom_quotient
    {I : Ideal A} (hI : I.FG) {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    {C : Type w} [CommRing C] [Algebra A C] [IsAdicComplete (I.map (algebraMap A C)) C]
    (n : ℕ)
    (ψn : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ n)
    (ψ : RestrictedPowerSeries I (Fin P.variableCount) →ₐ[A] C)
    (hψc : @Continuous _ _ (limitTopology I (Fin P.variableCount))
      ((I.map (algebraMap A C)).adicTopology) ψ)
    (hψred : ∀ g, Ideal.Quotient.mk ((I.map (algebraMap A C)) ^ n) (ψ g)
      = ψn (P.restrictedToAlgHom g)) :
    (∃ δ : Fin P.variableCount → C, (∀ i, δ i ∈ (I.map (algebraMap A C)) ^ n) ∧
        ∀ g ∈ P.restrictedKer, ψ g - ∑ i, ψ (partialDerivative I i g) * δ i
          ∈ (I.map (algebraMap A C)) ^ (2 * n))
      ↔ ∃ ψ₂ : B.carrier →ₐ[A] C ⧸ (I.map (algebraMap A C)) ^ (2 * n),
          (Ideal.Quotient.factorₐ A
            (Ideal.pow_le_pow_right (show n ≤ 2 * n by omega))).comp ψ₂ = ψn := by
  refine ⟨fun ⟨δ, hδ, hfac⟩ => ?_, fun ⟨ψ₂, hψ₂⟩ =>
    exists_obstruction_factors_of_exists_algHom_quotient hI P n ψn ψ hψc hψred ψ₂ hψ₂⟩
  obtain ⟨ψ₂, hψ₂⟩ :=
    exists_algHom_quotient_of_obstruction_factors hI P n n le_rfl ψn ψ hψc hψred δ hδ hfac
  refine ⟨ψ₂, hψ₂.trans <| AlgHom.ext fun b => ?_⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (ψn b)
  rw [AlgHom.comp_apply, ← hz]
  rfl

end Claim

end Rig

end
