module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.Deformation
public import StacksFrontier.RingTheory.RigSmooth.PerturbedIsomorphism

/-!
# The perturbation of the identity through which the comparison map factors

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `r ≥ 0` and `P = A[x₁, …, x_r]^∧`. Let
`a, b ⊆ P` be ideals and let `φ : P ⧸ a → P ⧸ b` be an `A`-algebra map which is congruent to
the identity to precision `N`, that is `φ(x mod a) - (x mod b) ∈ (I · (P ⧸ b))ᴺ` for every
`x ∈ P`. This file produces an `A`-algebra endomorphism `σ` of `P` with

* `σ x - x ∈ (IP)ᴺ` for every `x ∈ P`, and
* `(σ x mod b) = φ(x mod a)` for every `x ∈ P`,

that is, a perturbation of the identity of `P` through which `φ` factors. This is the one step
of Stacks 0GAR that `StacksFrontier.RingTheory.RigSmooth.PerturbedIsomorphism` carried as a
hypothesis: with it, `Rig.PerturbedPresentation.exists_perturbationBound_algEquiv` turns a
comparison map `φ : B → B'` into an isomorphism of `A`-algebras `B ≃ₐ[A] B'`.

## Main results

* `Rig.PerturbedPresentation.exists_perturbationEndomorphism_of_algHom`: the endomorphism `σ`.
* `Rig.PerturbedPresentation.exists_perturbationBound_algEquiv_of_algHom`: Stacks 0GAR with the
  comparison map `φ` of Stacks 0GAQ carried in place of the perturbation `σ`, which is now
  constructed.

## Construction

`P` is the `I`-adic completion of `A[x₁, …, x_r]`, hence (Stacks 0AL0,
`RestrictedPowerSeries.adicCompletionAlgEquiv`) the ring `A⟨x₁, …, x_r⟩` of restricted power
series, and that identification is a homeomorphism for the `IP`-adic topology
(`RestrictedPowerSeries.isHomeomorph_adicCompletionEquiv`). A continuous `A`-algebra map out of
`A⟨x₁, …, x_r⟩` into an `I`-adically complete algebra is therefore determined by, and exists
for, any prescription of the images of the variables (Stacks 0AK3,
`Rig.exists_continuousAlgHom_add_variables`).

Lift `φ(xᵢ mod a) - (xᵢ mod b) ∈ (I · (P ⧸ b))ᴺ` to `δᵢ ∈ (IP)ᴺ` — possible because
`(I · (P ⧸ b))ᴺ` is the image of `(IP)ᴺ` — and let `σ` be the unique continuous `A`-algebra
endomorphism of `P` with `σ(xᵢ) = xᵢ + δᵢ`. The first-order expansion of Stacks 0AK3
(`Rig.eval_add_variables_eq_linear_add_error`) gives

`σ(g) = g + ∑ᵢ (∂g/∂xᵢ) δᵢ + ξ`,  `ξ ∈ (δᵢδⱼ)`,

and both the linear term and `ξ` lie in `(IP)ᴺ`, which is the first conclusion. For the second,
`(· mod b) ∘ σ` and `φ ∘ (· mod a)` are two continuous `A`-algebra maps
`A⟨x₁, …, x_r⟩ → P ⧸ b` taking the same values on the variables, so the *uniqueness* half of
Stacks 0AK3 identifies them.

## Implementation notes

The two inputs the construction needs beyond what was already available are proved here.

* `IsAdicComplete (I · (P ⧸ b)) (P ⧸ b)`, needed for the uniqueness step: `P` is Noetherian
  (Stacks 0316) and `IP`-adically complete, so `IP ≤ jacobson ⊥` (Stacks 05GI) and the finite
  `P`-module `P ⧸ b` is `IP`-adically Hausdorff by Krull's intersection theorem
  (`IsHausdorff.of_le_jacobson`); Stacks 031B (`isAdicComplete_of_iInf_smul_eq_bot`) upgrades
  that to adic completeness. No closedness of `b` is needed, and the criterion of Stacks 031A is
  not used.
* The identification of `RestrictedPowerSeries.limitTopology` with the `IP`-adic topology. This
  is avoided rather than proved: everything is stated for `P` itself, and the restricted power
  series ring enters only through the `A`-algebra identification with `P`, across which the
  public `RestrictedPowerSeries.isHomeomorph_adicCompletionEquiv` already transports continuity.

Consequently nothing here is assumed. The remaining distance to the full statement of Stacks
0GAR is the interface of Stacks 0GAQ (`Rig.exists_algHom_lift_of_dualSituation`), which produces
the map `φ`: `B` has to be presented as an object of Stacks 0AL4 with a completed polynomial
presentation whose ideal is `LinearMap.range g`, and the map `ψₙ : B → B'/IⁿB'` has to be built
from `Rig.PerturbedPresentation.range_sup_pow_eq_of_congruentModPow`. The map `φ` is therefore
carried by `exists_perturbationBound_algEquiv_of_algHom`, with exactly the one property of it
that the final paragraph of the source proof uses.

## References

* [Stacks Project, Tag 0GAR](https://stacks.math.columbia.edu/tag/0GAR)
* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0AK3](https://stacks.math.columbia.edu/tag/0AK3)
* [Stacks Project, Tag 0AL0](https://stacks.math.columbia.edu/tag/0AL0)
* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B)
-/

@[expose] public noncomputable section

open RestrictedPowerSeries

universe u

namespace Rig.PerturbedPresentation

/-! ### Continuity for the adic topologies -/

section AdicContinuity

/-- An `A`-algebra map is continuous for the `I`-adic topologies of its source and target: it
carries `I · R` into `I · S` because it commutes with the structural maps. -/
private theorem continuous_adic_of_algHom {A : Type*} [CommRing A] (I : Ideal A)
    {R : Type*} [CommRing R] [Algebra A R] {S : Type*} [CommRing S] [Algebra A S]
    (f : R →ₐ[A] S) :
    @Continuous R S (I.map (algebraMap A R)).adicTopology
      (I.map (algebraMap A S)).adicTopology f :=
  continuous_adic_of_map_le _ _ (f : R →+* S)
    (le_of_eq (by rw [Ideal.map_map, AlgHom.comp_algebraMap]))

end AdicContinuity

/-! ### The extended ideal of a quotient -/

section QuotientIdeal

variable {A : Type*} [CommRing A] {T : Type*} [CommRing T] [Algebra A T]

/-- The structural map `A → T ⧸ b` is the reduction of the structural map `A → T`. -/
public theorem algebraMap_quotient_comp (b : Ideal T) :
    (Ideal.Quotient.mk b).comp (algebraMap A T) = algebraMap A (T ⧸ b) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A T (T ⧸ b),
    Ideal.Quotient.algebraMap_eq]

/-- The ideal `I · (T ⧸ b)` is the image of `I · T`. -/
private theorem map_quotient_eq (I : Ideal A) (b : Ideal T) :
    (I.map (algebraMap A T)).map (Ideal.Quotient.mk b) = I.map (algebraMap A (T ⧸ b)) := by
  rw [Ideal.map_map, algebraMap_quotient_comp]

/-- Every power of `I · (T ⧸ b)` is the image of the corresponding power of `I · T`; this is
what lets an element of `(I · (T ⧸ b))ⁿ` be lifted to `(I · T)ⁿ`. -/
public theorem map_pow_quotient (I : Ideal A) (b : Ideal T) (n : ℕ) :
    ((I.map (algebraMap A T)) ^ n).map (Ideal.Quotient.mk b)
      = (I.map (algebraMap A (T ⧸ b))) ^ n := by
  rw [Ideal.map_pow, map_quotient_eq]

end QuotientIdeal

/-! ### Adic completeness of a quotient -/

/-! ### The perturbation of the identity -/

section Perturbation

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The perturbation of the identity through which a comparison map factors**, for an
`A`-algebra `T` identified with the restricted power series ring `A⟨x₁, …, x_r⟩`.

The identification is carried as a pair of `A`-algebra maps `E`, `E'` with `E ∘ E' = id`
together with the continuity of `E`; only that much of it is used. See
`exists_perturbationEndomorphism_of_algHom` for the case
`T = A[x₁, …, x_r]^∧` that Stacks 0GAR is about, where all of this is discharged. -/
private theorem exists_perturbation_aux (hI : I.FG) (r N : ℕ)
    {T : Type u} [CommRing T] [Algebra A T]
    [IsAdicComplete (I.map (algebraMap A T)) T]
    (E : RestrictedPowerSeries I (Fin r) →ₐ[A] T)
    (E' : T →ₐ[A] RestrictedPowerSeries I (Fin r)) (hEE' : ∀ x : T, E (E' x) = x)
    (hEcont : @Continuous (RestrictedPowerSeries I (Fin r)) T (limitTopology I (Fin r))
      (I.map (algebraMap A T)).adicTopology E)
    (a b : Ideal T) [IsAdicComplete (I.map (algebraMap A (T ⧸ b))) (T ⧸ b)]
    (φ : (T ⧸ a) →ₐ[A] (T ⧸ b))
    (hφ : ∀ z : T, φ (Ideal.Quotient.mk a z) - Ideal.Quotient.mk b z
      ∈ (I.map (algebraMap A (T ⧸ b))) ^ N) :
    ∃ σ : T →ₐ[A] T,
      (∀ x, σ x - x ∈ (I.map (algebraMap A T)) ^ N) ∧
      ∀ z, Ideal.Quotient.mk b (σ z) = φ (Ideal.Quotient.mk a z) := by
  classical
  -- Lift the displacement of the `i`-th variable to an element of `(I · T) ^ N`.
  have hex : ∀ z : T, ∃ d ∈ (I.map (algebraMap A T)) ^ N,
      Ideal.Quotient.mk b d = φ (Ideal.Quotient.mk a z) - Ideal.Quotient.mk b z := fun z => by
    have h := hφ z
    rw [← map_pow_quotient I b N] at h
    exact (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h
  choose d hdmem hdeq using fun i : Fin r =>
    hex (E (polynomialAlgHom I (Fin r) (MvPolynomial.X i)))
  -- The deformation of `E` prescribing those displacements.
  obtain ⟨ψ, ⟨hψcont, hψX⟩, -⟩ :=
    Rig.exists_continuousAlgHom_add_variables I hI E hEcont d
  refine ⟨ψ.comp E', fun x => ?_, fun z => ?_⟩
  · obtain ⟨ξ, hξ, hx⟩ :=
      Rig.eval_add_variables_eq_linear_add_error I hI E ψ hEcont hψcont d hψX (E' x)
    have hspan : Ideal.span (Set.range (fun ij : Fin r × Fin r => d ij.1 * d ij.2))
        ≤ (I.map (algebraMap A T)) ^ N := by
      rw [Ideal.span_le]
      rintro y ⟨⟨i, j⟩, rfl⟩
      exact Ideal.mul_mem_left _ _ (hdmem j)
    have heq : ψ (E' x) - x = (∑ i, E (Rig.partialDerivative I i (E' x)) * d i) + ξ := by
      rw [hx, hEE' x]
      ring
    rw [AlgHom.comp_apply, heq]
    exact Submodule.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hdmem i))
      (hspan hξ)
  let _ : TopologicalSpace T := (I.map (algebraMap A T)).adicTopology
  let _ : TopologicalSpace (T ⧸ a) := (I.map (algebraMap A (T ⧸ a))).adicTopology
  let _ : TopologicalSpace (T ⧸ b) := (I.map (algebraMap A (T ⧸ b))).adicTopology
  have hqb : @Continuous T (T ⧸ b) (I.map (algebraMap A T)).adicTopology
      (I.map (algebraMap A (T ⧸ b))).adicTopology (Ideal.Quotient.mkₐ A b) :=
    continuous_adic_of_algHom I (Ideal.Quotient.mkₐ A b)
  have hu₁X : ∀ i : Fin r, ((Ideal.Quotient.mkₐ A b).comp ψ)
        (polynomialAlgHom I (Fin r) (MvPolynomial.X i))
      = ((Ideal.Quotient.mkₐ A b).comp E)
          (polynomialAlgHom I (Fin r) (MvPolynomial.X i))
        + Ideal.Quotient.mk b (d i) := by
    intro i
    simp only [AlgHom.comp_apply, hψX i, map_add, Ideal.Quotient.mkₐ_eq_mk]
  have hu₂X : ∀ i : Fin r, (φ.comp ((Ideal.Quotient.mkₐ A a).comp E))
        (polynomialAlgHom I (Fin r) (MvPolynomial.X i))
      = ((Ideal.Quotient.mkₐ A b).comp E)
          (polynomialAlgHom I (Fin r) (MvPolynomial.X i))
        + Ideal.Quotient.mk b (d i) := by
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [hdeq i]
    ring
  obtain ⟨w, -, huniq⟩ :=
    Rig.exists_continuousAlgHom_add_variables I hI ((Ideal.Quotient.mkₐ A b).comp E)
      (hqb.comp hEcont) (fun i => Ideal.Quotient.mk b (d i))
  have hkey : (Ideal.Quotient.mkₐ A b).comp ψ = φ.comp ((Ideal.Quotient.mkₐ A a).comp E) :=
    (huniq ((Ideal.Quotient.mkₐ A b).comp ψ) ⟨hqb.comp hψcont, hu₁X⟩).trans
      (huniq (φ.comp ((Ideal.Quotient.mkₐ A a).comp E))
        ⟨(continuous_adic_of_algHom I φ).comp
          ((continuous_adic_of_algHom I (Ideal.Quotient.mkₐ A a)).comp hEcont), hu₂X⟩).symm
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hEE' z] using
    DFunLike.congr_fun hkey (E' z)

end Perturbation

/-! ### Stacks 0GAR over `P = A[x₁, …, x_r]^∧` -/

section CompletedPolynomial

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- **The perturbation of the identity of `P = A[x₁, …, x_r]^∧` through which a comparison map
factors.**

Let `a, b ⊆ P` be ideals and let `φ : P ⧸ a → P ⧸ b` be an `A`-algebra map congruent to the
identity modulo `(IP')ᴺ`, `P' = P ⧸ b`. Then there is an `A`-algebra endomorphism `σ` of `P`
congruent to the identity modulo `(IP)ᴺ` with `(σ · mod b) = φ(· mod a)`.

This is the step of Stacks 0GAR that
`Rig.PerturbedPresentation.exists_perturbationBound_algEquiv` carried as a hypothesis; see the
module docstring for the construction. -/
public theorem exists_perturbationEndomorphism_of_algHom (N : ℕ)
    (a b : Ideal (completedPolynomialAlgebra I r))
    (φ : (completedPolynomialAlgebra I r ⧸ a) →ₐ[A] (completedPolynomialAlgebra I r ⧸ b))
    (hφ : ∀ z : completedPolynomialAlgebra I r,
      φ (Ideal.Quotient.mk a z) - Ideal.Quotient.mk b z
        ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r ⧸ b))) ^ N) :
    ∃ σ : completedPolynomialAlgebra I r →ₐ[A] completedPolynomialAlgebra I r,
      (∀ x, σ x - x ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r))) ^ N) ∧
      ∀ z, Ideal.Quotient.mk b (σ z) = φ (Ideal.Quotient.mk a z) := by
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hc : IsAdicComplete (I.map (algebraMap A (completedPolynomialAlgebra I r)))
      (completedPolynomialAlgebra I r) := isAdicComplete_completedPolynomialAlgebra A I r
  have hcq : IsAdicComplete (I.map (algebraMap A (completedPolynomialAlgebra I r ⧸ b)))
      (completedPolynomialAlgebra I r ⧸ b) := by
    rw [← map_quotient_eq I b]
    exact isAdicComplete_quotient (I.map (algebraMap A (completedPolynomialAlgebra I r))) b
  let _ : TopologicalSpace (completedPolynomialAlgebra I r) :=
    (I.map (algebraMap A (completedPolynomialAlgebra I r))).adicTopology
  exact exists_perturbation_aux (T := completedPolynomialAlgebra I r) I hI r N
    (adicCompletionAlgEquiv I (Fin r)).toAlgHom
    (adicCompletionAlgEquiv I (Fin r)).symm.toAlgHom
    (fun x => (adicCompletionAlgEquiv I (Fin r)).apply_symm_apply x)
    (isHomeomorph_adicCompletionEquiv I (Fin r) hI).continuous a b φ hφ

/-- **Stacks 0GAR, with the comparison map of Stacks 0GAQ carried.**

Given a resolution `P^⊕t --K--> P^⊕m --g--> P → B → 0` over `P = A[x₁, …, x_r]^∧` and the
precision loss `loss` of the lifting lemma Stacks 0GAQ, there is an integer `n₀` such that for
every `n ≥ n₀` and every complex `P^⊕t --K'--> P^⊕m --g'--> P` congruent to the given one modulo
`IⁿP`:

* the perturbed complex is again a resolution, and
* every `A`-algebra map `φ : B → B'` congruent to the identity modulo `I^{n-loss}B'` is an
  isomorphism of `A`-algebras `B ≃ₐ[A] B'`.

This is `Rig.PerturbedPresentation.exists_perturbationBound_algEquiv_completedPolynomial` with
its hypothesis on `σ` discharged by `exists_perturbationEndomorphism_of_algHom`: `σ` is
congruent to the identity modulo `I^{n-loss}P` by construction, and it carries each `gᵢ` into
`(g'₁, …, g'_m)` because `gᵢ` dies in `B` and `σ` descends to `φ`.

Only the construction of `φ` itself — the interface of Stacks 0GAQ — is left; see the module
docstring. -/
public theorem exists_perturbationBound_algEquiv_of_algHom (loss : ℕ) {t m : ℕ}
    (K : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      (Fin m → completedPolynomialAlgebra I r))
    (g : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
      completedPolynomialAlgebra I r)
    (hexact : LinearMap.ker g = LinearMap.range K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (K' : (Fin t → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          (Fin m → completedPolynomialAlgebra I r))
        (g' : (Fin m → completedPolynomialAlgebra I r) →ₗ[completedPolynomialAlgebra I r]
          completedPolynomialAlgebra I r),
      g'.comp K' = 0 →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) K K' n →
      CongruentModPow (I.map (algebraMap A (completedPolynomialAlgebra I r))) g g' n →
        LinearMap.ker g' = LinearMap.range K' ∧
        ∀ φ : (completedPolynomialAlgebra I r ⧸
              (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) →ₐ[A]
            (completedPolynomialAlgebra I r ⧸
              (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r))),
          (∀ z : completedPolynomialAlgebra I r,
            φ (Ideal.Quotient.mk (LinearMap.range g :
                Ideal (completedPolynomialAlgebra I r)) z)
              - Ideal.Quotient.mk (LinearMap.range g' :
                Ideal (completedPolynomialAlgebra I r)) z
            ∈ (I.map (algebraMap A (completedPolynomialAlgebra I r ⧸
                (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r))))) ^ (n - loss)) →
          Nonempty
            ((completedPolynomialAlgebra I r ⧸
                (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))) ≃ₐ[A]
              (completedPolynomialAlgebra I r ⧸
                (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r)))) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_perturbationBound_algEquiv_completedPolynomial A I r loss K g hexact
  refine ⟨n₀, fun n hn K' g' hcomplex hKK' hgg' => ?_⟩
  obtain ⟨hker, hbound⟩ := hn₀ n hn K' g' hcomplex hKK' hgg'
  refine ⟨hker, fun φ hφ => ?_⟩
  obtain ⟨σ, hσ1, hσ2⟩ := exists_perturbationEndomorphism_of_algHom A I r (n - loss)
    (LinearMap.range g : Ideal (completedPolynomialAlgebra I r))
    (LinearMap.range g' : Ideal (completedPolynomialAlgebra I r)) φ hφ
  refine hbound σ hσ1 fun i => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, hσ2,
    Ideal.Quotient.eq_zero_iff_mem.mpr (LinearMap.mem_range_self g _), map_zero]

end CompletedPolynomial

end Rig.PerturbedPresentation

end
