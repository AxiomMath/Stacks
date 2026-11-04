module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedPresentation

/-!
# Transitivity over an acyclic base

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` and `C` objects of the category of Stacks
0AL4 and `B → C` a morphism, with `B = A⟨x₁, …, x_r⟩ / J` a completed polynomial presentation
and `ψ : B⟨y₁, …, y_s⟩ ↠ C` a presentation of `C` over `B`.  If the differential of `NL^∧_{B/A}`
is bijective — the shape acyclicity takes for an étale base, by
`Rig.bijective_completedDifferential` — then both outer terms of the six-term exact sequence of
Stacks 0ALM vanish, so the sequence degenerates and

```
H⁻¹(NL^∧_{C/A}) ≅ H⁻¹(NL^∧_{C/B}),      H⁰(NL^∧_{C/A}) ≅ H⁰(NL^∧_{C/B}).
```

This is the second step of the proof of Stacks 0GCK: applied to `A → (A')^ → (B')^` it says that
`NL^∧_{(B')^/A} → NL^∧_{(B')^/(A')^}` is a quasi-isomorphism, which is what lets the Ext¹
annihilation be compared across the horizontal maps of a localization diagram.

## Main results

* `Rig.bijective_liftBaseChange_of_bijective` — base change of a bijective two-term
  differential with finite free degree-zero term is bijective.
* `Rig.CompletedPolynomialPresentation.bijective_innerBaseChangeDifferential` — hence the
  differential of `NL^∧_{B/A} ⊗_B C` is bijective.
* `Rig.CompletedPolynomialPresentation.bijective_onH₁_chainMapProj_of_bijective` and
  `Rig.CompletedPolynomialPresentation.bijective_onH₀_chainMapProj_of_bijective` — the two maps
  `H(NL^∧_{C/A}) → H(NL^∧_{C/B})` of Stacks 0ALM are bijective.

## Implementation notes

Only the degeneration of the sequence is proved here, not the lemma `H⁻¹(NL^∧_{B/A} ⊗_B C) = 0`
in the form "a flat base change of an acyclic complex is acyclic": bijectivity of the
differential is preserved by an arbitrary base change, so no flatness is needed and the
identification `S ⊗_R (⨁_{i<n} R) ≅ ⨁_{i<n} S` of `TensorProduct.piScalarRight` is the only
input beyond `LinearEquiv.baseChange`.

The two degeneration statements are deliberately phrased with the hypothesis "the differential
of `NL^∧_{B/A}` is bijective" rather than "`NL^∧_{B/A}` is acyclic", because the latter does not
survive base change and the former is what the étale case supplies.

## References

* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
-/

@[expose] public noncomputable section

namespace Rig

universe u v

section BaseChange

/-- Base change along `R → S` of a two-term differential `d : M → ⨁_{i<n} R` whose degree-zero
term is finite free: if `d` is bijective then so is its base change, with no flatness
hypothesis, because base change of a linear equivalence is a linear equivalence. -/
public theorem bijective_liftBaseChange_of_bijective {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (d : M →ₗ[R] (Fin n → R)) (h : Function.Bijective d) :
    Function.Bijective
      ((((Algebra.linearMap R S).compLeft (Fin n)) ∘ₗ d).liftBaseChange S) := by
  classical
  have hE : (TensorProduct.piScalarRight R S S (Fin n)).toLinearMap ∘ₗ (d.baseChange S) =
      (((Algebra.linearMap R S).compLeft (Fin n)) ∘ₗ d).liftBaseChange S := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun c => LinearMap.ext fun m => ?_
    funext j
    simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_comm]
  rw [← hE, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (TensorProduct.piScalarRight R S S (Fin n)).bijective.comp
    (LinearEquiv.baseChange R S M (Fin n → R) (LinearEquiv.ofBijective d h)).bijective

end BaseChange

section Degeneration

variable {R : Type*} [CommRing R]

/-- A map whose kernel is the range of a map out of a subsingleton is injective. -/
private theorem injective_of_exact_of_subsingleton_source
    {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Subsingleton M] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : Function.Exact f g) : Function.Injective g := by
  rw [← LinearMap.ker_eq_bot, LinearMap.exact_iff.mp h, LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- A map whose range is the kernel of a map into a subsingleton is surjective. -/
private theorem surjective_of_exact_of_subsingleton_target
    {N P Q : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Subsingleton Q] {g : N →ₗ[R] P} {δ : P →ₗ[R] Q}
    (h : Function.Exact g δ) : Function.Surjective g := by
  rw [← LinearMap.range_eq_top, ← LinearMap.exact_iff.mp h, LinearMap.ker_eq_top]
  exact LinearMap.ext fun _ => Subsingleton.elim _ _

end Degeneration

namespace CompletedPolynomialPresentation

section Inner

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B)
  {C : AdicFiniteTypeAlgebra.{u, v} A I} [Algebra B.carrier C.carrier]
  (KB : CompletedNaiveCotangentComplex P)

/-- If the differential of `NL^∧_{B/A}` is bijective then so is the differential of
`NL^∧_{B/A} ⊗_B C`, the complex `X` of Stacks 0ALM. -/
public theorem bijective_innerBaseChangeDifferential
    (hKB : Function.Bijective KB.differential) :
    Function.Bijective (P.innerBaseChangeDifferential (C := C) KB) :=
  bijective_liftBaseChange_of_bijective KB.differential hKB

/-- `H⁻¹(NL^∧_{B/A} ⊗_B C) = 0` when the differential of `NL^∧_{B/A}` is bijective. -/
public theorem subsingleton_h1_innerBaseChange (hKB : Function.Bijective KB.differential) :
    Subsingleton
      (NaiveCotangent.H₁
        (NaiveCotangent.TwoTerm.ofFree (P.innerBaseChangeDifferential (C := C) KB))) :=
  Submodule.subsingleton_iff_eq_bot.mpr
    (LinearMap.ker_eq_bot.mpr (P.bijective_innerBaseChangeDifferential (C := C) KB hKB).1)

/-- `H⁰(NL^∧_{B/A} ⊗_B C) = 0` when the differential of `NL^∧_{B/A}` is bijective. -/
public theorem subsingleton_h0_innerBaseChange (hKB : Function.Bijective KB.differential) :
    Subsingleton
      (NaiveCotangent.H₀
        (NaiveCotangent.TwoTerm.ofFree (P.innerBaseChangeDifferential (C := C) KB))) :=
  Submodule.Quotient.subsingleton_iff.mpr
    (LinearMap.range_eq_top.mpr (P.bijective_innerBaseChangeDifferential (C := C) KB hKB).2)

end Inner

section SixTerm

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B) [IsNoetherianRing A] (s : ℕ)
  {C : AdicFiniteTypeAlgebra.{u, v} A I} [Algebra B.carrier C.carrier]
  [IsScalarTower A B.carrier C.carrier]
  (ψ : AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s) →ₐ[B.carrier] C.carrier)
  (hψ : Function.Surjective (ψ.restrictScalars A))
  (KB : CompletedNaiveCotangentComplex P)
  (KC : CompletedNaiveCotangentComplex (P.combinedPresentation s (ψ.restrictScalars A) hψ))
  (F : Fin s → Derivation B.carrier
    (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s))
    (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s)))

/-- **`H⁻¹(NL^∧_{C/A}) ≅ H⁻¹(NL^∧_{C/B})` over an acyclic base.**  When the differential of
`NL^∧_{B/A}` is bijective, the first and fourth terms of the six-term exact sequence of Stacks
0ALM vanish, so its middle map in degree `-1` is injective by exactness on the left and
surjective because the connecting map lands in a zero module. -/
public theorem bijective_onH₁_chainMapProj_of_bijective
    (hKB : Function.Bijective KB.differential)
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology B.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology B.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) B.carrier),
      F j (algebraMap (MvPolynomial (Fin s) B.carrier)
          (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) B.carrier)
          (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q)) :
    Function.Bijective (NaiveCotangent.chainMapProj _
      (P.outerDifferential_comp_outerCotangentMap s ψ hψ KC F hFc hFp)).onH₁ := by
  have h1 := P.subsingleton_h1_innerBaseChange (C := C) KB hKB
  have h0 := P.subsingleton_h0_innerBaseChange (C := C) KB hKB
  obtain ⟨δ, hex₁, hex₂, -, -, -⟩ :=
    P.exists_sixTerm_exact_combined s ψ hψ KB KC F hFc hFp
  exact ⟨injective_of_exact_of_subsingleton_source hex₁,
    surjective_of_exact_of_subsingleton_target hex₂⟩

/-- **`H⁰(NL^∧_{C/A}) ≅ H⁰(NL^∧_{C/B})` over an acyclic base.**  When the differential of
`NL^∧_{B/A}` is bijective, the fourth term of the six-term exact sequence of Stacks 0ALM
vanishes, so its middle map in degree `0` is injective; surjectivity is the right exactness of
that sequence. -/
public theorem bijective_onH₀_chainMapProj_of_bijective
    (hKB : Function.Bijective KB.differential)
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology B.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology B.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) B.carrier),
      F j (algebraMap (MvPolynomial (Fin s) B.carrier)
          (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) B.carrier)
          (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q)) :
    Function.Bijective (NaiveCotangent.chainMapProj _
      (P.outerDifferential_comp_outerCotangentMap s ψ hψ KC F hFc hFp)).onH₀ := by
  have h0 := P.subsingleton_h0_innerBaseChange (C := C) KB hKB
  obtain ⟨δ, -, -, -, hex₄, hsurj⟩ :=
    P.exists_sixTerm_exact_combined s ψ hψ KB KC F hFc hFp
  exact ⟨injective_of_exact_of_subsingleton_source hex₄, hsurj⟩

end SixTerm

end CompletedPolynomialPresentation

end Rig

end
