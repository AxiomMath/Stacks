module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Extension.Generators
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ProIsomorphism

/-!
# `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` as a family of generators

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` be an object of the category
(Stacks 0AL4), and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`, where
`A⟨x⟩ = A[x₁, …, x_r]^∧` is the `I`-adic completion of a polynomial algebra.  Writing
`Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, Stacks 0AJS asserts that the presentation of `B` induces
presentations

`Bₙ = Aₙ[x₁, …, x_r] / Jₙ`,  `Jₙ = J / (J ∩ Iⁿ A⟨x⟩)`.

This file produces the presentation itself, as an `Algebra.Generators Aₙ Bₙ (Fin r)`: the
family of generators is the images of the variables `xᵢ` in `Bₙ`, and what has to be proved
is that `Aₙ[x₁, …, x_r] → Bₙ` is surjective — a family of generators in Mathlib's sense
carries a set-theoretic section of that map, which `Algebra.Generators.ofSurjective`
manufactures from the surjectivity.

Surjectivity comes from two facts.  First, `A⟨x⟩ → B` is surjective by construction of the
presentation.  Second, **polynomials are dense in `A⟨x⟩`**: every element of the completion
agrees with an honest polynomial modulo `Iⁿ A⟨x⟩`, because
`AdicCompletion.pow_smul_top_eq_ker_eval` identifies `Iⁿ A⟨x⟩` with the kernel of the
evaluation `A⟨x⟩ → A[x] / Iⁿ A[x]` and that evaluation is surjective.  Composing, every
element of `Bₙ` is the image of a polynomial with coefficients reduced modulo `Iⁿ`.

## Main definitions

* `Rig.AdicFiniteTypeAlgebra.reductionPow`: `Bₙ = B / IⁿB`, with the ideal written
  `(Iⁿ)·B` so that `Aₙ = A / Iⁿ` maps to it.
* `Rig.AdicFiniteTypeAlgebra.reductionPowAlgebra`: `Bₙ` as an `Aₙ`-algebra.
* `Rig.CompletedPolynomialPresentation.reductionVal`: the images of `x₁, …, x_r` in `Bₙ`.
* `Rig.CompletedPolynomialPresentation.reductionGenerators`: **the presentation
  `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` of Stacks 0AJS**, as an `Algebra.Generators Aₙ Bₙ (Fin r)`.

## Main results

* `Rig.CompletedPolynomialPresentation.exists_sub_mem_adicPow`: polynomials are dense in
  `A⟨x⟩` modulo `Iⁿ A⟨x⟩`.
* `Rig.CompletedPolynomialPresentation.aeval_reductionVal_map`: evaluating a polynomial with
  coefficients reduced modulo `Iⁿ` at the generators is the same as pushing it through
  `A[x] → A⟨x⟩ → B → Bₙ`.
* `Rig.CompletedPolynomialPresentation.surjective_aeval_reductionVal`: `Aₙ[x] → Bₙ` is
  surjective.

## Implementation notes

The ideal of `B` is written `(Iⁿ)·B = Ideal.map (algebraMap A B) (Iⁿ)` rather than
`(I·B)ⁿ = B.adicIdeal ^ n`; the two agree (`reductionPow_eq`, which is `Ideal.map_pow`), but
only the first spelling makes `Iⁿ ≤ (algebraMap A B)⁻¹(IⁿB)` hold by `Ideal.le_comap_map`,
which is what the `Aₙ`-algebra structure is built from.

Following `Rig/NaiveCotangent/Transitivity.lean`, `reductionPowAlgebra` is a named
definition rather than an instance, and the statements that need it carry it in a `letI`.
Making it an instance would put a second `Algebra` structure on a quotient that Mathlib
already reaches through `Ideal.Quotient.quotientAlgebra`, which is the diamond that file
records.

## References

* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 0AJP](https://stacks.math.columbia.edu/tag/0AJP)
* [Stacks Project, Tag 0AL4](https://stacks.math.columbia.edu/tag/0AL4)
-/

@[expose] public section

open Algebra MvPolynomial

namespace Rig

namespace AdicFiniteTypeAlgebra

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The ideal `IⁿB` of an object of (0AL4), written with the power taken in `A`.  This is
`B.adicIdeal ^ n`, but the spelling with the power inside the pushforward is the one for
which `Iⁿ` lies over it by `Ideal.le_comap_map`. -/
public abbrev adicIdealPow (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) : Ideal B.carrier :=
  (I ^ n).map (algebraMap A B.carrier)

/-- `IⁿB = (IB)ⁿ`. -/
public theorem adicIdealPow_eq (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    B.adicIdealPow n = B.adicIdeal ^ n :=
  Ideal.map_pow _ _ _

/-- `Bₙ = B / IⁿB`, the `n`-th reduction of an object of (0AL4). -/
public abbrev reductionPow (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :=
  B.carrier ⧸ B.adicIdealPow n

/-- `Bₙ = B / IⁿB` as an algebra over `Aₙ = A / Iⁿ`, through the map induced by `A → B`,
which sends `Iⁿ` into `IⁿB`. -/
@[instance_reducible]
public noncomputable def reductionPowAlgebra (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    Algebra (A ⧸ I ^ n) (B.reductionPow n) :=
  Ideal.Quotient.algebraQuotientOfLEComap (p := I ^ n) (P := B.adicIdealPow n)
    Ideal.le_comap_map

/-- The structure map `Aₙ → Bₙ` sends the class of `a` to the class of the image of `a`. -/
public theorem reductionPowAlgebra_algebraMap_mk (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ)
    (a : A) :
    letI := reductionPowAlgebra B n
    algebraMap (A ⧸ I ^ n) (B.reductionPow n) (Ideal.Quotient.mk (I ^ n) a)
      = Ideal.Quotient.mk (B.adicIdealPow n) (algebraMap A B.carrier a) :=
  rfl

end AdicFiniteTypeAlgebra

namespace CompletedPolynomialPresentation

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B)

/-- The ideal `Iⁿ A⟨x⟩` of the completed polynomial algebra, on the
`P.completedPolynomialRing` spelling of that ring. -/
public noncomputable abbrev completedAdicPow (n : ℕ) : Ideal P.completedPolynomialRing :=
  (I ^ n).map (algebraMap A P.completedPolynomialRing)

/-- **Polynomials are dense in `A⟨x⟩`.**  Every element of the completed polynomial algebra
agrees with a polynomial modulo `Iⁿ A⟨x⟩`.  This is `AdicCompletion.eval` being surjective
together with `AdicCompletion.pow_smul_top_eq_ker_eval`, which identifies its kernel with
`Iⁿ A⟨x⟩`. -/
public theorem exists_sub_mem_adicPow [IsNoetherianRing A] (n : ℕ)
    (ρ : P.completedPolynomialRing) :
    ∃ q : MvPolynomial (Fin P.variableCount) A,
      ρ - algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing q ∈
        P.completedAdicPow n := by
  have hfg : (I.map (C : A →+* MvPolynomial (Fin P.variableCount) A)).FG :=
    (Ideal.fg_of_isNoetherianRing I).map _
  obtain ⟨q, hq⟩ := Submodule.mkQ_surjective
    ((I.map (C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n •
      (⊤ : Submodule (MvPolynomial (Fin P.variableCount) A)
        (MvPolynomial (Fin P.variableCount) A)))
    (AdicCompletion.eval (I.map (C : A →+* MvPolynomial (Fin P.variableCount) A))
      (MvPolynomial (Fin P.variableCount) A) n ρ)
  refine ⟨q, ?_⟩
  -- `ρ` and the image of `q` have the same `n`-th truncation, so their difference is in the
  -- kernel of the `n`-th evaluation, which is `Iⁿ A⟨x⟩`.
  have hof : algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing q =
      AdicCompletion.of (I.map (C : A →+* MvPolynomial (Fin P.variableCount) A))
        (MvPolynomial (Fin P.variableCount) A) q := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hker : ρ - algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing q ∈
      LinearMap.ker (AdicCompletion.eval
        (I.map (C : A →+* MvPolynomial (Fin P.variableCount) A))
        (MvPolynomial (Fin P.variableCount) A) n) := by
    rw [LinearMap.mem_ker, map_sub, hof, AdicCompletion.eval_of, ← hq, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hfg] at hker
  -- The `A[x]`-submodule `Iⁿ A[x] · A⟨x⟩` is contained in the ideal `Iⁿ A⟨x⟩`.
  have hbridge := map_smul_top_le_map_smul_top (A := A)
    (R := MvPolynomial (Fin P.variableCount) A) (S := P.completedPolynomialRing)
    (M := P.completedPolynomialRing) (I ^ n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at hbridge
  have hmap : (I ^ n).map (algebraMap A (MvPolynomial (Fin P.variableCount) A)) =
      (I.map (C : A →+* MvPolynomial (Fin P.variableCount) A)) ^ n := by
    rw [MvPolynomial.algebraMap_eq, Ideal.map_pow]
  rw [hmap] at hbridge
  have := hbridge hker
  rwa [Submodule.restrictScalars_mem] at this

/-- The presentation map carries `Iⁿ A⟨x⟩` into `IⁿB`. -/
public theorem toAlgHom_mem_adicIdealPow {n : ℕ} {x : P.completedPolynomialRing}
    (hx : x ∈ P.completedAdicPow n) : P.toAlgHom x ∈ B.adicIdealPow n := by
  have hcomp : (P.toAlgHom.toRingHom).comp
      (algebraMap A P.completedPolynomialRing) = algebraMap A B.carrier := by
    ext a
    exact P.toAlgHom.commutes a
  have h := Ideal.mem_map_of_mem P.toAlgHom.toRingHom hx
  rwa [Ideal.map_map, hcomp] at h

/-- The image of the `i`-th variable `xᵢ` in `Bₙ = B / IⁿB`. -/
public noncomputable def reductionVal (n : ℕ) : Fin P.variableCount → B.reductionPow n :=
  fun i => Ideal.Quotient.mk (B.adicIdealPow n)
    (P.toAlgHom (algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing (X i)))

/-- Evaluating a polynomial whose coefficients have been reduced modulo `Iⁿ` at the
generators of `Bₙ` is the same as pushing the polynomial through
`A[x] → A⟨x⟩ → B → B / IⁿB`.  Both sides are ring maps out of `A[x]` agreeing on the
constants and on the variables, so this is an induction over polynomials. -/
public theorem aeval_reductionVal_map (n : ℕ) (q : MvPolynomial (Fin P.variableCount) A) :
    letI := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
    aeval (P.reductionVal n) (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) q) =
      Ideal.Quotient.mk (B.adicIdealPow n) (P.toAlgHom
        (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing q)) := by
  let _ := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
  induction q using MvPolynomial.induction_on with
  | C a =>
    have hC : algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (C a) = algebraMap A P.completedPolynomialRing a :=
      (IsScalarTower.algebraMap_apply A (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing a).symm
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C,
      AdicFiniteTypeAlgebra.reductionPowAlgebra_algebraMap_mk, hC, P.toAlgHom.commutes a]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]
    rfl

/-- **`Aₙ[x₁, …, x_r] → Bₙ` is surjective.**  Every element of `Bₙ = B / IⁿB` lifts to `B`,
then to `A⟨x⟩` since the presentation map is surjective, and then agrees with a polynomial
modulo `Iⁿ A⟨x⟩`, whose image in `Bₙ` is zero. -/
public theorem surjective_aeval_reductionVal [IsNoetherianRing A] (n : ℕ) :
    letI := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
    Function.Surjective (aeval (R := A ⧸ I ^ n) (P.reductionVal n)) := by
  let _ := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
  intro b
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨ρ, rfl⟩ := P.toAlgHom_surjective b'
  obtain ⟨q, hq⟩ := P.exists_sub_mem_adicPow n ρ
  refine ⟨MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) q, ?_⟩
  rw [P.aeval_reductionVal_map n q, Ideal.Quotient.eq, ← neg_sub, neg_mem_iff, ← map_sub]
  exact P.toAlgHom_mem_adicIdealPow hq

/-- **The presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` of Stacks 0AJS**, as a family of
generators of `Bₙ` over `Aₙ` indexed by the same `Fin r` as the presentation of `B` over
`A`.  The generators are the images of the variables `xᵢ`, and the section is the one
`Algebra.Generators.ofSurjective` extracts from `surjective_aeval_reductionVal`. -/
public noncomputable def reductionGenerators [IsNoetherianRing A] (n : ℕ) :
    letI := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
    Algebra.Generators (A ⧸ I ^ n) (B.reductionPow n) (Fin P.variableCount) :=
  letI := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
  Algebra.Generators.ofSurjective (P.reductionVal n) (P.surjective_aeval_reductionVal n)

/-- The generators of `Bₙ` over `Aₙ` are the images of the variables. -/
public theorem reductionGenerators_val [IsNoetherianRing A] (n : ℕ) :
    letI := AdicFiniteTypeAlgebra.reductionPowAlgebra B n
    (P.reductionGenerators n).val = P.reductionVal n :=
  rfl

end CompletedPolynomialPresentation

end Rig

end
