module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms

/-!
# The completed differentials `Ω_{D(n)}` are the completed one-forms of the envelope

Two realisations of the module `Ω_{D(n)}` of [Stacks, Equation 60.17.2, Tag 07J9] live in the
library: `Crystalline.completedTensorPowerDifferentials`, the `p`-adic completion of the divided
power differentials of the envelope `D_{P(n),γ}(J(n))`, which is where the connection of
[Stacks, Lemma 60.17.3, Tag 07JG] takes its values; and the degree one completed forms
`(Crystalline.envelopeDPAlgebra s f).forms s.p 1 n`, the `p`-adic completion of the first
exterior power of the same module, which is where the de Rham complex of
[Stacks, Proposition 60.21.3, Tag 07LG] lives.  This module identifies the two, linearly over
`D(n)`, and shows that the identification carries the universal derivation of the first to the
universal differential of the second.

## Main definitions

* `Crystalline.tensorPowerDifferentialsFormsEquiv` — the identification
  `Ω_{D(n)} ≃ Ω̂¹_{D(n)}`, the completion of `(⋀¹ ≃ id)⁻¹`.

## Main results

* `Crystalline.tensorPowerDifferentialsFormsEquiv_tensorPowerDerivation` — it carries
  `Crystalline.tensorPowerDerivation` to `Crystalline.CosimplicialDPAlgebra.differential`.
-/

@[expose] public section

open DividedPowers

universe u v w

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The completed differentials `Ω_{D(n)}` are the completed one-forms of the envelope**:
the `p`-adic completion of the identification of the divided power differentials with their first
exterior power, linear over `D(n)`. -/
noncomputable def tensorPowerDifferentialsFormsEquiv (n : ℕ) :
    letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
      (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
    completedTensorPowerDifferentials s f n ≃ₗ[completedTensorPowerDividedPowerRing s f hf n]
      completedDividedPowerForms s.p (s.A : Type u)
        (tensorPowerEnvelope s f n).object.dividedPowers 1 :=
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  AdicCompletion.congr (pAdicIdeal (A := (tensorPowerEnvelope s f n).object) s.p)
    (exteriorPower.oneEquiv (tensorPowerEnvelope s f n).object
      (dividedPowerDifferentials (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.dividedPowers)).symm

/-- The identification of `Ω_{D(n)}` with the completed one-forms on the image of an
uncompleted differential. -/
theorem tensorPowerDifferentialsFormsEquiv_of (n : ℕ)
    (ω : letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
        (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
      dividedPowerDifferentials (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.dividedPowers) :
    tensorPowerDifferentialsFormsEquiv s f hf n (AdicCompletion.of _ _ ω) =
      AdicCompletion.of _ _ ((exteriorPower.oneEquiv _ _).symm ω) :=
  rfl

/-- **The identification of `Ω_{D(n)}` with the completed one-forms carries the universal
derivation `d : D(n) → Ω_{D(n)}` to the universal differential `D(n) → Ω̂¹_{D(n)}`.**  Both
sides are additive maps between `p`-adic completions and agree on the image of the uncompleted
envelope, where both are the uncompleted universal differential. -/
theorem tensorPowerDifferentialsFormsEquiv_tensorPowerDerivation (n : ℕ)
    (a : completedTensorPowerDividedPowerRing s f hf n) :
    tensorPowerDifferentialsFormsEquiv s f hf n (tensorPowerDerivation s f hf n a) =
      (envelopeDPAlgebra s f).differential s.p n
        (show completedDividedPowerRing s.p (B := (envelopeDPAlgebra s f).carrier n) from a) := by
  let : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  let E := (tensorPowerEnvelope s f n).object
  let Y := dividedPowerDifferentialForms (A := (s.A : Type u)) E.dividedPowers 1
  let F : AdicCompletion (pAdicIdeal (A := (E : Type (max u w))) s.p) (E : Type (max u w)) →+
      AdicCompletion (pAdicIdeal (A := (E : Type (max u w))) s.p) Y :=
    (tensorPowerDifferentialsFormsEquiv s f hf n).toLinearMap.toAddMonoidHom.comp
      (tensorPowerDerivation s f hf n).toDerivation.toLinearMap.toAddMonoidHom
  let G : AdicCompletion (pAdicIdeal (A := (E : Type (max u w))) s.p) (E : Type (max u w)) →+
      AdicCompletion (pAdicIdeal (A := (E : Type (max u w))) s.p) Y :=
    PAdicCompletion.mapAddHom s.p _ _ (dividedPowerOneForm (s.A : Type u) E.dividedPowers)
  have hFG : F = G := by
    refine adicCompletion_addMonoidHom_ext_of_of s.p fun b => ?_
    refine (congrArg (tensorPowerDifferentialsFormsEquiv s f hf n)
      ((completedTensorPowerDifferential s f hf n).2.2 b)).trans ?_
    exact (PAdicCompletion.mapAddHom_of s.p E E
      (dividedPowerOneForm (s.A : Type u) E.dividedPowers) b).symm
  exact DFunLike.congr_fun hFG a

end Crystalline

end
