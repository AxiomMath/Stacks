module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsOfCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetractEquivalence
public import StacksFrontier.AlgebraicGeometry.Crystalline.PairFormsTransport

/-!
# The two spellings of `Ω_D` for the completed envelope of a presentation

Let `g : A[x_i] → C` be a surjective presentation in finitely many variables, `E` the divided
power envelope of the kernel of `A[x_{(0,i)}] → C` (the degree-zero tensor power of `g`, the
presentation [Stacks, Lemma 60.17.3, Tag 07JG] works with) and `D = Ê` its `p`-adic completion.
The library has two spellings of the module `Ω_D` of [Stacks, Tag 07J9]:

* `Crystalline.completedTensorPowerDifferentials`, the completion `Ω̂_{E/A,δ}` of the divided
  power differentials of `E`, with the derivation `Crystalline.tensorPowerDerivation`: where the
  connections of the pairs of [Stacks, Tag 07JG] take their values;
* `Crystalline.envelopeCompletionForms`, the completed one-forms `Ω̂¹_{D/A,γ̂}` of the completed
  ring `D` itself, with its universal differential: where the connections of the pairs of
  [Stacks, Lemma 60.17.5, Tag 07L5] take their values
  (`Crystalline.polynomialEnvelopeCoordinates`).

This module identifies the two, `D`-linearly and compatibly with the derivations
(`Crystalline.tensorPowerOneFormsEquiv`, `Crystalline.tensorPowerOneFormsEquiv_derivation`), and
deduces that the two categories of pairs are the same
(`Crystalline.tensorPowerPairFormsEquivalence`): a pair of [Stacks, Tag 07JG] for the presentation
`g` is a pair of [Stacks, Tag 07L5] by composing its connection with the identification.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers

universe u v

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type u} [Fintype ι] [DecidableEq ι]
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-- The envelope of the presentation `A[x_{(0,i)}] → C` of the degree-zero tensor power, as
`Crystalline.polynomialEnvelopeCoordinates` spells it. -/
local notation "E₀" => presentationEnvelope s (tensorPowerPresentation s g 0)

/-- The same envelope, as `Crystalline.completedTensorPowerDifferentials` spells it. -/
local notation "T₀" => tensorPowerEnvelope s g 0

omit [Fintype ι] [DecidableEq ι] in
/-- `p` is nilpotent modulo the divided power ideal of the envelope; unlike
`Crystalline.presentationEnvelope_prime_nilpotent`, this does not mention the surjectivity of the
presentation, so that an instance stated with it can be found. -/
theorem tensorPowerPresentationEnvelope_prime_nilpotent :
    IsNilpotent (Ideal.Quotient.mk
      (presentationEnvelope s (tensorPowerPresentation s g 0)).object.ideal
      (s.p : (presentationEnvelope s (tensorPowerPresentation s g 0)).object)) :=
  polynomialDividedPowerEnvelope_prime_nilpotent s (tensorPowerPresentation s g 0)

/-- `p` is nilpotent modulo the divided power ideal of the envelope. -/
local notation "hE₀" => tensorPowerPresentationEnvelope_prime_nilpotent s g

/-- The coordinates of the completed envelope `D` of the degree-zero tensor power. -/
local notation "C₀" => polynomialEnvelopeCoordinates s (tensorPowerPresentation s g 0)
  (tensorPowerPresentation_surjective s g hg 0)

/-- `Ω̂_{E/A,δ}` is a module over the completed envelope `D`, as the completion of a module over
the envelope `E`. -/
instance moduleEnvelopeCompletionTensorPowerDifferentials :
    Module (envelopeCompletion E₀ s.p hE₀) (completedTensorPowerDifferentials s g 0) :=
  inferInstanceAs (Module
    (AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
    (completedTensorPowerDifferentials s g 0))

omit [Fintype ι] [DecidableEq ι] in
/-- **The universal derivation `d : D → Ω̂_{E/A,δ}` is the completion of the universal divided
power differential of the envelope.** -/
theorem tensorPowerDerivation_eq_mapAddHom
    (x : AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object) :
    letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
    tensorPowerDerivation s g hg 0 x = PAdicCompletion.mapAddHom s.p (T₀).object (T₀).object
      (AddMonoidHom.mk' (dividedPowerDifferential (A := (s.A : Type u))
        (T₀).object.dividedPowers) (dividedPowerDifferential_add _)) x := by
  let : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
  have h := adicCompletion_addMonoidHom_ext_of_of s.p
    (f := (tensorPowerDerivation s g hg 0).toDerivation.toLinearMap.toAddMonoidHom)
    (g := PAdicCompletion.mapAddHom s.p (T₀).object (T₀).object
      (AddMonoidHom.mk' (dividedPowerDifferential (A := (s.A : Type u))
        (T₀).object.dividedPowers) (dividedPowerDifferential_add _))) fun b ↦
      (tensorPowerDerivation_of s g hg 0 b).trans
        (PAdicCompletion.mapAddHom_of s.p (T₀).object (T₀).object
          (AddMonoidHom.mk' (dividedPowerDifferential (A := (s.A : Type u))
            (T₀).object.dividedPowers) (dividedPowerDifferential_add _)) b).symm
  exact DFunLike.congr_fun h x

/-- Step one: `Ω̂_{E/A,δ} ≃ Ω̂¹_{E/A,δ}`. -/
def tensorPowerOneFormsEquivAux₁ :
    letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
    completedTensorPowerDifferentials s g 0 ≃ₗ[AdicCompletion
        (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object]
      completedDividedPowerForms s.p (s.A : Type u) (T₀).object.dividedPowers 1 :=
  letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
  (completedOneFormsEquiv s.p (s.A : Type u) (T₀).object.dividedPowers).symm

/-- **The two spellings of `Ω_D` agree**: the completion `Ω̂_{E/A,δ}` of the divided power
differentials of the envelope `E` (`Crystalline.completedTensorPowerDifferentials`), and the
completed one-forms `Ω̂¹_{D/A,γ̂}` of the completed ring `D = Ê` itself
(`Crystalline.envelopeCompletionForms`), linearly over `D`. -/
def tensorPowerOneFormsEquiv :
    completedTensorPowerDifferentials s g 0 ≃ₗ[envelopeCompletion E₀ s.p hE₀] (C₀).forms :=
  letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
  ((tensorPowerOneFormsEquivAux₁ s g).trans
    ((completedFormsOfCompletionEquiv s.p (s.A : Type u) (T₀).object.dividedPowers hE₀ 1).trans
    (completedDividedPowerFormsAlgebraCongr s.p (s.A : Type u)
      (B := AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
      (completedDividedPowers (T₀).object.ideal (T₀).object.dividedPowers s.p hE₀).1 1
      inferInstance (algebraBaseEnvelopeCompletion E₀ s.p hE₀)
      (Algebra.algebra_ext _ _ fun _ ↦ rfl))) :
    _ ≃ₗ[AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object] _)

omit [Fintype ι] [DecidableEq ι] in
/-- Step one carries the universal derivation of [Stacks, Tag 07JA] to the universal
differential of `Ω̂¹_{E/A,δ}`. -/
theorem tensorPowerOneFormsEquivAux₁_derivation
    (x : AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object) :
    letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
    tensorPowerOneFormsEquivAux₁ s g (tensorPowerDerivation s g hg 0 x) =
      completedFormsDifferential s.p (s.A : Type u) (T₀).object.dividedPowers x := by
  let : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  refine (tensorPowerDerivation_eq_mapAddHom s g hg x).trans ?_
  exact (completedOneFormsEquiv_completedFormsDifferential s.p (s.A : Type u)
    (T₀).object.dividedPowers x).symm

/-- The value of `Crystalline.tensorPowerOneFormsEquiv`. -/
theorem tensorPowerOneFormsEquiv_apply (ω : completedTensorPowerDifferentials s g 0) :
    letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
    tensorPowerOneFormsEquiv s g hg ω = completedDividedPowerFormsAlgebraCongr s.p (s.A : Type u)
      (B := AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
      (completedDividedPowers (T₀).object.ideal (T₀).object.dividedPowers s.p hE₀).1 1
      inferInstance (algebraBaseEnvelopeCompletion E₀ s.p hE₀)
      (Algebra.algebra_ext _ _ fun _ ↦ rfl)
      (completedFormsOfCompletionEquiv s.p (s.A : Type u) (T₀).object.dividedPowers hE₀ 1
        (tensorPowerOneFormsEquivAux₁ s g ω)) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Steps one and two carry the universal derivation to the universal differential. -/
theorem tensorPowerOneFormsEquivAux_derivation
    (x : AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object) :
    letI : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
    completedDividedPowerFormsAlgebraCongr s.p (s.A : Type u)
      (B := AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
      (completedDividedPowers (T₀).object.ideal (T₀).object.dividedPowers s.p hE₀).1 1
      inferInstance (algebraBaseEnvelopeCompletion E₀ s.p hE₀)
      (Algebra.algebra_ext _ _ fun _ ↦ rfl)
      (completedFormsOfCompletionEquiv s.p (s.A : Type u) (T₀).object.dividedPowers hE₀ 1
        (tensorPowerOneFormsEquivAux₁ s g (tensorPowerDerivation s g hg 0 x))) =
    @completedDividedPowerDifferentialOnRing s.p (s.A : Type u) _
      (AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object) _
      (algebraBaseEnvelopeCompletion E₀ s.p hE₀) _
      (completedDividedPowers (T₀).object.ideal (T₀).object.dividedPowers s.p hE₀).1 x := by
  let : Algebra (s.A : Type u) (T₀).object := (T₀).structureMap.toRingHom.toAlgebra
  have h1 := tensorPowerOneFormsEquivAux₁_derivation s g hg x
  have h2 := completedFormsOfCompletionEquiv_completedFormsDifferential s.p (s.A : Type u)
    (T₀).object.dividedPowers hE₀ x
  have h3 := completedDividedPowerFormsAlgebraCongr_differentialOnRing s.p (s.A : Type u)
    (B := AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
    (completedDividedPowers (T₀).object.ideal (T₀).object.dividedPowers s.p hE₀).1
    inferInstance (algebraBaseEnvelopeCompletion E₀ s.p hE₀)
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) x
  refine (DFunLike.congr_arg _ ((DFunLike.congr_arg _ h1).trans h2)).trans h3

/-- **The identification carries the universal derivation `d : D → Ω̂_{E/A,δ}` of
[Stacks, Tag 07JA] to the universal differential `D → Ω̂¹_{D/A,γ̂}`.** -/
theorem tensorPowerOneFormsEquiv_derivation (x : envelopeCompletion E₀ s.p hE₀) :
    tensorPowerOneFormsEquiv s g hg (tensorPowerDerivation s g hg 0 x) = (C₀).diff x :=
  (tensorPowerOneFormsEquiv_apply s g hg _).trans (tensorPowerOneFormsEquivAux_derivation s g hg x)

/-- **The differentials `d x_i ∈ Ω̂_{E/A,δ}` of the variables** of the presentation, the
coordinates of the pairs of [Stacks, Lemma 60.17.3, Tag 07JG]. -/
def tensorPowerVariableDifferential (i : ι) : completedTensorPowerDifferentials s g 0 :=
  tensorPowerDerivation s g hg 0 (algebraMap (T₀).object
    (AdicCompletion (pAdicIdeal (A := ((T₀).object : Type u)) s.p) (T₀).object)
    ((T₀).algebraMap.toRingHom (MvPolynomial.X ((0 : Fin 1), i))))

/-- The identification carries `d x_i` to the coordinate differential `d x_{(0,i)}`. -/
theorem tensorPowerOneFormsEquiv_variableDifferential (i : ι) :
    tensorPowerOneFormsEquiv s g hg (tensorPowerVariableDifferential s g hg i) =
      (C₀).dx ((Equiv.uniqueProd ι (Fin 1)).symm i) :=
  tensorPowerOneFormsEquiv_derivation s g hg _

/-- The basis of `Ω̂_{E/A,δ}` on the `d x_i`, carried from the basis of the completed one-forms
of `D`. -/
def tensorPowerOneFormsBasis :
    Module.Basis ι (envelopeCompletion E₀ s.p hE₀) (completedTensorPowerDifferentials s g 0) :=
  (((C₀).basis.map (tensorPowerOneFormsEquiv s g hg).symm)).reindex
    (Equiv.uniqueProd ι (Fin 1))

/-- The identification carries the basis vector `d x_i` to the basis vector `d x_{(0,i)}`. -/
theorem tensorPowerOneFormsEquiv_basis (i : ι) :
    tensorPowerOneFormsEquiv s g hg (tensorPowerOneFormsBasis s g hg i) =
      (C₀).basis ((Equiv.uniqueProd ι (Fin 1)).symm i) :=
  (congrArg (tensorPowerOneFormsEquiv s g hg)
    (((C₀).basis.map (tensorPowerOneFormsEquiv s g hg).symm).reindex_apply
      (Equiv.uniqueProd ι (Fin 1)) i)).trans
    ((congrArg (tensorPowerOneFormsEquiv s g hg) (Module.Basis.map_apply _ _ _)).trans
      (LinearEquiv.apply_symm_apply _ _))

/-- The basis of `Ω̂_{E/A,δ}` is the family of the `d x_i`. -/
theorem tensorPowerVariableDifferential_eq_basis (i : ι) :
    tensorPowerVariableDifferential s g hg i = tensorPowerOneFormsBasis s g hg i := by
  refine (tensorPowerOneFormsEquiv s g hg).injective ?_
  exact (tensorPowerOneFormsEquiv_variableDifferential s g hg i).trans
    (((C₀).dx_eq _).trans (tensorPowerOneFormsEquiv_basis s g hg i).symm)

/-- **The pairs over `D` for the two spellings of `Ω_D` are the same**: the pairs `(M, ∇)` of
[Stacks, Lemma 60.17.3, Tag 07JG], with values in `M ⊗̂ Ω̂_{E/A,δ}` and coordinates the `d x_i`,
and the pairs with values in `M ⊗̂ Ω̂¹_{D/A,γ̂}` and coordinates the `d x_{(0,i)}`, which are those
of [Stacks, Lemma 60.17.5, Tag 07L5] (`Crystalline.exists_presentation_retract_pairEquivalence`).
The functor composes the connection with the identification
`Crystalline.tensorPowerOneFormsEquiv`; the module is unchanged. -/
def tensorPowerPairFormsEquivalence :
    Pair.{u, u, u, u} s.p (envelopeCompletion E₀ s.p hE₀) (completedTensorPowerDifferentials s g 0)
        (tensorPowerVariableDifferential s g hg)
        (fun x : envelopeCompletion E₀ s.p hE₀ ↦ tensorPowerDerivation s g hg 0 x) ≌
      Pair.{u, u, u, u} s.p (envelopeCompletion E₀ s.p hE₀) (C₀).forms (C₀).dx (C₀).diff :=
  Pair.formsTransportEquivalence s.p (tensorPowerOneFormsEquiv s g hg)
    (tensorPowerOneFormsEquiv_derivation s g hg) (Equiv.uniqueProd ι (Fin 1)).symm
    (tensorPowerOneFormsBasis s g hg) (C₀).basis (tensorPowerOneFormsEquiv_basis s g hg)
    (tensorPowerVariableDifferential_eq_basis s g hg) (C₀).dx_eq
    (fun x ↦ (LinearEquiv.symm_apply_eq _).mpr (tensorPowerOneFormsEquiv_derivation s g hg x).symm)
    (fun j ↦ (LinearEquiv.symm_apply_eq _).mpr ((tensorPowerOneFormsEquiv_basis s g hg _).trans
      (congrArg (C₀).basis ((Equiv.uniqueProd ι (Fin 1)).symm.apply_symm_apply j))).symm)

/-- The functor of `Crystalline.tensorPowerPairFormsEquivalence` keeps the module and composes
the connection with `1 ⊗ Crystalline.tensorPowerOneFormsEquiv`. -/
theorem tensorPowerPairFormsEquivalence_functor_obj_nabla
    (P : Pair.{u, u, u, u} s.p (envelopeCompletion E₀ s.p hE₀)
      (completedTensorPowerDifferentials s g 0) (tensorPowerVariableDifferential s g hg)
      (fun x : envelopeCompletion E₀ s.p hE₀ ↦ tensorPowerDerivation s g hg 0 x))
    (m : P.carrier) :
    ((tensorPowerPairFormsEquivalence s g hg).functor.obj P).nabla m =
      AdicCompletion.map (pAdicIdeal (A := (envelopeCompletion E₀ s.p hE₀ : Type u)) s.p)
        (LinearMap.lTensor P.carrier (tensorPowerOneFormsEquiv s g hg).toLinearMap) (P.nabla m) :=
  rfl

end Crystalline

end
