module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsComplexIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallinePresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelopeLifts

/-!
# The complex `D → Ω¹_D → ⋯` of the example of [Stacks, Tag 07LK] is the complex of Section 07J7

The example of [Stacks, Tag 07LK] writes down the complex `D → Ω¹_D → Ω²_D → ⋯` for `D = P^∧`,
`P = 𝐙_p[x_1, …, x_r]`: `Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat`, the
`p`-adic completion of the divided power de Rham complex of `D` over `𝐙_p`.  Section 07J7, and
with it [Stacks, Lemma 60.21.4, Tag 07LH], attaches to the presentation `P → Γ(X, 𝒪_X)` of the
situation `X/S` the completed divided power de Rham complex of the divided power envelope
`D_{P, γ}(pP)` over the base ring `Γ(Spec 𝐙_p, 𝒪)` of the situation.  This module identifies the
two complexes, through

* the envelope `D_{P, γ}(pP) ≅ P` (`Crystalline.AffineSpaceCrystallineSetup.envelopeEquiv`);
* the forms of `P` and of its completion `D` (`Crystalline.FormsData.formsComplexIsoOfCompletion`);
* the base rings `Γ(Spec 𝐙_p, 𝒪) ≅ 𝐙_p` (`Crystalline.FormsData.formsComplexBaseRingIso`);
* the two ways of writing the `p`-adic completion of the forms of `D`.

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNatIsoEnvelope` — the identification
  of `deRhamComplexNat` with the completed de Rham complex of the envelope of the presentation.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Section 60.17, Tag 07J7](https://stacks.math.columbia.edu/tag/07J7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DividedPowers

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

attribute [local instance] presentationEnvelopeAlgebraInst

/-! ### The two completions of the forms of `D` -/

/-- The completion of the forms of `D` along `(p) ⊆ 𝐙_p` is their completion along `(p) ⊆ D`. -/
def completedFormsEquiv (i : ℕ) :
    T.completedForms i ≃+ completedDividedPowerForms T.p T.A T.completedDividedPowers i where
  toFun := PAdicCompletion.mapAddHom T.p T.A T.D (AddMonoidHom.id (T.forms i))
  invFun := PAdicCompletion.mapAddHom T.p T.D T.A (AddMonoidHom.id (T.forms i))
  left_inv x := by
    have h := adicCompletion_addMonoidHom_ext_of_of T.p
      (f := (PAdicCompletion.mapAddHom T.p T.D T.A (AddMonoidHom.id (T.forms i))).comp
        (PAdicCompletion.mapAddHom T.p T.A T.D (AddMonoidHom.id (T.forms i))))
      (g := AddMonoidHom.id _) fun t ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, PAdicCompletion.mapAddHom_of,
          AddMonoidHom.id_apply]
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h := adicCompletion_addMonoidHom_ext_of_of T.p
      (f := (PAdicCompletion.mapAddHom T.p T.A T.D (AddMonoidHom.id (T.forms i))).comp
        (PAdicCompletion.mapAddHom T.p T.D T.A (AddMonoidHom.id (T.forms i))))
      (g := AddMonoidHom.id _) fun t ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, PAdicCompletion.mapAddHom_of,
          AddMonoidHom.id_apply]
    exact DFunLike.congr_fun h x
  map_add' := map_add _

/-- The identification of the two completions fixes the image of an uncompleted form. -/
theorem completedFormsEquiv_ofForms (i : ℕ) (ω : T.forms i) :
    T.completedFormsEquiv i (T.ofForms i ω) = AdicCompletion.of _ _ ω :=
  PAdicCompletion.mapAddHom_of T.p T.A T.D _ ω

/-- The identification of the two completions commutes with the de Rham differentials. -/
theorem completedFormsEquiv_differential (i : ℕ) (x : T.completedForms i) :
    T.completedFormsEquiv (i + 1) (T.completedDifferential i x) =
      completedDividedPowerDeRham T.p T.A T.completedDividedPowers i
        (T.completedFormsEquiv i x) := by
  have h := adicCompletion_addMonoidHom_ext_of_of T.p
    (f := (T.completedFormsEquiv (i + 1)).toAddMonoidHom.comp
      (T.completedDifferential i).toAddMonoidHom)
    (g := (completedDividedPowerDeRham T.p T.A T.completedDividedPowers i).comp
      (T.completedFormsEquiv i).toAddMonoidHom) fun ω ↦ by
      show T.completedFormsEquiv (i + 1) (T.completedDifferential i (T.ofForms i ω)) =
        completedDividedPowerDeRham T.p T.A T.completedDividedPowers i
          (T.completedFormsEquiv i (T.ofForms i ω))
      rw [completedDifferential_ofForms, completedFormsEquiv_ofForms, completedFormsEquiv_ofForms]
      exact (completedDividedPowerDeRham_of T.p T.A T.completedDividedPowers i ω).symm
  exact DFunLike.congr_fun h x

/-- **The complex `D → Ω¹_D → ⋯` of the example is the completed divided power de Rham complex of
`D` over `𝐙_p`.** -/
def deRhamComplexNatIsoFormsComplex :
    T.deRhamComplexNat ≅ FormsData.formsComplex T.p T.A T.completedDividedPowers :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ (T.completedFormsEquiv i).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      refine AddCommGrpCat.ext fun x ↦ ?_
      change (FormsData.formsComplex T.p T.A T.completedDividedPowers).d i (i + 1)
          (T.completedFormsEquiv i x) =
        T.completedFormsEquiv (i + 1) (T.deRhamComplexNat.d i (i + 1) x)
      exact (FormsData.formsComplex_d T.p T.A T.completedDividedPowers i _).trans
        ((T.completedFormsEquiv_differential i x).symm.trans
          (congrArg (T.completedFormsEquiv (i + 1)) (T.deRhamComplexNat_d i x).symm)))

/-! ### The envelope of the presentation -/

/-- A divided power structure transported along an equality of ideals, as a source. -/
theorem _root_.Crystalline.isDPMorphism_cast_left {R S : Type*} [CommRing R] [CommRing S]
    {J J' : Ideal R} (h : J = J') (δ : DividedPowers J) {K : Ideal S} {ε : DividedPowers K}
    {f : R →+* S} (hf : IsDPMorphism (h ▸ δ) ε f) : IsDPMorphism δ ε f := by
  subst h
  exact hf

/-- A divided power structure transported along an equality of ideals, as a target. -/
theorem _root_.Crystalline.isDPMorphism_cast_right {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} {ε : DividedPowers I} {J J' : Ideal S} (h : J = J') (δ : DividedPowers J)
    {f : R →+* S} (hf : IsDPMorphism ε (h ▸ δ) f) : IsDPMorphism ε δ f := by
  subst h
  exact hf

/-- **`P ≃ D_{P, γ}(pP)` as algebras over the base ring of the situation.** -/
def envelopeAlgEquiv :
    T.P ≃ₐ[(T.affineSit.A : Type)] (presentationEnvelope T.affineSit T.presentation).object :=
  AlgEquiv.ofRingEquiv (f := T.envelopeEquiv.symm) fun a ↦
    RingHom.congr_fun (presentationEnvelope T.affineSit T.presentation).algebraMap_comp a

/-- `P → D_{P, γ}(pP)` is a divided power morphism for the divided powers of `pP`. -/
theorem envelopeAlgEquiv_isDPMorphism :
    IsDPMorphism T.polynomialDividedPowers
      (presentationEnvelope T.affineSit T.presentation).object.dividedPowers
      T.envelopeAlgEquiv.toAlgHom.toRingHom :=
  isDPMorphism_cast_left T.presentationKernel_eq.symm T.polynomialDividedPowers
    (DividedPowerEnvelope.equivOfExtension_symm_isDPMorphism _ T.kernelDividedPowers
      (isDPMorphism_cast T.presentationKernel_eq.symm _ T.algebraMap_polynomial_isDPMorphism)
      (T.presentationKernel_eq.trans T.J_eq_map_ideal))

/-- `D_{P, γ}(pP) → P` is a divided power morphism for the divided powers of `pP`. -/
theorem envelopeAlgEquiv_symm_isDPMorphism :
    IsDPMorphism (presentationEnvelope T.affineSit T.presentation).object.dividedPowers
      T.polynomialDividedPowers T.envelopeAlgEquiv.symm.toAlgHom.toRingHom :=
  isDPMorphism_cast_right T.presentationKernel_eq.symm T.polynomialDividedPowers
    (DividedPowerEnvelope.equivOfExtension_isDPMorphism _ T.kernelDividedPowers
      (isDPMorphism_cast T.presentationKernel_eq.symm _ T.algebraMap_polynomial_isDPMorphism)
      (T.presentationKernel_eq.trans T.J_eq_map_ideal))

/-- **The complex `D → Ω¹_D → ⋯` of the example is the completed divided power de Rham complex of
the divided power envelope of the presentation `P → Γ(X, 𝒪_X)`, over the base ring
`Γ(Spec 𝐙_p, 𝒪)` of the situation** — the complex Section 07J7 attaches to the presentation. -/
def deRhamComplexNatIsoEnvelope :
    T.deRhamComplexNat ≅ FormsData.formsComplex T.p (T.affineSit.A : Type)
      (presentationEnvelope T.affineSit T.presentation).object.dividedPowers :=
  T.deRhamComplexNatIsoFormsComplex ≪≫
    (FormsData.formsComplexBaseRingIso T.p (B := T.D) T.completedDividedPowers
      (T.affineSit.A : Type) T.A T.algebraMap_baseSections_surjective).symm ≪≫
    (FormsData.formsComplexIsoOfCompletion T.p (T.affineSit.A : Type) T.polynomialDividedPowers
      T.p_nilpotent_mod_J).symm ≪≫
    FormsData.formsComplexIsoOfAlgEquiv T.p (T.affineSit.A : Type) T.polynomialDividedPowers
      (presentationEnvelope T.affineSit T.presentation).object.dividedPowers T.envelopeAlgEquiv
      T.envelopeAlgEquiv_isDPMorphism T.envelopeAlgEquiv_symm_isDPMorphism

end AffineSpaceCrystallineSetup

end Crystalline

end
