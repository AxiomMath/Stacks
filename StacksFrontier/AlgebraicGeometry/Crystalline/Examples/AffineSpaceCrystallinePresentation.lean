module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Completed
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeOfExtendedIdeal
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecSchemeThickening

/-!
# The presentation `C = P/pP` of the example of [Stacks, Tag 07LK] in Situation 07MD

The crystalline site `Cris(X/S)` of the example is indexed by the global crystalline situation
`Crystalline.AffineSpaceCrystallineSetup.situation`, whose affine situation
`(affineSituation S hp)` of [Stacks, Situation 07MD] has as base ring the global sections
`Γ(Spec 𝐙_p, 𝒪)` and as coordinate ring `Γ(X, 𝒪_X)`.  This module reads the example's own
presentation `C = P/J = P/pP`, `P = 𝐙_p[x_1, …, x_r]`, in that situation:

* `Γ(Spec 𝐙_p, 𝒪) ≅ 𝐙_p` as divided power rings, which makes `P` an algebra over the base ring of
  the situation;
* the presentation `P → Γ(X, 𝒪_X)` is a surjection of algebras over that base ring with kernel
  `J = pP`, and `P` is smooth over it;
* the divided power envelope `D_{P, γ}(J)` of the presentation is `P` itself, `J` already
  carrying divided powers compatible with `γ` ([Stacks, Tag 07H1]) — the source's "note that `pP`
  has divided powers by Divided Power Algebra, Lemma 07H1".

## Main definitions

* `Crystalline.AffineSpaceCrystallineSetup.affineSit` — the affine situation of `X/S`.
* `Crystalline.AffineSpaceCrystallineSetup.baseSectionsEquiv` — `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p`.
* `Crystalline.AffineSpaceCrystallineSetup.presentation` — `P → Γ(X, 𝒪_X)`.
* `Crystalline.AffineSpaceCrystallineSetup.envelopeEquiv` — `D_{P, γ}(J) ≃ P`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07H1](https://stacks.math.columbia.edu/tag/07H1)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DividedPowers
open Crystalline.DividedPowerScheme

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

attribute [local instance] DividedPowers.padicIntAlgebraAtPrime

/-- **The affine situation of [Stacks, Situation 07MD] of the example**, `X/S` read through the
global sections of `X` and of `S`. -/
abbrev affineSit : AffineCrystallineSituation.{0, 0} :=
  GlobalCrystallineSituation.affineSituation T.situation T.isNilpotent_prime_sections

/-- The base ring of the affine situation is `Γ(Spec 𝐙_p, 𝒪)`. -/
theorem affineSit_A_carrier :
    (T.affineSit.A : Type) = Γ(Spec (CommRingCat.of T.A), ⊤) := rfl

/-- **`Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p`**, the inverse of the `Γ`-`Spec` identification. -/
def baseSectionsEquiv : (T.affineSit.A : Type) ≃+* T.A :=
  (Scheme.ΓSpecIso (CommRingCat.of T.A)).commRingCatIsoToRingEquiv

/-- `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p` acts on a section as the forward `Γ`-`Spec` identification. -/
theorem baseSectionsEquiv_apply (a : (T.affineSit.A : Type)) :
    T.baseSectionsEquiv a = (Scheme.ΓSpecIso (CommRingCat.of T.A)).hom.hom a := rfl

/-- **`Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p` is an isomorphism of divided power rings**: its inverse is the
global sections map of `Spec(𝐙_p, (p), γ)`,
`Crystalline.DividedPowerScheme.specSectionsRingIso`. -/
theorem baseSectionsEquiv_isDPMorphism :
    IsDPMorphism T.affineSit.A.dividedPowers T.baseDividedPowers
      T.baseSectionsEquiv.toRingHom :=
  (specSectionsRingIso (DividedPowerRing.of T.A T.baseIdeal T.baseDividedPowers)).inv.isDPMorphism

/-- `𝐙_p` as an algebra over the base ring `Γ(Spec 𝐙_p, 𝒪)` of the situation. -/
instance baseSectionsAlgebra : Algebra (T.affineSit.A : Type) T.A :=
  T.baseSectionsEquiv.toRingHom.toAlgebra

/-- The structure map of `𝐙_p` over the base ring of the situation is `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p`. -/
theorem algebraMap_baseSections (a : (T.affineSit.A : Type)) :
    algebraMap (T.affineSit.A : Type) T.A a = T.baseSectionsEquiv a := rfl

/-- The algebra map `Γ(Spec 𝐙_p, 𝒪) → 𝐙_p` is surjective. -/
theorem algebraMap_baseSections_surjective :
    Function.Surjective (algebraMap (T.affineSit.A : Type) T.A) :=
  T.baseSectionsEquiv.surjective

/-- **The structure morphism `X ⟶ S` of the example is `Spec` of `𝐙_p → P → C`.** -/
theorem sourceToBase_eq :
    T.situation.sourceToBase =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp (algebraMap T.A T.P))) := by
  change (Spec.map (CommRingCat.ofHom T.residueToCoordinateRing) ≫
      (specClosedFiberIso (DividedPowerRing.of T.A T.baseIdeal T.baseDividedPowers)).inv) ≫
    closedFiberι _ = _
  rw [Category.assoc, specClosedFiberIso_inv_closedFiberι]
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.hom_ext ?_))
  ext a
  rfl

/-- **The example's presentation `P → Γ(X, 𝒪_X)`**: the quotient map `P → P/pP = C` followed by
the `Γ`-`Spec` identification `C ≃ Γ(Spec C, 𝒪)`. -/
def presentationRingHom : T.P →+* T.affineSit.C :=
  (Scheme.ΓSpecIso (CommRingCat.of T.C)).inv.hom.comp (Ideal.Quotient.mk T.J)

/-- The presentation is compatible with the structure maps from the base ring. -/
theorem presentationRingHom_algebraMap (a : (T.affineSit.A : Type)) :
    T.presentationRingHom (algebraMap (T.affineSit.A : Type) T.P a) =
      algebraMap (T.affineSit.A : Type) T.affineSit.C a := by
  rw [GlobalCrystallineSituation.affineSituation_algebraMap]
  change _ = (T.situation.sourceToBase).appTop.hom a
  rw [sourceToBase_eq]
  have h := RingHom.congr_fun (congrArg (fun φ ↦ CommRingCat.Hom.hom φ)
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom ((Ideal.Quotient.mk T.J).comp (algebraMap T.A T.P))))) a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
  exact (Scheme.ΓSpecIso (CommRingCat.of T.C)).commRingCatIsoToRingEquiv.symm_apply_eq.mpr h.symm

/-- `P = 𝐙_p[x_1, …, x_r]` is an algebra over the base ring `Γ(Spec 𝐙_p, 𝒪)` of the situation
through `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p`, its structure map being the constant polynomials. -/
theorem algebraMap_polynomial (a : (T.affineSit.A : Type)) :
    algebraMap (T.affineSit.A : Type) T.P a = MvPolynomial.C (T.baseSectionsEquiv a) := rfl

/-- `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p` as an isomorphism of algebras over `Γ(Spec 𝐙_p, 𝒪)`. -/
def baseSectionsAlgEquiv : (T.affineSit.A : Type) ≃ₐ[(T.affineSit.A : Type)] T.A :=
  AlgEquiv.ofRingEquiv (f := T.baseSectionsEquiv) fun _ ↦ rfl

/-- **`P` is smooth over the base ring of the situation**: it is the polynomial ring over
`Γ(Spec 𝐙_p, 𝒪)` transported along `Γ(Spec 𝐙_p, 𝒪) ≃ 𝐙_p`. -/
instance smooth_polynomial : Algebra.Smooth (T.affineSit.A : Type) T.P :=
  haveI : Algebra.Smooth (T.affineSit.A : Type) (MvPolynomial (Fin T.r) (T.affineSit.A : Type)) :=
    { }
  Algebra.Smooth.of_equiv (MvPolynomial.mapAlgEquiv (Fin T.r) T.baseSectionsAlgEquiv)

/-- **The example's presentation `P → Γ(X, 𝒪_X)`, as an algebra map over the base ring of the
situation.** -/
def presentation : T.P →ₐ[(T.affineSit.A : Type)] T.affineSit.C where
  __ := T.presentationRingHom
  commutes' := T.presentationRingHom_algebraMap

/-- The presentation sends `x ∈ P` to the class of `x` in `P/pP = C`, read in `Γ(X, 𝒪_X)`. -/
theorem presentation_apply (x : T.P) :
    T.presentation x = (Scheme.ΓSpecIso (CommRingCat.of T.C)).inv.hom (Ideal.Quotient.mk T.J x) :=
  rfl

/-- The presentation `P → Γ(X, 𝒪_X)` is surjective. -/
theorem presentation_surjective : Function.Surjective T.presentation := by
  intro y
  obtain ⟨c, rfl⟩ :=
    (Scheme.ΓSpecIso (CommRingCat.of T.C)).commRingCatIsoToRingEquiv.symm.surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact ⟨x, rfl⟩

/-- **The kernel of the presentation is `J = pP`.** -/
theorem presentationKernel_eq : presentationKernel T.affineSit T.presentation = T.J := by
  ext x
  change T.presentation x = 0 ↔ x ∈ T.J
  rw [presentation_apply, ← Ideal.Quotient.eq_zero_iff_mem]
  exact map_eq_zero_iff (Scheme.ΓSpecIso (CommRingCat.of T.C)).inv.hom
    (Scheme.ΓSpecIso (CommRingCat.of T.C)).commRingCatIsoToRingEquiv.symm.injective

/-- The divided power ideal of the base ring `Γ(Spec 𝐙_p, 𝒪)` is the image of `(p)`. -/
theorem affineSit_ideal :
    T.affineSit.A.ideal = T.baseIdeal.map T.baseSectionsEquiv.symm.toRingHom :=
  (specDividedPowerIdeal_top (DividedPowerRing.of T.A T.baseIdeal T.baseDividedPowers)).symm

/-- **`J = pP` is the extension of the divided power ideal of the base**, as an ideal of `P` over
the base ring of the situation. -/
theorem J_eq_map_ideal : T.J = T.affineSit.A.ideal.map (algebraMap (T.affineSit.A : Type) T.P) := by
  rw [affineSit_ideal, Ideal.map_map]
  refine congrArg (fun g : T.A →+* T.P ↦ T.baseIdeal.map g) (RingHom.ext fun a ↦ ?_)
  change algebraMap T.A T.P a =
    algebraMap T.A T.P (T.baseSectionsEquiv (T.baseSectionsEquiv.symm a))
  rw [RingEquiv.apply_symm_apply]

/-- The structure map of `P` over the base ring of the situation is a divided power morphism for
the divided powers of `J = pP` extending those of `(p)` ([Stacks, Tag 07H1]). -/
theorem algebraMap_polynomial_isDPMorphism :
    IsDPMorphism T.affineSit.A.dividedPowers T.polynomialDividedPowers
      (algebraMap (T.affineSit.A : Type) T.P) :=
  IsDPMorphism.comp _ T.polynomialDividedPowers_isDPMorphism T.baseSectionsEquiv_isDPMorphism

/-- Divided powers transported along an equality of ideals keep their morphism property. -/
theorem _root_.Crystalline.isDPMorphism_cast {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} {hI : DividedPowers I} {J J' : Ideal S} (h : J = J') (δ : DividedPowers J)
    {f : R →+* S} (hf : IsDPMorphism hI δ f) : IsDPMorphism hI (h ▸ δ) f := by
  subst h
  exact hf

/-- The divided powers of `J = pP` read on the kernel of the presentation. -/
def kernelDividedPowers : DividedPowers (presentationKernel T.affineSit T.presentation) :=
  T.presentationKernel_eq.symm ▸ T.polynomialDividedPowers

/-- **The divided power envelope of the presentation is `P` itself**: `D_{P, γ}(pP) ≃ P`, `pP`
already carrying divided powers compatible with `γ` ([Stacks, Tag 07H1]). -/
def envelopeEquiv : (presentationEnvelope T.affineSit T.presentation).object ≃+* T.P :=
  DividedPowerEnvelope.equivOfExtension (presentationEnvelope T.affineSit T.presentation)
    (T.kernelDividedPowers)
    (isDPMorphism_cast T.presentationKernel_eq.symm _ T.algebraMap_polynomial_isDPMorphism)
    (T.presentationKernel_eq.trans T.J_eq_map_ideal)

end AffineSpaceCrystallineSetup

end Crystalline

end
