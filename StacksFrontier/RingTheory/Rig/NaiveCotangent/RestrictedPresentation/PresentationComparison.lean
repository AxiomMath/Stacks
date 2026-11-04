module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.PresentationIndependence
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation.Construction
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation.NoetherianComparison

/-!
# Well-definedness of the restricted naive cotangent complex in `K(B)`

Morphisms of presentations by restricted power series, the maps of complexes they induce, and
the homotopies between them: the complex attached to a presentation is well defined up to
unique isomorphism in the homotopy category `K(B)`. Part of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory
open ComplexShape (upIntRelNegOneZero)

universe u v

namespace Rig

open TopologicalRing

attribute [local implicit_reducible] Algebra.Extension.ofSurjective
  AdicFiniteTypeAlgebra.of

/-! ### Well-definedness in `K(B)` -/

section Comparison

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]

open RestrictedPowerSeriesPresentation

private def restrictedLinearExtension
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (F : MvPolynomial σ A →ₗ[A] RestrictedPowerSeries A τ) :
    RestrictedPowerSeries A σ → RestrictedPowerSeries A τ := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.extension F

private theorem continuous_restrictedLinearExtension
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (F : MvPolynomial σ A →ₗ[A] RestrictedPowerSeries A τ) :
    Continuous (restrictedLinearExtension F) := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.continuous_extension

private theorem restrictedLinearExtension_polynomial
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (F : MvPolynomial σ A →ₗ[A] RestrictedPowerSeries A τ) (p : MvPolynomial σ A) :
    restrictedLinearExtension F (polynomialToRestrictedPowerSeries A σ p) = F p := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : UniformSpace (MvPolynomial τ A) := restrictedPolynomialUniformSpace A τ
  let : IsUniformAddGroup (MvPolynomial τ A) :=
    (restrictedPolynomialRingFilterBasis A τ).toAddGroupFilterBasis.isUniformAddGroup
  let : IsUniformAddGroup (RestrictedPowerSeries A τ) :=
    inferInstanceAs (IsUniformAddGroup (UniformSpace.Completion (MvPolynomial τ A)))
  exact UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous (f := F.toAddMonoidHom)
      (continuous_restrictedPolynomialLinearMap F)) p

/-- The inclusion of polynomials into the restricted power series ring of a presentation, as an
algebra map. -/
private def polynomialAlgHom (P : RestrictedPowerSeriesPresentation A B) :
    MvPolynomial (Fin P.variableCount) A →ₐ[A] P.ring :=
  { toRingHom := polynomialToRestrictedPowerSeries A (Fin P.variableCount)
    commutes' := fun _ => rfl }

private theorem presentationMap_polynomial
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F : P.ring →ₐ[A] Q.ring) (p : MvPolynomial (Fin P.variableCount) A) :
    F (polynomialToRestrictedPowerSeries A (Fin P.variableCount) p) =
      MvPolynomial.aeval (fun i => F (P.var i)) p := by
  have h : F.comp (polynomialAlgHom P) = MvPolynomial.aeval (fun i => F (P.var i)) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun h p

/-- Two maps out of the restricted power series ring into a Hausdorff space that are continuous
and agree on polynomials are equal. -/
private theorem eq_of_forall_polynomial {σ : Type*} {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : RestrictedPowerSeries A σ → X} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, f (polynomialToRestrictedPowerSeries A σ p) =
      g (polynomialToRestrictedPowerSeries A σ p)) : f = g := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact (UniformSpace.Completion.denseRange_coe (α := MvPolynomial σ A)).equalizer hf hg
    (funext h)

private def restrictedSubstitution
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (g : σ → RestrictedPowerSeries A τ) :
    RestrictedPowerSeries A σ →ₐ[A] RestrictedPowerSeries A τ := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : UniformSpace (MvPolynomial τ A) := restrictedPolynomialUniformSpace A τ
  let : IsUniformAddGroup (MvPolynomial τ A) :=
    (restrictedPolynomialRingFilterBasis A τ).toAddGroupFilterBasis.isUniformAddGroup
  let : IsUniformAddGroup (RestrictedPowerSeries A τ) :=
    inferInstanceAs (IsUniformAddGroup (UniformSpace.Completion (MvPolynomial τ A)))
  let f : MvPolynomial σ A →ₐ[A] RestrictedPowerSeries A τ := MvPolynomial.aeval g
  let h := continuous_restrictedPolynomialLinearMap f.toLinearMap
  refine { UniformSpace.Completion.extensionHom f.toRingHom h with commutes' := ?_ }
  intro a
  change UniformSpace.Completion.extensionHom f.toRingHom h
    (↑(MvPolynomial.C a : MvPolynomial σ A) : UniformSpace.Completion (MvPolynomial σ A)) = _
  exact (UniformSpace.Completion.extensionHom_coe f.toRingHom h
    (MvPolynomial.C a)).trans (f.commutes a)

private theorem restrictedSubstitution_polynomial
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (g : σ → RestrictedPowerSeries A τ) (p : MvPolynomial σ A) :
    restrictedSubstitution g (polynomialToRestrictedPowerSeries A σ p) =
      MvPolynomial.aeval g p := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : UniformSpace (MvPolynomial τ A) := restrictedPolynomialUniformSpace A τ
  let : IsUniformAddGroup (MvPolynomial τ A) :=
    (restrictedPolynomialRingFilterBasis A τ).toAddGroupFilterBasis.isUniformAddGroup
  let : IsUniformAddGroup (RestrictedPowerSeries A τ) :=
    inferInstanceAs (IsUniformAddGroup (UniformSpace.Completion (MvPolynomial τ A)))
  show UniformSpace.Completion.extension
      (MvPolynomial.aeval g : MvPolynomial σ A →ₐ[A] RestrictedPowerSeries A τ)
      (↑p : UniformSpace.Completion (MvPolynomial σ A)) = _
  exact UniformSpace.Completion.extension_coe
    (uniformContinuous_addMonoidHom_of_continuous
      (f := (MvPolynomial.aeval g).toLinearMap.toAddMonoidHom)
      (continuous_restrictedPolynomialLinearMap (MvPolynomial.aeval g).toLinearMap)) p

private theorem continuous_restrictedSubstitution
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (g : σ → RestrictedPowerSeries A τ) : Continuous (restrictedSubstitution g) := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.continuous_extension
    (f := (MvPolynomial.aeval g : MvPolynomial σ A →ₐ[A] RestrictedPowerSeries A τ))

private theorem exists_continuous_presentationMap
    (P Q : RestrictedPowerSeriesPresentation A B) :
    ∃ F : P.ring →ₐ[A] Q.ring, Continuous F ∧ Q.toAlgHom.comp F = P.toAlgHom := by
  classical
  choose g hg using fun i => Q.toAlgHom_surjective (P.toAlgHom (P.var i))
  let F : P.ring →ₐ[A] Q.ring := restrictedSubstitution g
  refine ⟨F, continuous_restrictedSubstitution g, ?_⟩
  have hpol : Q.toAlgHom.comp (MvPolynomial.aeval g) = P.toAlgHom.comp (polynomialAlgHom P) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    show Q.toAlgHom (g i) = P.toAlgHom (P.var i)
    exact hg i
  have hPc : Continuous P.toAlgHom :=
    P.continuous_quotientEquiv.comp continuous_quotient_mk'
  have hQc : Continuous Q.toAlgHom :=
    Q.continuous_quotientEquiv.comp continuous_quotient_mk'
  let : IsClosed (Q.ideal : Set Q.ring) := Q.ideal_isClosed
  let e : (Q.ring ⧸ Q.ideal) ≃ₜ B :=
    { Q.quotientEquiv.toEquiv with
      continuous_toFun := Q.continuous_quotientEquiv
      continuous_invFun := Q.continuous_quotientEquiv_symm }
  let : IsClosed (Q.ideal.toAddSubgroup : Set Q.ring) := Q.ideal_isClosed
  let : T2Space (Q.ring ⧸ Q.ideal) :=
    inferInstanceAs (T2Space (Q.ring ⧸ Q.ideal.toAddSubgroup))
  let : T2Space B := e.t2Space
  apply DFunLike.ext'
  refine eq_of_forall_polynomial (hQc.comp (continuous_restrictedSubstitution g)) hPc fun p => ?_
  show Q.toAlgHom (restrictedSubstitution g
    (polynomialToRestrictedPowerSeries A (Fin P.variableCount) p)) = _
  rw [restrictedSubstitution_polynomial]
  exact DFunLike.congr_fun hpol p

private theorem presentationMap_sub_sub_mem_sq
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P)
    (F G : P.ring →ₐ[A] Q.ring) (hF : Continuous F) (hG : Continuous G)
    (I : Ideal Q.ring) (hI : ∀ i, F (P.var i) - G (P.var i) ∈ I)
    (z : P.ring) :
    F z - G z - ∑ i, G (K.partialDeriv i z) * (F (P.var i) - G (P.var i)) ∈ I ^ 2 := by
  classical
  obtain ⟨T, hT⟩ := exists_taylor_remainder_linearMap A (Fin P.variableCount)
  let ev : MvPolynomial (Fin P.variableCount ⊕ Fin P.variableCount) A →ₐ[A] Q.ring :=
    MvPolynomial.aeval (Sum.elim (fun i => F (P.var i)) (fun i => G (P.var i)))
  let c (ij : Fin P.variableCount × Fin P.variableCount) :
      MvPolynomial (Fin P.variableCount) A →ₗ[A] Q.ring :=
    ev.toLinearMap.comp ((LinearMap.proj ij).comp T)
  let C (ij : Fin P.variableCount × Fin P.variableCount) := restrictedLinearExtension (c ij)
  have hC (ij : Fin P.variableCount × Fin P.variableCount) : Continuous (C ij) :=
    continuous_restrictedLinearExtension _
  have hpoly (H : P.ring →ₐ[A] Q.ring) (s : Fin P.variableCount → Fin P.variableCount ⊕ _)
      (hs : ∀ i, ev (MvPolynomial.X (s i)) = H (P.var i))
      (p : MvPolynomial (Fin P.variableCount) A) :
      ev (MvPolynomial.aeval (fun i => MvPolynomial.X (s i)) p) =
        H (polynomialToRestrictedPowerSeries A (Fin P.variableCount) p) := by
    rw [presentationMap_polynomial]
    have he : ev.comp (MvPolynomial.aeval (fun i => MvPolynomial.X (s i))) =
        MvPolynomial.aeval (fun i => H (P.var i)) := by
      ext i
      simp [hs]
    exact DFunLike.congr_fun he p
  have hpF := hpoly F Sum.inl fun i => by simp [ev]
  have hpG := hpoly G Sum.inr fun i => by simp [ev]
  have he : (fun x => F x - G x -
        ∑ i, G (K.partialDeriv i x) * (F (P.var i) - G (P.var i))) =
      (fun x => ∑ ij : Fin P.variableCount × Fin P.variableCount,
        C ij x * (F (P.var ij.1) - G (P.var ij.1)) *
          (F (P.var ij.2) - G (P.var ij.2))) := by
    refine eq_of_forall_polynomial ((hF.sub hG).sub (continuous_finsetSum _ fun i _ =>
        (hG.comp (K.partialDeriv_continuous i)).mul continuous_const))
      (continuous_finsetSum _ fun ij _ =>
        ((hC ij).mul continuous_const).mul continuous_const) fun p => ?_
    have hp := congrArg ev (hT p)
    simp only [map_sub, map_sum, map_mul, hpF, hpG] at hp
    simpa only [Function.comp_apply, K.partialDeriv_polynomial,
      C, restrictedLinearExtension_polynomial, c, LinearMap.comp_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, ev, MvPolynomial.aeval_X,
      Sum.elim_inl, Sum.elim_inr] using hp
  rw [congrFun he z]
  exact (I ^ 2).sum_mem fun ij _ => by
    simpa only [pow_two] using
      Ideal.mul_mem_mul (I.mul_mem_left (C ij z) (hI ij.1)) (hI ij.2)

private theorem restrictedSubstitution_chainRule
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hF : Continuous F)
    (j : Fin Q.variableCount) (x : P.ring) :
    L.partialDeriv j (F x) =
      ∑ i : Fin P.variableCount,
        F (K.partialDeriv i x) * L.partialDeriv j (F (P.var i)) := by
  classical
  have hEq : (fun y => L.partialDeriv j (F y)) =
      (fun y => ∑ i : Fin P.variableCount,
        F (K.partialDeriv i y) * L.partialDeriv j (F (P.var i))) := by
    refine eq_of_forall_polynomial ((L.partialDeriv_continuous j).comp hF)
      (continuous_finsetSum _ fun i _ =>
        (hF.comp (K.partialDeriv_continuous i)).mul continuous_const) fun f => ?_
    have h := mvPolynomial_derivation_chainRule (L.partialDeriv j) (F.comp (polynomialAlgHom P)) f
    change L.partialDeriv j (F (polynomialToRestrictedPowerSeries A
        (Fin P.variableCount) f)) =
      ∑ i, F (polynomialToRestrictedPowerSeries A (Fin P.variableCount)
        (MvPolynomial.pderiv i f)) * L.partialDeriv j (F (P.var i)) at h
    simpa only [Function.comp_apply, K.partialDeriv_polynomial] using h
  exact congrFun hEq x

private def presentationExtensionHom
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F : P.ring →ₐ[A] Q.ring) (hF : Q.toAlgHom.comp F = P.toAlgHom) :
    P.extension.Hom Q.extension where
  toRingHom := F.toRingHom
  toRingHom_algebraMap a := F.commutes a
  algebraMap_toRingHom x := DFunLike.congr_fun hF x

private def presentationConormalMap
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F : P.ring →ₐ[A] Q.ring) (hF : Q.toAlgHom.comp F = P.toAlgHom) :
    P.extension.Cotangent →ₗ[B] Q.extension.Cotangent :=
  Algebra.Extension.Cotangent.map (presentationExtensionHom F hF)

private theorem presentationConormalMap_mk
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F : P.ring →ₐ[A] Q.ring) (hF : Q.toAlgHom.comp F = P.toAlgHom)
    (g : P.extension.ker) :
    presentationConormalMap F hF (Algebra.Extension.Cotangent.mk g) =
      Algebra.Extension.Cotangent.mk ⟨F g.1, by
        change Q.toAlgHom (F g.1) = 0
        rw [← AlgHom.comp_apply, hF]
        exact g.2⟩ :=
  by
    exact Algebra.Extension.Cotangent.map_mk (presentationExtensionHom F hF) g

private def presentationDifferentialsMap
    {P Q : RestrictedPowerSeriesPresentation A B}
    (L : RestrictedNaiveCotangentComplex Q) (F : P.ring →ₐ[A] Q.ring) :
    (Fin P.variableCount → B) →ₗ[B] (Fin Q.variableCount → B) :=
  LinearMap.pi fun j => ∑ i : Fin P.variableCount,
    Q.toAlgHom (L.partialDeriv j (F (P.var i))) • LinearMap.proj i

private theorem presentationDifferentialsMap_apply
    {P Q : RestrictedPowerSeriesPresentation A B}
    (L : RestrictedNaiveCotangentComplex Q) (F : P.ring →ₐ[A] Q.ring)
    (v : Fin P.variableCount → B) (j : Fin Q.variableCount) :
    presentationDifferentialsMap L F v j =
      ∑ i, v i * Q.toAlgHom (L.partialDeriv j (F (P.var i))) := by
  simp [presentationDifferentialsMap, mul_comm]

private theorem presentationConormalMap_differential
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hcont : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) :
    L.differential.comp (presentationConormalMap F hF) =
      (presentationDifferentialsMap L F).comp K.differential := by
  ext x j
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [LinearMap.comp_apply]
  rw [presentationConormalMap_mk, L.differential_mk, K.differential_mk]
  rw [presentationDifferentialsMap_apply]
  show Q.toAlgHom (L.partialDeriv j (F g.1)) = _
  rw [restrictedSubstitution_chainRule K L F hcont]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← AlgHom.comp_apply, hF]

open HomologicalComplex

private def doubleHomotopy {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    {X₀ X₁ Y₀ Y₁ : C} (d : X₀ ⟶ X₁) (e : Y₀ ⟶ Y₁)
    {f g : double d upIntRelNegOneZero ⟶
      double e upIntRelNegOneZero}
    (h : (double d upIntRelNegOneZero).X 0 ⟶
      (double e upIntRelNegOneZero).X (-1))
    (h₀ : f.f (-1) =
      (double d upIntRelNegOneZero).d (-1) 0 ≫ h + g.f (-1))
    (h₁ : f.f 0 = h ≫ (double e upIntRelNegOneZero).d (-1) 0 + g.f 0) :
    Homotopy f g := by
  classical
  let H : ∀ i j, (double d upIntRelNegOneZero).X i ⟶
      (double e upIntRelNegOneZero).X j := fun i j =>
    if hi : i = 0 then if hj : j = -1 then
      eqToHom (by rw [hi]) ≫ h ≫ eqToHom (by rw [hj]) else 0 else 0
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = -1 <;> simp_all [H]
  · intro i
    by_cases hi : i = -1
    · subst i
      rw [dNext_eq H upIntRelNegOneZero,
        prevD_eq H upRel_negTwo_negOne]
      simpa [H] using h₀
    · by_cases hi' : i = 0
      · subst i
        rw [dNext_eq H upRel_zero_one,
          prevD_eq H upIntRelNegOneZero]
        simpa [H] using h₁
      · exact (isZero_double_X d _ i hi hi').eq_of_src _ _

private def presentationDifference
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F G : P.ring →ₐ[A] Q.ring)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom)
    (i : Fin P.variableCount) : Q.extension.ker :=
  ⟨F (P.var i) - G (P.var i), by
    change Q.toAlgHom (F (P.var i) - G (P.var i)) = 0
    rw [map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hF, hG, sub_self]⟩

private def presentationHomotopyMap
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F G : P.ring →ₐ[A] Q.ring)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom) :
    (Fin P.variableCount → B) →ₗ[B] Q.extension.Cotangent :=
  ∑ i, (LinearMap.id.smulRight (Algebra.Extension.Cotangent.mk
    (presentationDifference F G hF hG i))).comp (LinearMap.proj i)

private theorem presentationHomotopyMap_apply
    {P Q : RestrictedPowerSeriesPresentation A B}
    (F G : P.ring →ₐ[A] Q.ring)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom)
    (v : Fin P.variableCount → B) :
    presentationHomotopyMap F G hF hG v = ∑ i, v i •
      Algebra.Extension.Cotangent.mk (presentationDifference F G hF hG i) := by
  simp [presentationHomotopyMap]

private theorem cotangentMk_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (E : Algebra.Extension R S) (a : E.Ring) (x : E.ker) :
    Algebra.Extension.Cotangent.mk (a • x) =
      algebraMap E.Ring S a • Algebra.Extension.Cotangent.mk x := by
  rw [map_smul, algebraMap_smul]

private theorem presentationHomotopyMap_differential
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P)
    (F G : P.ring →ₐ[A] Q.ring) (hFc : Continuous F) (hGc : Continuous G)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom) :
    (presentationHomotopyMap F G hF hG).comp K.differential =
      presentationConormalMap F hF - presentationConormalMap G hG := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply]
  rw [presentationConormalMap_mk F hF z, presentationConormalMap_mk G hG z,
    K.differential_mk z]
  rw [presentationHomotopyMap_apply]
  have hsm (i : Fin P.variableCount) :
      P.toAlgHom (K.partialDeriv i z.1) •
          Algebra.Extension.Cotangent.mk (presentationDifference F G hF hG i) =
        Algebra.Extension.Cotangent.mk
          ((show Q.extension.Ring from G (K.partialDeriv i z.1)) •
            presentationDifference F G hF hG i) := by
    have hc := DFunLike.congr_fun hG (K.partialDeriv i z.1)
    change Q.toAlgHom (G (K.partialDeriv i z.1)) = _ at hc
    rw [← hc]
    exact (cotangentMk_smul Q.extension _ _).symm
  simp_rw [hsm]
  rw [← map_sum, ← map_sub]
  apply (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mpr
  have ht := presentationMap_sub_sub_mem_sq K F G hFc hGc Q.ker
    (fun i => (presentationDifference F G hF hG i).2) z.1
  simp only [Submodule.coe_sum, SetLike.val_smul, smul_eq_mul, presentationDifference] at *
  show (∑ i, G (K.partialDeriv i z.1) * (F (P.var i) - G (P.var i))) -
      (F z.1 - G z.1) ∈ Q.ker ^ 2
  rw [show (∑ i, G (K.partialDeriv i z.1) * (F (P.var i) - G (P.var i))) - (F z.1 - G z.1) =
    -(F z.1 - G z.1 -
      ∑ i, G (K.partialDeriv i z.1) * (F (P.var i) - G (P.var i))) from by ring]
  exact neg_mem ht

private theorem differential_presentationHomotopyMap
    {P Q : RestrictedPowerSeriesPresentation A B}
    (L : RestrictedNaiveCotangentComplex Q)
    (F G : P.ring →ₐ[A] Q.ring)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom) :
    L.differential.comp (presentationHomotopyMap F G hF hG) =
      presentationDifferentialsMap L F - presentationDifferentialsMap L G := by
  ext v j
  simp only [LinearMap.comp_apply, presentationHomotopyMap_apply, map_sum, map_smul,
    L.differential_mk, LinearMap.sub_apply, Pi.sub_apply,
    presentationDifferentialsMap_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [presentationDifference, map_sub, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

private def uliftLinearMap
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    ULift.{u} M →ₗ[R] ULift.{v} N :=
  ULift.moduleEquiv.symm.toLinearMap.comp (f.comp ULift.moduleEquiv.toLinearMap)

private theorem uliftLinearMap_up
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (x : M) :
    uliftLinearMap f (ULift.up x : ULift.{u} M) = (ULift.up (f x) : ULift.{v} N) := rfl

private def presentationCochainMap
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hFc : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) : K.cochainComplex ⟶ L.cochainComplex :=
  doubleMap (ModuleCat.ofHom K.liftedDifferential) (ModuleCat.ofHom L.liftedDifferential)
    (ModuleCat.ofHom (uliftLinearMap (presentationConormalMap F hF)))
    (ModuleCat.ofHom (uliftLinearMap (presentationDifferentialsMap L F))) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (L.differential (presentationConormalMap F hF x.down)) =
        ULift.up (presentationDifferentialsMap L F (K.differential x.down))
      exact congrArg ULift.up (DFunLike.congr_fun
        (presentationConormalMap_differential K L F hFc hF) x.down))

private theorem presentationCochainMap_negOne
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hFc : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) :
    (presentationCochainMap K L F hFc hF).f (-1) =
      K.degreeNegOneIso.hom ≫ ModuleCat.ofHom (uliftLinearMap (presentationConormalMap F hF)) ≫
        L.degreeNegOneIso.inv := by
  simp [presentationCochainMap, doubleMap, RestrictedNaiveCotangentComplex.degreeNegOneIso]
  rfl

private theorem presentationCochainMap_zero
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hFc : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) :
    (presentationCochainMap K L F hFc hF).f 0 =
      K.degreeZeroIso.hom ≫ ModuleCat.ofHom (uliftLinearMap (presentationDifferentialsMap L F)) ≫
        L.degreeZeroIso.inv := by
  simp [presentationCochainMap, doubleMap, RestrictedNaiveCotangentComplex.degreeZeroIso]
  rfl

private theorem presentationConormalMap_comp
    {P Q R : RestrictedPowerSeriesPresentation A B}
    (F : P.ring →ₐ[A] Q.ring) (G : Q.ring →ₐ[A] R.ring)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : R.toAlgHom.comp G = Q.toAlgHom) :
    presentationConormalMap (G.comp F) (by rw [← AlgHom.comp_assoc, hG, hF]) =
      (presentationConormalMap G hG).comp (presentationConormalMap F hF) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  simp only [LinearMap.comp_apply]
  rw [presentationConormalMap_mk, presentationConormalMap_mk, presentationConormalMap_mk]
  rfl

private theorem presentationDifferentialsMap_comp
    {P Q R : RestrictedPowerSeriesPresentation A B}
    (L : RestrictedNaiveCotangentComplex Q) (M : RestrictedNaiveCotangentComplex R)
    (F : P.ring →ₐ[A] Q.ring) (G : Q.ring →ₐ[A] R.ring)
    (hGc : Continuous G) (hG : R.toAlgHom.comp G = Q.toAlgHom) :
    presentationDifferentialsMap M (G.comp F) =
      (presentationDifferentialsMap M G).comp (presentationDifferentialsMap L F) := by
  apply LinearMap.ext
  intro v
  funext k
  simp only [LinearMap.comp_apply, presentationDifferentialsMap_apply, AlgHom.comp_apply]
  have he (x : Q.ring) : R.toAlgHom (G x) = Q.toAlgHom x := DFunLike.congr_fun hG x
  trans ∑ i, v i * (∑ j, Q.toAlgHom (L.partialDeriv j (F (P.var i))) *
    R.toAlgHom (M.partialDeriv k (G (Q.var j))))
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [restrictedSubstitution_chainRule L M G hGc]
    simp only [map_sum, map_mul, he]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Continuity of the identity algebra map, stated for the identity algebra map itself rather
than for `id`; the two differ by an unfolding that `rw` will not perform. -/
private theorem continuous_id_algHom {R X : Type*} [CommSemiring R] [Semiring X] [Algebra R X]
    [TopologicalSpace X] : Continuous (AlgHom.id R X) := continuous_id

/-- Continuity of a composite of algebra maps, stated for the composite algebra map itself
rather than for the composite of the underlying functions.  The two differ by an unfolding that
`rw` will not perform, so the composite map's continuity has to be available in this shape. -/
private theorem continuous_comp_algHom {R X Y Z : Type*} [CommSemiring R]
    [Semiring X] [Semiring Y] [Semiring Z] [Algebra R X] [Algebra R Y] [Algebra R Z]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X →ₐ[R] Y) (G : Y →ₐ[R] Z) (hF : Continuous F) (hG : Continuous G) :
    Continuous (G.comp F) := hG.comp hF

private theorem presentationCochainMap_comp
    {P Q R : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (M : RestrictedNaiveCotangentComplex R)
    (F : P.ring →ₐ[A] Q.ring) (G : Q.ring →ₐ[A] R.ring)
    (hFc : Continuous F) (hGc : Continuous G)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : R.toAlgHom.comp G = Q.toAlgHom) :
    presentationCochainMap K M (G.comp F) (continuous_comp_algHom F G hFc hGc)
        (by rw [← AlgHom.comp_assoc, hG, hF]) =
      presentationCochainMap K L F hFc hF ≫ presentationCochainMap L M G hGc hG := by
  apply from_double_hom_ext
  · simp only [HomologicalComplex.comp_f, presentationCochainMap_negOne,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [presentationConormalMap_comp]
    rfl
  · simp only [HomologicalComplex.comp_f, presentationCochainMap_zero,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [presentationDifferentialsMap_comp L M F G hGc hG]
    rfl

private theorem presentationCochainMap_id
    {P : RestrictedPowerSeriesPresentation A B} (K : RestrictedNaiveCotangentComplex P) :
    presentationCochainMap K K (AlgHom.id A P.ring) continuous_id_algHom
      (AlgHom.comp_id _) = 𝟙 K.cochainComplex := by
  have ha : presentationConormalMap (AlgHom.id A P.ring) (AlgHom.comp_id P.toAlgHom) =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    rw [presentationConormalMap_mk]
    rfl
  have hb : presentationDifferentialsMap K (AlgHom.id A P.ring) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    funext j
    rw [presentationDifferentialsMap_apply]
    show (∑ i, v i * P.toAlgHom (K.partialDeriv j
      (polynomialToRestrictedPowerSeries A (Fin P.variableCount) (MvPolynomial.X i)))) = v j
    simp [K.partialDeriv_polynomial, MvPolynomial.pderiv_X, Pi.single_apply]
  apply from_double_hom_ext
  · show (presentationCochainMap K K (AlgHom.id A P.ring) continuous_id_algHom
        (AlgHom.comp_id P.toAlgHom)).f (-1) =
      HomologicalComplex.Hom.f (𝟙 K.cochainComplex) (-1)
    rw [presentationCochainMap_negOne, ha]
    show K.degreeNegOneIso.hom ≫ 𝟙 _ ≫ K.degreeNegOneIso.inv = 𝟙 _
    simp
  · show (presentationCochainMap K K (AlgHom.id A P.ring) continuous_id_algHom
        (AlgHom.comp_id P.toAlgHom)).f 0 =
      HomologicalComplex.Hom.f (𝟙 K.cochainComplex) 0
    rw [presentationCochainMap_zero, hb]
    show K.degreeZeroIso.hom ≫ 𝟙 _ ≫ K.degreeZeroIso.inv = 𝟙 _
    simp

private def presentationCochainHomotopy
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F G : P.ring →ₐ[A] Q.ring) (hFc : Continuous F) (hGc : Continuous G)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : Q.toAlgHom.comp G = P.toAlgHom) :
    Homotopy (presentationCochainMap K L F hFc hF)
      (presentationCochainMap K L G hGc hG) := by
  apply doubleHomotopy (ModuleCat.ofHom K.liftedDifferential)
    (ModuleCat.ofHom L.liftedDifferential)
    (K.degreeZeroIso.hom ≫ ModuleCat.ofHom (uliftLinearMap
      (presentationHomotopyMap F G hF hG)) ≫ L.degreeNegOneIso.inv)
  · change (presentationCochainMap K L F hFc hF).f (-1) =
      K.cochainComplex.d (-1) 0 ≫ (K.degreeZeroIso.hom ≫ ModuleCat.ofHom (uliftLinearMap
          (presentationHomotopyMap F G hF hG)) ≫ L.degreeNegOneIso.inv) +
        (presentationCochainMap K L G hGc hG).f (-1)
    rw [presentationCochainMap_negOne, presentationCochainMap_negOne, K.cochainComplex_d]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add]
    apply congrArg
    rw [← Category.assoc, ← Preadditive.add_comp]
    apply congrArg (fun f => f ≫ L.degreeNegOneIso.inv)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ULift.up (presentationConormalMap F hF x.down) =
      ULift.up (presentationHomotopyMap F G hF hG (K.differential x.down)) +
        ULift.up (presentationConormalMap G hG x.down)
    have he := DFunLike.congr_fun
      (presentationHomotopyMap_differential K F G hFc hGc hF hG) x.down
    change presentationHomotopyMap F G hF hG (K.differential x.down) =
      presentationConormalMap F hF x.down - presentationConormalMap G hG x.down at he
    rw [he]
    exact congrArg ULift.up (sub_add_cancel _ _).symm
  · change (presentationCochainMap K L F hFc hF).f 0 =
      (K.degreeZeroIso.hom ≫ ModuleCat.ofHom (uliftLinearMap
          (presentationHomotopyMap F G hF hG)) ≫ L.degreeNegOneIso.inv) ≫
          L.cochainComplex.d (-1) 0 +
        (presentationCochainMap K L G hGc hG).f 0
    rw [presentationCochainMap_zero, presentationCochainMap_zero, L.cochainComplex_d]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add]
    apply congrArg
    rw [← Category.assoc, ← Preadditive.add_comp]
    apply congrArg (fun f => f ≫ L.degreeZeroIso.inv)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ULift.up (presentationDifferentialsMap L F x.down) =
      ULift.up (L.differential (presentationHomotopyMap F G hF hG x.down)) +
        ULift.up (presentationDifferentialsMap L G x.down)
    have he := DFunLike.congr_fun (differential_presentationHomotopyMap L F G hF hG) x.down
    change L.differential (presentationHomotopyMap F G hF hG x.down) =
      presentationDifferentialsMap L F x.down - presentationDifferentialsMap L G x.down at he
    rw [he]
    exact congrArg ULift.up (sub_add_cancel _ _).symm

private def presentationCochainEquiv
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (G : Q.ring →ₐ[A] P.ring)
    (hFc : Continuous F) (hGc : Continuous G)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (hG : P.toAlgHom.comp G = Q.toAlgHom) :
    HomotopyEquiv K.cochainComplex L.cochainComplex where
  hom := presentationCochainMap K L F hFc hF
  inv := presentationCochainMap L K G hGc hG
  homotopyHomInvId := by
    rw [← presentationCochainMap_comp, ← presentationCochainMap_id K]
    exact presentationCochainHomotopy K K _ _ _ _ _ _
  homotopyInvHomId := by
    rw [← presentationCochainMap_comp, ← presentationCochainMap_id L]
    exact presentationCochainHomotopy L L _ _ _ _ _ _

private theorem presentationCochainMap_mk
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hFc : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (g : P.extension.ker) :
    (presentationCochainMap K L F hFc hF).f (-1)
        (K.degreeNegOneIso.inv (ULift.up (Algebra.Extension.Cotangent.mk g))) =
      L.degreeNegOneIso.inv (ULift.up (presentationConormalMap F hF
        (Algebra.Extension.Cotangent.mk g))) := by
  rw [presentationCochainMap_negOne]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

private theorem presentationCochainMap_free
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)
    (F : P.ring →ₐ[A] Q.ring) (hFc : Continuous F)
    (hF : Q.toAlgHom.comp F = P.toAlgHom) (v : Fin P.variableCount → B) :
    (presentationCochainMap K L F hFc hF).f 0 (K.degreeZeroIso.inv (ULift.up v)) =
      L.degreeZeroIso.inv (ULift.up fun j =>
        ∑ i, v i * Q.toAlgHom (L.partialDeriv j (F (P.var i)))) := by
  rw [presentationCochainMap_zero]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  exact congrArg (fun f => L.degreeZeroIso.inv (ULift.up f))
    (funext (presentationDifferentialsMap_apply L F v))

/-- A morphism of presentations, in the sense of Step 1 of the proof of Lemma 0GAE: a
continuous `A`-algebra map `A{x₁, …, x_r} → A{y₁, …, y_s}` compatible with the two surjections
onto `B`, together with the map of complexes it induces. The two compatibility fields pin that
map: in degree `-1` it is induced by `map` on conormal classes, and in degree `0` it is
`dxᵢ ↦ ∑ j, (∂gᵢ/∂y_j) dy_j` for `gᵢ = map xᵢ`, as in the source. -/
public structure RestrictedPresentationComparison
    {P Q : RestrictedPowerSeriesPresentation A B}
    (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q) where
  /-- The map of presentations `A{x₁, …, x_r} → A{y₁, …, y_s}`. -/
  map : P.ring →ₐ[A] Q.ring
  /-- It is continuous. -/
  continuous_map : Continuous map
  /-- It is compatible with the surjections onto `B`. -/
  commutes : Q.toAlgHom.comp map = P.toAlgHom
  /-- The induced map of complexes, which is a homotopy equivalence. -/
  equiv : HomotopyEquiv K.cochainComplex L.cochainComplex
  /-- In degree `-1` it is `J / J² → K / K²`, induced by `map`. -/
  conormal_mk : ∀ g : P.extension.ker,
    equiv.hom.f (-1)
        (K.degreeNegOneIso.inv (ULift.up (Algebra.Extension.Cotangent.mk g))) =
      L.degreeNegOneIso.inv (ULift.up (Algebra.Extension.Cotangent.mk ⟨map g.1, by
        change Q.toAlgHom (map g.1) = 0
        rw [← AlgHom.comp_apply, commutes]
        exact g.2⟩))
  /-- In degree `0` it is `dxᵢ ↦ ∑ j, (∂gᵢ/∂y_j) dy_j`. -/
  free_apply : ∀ v : Fin P.variableCount → B,
    equiv.hom.f 0 (K.degreeZeroIso.inv (ULift.up v)) =
      L.degreeZeroIso.inv (ULift.up fun j =>
        ∑ i, v i * Q.toAlgHom (L.partialDeriv j (map (P.var i))))

variable {P Q : RestrictedPowerSeriesPresentation A B}
  (K : RestrictedNaiveCotangentComplex P) (L : RestrictedNaiveCotangentComplex Q)

/-- **Stacks Project, Tag 0GBX.** Any two presentations of `B` are related by a morphism of
presentations, and the map of complexes it induces is a homotopy equivalence. This is the
existence half of "the complex is well defined in `K(B)`". -/
@[stacks 0GBX "well defined in K(B)"]
public theorem exists_restrictedPresentationComparison :
    Nonempty (RestrictedPresentationComparison K L) := by
  obtain ⟨F, hFc, hF⟩ := exists_continuous_presentationMap P Q
  obtain ⟨G, hGc, hG⟩ := exists_continuous_presentationMap Q P
  refine ⟨{ map := F, continuous_map := hFc, commutes := hF
            equiv := presentationCochainEquiv K L F G hFc hGc hF hG
            conormal_mk := ?_, free_apply := ?_ }⟩
  · intro g
    show (presentationCochainMap K L F hFc hF).f (-1) _ = _
    rw [presentationCochainMap_mk, presentationConormalMap_mk]
  · intro v
    show (presentationCochainMap K L F hFc hF).f 0 _ = _
    rw [presentationCochainMap_free]


private theorem restrictedPresentationComparison_hom_eq
    (e : RestrictedPresentationComparison K L) :
    e.equiv.hom = presentationCochainMap K L e.map e.continuous_map e.commutes := by
  apply from_double_hom_ext
  · apply (cancel_epi K.degreeNegOneIso.inv).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    show e.equiv.hom.f (-1) (K.degreeNegOneIso.inv (ULift.up _)) =
      (presentationCochainMap K L e.map e.continuous_map e.commutes).f (-1)
        (K.degreeNegOneIso.inv (ULift.up (Algebra.Extension.Cotangent.mk g)))
    rw [e.conormal_mk, presentationCochainMap_mk, presentationConormalMap_mk]
  · apply (cancel_epi K.degreeZeroIso.inv).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨v⟩
    show e.equiv.hom.f 0 (K.degreeZeroIso.inv (ULift.up v)) =
      (presentationCochainMap K L e.map e.continuous_map e.commutes).f 0
        (K.degreeZeroIso.inv (ULift.up v))
    rw [e.free_apply, presentationCochainMap_free]

/-- **Stacks Project, Tag 0GBX.** The isomorphism in `K(B)` is *unique*: any two morphisms of
presentations induce homotopic maps of complexes. This is Step 2 of the proof of Lemma
0GAE. -/
@[stacks 0GBX "unique isomorphism in K(B)"]
public theorem homotopy_of_restrictedPresentationComparison
    (e e' : RestrictedPresentationComparison K L) :
    Nonempty (Homotopy e.equiv.hom e'.equiv.hom) := by
  rw [restrictedPresentationComparison_hom_eq K L e,
    restrictedPresentationComparison_hom_eq K L e']
  exact ⟨presentationCochainHomotopy K L e.map e'.map e.continuous_map
    e'.continuous_map e.commutes e'.commutes⟩

/-- The completed naive cotangent complexes of any two presentations of `B` are homotopy
equivalent. -/
public theorem nonempty_homotopyEquiv_of_restrictedPresentations :
    Nonempty (HomotopyEquiv K.cochainComplex L.cochainComplex) :=
  (exists_restrictedPresentationComparison K L).map (fun e => e.equiv)

end Comparison

end Rig

end
