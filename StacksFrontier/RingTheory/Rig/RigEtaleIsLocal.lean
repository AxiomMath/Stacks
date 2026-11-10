module

public import StacksFrontier.RingTheory.Rig.RigEtaleLocality
public import StacksFrontier.RingTheory.Rig.RigEtaleSurjection
public import StacksFrontier.RingTheory.Rig.RigSmoothLocality
public import StacksFrontier.RingTheory.Rig.RigSmoothStableUnderComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothTower
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverPi
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian

/-!
# Rig-étaleness is a local property of arrows of `WAdm^Noeth`

**Stacks 0AQL** asserts that rig-étaleness (Stacks 0GCV) is a local property of arrows of
`WAdm^Noeth` in the sense of Situation 0CBA, in the Noetherian form of Remark 0ANI.  This file
proves it outright.

## Main results

* `Rig.isRigEtale_canonicalMap`: the map to the completion of an étale algebra is rig-étale.
* `Rig.rigEtale_localizationPreserves`, `Rig.rigEtale_faithfullyFlatDescent` and
  `Rig.rigEtale_finiteProductPreserves`: the three axioms of Situation 0CBA.
* `Rig.isRigEtale_iff_isRigSmooth_and_annihilator`: rig-étale is rig-smooth with annihilated
  `H⁰(NL^∧)`.
* `Rig.rigEtale_propertyIsLocalNoetherian`: **Stacks 0AQL**.

## Implementation notes

The source proves Stacks 0AQL by repeating the proof of Stacks 0GCK.  Ascent is shorter here,
because rig-étaleness, unlike rig-smoothness, cancels on the left (`Rig.rigEtale_cancel`, the
cancellation step of Stacks 0GCY): in a localization diagram the composite `B → A → (A')^` is
rig-étale by Stacks 0GCX, it equals `B → (B')^ → (A')^`, and `B → (B')^` is rig-étale, so
`(B')^ → (A')^` is rig-étale.

For descent and for finite products, rig-étaleness is split as rig-smoothness together with
annihilation of `H⁰(NL^∧)` by a power of the ideal of definition
(`Rig.isRigEtale_iff_isRigSmooth_and_annihilator`): a rig-smooth algebra already has `H⁻¹(NL^∧)`
annihilated by condition (3) of Stacks 0GAJ, so this is condition (3) of Stacks 0AJU.  The
rig-smooth half is Stacks 0GCK.  The `H⁰` half is transported along the transitivity sequence of
Stacks 0ALM for `B → A → (A')^`, in which the outer complex `NL^∧_{(A')^/A}` has bijective
differential, so that `H⁰(NL^∧_{A/B}) ⊗_A (A')^ = H⁰(NL^∧_{(A')^/B})`; faithful flatness of
`A → (A')^` then descends the annihilation.

## References

* [Stacks Project, Tag 0AQL](https://stacks.math.columbia.edu/tag/0AQL)
* [Stacks Project, Tag 0ANI](https://stacks.math.columbia.edu/tag/0ANI)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0GCK](https://stacks.math.columbia.edu/tag/0GCK)
* [Stacks Project, Tag 0GCX](https://stacks.math.columbia.edu/tag/0GCX)
* [Stacks Project, Tag 0GCY](https://stacks.math.columbia.edu/tag/0GCY)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
-/

@[expose] public noncomputable section

open TopologicalRing Rig.CompletedPolynomialPresentation
open scoped TensorProduct

universe u

namespace Rig

section CompletionOver

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [IsNoetherianRing B] [CommRing A] (f : B →+* A)

/-- **The canonical map to the completion of an étale algebra is rig-étale.**  For an étale
`f : B →+* A` out of a Noetherian adic ring whose completion over `B` is Noetherian and adic,
`B → (A)^∧` is rig-étale with exponent zero: the completed naive cotangent complex of a
suitable presentation has bijective differential, so both of its cohomology modules vanish. -/
public theorem isRigEtale_canonicalMap [IsLinearTopology (CompletionOver f) (CompletionOver f)]
    [IsNoetherianRing (CompletionOver f)] (hf : f.Etale) (hB : TopologicalRing.IsAdic B)
    (hC : TopologicalRing.IsAdic (CompletionOver f)) :
    Continuous (CompletionOver.canonicalMap f) ∧
      RingHom.IsRigEtale (CompletionOver.canonicalMap f) := by
  obtain ⟨-, hcont, hadic, htft, -⟩ := canonicalMap_facts f hB hC hf
  have hft : FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap f) :=
    ((adicFiniteType_tfae _ hB hC (exists_idealOfDefinition_fg hB inferInstance)
      (exists_idealOfDefinition_fg hC inferInstance)).out 1 6).mp (And.intro hadic htft)
  obtain ⟨I, hI, hIadic⟩ := hB.1
  obtain ⟨Q, hQ⟩ := exists_presentation_bijective_canonicalMap f hf hft hI hIadic
  refine ⟨hcont, hft, I, hI, isRigEtaleOver_of_isRigEtale _ hft I hI ?_⟩
  refine (isRigEtale_iff_exists_annihilator_cohomology _ Q).mpr ⟨0, ?_, ?_⟩
  · refine fun a _ ↦ Module.mem_annihilator.mpr fun z ↦ ?_
    have hz : z.1 = 0 := hQ.1 ((LinearMap.mem_ker.mp z.2).trans (map_zero _).symm)
    exact Subtype.ext (by simp [hz])
  · refine fun a _ ↦ Module.mem_annihilator.mpr fun z ↦ ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨x, rfl⟩ := hQ.2 y
    rw [← map_smul, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self _ _

end CompletionOver

/-- **Rig-étaleness ascends along a localization diagram** (axiom (1) of Situation 0CBA).
The composite `B → A → (A')^` is rig-étale by Stacks 0GCX, `A → (A')^` being rig-étale as the
completion of an étale map; it equals `B → (B')^ → (A')^`, and `B → (B')^` is rig-étale for the
same reason, so `(B')^ → (A')^` is rig-étale by the cancellation step of Stacks 0GCY. -/
public theorem rigEtale_localizationPreserves :
    TopologicalRing.LocalizationPreserves.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hP _ _ _ _
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  obtain ⟨hmapcont, hmap⟩ : Continuous D.map ∧ RingHom.IsRigEtale D.map := hP
  obtain ⟨hβcont, hβ⟩ := isRigEtale_canonicalMap D.toA' D.etaleA hA.1 hA'.1
  obtain ⟨hαcont, hα⟩ := isRigEtale_canonicalMap D.toB' D.etaleB hB.1 hB'.1
  have hcomp := rigEtale_comp hA'.1 hA.1 hB.1 (CompletionOver.canonicalMap D.toA') D.map hβcont
    hmapcont hβ hmap
  rw [D.commutes] at hcomp
  exact ⟨D.continuousCompletedMap, rigEtale_cancel hA'.1 hB'.1 hB.1 D.completedMap
    (CompletionOver.canonicalMap D.toB') D.continuousCompletedMap hαcont hα hcomp⟩

/-! ## Rig-étale is rig-smooth with annihilated `H⁰` -/

section Split

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Rig-étale is rig-smooth with annihilated `H⁰`.**  An object `B` of (Stacks 0AL4) over
`(A, I)` is rig-étale exactly when it is rig-smooth and a power of `I` annihilates
`H⁰(NL^∧_{B/A})` for one (equivalently every) completed polynomial presentation.

A rig-smooth `B` has `H⁻¹(NL^∧_{B/A})` annihilated by a power of `I`, since by condition (3) of
Stacks 0GAJ that power factors through the differential; so the right-hand side is condition (3)
of Stacks 0AJU.  Conversely a rig-étale algebra is rig-smooth by Stacks 0GB1. -/
public theorem isRigEtale_iff_isRigSmooth_and_annihilator (B : AdicFiniteTypeAlgebra.{u, u} A I)
    (P : CompletedPolynomialPresentation I B) :
    IsRigEtale B ↔ IsRigSmooth B ∧
      ∃ c : ℕ, (I ^ c).map (algebraMap A B.carrier) ≤
        Module.annihilator B.carrier
          ((Fin P.variableCount → B.carrier) ⧸
            LinearMap.range (completedNaiveCotangentComplex B P).differential) := by
  refine ⟨fun h ↦ ⟨isRigSmooth_of_isRigEtale B h, ?_⟩, fun ⟨hs, c, hc⟩ ↦ ?_⟩
  · exact ((isRigEtale_iff_exists_annihilator_cohomology B P).mp h).imp fun _ ↦ And.right
  · obtain ⟨b, hb⟩ := (isRigSmooth_iff_cotangentFactorization B P).mp hs
    refine (isRigEtale_iff_exists_annihilator_cohomology B P).mpr ⟨b + c, ?_, ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Module.mem_annihilator.mpr fun z ↦ ?_
      obtain ⟨h, hh⟩ := hb a (Ideal.pow_le_pow_right (Nat.le_add_right b c) ha)
      refine Subtype.ext ?_
      have hz := LinearMap.congr_fun hh z.1
      rw [LinearMap.comp_apply, LinearMap.mem_ker.mp z.2, map_zero] at hz
      simpa using hz.symm
    · exact (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_add_left c b))).trans hc

end Split

/-- A rig-étale arrow of `WAdm^Noeth` is rig-smooth, by Stacks 0GB1 on each ideal of
definition. -/
public theorem isRigSmoothArrow_of_isRigEtaleArrow {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] {φ : B →+* A} (h : RingHom.IsRigEtaleArrow φ) :
    RingHom.IsRigSmoothArrow φ := by
  intro _ _ _ _
  obtain ⟨hcont, hft, I, hI, hc, hfin, hrig⟩ := h
  refine ⟨hcont, hft, I, hI, ?_⟩
  let _ : Algebra B A := φ.toAlgebra
  let _ : Algebra.FiniteType (B ⧸ I) (A ⧸ I.map (algebraMap B A)) := hfin
  rw [show adicFiniteTypeAlgebra φ hft I hI = AdicFiniteTypeAlgebra.of (I := I) A hc from
    CategoryTheory.ObjectProperty.FullSubcategory.ext rfl]
  exact isRigSmooth_of_isRigEtale _ hrig

/-! ## Isomorphisms -/

/-- **An isomorphism of Noetherian adic rings is rig-étale.**  A ring isomorphism `e : R ≃ R'`
which is a homeomorphism is adic of topologically finite type, and with respect to any ideal of
definition `I` its target is the quotient of `R` by the zero ideal, so it is rig-étale by the
zero-variable criterion `Rig.isRigEtale_iff_exists_pow_mul_ker_le_sq`. -/
public theorem isRigEtale_ringEquiv {R R' : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R] [CommRing R']
    [TopologicalSpace R'] [IsTopologicalRing R'] [IsLinearTopology R' R'] [IsNoetherianRing R']
    (hR : TopologicalRing.IsAdic R) (hR' : TopologicalRing.IsAdic R') (e : R ≃+* R')
    (he : Continuous e) (he' : Continuous e.symm) :
    RingHom.IsRigEtale (e : R →+* R') := by
  obtain ⟨I, hI, -⟩ := hR.1
  have hIadic := idealOfDefinition_isAdic_of_isAdicRing hR I hI
  have hsome : FiniteTypeModuloSomeIdealOfDefinition (e : R →+* R') :=
    ⟨⟨I, hI, TopologicalRing.isAdic_map_of_ringEquiv e he he' hIadic⟩, ⟨I, hI,
      RingHom.FiniteType.of_surjective _
        (Ideal.quotientMap_surjective e.surjective)⟩⟩
  have hft : FiniteTypeAdicAlgebraForEveryIdeal (e : R →+* R') :=
    ((adicFiniteType_tfae (e : R →+* R') hR hR'
      (exists_idealOfDefinition_fg hR inferInstance)
      (exists_idealOfDefinition_fg hR' inferInstance)).out 3 6).mp hsome
  refine ⟨hft, I, hI, isRigEtaleOver_of_isRigEtale _ hft I hI ?_⟩
  have hc : IsAdicComplete (I.map (e : R →+* R')) R' := (hft I hI).2.1
  have : IsAdicComplete I R := (IsAdicComplete.congr_ringEquiv I e).mp hc
  refine (isRigEtale_iff_exists_pow_mul_ker_le_sq _ e.surjective).mpr ⟨0, fun a _ y hy ↦ ?_⟩
  have hy0 : y = 0 := e.injective ((RingHom.mem_ker.mp hy).trans (map_zero e).symm)
  rw [hy0, mul_zero]
  exact Ideal.zero_mem _

/-- Rig-étaleness of an arrow of `WAdm^Noeth` is invariant under isomorphisms of its source and
of its target: it is Stacks 0GCX together with `Rig.isRigEtale_ringEquiv`. -/
public theorem isRigEtale_ringEquiv_comp_comp {A A' R R' : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A'] [IsLinearTopology A' A']
    [IsNoetherianRing A'] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] [IsNoetherianRing R] [CommRing R'] [TopologicalSpace R']
    [IsTopologicalRing R'] [IsLinearTopology R' R'] [IsNoetherianRing R']
    (hA : TopologicalRing.IsAdic A) (hA' : TopologicalRing.IsAdic A')
    (hR : TopologicalRing.IsAdic R) (hR' : TopologicalRing.IsAdic R')
    (α : A' ≃+* A) (hα : Continuous α) (hα' : Continuous α.symm)
    (β : R ≃+* R') (hβ : Continuous β) (hβ' : Continuous β.symm)
    (ψ : A →+* R) (hψ : Continuous ψ) (h : RingHom.IsRigEtale ψ) :
    RingHom.IsRigEtale ((β : R →+* R').comp (ψ.comp (α : A' →+* A))) :=
  rigEtale_comp hR' hR hA' (β : R →+* R') (ψ.comp (α : A' →+* A)) hβ (hψ.comp hα)
    (isRigEtale_ringEquiv hR hR' β hβ hβ')
    (rigEtale_comp hR hA hA' ψ (α : A' →+* A) hψ hα h (isRigEtale_ringEquiv hA' hA α hα hα'))

/-! ## Descending the annihilation of `H⁰` -/

section Descent

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
  {base total : AdicFiniteTypeAlgebra.{u, u} R I}
  [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier]

/-- **`H⁰` after an étale-like step.**  Let `base → total` be a morphism of (Stacks 0AL4) over
`(R, I)`, presented over `base` by `ψ` with bijective differential of `NL^∧_{total/base}`.  If
`total` is rig-étale over `(R, I)`, then a power of `I` annihilates
`total ⊗ H⁰(NL^∧_{base/R})` for every presentation of `base`.

In the six-term sequence of Stacks 0ALM for `R → base → total` the term `H⁻¹(NL^∧_{total/base})`
vanishes, so `H⁰(NL^∧_{base/R} ⊗ total) → H⁰(NL^∧_{total/R})` is injective, and the target is
annihilated by condition (3) of Stacks 0AJU. -/
public theorem exists_annihilator_tensor_h0_of_bijective_outer
    (P : CompletedPolynomialPresentation I base) (s : ℕ)
    (ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s) →ₐ[base.carrier]
      total.carrier)
    (hψ : Function.Surjective (ψ.restrictScalars R))
    (F : Fin s → Derivation base.carrier
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)))
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) base.carrier),
      F j (algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q))
    (hbij : Function.Bijective (outerDifferential s ψ hψ F))
    (htotal : IsRigEtale total) :
    ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ y : (Fin P.variableCount → base.carrier) ⧸
        LinearMap.range (completedNaiveCotangentComplex base P).differential,
      (1 : total.carrier) ⊗ₜ[base.carrier] (algebraMap R base.carrier a • y) = 0 := by
  classical
  let Pt := P.combinedPresentation s (ψ.restrictScalars R) hψ
  let KB := completedNaiveCotangentComplex base P
  let KC := completedNaiveCotangentComplex total Pt
  obtain ⟨c, -, hc⟩ := (isRigEtale_iff_exists_annihilator_cohomology total Pt).mp htotal
  obtain ⟨δ, -, -, hexδ, -, -⟩ := P.exists_sixTerm_exact_combined s ψ hψ KB KC F hFc hFp
  have hδ : ∀ z, δ z = 0 := fun z ↦ by
    rw [show z = 0 from Subtype.ext (hbij.1 ((LinearMap.mem_ker.mp z.2).trans (map_zero _).symm)),
      map_zero]
  let inl := NaiveCotangent.chainMapInl _
    (P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC)
  have hinj : Function.Injective inl.onH₀ := by
    refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
    obtain ⟨w, rfl⟩ := (hexδ z).mp hz
    exact hδ w
  refine ⟨c, fun a ha y ↦ ?_⟩
  have hinner : algebraMap R total.carrier a •
      P.innerBaseChangeH0Equiv (C := total) KB (1 ⊗ₜ y) = 0 := hinj (by
    rw [map_smul, map_zero]
    exact Module.mem_annihilator.mp (hc (Ideal.mem_map_of_mem _ ha)) _)
  rw [← map_smul, LinearEquiv.map_eq_zero_iff] at hinner
  have heq : algebraMap R total.carrier a • ((1 : total.carrier) ⊗ₜ[base.carrier] y) =
      (1 : total.carrier) ⊗ₜ (algebraMap R base.carrier a • y) := by
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul total.carrier
      (algebraMap R base.carrier a), ← IsScalarTower.algebraMap_apply]
  rwa [heq] at hinner

/-- **`H⁰` descends along a faithfully flat step with acyclic completed cotangent complex.**
In the situation of `Rig.exists_annihilator_tensor_h0_of_bijective_outer`, if moreover `total`
is faithfully flat over `base`, then a power of `I` annihilates `H⁰(NL^∧_{base/R})`. -/
public theorem exists_annihilator_h0_of_faithfullyFlat_of_bijective_outer
    [Module.FaithfullyFlat base.carrier total.carrier]
    (P : CompletedPolynomialPresentation I base) (s : ℕ)
    (ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s) →ₐ[base.carrier]
      total.carrier)
    (hψ : Function.Surjective (ψ.restrictScalars R))
    (F : Fin s → Derivation base.carrier
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)))
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) base.carrier),
      F j (algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q))
    (hbij : Function.Bijective (outerDifferential s ψ hψ F))
    (htotal : IsRigEtale total) :
    ∃ c : ℕ, (I ^ c).map (algebraMap R base.carrier) ≤
      Module.annihilator base.carrier
        ((Fin P.variableCount → base.carrier) ⧸
          LinearMap.range (completedNaiveCotangentComplex base P).differential) := by
  obtain ⟨c, hc⟩ := exists_annihilator_tensor_h0_of_bijective_outer P s ψ hψ F hFc hFp hbij
    htotal
  refine ⟨c, Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Module.mem_annihilator.mpr fun y ↦ ?_⟩
  simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hc a ha y

end Descent

/-- A rig-étale map gives a rig-étale `adicFiniteTypeAlgebra` over any ideal of definition. -/
private theorem isRigEtale_adicFiniteTypeAlgebra {B A : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A]
    {φ : B →+* A} (hφ : Continuous φ) (hB : TopologicalRing.IsAdic B)
    (hA : TopologicalRing.IsAdic A) (h : RingHom.IsRigEtale φ)
    (hft : FiniteTypeAdicAlgebraForEveryIdeal φ) (I : Ideal B)
    (hI : TopologicalRing.IsIdealOfDefinition I) :
    IsRigEtale (adicFiniteTypeAlgebra φ hft I hI) := by
  obtain ⟨hc, hfin, hrig⟩ := h.forall_idealOfDefinition hφ hB hA I hI
  let _ : Algebra B A := φ.toAlgebra
  let _ := hfin
  rw [show adicFiniteTypeAlgebra φ hft I hI = AdicFiniteTypeAlgebra.of (I := I) A hc from
    CategoryTheory.ObjectProperty.FullSubcategory.ext rfl]
  exact hrig

/-- **Rig-étaleness descends along a faithfully flat localization diagram** (axiom (2) of
Situation 0CBA).  Rig-smoothness of `B → A` is Stacks 0GCK.  For the annihilation of
`H⁰(NL^∧_{A/B})`: the composite `B → (B')^ → (A')^` is rig-étale by Stacks 0GCX, it equals
`B → A → (A')^`, and `A → (A')^` is faithfully flat with a presentation of bijective completed
cotangent differential, so `Rig.exists_annihilator_h0_of_faithfullyFlat_of_bijective_outer`
applies. -/
public theorem rigEtale_faithfullyFlatDescent :
    TopologicalRing.FaithfullyFlatDescent.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ D hA hB hA' hB' hFF hP _ _ _ _
  have : IsNoetherianRing (CompletionOver D.toA') := hA'.2
  have : IsNoetherianRing (CompletionOver D.toB') := hB'.2
  obtain ⟨hmapcont, hsm⟩ : Continuous D.map ∧ RingHom.IsRigSmooth D.map :=
    rigSmooth_faithfullyFlatDescent D hA hB hA' hB' hFF (isRigSmoothArrow_of_isRigEtaleArrow hP)
  have hft := hsm.1
  obtain ⟨hcompcont, hcomp⟩ : Continuous D.completedMap ∧
      RingHom.IsRigEtale D.completedMap := hP
  obtain ⟨hαcont, hα⟩ := isRigEtale_canonicalMap D.toB' D.etaleB hB.1 hB'.1
  obtain ⟨hA'noeth, hβcont, hβadic, hβft, -⟩ := canonicalMap_facts D.toA' hA.1 hA'.1 D.etaleA
  have htot := rigEtale_comp hA'.1 hB'.1 hB.1 D.completedMap
    (CompletionOver.canonicalMap D.toB') hcompcont hαcont hcomp hα
  rw [← D.commutes] at htot
  obtain ⟨I, hI, -⟩ := hB.1.1
  have hsmoothI := hsm.forall_idealOfDefinition hmapcont
    (weaklyAdmissible_of_isAdicRing hB.1) (weaklyAdmissible_of_isAdicRing hA.1) hft I hI
  have hftβ : Rig.FiniteTypeAdicAlgebraForEveryIdeal (CompletionOver.canonicalMap D.toA') :=
    ((Rig.adicFiniteType_tfae _ hA.1 hA'.1 (exists_idealOfDefinition_fg hA.1 hA.2)
      (exists_idealOfDefinition_fg hA'.1 hA'.2)).out 1 6).mp (And.intro hβadic hβft)
  have hJadic : _root_.IsAdic (I.map D.map) := (hft I hI).1
  have hJ := Rig.isIdealOfDefinition_of_isAdic hJadic
  let : Algebra B A := D.map.toAlgebra
  let : Algebra A (CompletionOver D.toA') := (CompletionOver.canonicalMap D.toA').toAlgebra
  let : Algebra B (CompletionOver D.toA') :=
    ((CompletionOver.canonicalMap D.toA').comp D.map).toAlgebra
  let base := adicFiniteTypeAlgebra D.map hft I hI
  let total := adicFiniteTypeAlgebra ((CompletionOver.canonicalMap D.toA').comp D.map) htot.1 I hI
  let fiber : AdicFiniteTypeAlgebra.{u, u} base.carrier base.adicIdeal :=
    adicFiniteTypeAlgebra (CompletionOver.canonicalMap D.toA') hftβ (I.map D.map) hJ
  let : Algebra base.carrier total.carrier := (inferInstance : Algebra base.carrier fiber.carrier)
  have : IsScalarTower B base.carrier total.carrier := .of_algebraMap_eq fun _ => rfl
  obtain ⟨Q, hQ⟩ := exists_presentation_bijective_canonicalMap D.toA' D.etaleA hftβ hJ hJadic
  let KF := completedNaiveCotangentComplex fiber Q
  let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin Q.variableCount)
      →ₐ[base.carrier] total.carrier := Q.toAlgHom
  have hψ : Function.Surjective (ψ.restrictScalars B) := Q.toAlgHom_surjective
  have houter : outerDifferential Q.variableCount ψ hψ (fun j => KF.partialDeriv j) =
      KF.differential := LinearMap.ext fun z => by
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Q.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  have : Module.FaithfullyFlat base.carrier total.carrier :=
    TopologicalRing.CompletionOver.faithfullyFlat_canonicalMap hA.1 hFF
  have htotal : IsRigEtale total :=
    isRigEtale_adicFiniteTypeAlgebra (hβcont.comp hmapcont : Continuous
      ((CompletionOver.canonicalMap D.toA').comp D.map)) hB.1 hA'.1 htot htot.1 I hI
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  obtain ⟨c, hc⟩ := exists_annihilator_h0_of_faithfullyFlat_of_bijective_outer P
    Q.variableCount ψ hψ (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
    (fun j => KF.partialDeriv_polynomial j) (houter ▸ hQ) htotal
  exact ⟨hmapcont, hft, I, hI, isRigEtaleOver_of_isRigEtale D.map hft I hI
    ((isRigEtale_iff_isRigSmooth_and_annihilator base P).mpr ⟨hsmoothI, c, hc⟩)⟩

/-- **Rig-étaleness is preserved by finite products of targets** (axiom (3) of Situation
0CBA).  Rig-smoothness of `B → ∏ Aⱼ` is Stacks 0GCK.  Each projection `∏ Aⱼ → Aᵢ` is the
localization at an idempotent, so `Rig.exists_annihilator_tensor_h0_of_bijective_outer` applies
to `B → ∏ Aⱼ → Aᵢ` and annihilates `Aᵢ ⊗ H⁰(NL^∧_{∏ Aⱼ/B})`; an element of a module over
`∏ Aⱼ` all of whose localizations at the idempotents vanish is zero. -/
public theorem rigEtale_finiteProductPreserves :
    TopologicalRing.FiniteProductPreserves.{u}
      (fun R [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] ↦
        TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro B _ _ _ _ hBweak hBcount ι _ A _ _ _ _ hAweak hAcount f hf hCB hCA hPi _ _ _ _
  classical
  have : ∀ i, IsNoetherianRing (A i) := fun i ↦ (hCA i).2
  have hsm : Continuous (RingHom.pi f) ∧ RingHom.IsRigSmooth (RingHom.pi f) :=
    rigSmooth_finiteProductPreserves hBweak hBcount A hAweak hAcount f hf hCB hCA
      (fun i ↦ isRigSmoothArrow_of_isRigEtaleArrow (hPi i))
  have hft := hsm.2.1
  have hprodadic : TopologicalRing.IsAdic (∀ i, A i) := isAdic_pi A fun i ↦ (hCA i).1
  obtain ⟨I, hI, -⟩ := hCB.1.1
  have hsmoothI := hsm.2.forall_idealOfDefinition hsm.1 (weaklyAdmissible_of_isAdicRing hCB.1)
    (weaklyAdmissible_of_isAdicRing hprodadic) hft I hI
  have hPi' : ∀ i, Continuous (f i) ∧ RingHom.IsRigEtale (f i) := fun i ↦ hPi i
  have hfti : ∀ i, Rig.FiniteTypeAdicAlgebraForEveryIdeal (f i) := fun i ↦ (hPi' i).2.1
  have hrigi : ∀ i, IsRigEtale (adicFiniteTypeAlgebra (f i) (hfti i) I hI) := fun i ↦
    isRigEtale_adicFiniteTypeAlgebra (hf i) hCB.1 (hCA i).1 (hPi' i).2 (hfti i) I hI
  let : Algebra B (∀ j, A j) := (RingHom.pi f).toAlgebra
  let : ∀ i, Algebra B (A i) := fun i ↦ (f i).toAlgebra
  let base := adicFiniteTypeAlgebra (RingHom.pi f) hft I hI
  let total : ι → AdicFiniteTypeAlgebra.{u, u} B I := fun i ↦
    adicFiniteTypeAlgebra (f i) (hfti i) I hI
  let : ∀ i, Algebra (∀ j, A j) (A i) := fun i ↦ (Pi.evalRingHom A i).toAlgebra
  let : ∀ i, Algebra base.carrier (total i).carrier := fun i ↦ (Pi.evalRingHom A i).toAlgebra
  have : ∀ i, IsScalarTower B base.carrier (total i).carrier := fun i ↦
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hidem : ∀ i, IsIdempotentElem (Pi.single i 1 : ∀ j, A j) := fun i ↦ by
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  have hloc : ∀ i, IsLocalization.Away (Pi.single i 1 : ∀ j, A j) (A i) := fun i ↦
    IsLocalization.away_of_isIdempotentElem (hidem i) (RingHom.ker_evalRingHom _ _)
      (Function.surjective_eval i)
  have hétale : ∀ i, (algebraMap base.carrier (total i).carrier).Etale := fun i ↦
    (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway
      (Pi.single i 1 : ∀ j, A j)) : (Pi.evalRingHom A i).Etale)
  have : ∀ i, Module.Flat base.carrier (total i).carrier := fun i ↦
    (IsLocalization.flat (A i) (Submonoid.powers (Pi.single i 1 : ∀ j, A j)) :
      Module.Flat (∀ j, A j) (A i))
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  have key : ∀ i, ∃ c : ℕ, ∀ a ∈ I ^ c, ∀ y : (Fin P.variableCount → base.carrier) ⧸
        LinearMap.range (completedNaiveCotangentComplex base P).differential,
      (1 : (total i).carrier) ⊗ₜ[base.carrier] (algebraMap B base.carrier a • y) = 0 := by
    intro i
    let K := base.adicIdeal.map (algebraMap base.carrier (total i).carrier)
    have hid : K = (total i).adicIdeal := AdicFiniteTypeAlgebra.map_adicIdeal_tower
    have hcompl : IsAdicComplete K (total i).carrier := hid ▸ (total i).isAdicallyComplete
    have : Algebra.FiniteType (base.carrier ⧸ base.adicIdeal) ((total i).carrier ⧸ K) := by
      refine Algebra.FiniteType.of_surjective (Algebra.ofId _ _) fun y => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨Ideal.Quotient.mk _ (show base.carrier from Pi.single i (show A i from x)), ?_⟩
      exact congrArg (Ideal.Quotient.mk K) (Pi.single_eq_same i (show A i from x))
    let X : AdicFiniteTypeAlgebra.{u, u} base.carrier base.adicIdeal :=
      AdicFiniteTypeAlgebra.of (total i).carrier hcompl
    obtain ⟨Q, hQ⟩ := exists_presentation_bijective_of_etale base.adicIdeal
      (algebraMap base.carrier (total i).carrier) (hétale i) X
      (AdicCompletion.ofAlgEquiv K).symm.toRingEquiv fun s => by
        have h1 : algebraMap (total i).carrier (AdicCompletion K (total i).carrier)
            (algebraMap base.carrier (total i).carrier s) =
            AdicCompletion.ofAlgEquiv K (algebraMap base.carrier (total i).carrier s) :=
          ((AdicCompletion.ofAlgEquiv K).commutes _).symm
        exact (congrArg _ h1).trans ((AdicCompletion.ofAlgEquiv K).symm_apply_apply _)
    let KF := completedNaiveCotangentComplex X Q
    let ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin Q.variableCount)
        →ₐ[base.carrier] (total i).carrier := Q.toAlgHom
    have hψ : Function.Surjective (ψ.restrictScalars B) := Q.toAlgHom_surjective
    have houter : outerDifferential Q.variableCount ψ hψ (fun j => KF.partialDeriv j) =
        KF.differential := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Q.extension) z
      funext j
      exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ hψ)
        (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
    exact exists_annihilator_tensor_h0_of_bijective_outer P Q.variableCount ψ hψ
      (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
      (fun j => KF.partialDeriv_polynomial j) (houter ▸ hQ) (hrigi i)
  choose c hc using key
  refine ⟨continuous_pi hf, hft, I, hI, isRigEtaleOver_of_isRigEtale _ hft I hI
    ((isRigEtale_iff_isRigSmooth_and_annihilator base P).mpr ⟨hsmoothI, Finset.univ.sup c, ?_⟩)⟩
  refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Module.mem_annihilator.mpr fun y ↦ ?_
  set z := algebraMap B base.carrier a • y
  let e : ι → base.carrier := fun i ↦ (Pi.single i 1 : ∀ j, A j)
  have hcomp : ∀ i, e i • z = 0 := by
    intro i
    have h0 := hc i a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) ha) y
    have hloc' : IsLocalization.Away (e i) (total i).carrier := hloc i
    have hbc : IsLocalizedModule (Submonoid.powers (e i))
        (TensorProduct.mk base.carrier (total i).carrier
          ((Fin P.variableCount → base.carrier) ⧸
            LinearMap.range (completedNaiveCotangentComplex base P).differential) 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers (e i))
        (total i).carrier _).mpr (TensorProduct.isBaseChange _ _ _)
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (e i))
      (TensorProduct.mk base.carrier (total i).carrier
          ((Fin P.variableCount → base.carrier) ⧸
            LinearMap.range (completedNaiveCotangentComplex base P).differential) 1)).mp h0
    have hidem' : IsIdempotentElem (e i) := hidem i
    rw [show e i = e i * e i ^ n by rw [← pow_succ', hidem'.pow_succ_eq], mul_smul]
    exact (congrArg _ hn).trans (smul_zero _)
  have hsum : ∑ i, e i = 1 := Finset.univ_sum_single (1 : ∀ j, A j)
  change z = 0
  rw [← one_smul base.carrier z, ← hsum, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ ↦ hcomp i

/-! ## Descent along a finite family -/


/-- **An adic ring is its own completion.**  For an adic topological ring `B`, the canonical
map `B → (B)^∧` to the completion of `B` over itself is a ring isomorphism which is a
homeomorphism. -/
public theorem exists_ringEquiv_completionOver_id {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsLinearTopology B B] (hB : TopologicalRing.IsAdic B) :
    ∃ e : B ≃+* CompletionOver (RingHom.id B),
      ⇑e = ⇑(CompletionOver.canonicalMap (RingHom.id B)) ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨⟨I, hIdef, hIadic⟩, hT2, hCompl⟩ := hB
  have hIc : IsAdicComplete I B := by
    let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
    have _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
    exact (IsAdic.isAdicComplete_iff hIadic).mpr ⟨hCompl, hT2⟩
  have hIc' : IsAdicComplete (I.map (RingHom.id B)) B := by rwa [Ideal.map_id]
  let e₁ := CompletionOver.adicCompletionRingEquiv hIdef hIadic (RingHom.id B)
  have hcomp' : ∀ b, e₁ (CompletionOver.canonicalMap (RingHom.id B) b) =
      AdicCompletion.of (I.map (RingHom.id B)) B b :=
    DFunLike.congr_fun (adicCompletionRingEquiv_comp_canonicalMap (RingHom.id B) hIdef hIadic)
  have hbij : Function.Bijective (CompletionOver.canonicalMap (RingHom.id B)) := by
    refine ⟨fun a b hab ↦ (AdicCompletion.of_bijective (I.map (RingHom.id B)) B).1 ?_,
      fun x ↦ ?_⟩
    · rw [← hcomp', ← hcomp', hab]
    · obtain ⟨b, hb⟩ := (AdicCompletion.of_bijective (I.map (RingHom.id B)) B).2 (e₁ x)
      exact ⟨b, e₁.injective (by rw [hcomp', hb])⟩
  let e := RingEquiv.ofBijective _ hbij
  refine ⟨e, rfl, TopologicalRing.continuous_canonicalMap _, ?_⟩
  refine continuous_of_continuousAt_zero e.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, hIadic.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  let J : TopologicalRing.WeakIdealOfDefinitionIndex B :=
    ⟨I ^ (n + 1), TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hIadic n⟩
  filter_upwards [(TopologicalRing.CompletionOver.isOpen_ker_projection (RingHom.id B) J).mem_nhds
    (RingHom.mem_ker.mpr (map_zero _))] with x hx
  have hx' : CompletionOver.projection (RingHom.id B) J
      (CompletionOver.canonicalMap (RingHom.id B) (e.symm x)) = 0 := by
    rwa [show CompletionOver.canonicalMap (RingHom.id B) (e.symm x) = x from e.apply_symm_apply x]
  rw [CompletionOver.projection_canonicalMap, Ideal.Quotient.eq_zero_iff_mem,
    TopologicalRing.extendedIdeal, Ideal.map_id] at hx'
  exact Ideal.pow_le_pow_right (Nat.le_succ n) hx'

/-- **Rig-étaleness descends along a finite jointly faithfully flat family of completed étale
maps.**  Let `g : B → A` be a continuous homomorphism of Noetherian adic rings and let
`A → A'ₛ` be finitely many étale ring maps with `A → ∏ₛ A'ₛ` faithfully flat. If each composite
`B → A → (A'ₛ)^` is rig-étale, then so is `g`.

This is axioms (2) and (3) of Situation 0CBA together: by finite products `B → ∏ₛ (A'ₛ)^` is
rig-étale, `∏ₛ (A'ₛ)^` is the completion of `∏ₛ A'ₛ`
(`TopologicalRing.CompletionOver.piRingEquiv`), and faithfully flat descent along `A → ∏ₛ A'ₛ`
with the identity on `B` applies. -/
public theorem isRigEtaleArrow_of_finite_etale_family {B A : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hB : TopologicalRing.IsNoetherianAdic B) (hA : TopologicalRing.IsNoetherianAdic A)
    (g : B →+* A) (hg : Continuous g) {σ : Type u} [Finite σ] (A' : σ → Type u)
    [∀ s, CommRing (A' s)] [∀ s, Algebra A (A' s)] [∀ s, Algebra.Etale A (A' s)]
    (hff : Module.FaithfullyFlat A (∀ s, A' s))
    (hP : ∀ s, RingHom.IsRigEtaleArrow
      ((CompletionOver.canonicalMap (algebraMap A (A' s))).comp g)) :
    RingHom.IsRigEtaleArrow g := by
  have : Fintype σ := Fintype.ofFinite σ
  have : IsNoetherianRing A := hA.2
  have : IsNoetherianRing B := hB.2
  have : ∀ s, IsNoetherianRing (A' s) := fun s ↦ Algebra.FiniteType.isNoetherianRing A (A' s)
  let f : A →+* ∀ s, A' s := RingHom.pi fun s ↦ algebraMap A (A' s)
  have hT : ∀ s, TopologicalRing.IsNoetherianAdic (CompletionOver (algebraMap A (A' s))) :=
    fun s ↦ TopologicalRing.completionOver_isNoetherianAdic _ hA inferInstance
  have hTf : TopologicalRing.IsNoetherianAdic (CompletionOver f) :=
    TopologicalRing.completionOver_isNoetherianAdic _ hA inferInstance
  have hTB : TopologicalRing.IsNoetherianAdic (CompletionOver (RingHom.id B)) :=
    TopologicalRing.completionOver_isNoetherianAdic _ hB inferInstance
  have : ∀ s, IsNoetherianRing (CompletionOver (algebraMap A (A' s))) := fun s ↦ (hT s).2
  have : IsNoetherianRing (CompletionOver f) := hTf.2
  have : IsNoetherianRing (CompletionOver (RingHom.id B)) := hTB.2
  have hcont : ∀ s, Continuous ((CompletionOver.canonicalMap (algebraMap A (A' s))).comp g) :=
    fun s ↦ (TopologicalRing.continuous_canonicalMap _).comp hg
  have hTpi : TopologicalRing.IsAdic (∀ s, CompletionOver (algebraMap A (A' s))) :=
    isAdic_pi _ fun s ↦ (hT s).1
  -- an adic ring is linearly topologized, by the powers of an ideal defining its topology
  have : IsLinearTopology (∀ s, CompletionOver (algebraMap A (A' s)))
      (∀ s, CompletionOver (algebraMap A (A' s))) := by
    obtain ⟨⟨J, -, hJ⟩, -, -⟩ := hTpi
    exact IsLinearTopology.mk_of_hasBasis _ (S := Ideal _) (s := fun n ↦ J ^ n)
      hJ.hasBasis_nhds_zero
  -- finite products
  have hprod := rigEtale_finiteProductPreserves hB.1.isWeaklyAdmissible
    (countablyGenerated_nhds_of_isAdicRing hB.1)
    (fun s ↦ CompletionOver (algebraMap A (A' s))) (fun s ↦ (hT s).1.isWeaklyAdmissible)
    (fun s ↦ countablyGenerated_nhds_of_isAdicRing (hT s).1) _ hcont hB hT hP
  obtain ⟨hpc, hpr⟩ : Continuous (RingHom.pi fun s ↦
      (CompletionOver.canonicalMap (algebraMap A (A' s))).comp g) ∧
      RingHom.IsRigEtale (RingHom.pi fun s ↦
        (CompletionOver.canonicalMap (algebraMap A (A' s))).comp g) := hprod
  -- the identifications
  obtain ⟨eB, heB, heBc, heBc'⟩ := exists_ringEquiv_completionOver_id hB.1
  let Φ := CompletionOver.piRingEquiv fun s ↦ algebraMap A (A' s)
  have hΦc := CompletionOver.continuous_piRingEquiv fun s ↦ algebraMap A (A' s)
  have hΦc' := CompletionOver.continuous_piRingEquiv_symm fun s ↦ algebraMap A (A' s)
  let φ : CompletionOver (RingHom.id B) →+* CompletionOver f :=
    (Φ.symm : (∀ s, CompletionOver (algebraMap A (A' s))) →+* CompletionOver f).comp
      ((RingHom.pi fun s ↦ (CompletionOver.canonicalMap (algebraMap A (A' s))).comp g).comp
        (eB.symm : CompletionOver (RingHom.id B) →+* B))
  have hφ : RingHom.IsRigEtale φ :=
    isRigEtale_ringEquiv_comp_comp hB.1 hTB.1 hTpi hTf.1 eB.symm heBc' heBc Φ.symm hΦc' hΦc
      _ hpc hpr
  have hφc : Continuous φ := hΦc'.comp (hpc.comp heBc')
  let LD : TopologicalRing.LocalizationDiagram A B (∀ s, A' s) B :=
    { toA' := f
      toB' := RingHom.id B
      map := g
      completedMap := φ
      weaklyAdmissibleA := hA.1.isWeaklyAdmissible
      weaklyAdmissibleB := hB.1.isWeaklyAdmissible
      countableA := countablyGenerated_nhds_of_isAdicRing hA.1
      countableB := countablyGenerated_nhds_of_isAdicRing hB.1
      etaleA := (RingHom.etale_algebraMap.mpr inferInstance : (algebraMap A (∀ s, A' s)).Etale)
      etaleB := (RingHom.etale_algebraMap.mpr inferInstance : (algebraMap B B).Etale)
      continuousMap := hg
      continuousCompletedMap := hφc
      commutes := by
        refine RingHom.ext fun b ↦ Φ.injective ?_
        have h1 : eB.symm (CompletionOver.canonicalMap (RingHom.id B) b) = b := by
          rw [← heB]
          exact eB.symm_apply_apply b
        simp only [RingHom.comp_apply, φ, RingEquiv.coe_toRingHom, h1, RingEquiv.apply_symm_apply]
        rw [CompletionOver.piRingEquiv_canonicalMap]
        rfl }
  intro _ _ _ _
  exact rigEtale_faithfullyFlatDescent LD hA hB hTf hTB
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff : f.FaithfullyFlat)
    (by intro _ _ _ _; exact ⟨hφc, hφ⟩)

/-- **Stacks 0AQL.** Rig-étaleness is a local property of arrows of `WAdm^Noeth`, in the sense
of Situation 0CBA in the Noetherian form of Remark 0ANI: it ascends along a completed étale
localization diagram, descends along one whose target-side horizontal map is faithfully flat,
and is preserved by finite products of targets. -/
@[stacks 0AQL]
public theorem rigEtale_propertyIsLocalNoetherian :
    TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsRigEtaleArrow φ) :=
  ⟨rigEtale_localizationPreserves, rigEtale_faithfullyFlatDescent,
    rigEtale_finiteProductPreserves⟩

end Rig

end
