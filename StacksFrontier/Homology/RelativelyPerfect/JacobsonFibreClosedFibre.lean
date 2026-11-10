module

public import StacksFrontier.Homology.RelativelyPerfect.JacobsonFibre
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonStalks
public import StacksFrontier.RingTheory.Localization.AtPrimeIsPushout
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp

/-!
# Tor amplitude at a generization, from the closed fibre

Let `A` be flat and of finite presentation over `R`, presented by `d` variables, let `I` be an
ideal of `R` and `A₀ = A ⊗_R R/I`. Let `P` be a bounded above complex of finite free `A`-modules
and `𝔮 ⊆ 𝔮₀` primes of `A` with `𝔮₀` the contraction of a prime `𝔮₀'` of `A₀`. If the closed fibre
`P ⊗_A A₀` has Tor amplitude in `[a, b]` over `R/I` at `𝔮₀'`, then `P` has Tor amplitude in
`[a - d, b]` over `R` at `𝔮`. This is the ring-theoretic heart of Stacks 0DL5 and 0DJZ.

The local rings at `𝔮₀'` and its contractions form a pushout square
(`Algebra.IsPushout.of_isLocalization_atPrime_of_surjective`); `A_{𝔮₀}` being flat over `R_{𝔭₀}`,
the derived fibre of `P_{𝔮₀}` along `R_{𝔭₀} → (R/I)_{𝔭₀}` is the localization of the closed fibre,
and Stacks 0DJH applies.

## Main results

* `PseudoCoherence.hasTorAmplitudeAt_of_hasTorAmplitudeAt_closedFibre`: the statement above.

## References

* [Stacks Project, Lemma 15.85.9 (Tag 0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 76.54.5 (Tag 0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars StacksDraft.TorAmplitude

namespace PseudoCoherence

universe u

/-- If the composite `A → B → C` agrees with `A → A' → C` and `A, A', C` form a tower, then
`A, B, C` form a tower. -/
private theorem isScalarTower_of_algebraMap_comp_eq (A' : Type*) {A B C : Type*} [CommRing A]
    [CommRing A'] [CommRing B] [CommRing C] [Algebra A A'] [Algebra A B] [Algebra A C]
    [Algebra B C] [Algebra A' C] [IsScalarTower A A' C]
    (h : ∀ x : A, algebraMap B C (algebraMap A B x) = algebraMap A' C (algebraMap A A' x)) :
    IsScalarTower A B C :=
  IsScalarTower.of_algebraMap_eq fun x => by rw [h, ← IsScalarTower.algebraMap_apply]

-- The statement involves no derived category; the proof goes through Stacks 0DJH
-- (`hasTorAmplitudeAt_of_derivedFibre_of_le`) and the derived base change of
-- `Stacks.Thickenings.hasTorAmplitudeCanonical_derivedExtensionScalars_restrictScalars`, both
-- stated at the standard model of `D(R)`; a higher-priority model of `D(R)` is visible here, so
-- the standard one is given priority.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Tor amplitude at a generization, from the closed fibre.** Let `A` be a flat, finitely
presented `R`-algebra presented by `d` variables, let `I` be an ideal of `R`, let `A₀` be a pushout
`A ⊗_R R/I`, and let `P` be a bounded above complex of finite free `A`-modules. Let `𝔮₀'` be a
prime of `A₀` and `𝔮` a prime of `A` contained in the contraction of `𝔮₀'`. If `P ⊗_A A₀` has Tor
amplitude in `[a, b]` over `R/I` at `𝔮₀'`, then `P` has Tor amplitude in `[a - d, b]` over `R` at
`𝔮`. -/
theorem hasTorAmplitudeAt_of_hasTorAmplitudeAt_closedFibre
    {R A A₀ : Type u} [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpresentation : Function.Surjective presentation) (I : Ideal R)
    [Algebra (R ⧸ I) A₀] [Algebra A A₀] [Algebra R A₀] [IsScalarTower R (R ⧸ I) A₀]
    [IsScalarTower R A A₀] [Algebra.IsPushout R (R ⧸ I) A A₀]
    (q₀' : Ideal A₀) [q₀'.IsPrime] (q : Ideal A) [q.IsPrime] (hq : q ≤ q₀'.under A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsBoundedAboveFiniteFree P) (a b : ℤ)
    (h₀ : HasTorAmplitudeAt (R ⧸ I) ((CochainComplex.extendScalars (algebraMap A A₀)).obj P)
      q₀' a b) :
    HasTorAmplitudeAt R P q (a - (d : ℤ)) b := by
  let q₀ := q₀'.under A
  let p := q₀.under R
  let p' := q₀'.under (R ⧸ I)
  have : p'.LiesOver p := ⟨by
    change (q₀'.under A).under R = (q₀'.under (R ⧸ I)).under R
    rw [Ideal.under_under, Ideal.under_under]⟩
  let Rp := Localization.AtPrime p
  let Aq := Localization.AtPrime q₀
  let R'p := Localization.AtPrime p'
  let T := Localization.AtPrime q₀'
  let : Algebra Rp Aq := Localization.AtPrime.algebraOfLiesOver p q₀
  let : Algebra Rp R'p := Localization.AtPrime.algebraOfLiesOver p p'
  let : Algebra R'p T := Localization.AtPrime.algebraOfLiesOver p' q₀'
  let : Algebra Aq T := Localization.AtPrime.algebraOfLiesOver q₀ q₀'
  let : Algebra Rp T := ((algebraMap Aq T).comp (algebraMap Rp Aq)).toAlgebra
  have hRA : ∀ r : R, algebraMap Rp Aq (algebraMap R Rp r) = algebraMap A Aq (algebraMap R A r) :=
    fun r => Localization.localRingHom_to_map _ _ _ _ r
  have hRR : ∀ r : R, algebraMap Rp R'p (algebraMap R Rp r) =
      algebraMap (R ⧸ I) R'p (algebraMap R (R ⧸ I) r) :=
    fun r => Localization.localRingHom_to_map _ _ _ _ r
  have hR'A' : ∀ r : R ⧸ I, algebraMap R'p T (algebraMap (R ⧸ I) R'p r) =
      algebraMap A₀ T (algebraMap (R ⧸ I) A₀ r) :=
    fun r => Localization.localRingHom_to_map _ _ _ _ r
  have hAA : ∀ x : A, algebraMap Aq T (algebraMap A Aq x) = algebraMap A₀ T (algebraMap A A₀ x) :=
    fun x => Localization.localRingHom_to_map _ _ _ _ x
  have : IsScalarTower R Rp Aq := isScalarTower_of_algebraMap_comp_eq A hRA
  have : IsScalarTower A Aq T := isScalarTower_of_algebraMap_comp_eq A₀ hAA
  have : IsScalarTower R Aq T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A Aq, hAA, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A₀ T]
  have : IsScalarTower R Rp R'p := isScalarTower_of_algebraMap_comp_eq (R ⧸ I) hRR
  have : IsScalarTower (R ⧸ I) R'p T := isScalarTower_of_algebraMap_comp_eq A₀ hR'A'
  have : IsScalarTower R R'p T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I) R'p, hR'A', ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A₀ T]
  have : IsScalarTower Rp Aq T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Rp R'p T := IsScalarTower.of_algebraMap_eq' <|
    IsLocalization.ringHom_ext p.primeCompl <| RingHom.ext fun r => by
      simp only [RingHom.comp_apply]
      rw [show algebraMap Rp T (algebraMap R Rp r) =
          algebraMap Aq T (algebraMap Rp Aq (algebraMap R Rp r)) from rfl, hRA, hAA, hRR, hR'A',
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hmk : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have : Algebra.IsPushout Rp Aq R'p T :=
    Algebra.IsPushout.of_isLocalization_atPrime_of_surjective (R := R) (R' := R ⧸ I) (A := A)
      hmk q₀' Rp R'p Aq T
  -- The map `R_{𝔭₀} → (R/I)_{𝔭₀}` is surjective.
  have hh : Function.Surjective (algebraMap Rp R'p) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) R'p :=
      IsLocalization.algebraMapSubmonoid_primeCompl_of_surjective hmk p' p
        (Ideal.LiesOver.over (P := p') (p := p)).symm
    have : Algebra.IsPushout R (R ⧸ I) Rp R'p :=
      Algebra.isPushout_of_isLocalization p.primeCompl Rp (R ⧸ I) R'p
    exact Algebra.IsPushout.algebraMap_surjective_of_surjective (R := R) (R' := R ⧸ I) hmk
  -- The derived fibre of `P_{𝔮₀}` along `R_{𝔭₀} → (R/I)_{𝔭₀}` is the localization of the closed
  -- fibre.
  obtain ⟨n, hn⟩ := hP.upperBound
  have := hn
  have : ∀ i, Module.Flat A (P.X i) := fun i =>
    have := (hP.finiteFree i).2
    inferInstance
  let DT := totalDerivedExtensionScalars.{u, u, u} (algebraMap A T)
  have := DT.comparison_isIso_of_flat P n
  let K' := (totalDerivedExtensionScalars.{u, u, u} (algebraMap A Aq)).functor.obj
    (DerivedCategory.Q.obj P)
  let K := DerivedCategory.Q.obj ((CochainComplex.extendScalars (algebraMap A₀ T)).obj
    ((CochainComplex.extendScalars (algebraMap A A₀)).obj P))
  let eK : (totalDerivedExtensionScalars.{u, u, u} (algebraMap Aq T)).functor.obj K' ≅ K :=
    (totalDerivedExtensionScalarsComp (algebraMap A Aq) (algebraMap Aq T)).app _ ≪≫
      eqToIso (by rw [← IsScalarTower.algebraMap_eq]; rfl) ≪≫ asIso (DT.comparison.app P) ≪≫
      DerivedCategory.Q.mapIso (eqToIso (by rw [IsScalarTower.algebraMap_eq A A₀ T]) ≪≫
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp (algebraMap A A₀)
          (algebraMap A₀ T)) (ComplexShape.up ℤ)).app P)
  have hK : HasTorAmplitudeCanonical R'p
      ((ModuleCat.restrictScalars (algebraMap R'p T)).mapDerivedCategory.obj K) a b :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars (algebraMap R'p T)).mapDerivedCategoryFactors.app _).symm a b
      (AlgebraicGeometry.AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
        _ _ _ |>.mpr h₀)
  exact hasTorAmplitudeAt_of_derivedFibre_of_le d presentation hpresentation q₀ q hq P
    ⟨P, hP, ⟨Iso.refl _⟩⟩ a b (algebraMap Rp R'p) _ (restrictScalarsResidueFieldIso _ hh)
    (Stacks.Thickenings.hasTorAmplitudeCanonical_derivedExtensionScalars_restrictScalars
      (R' := Rp) (A' := Aq) (R := R'p) (A := T) K' K eK a b hK)

end PseudoCoherence

end
