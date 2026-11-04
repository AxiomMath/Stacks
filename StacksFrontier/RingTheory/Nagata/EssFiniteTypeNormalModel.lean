module

public import StacksFrontier.RingTheory.Blowup.FractionFieldAffineBlowup
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.RingTheory.Nagata.Universes
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# A normal local extension essentially of finite type is a local ring of an affine blowup

Let `A` be a Nagata domain with fraction field `K` and let `A ⟶ B` be a local extension, with `B`
a normal local domain with the same fraction field `K`, essentially of finite type over `A`. Then
`B` is the localization at a prime of an integrally closed affine blowup algebra `A[J/t]`. This
is the algebra of Steps 1 and 2 of the proof of [Stacks, Tag 0BG0]: `B = C_𝔮` for a finite type
`A`-algebra `C ⊆ B`; replacing `C` by its integral closure, which is finite because `C` is
Nagata and contained in `B` because `B` is normal, makes the chart normal; and a finitely
generated `A`-subalgebra of `K` is an affine blowup algebra.

## Main results

* `Stacks.Blowup.nonempty_ringEquiv_localization_of_surjective`: a local ring which is a
  localization, in the elementary sense, of a subring is its localization at the prime cut out
  by the maximal ideal.
* `Stacks.Blowup.exists_affineBlowup_localization_of_essFiniteType`: the main statement.

## References

* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 0BIS](https://stacks.math.columbia.edu/tag/0BIS)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Blowup

/-- **A local ring which is a localization of a subring at its maximal ideal.** If
`φ : R ⟶ B` is injective, `B` is local, and every element of `B` is `φ c / φ t` with `φ t` a
unit, then `B` is the localization of `R` at the prime `φ⁻¹(𝔪_B)`. -/
theorem nonempty_ringEquiv_localization_of_surjective {R B : Type*} [CommRing R] [CommRing B]
    [IsLocalRing B] (φ : R →+* B) (hφ : Function.Injective φ)
    (hsurj : ∀ b : B, ∃ c t : R, IsUnit (φ t) ∧ b * φ t = φ c) :
    Nonempty (B ≃+* Localization.AtPrime ((maximalIdeal B).comap φ)) := by
  let := φ.toAlgebra
  have : IsLocalization.AtPrime B ((maximalIdeal B).comap φ) := by
    rw [IsLocalization.AtPrime, isLocalization_iff]
    refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by rw [hφ h]⟩⟩
    · exact notMem_maximalIdeal.mp y.2
    · obtain ⟨c, t, ht, hct⟩ := hsurj z
      exact ⟨⟨c, ⟨t, notMem_maximalIdeal.mpr ht⟩⟩, hct⟩
  exact ⟨(IsLocalization.algEquiv ((maximalIdeal B).comap φ).primeCompl
    (Localization.AtPrime ((maximalIdeal B).comap φ)) B).symm.toRingEquiv⟩

/-- **An intermediate domain of a fraction field has the same fraction field.** If
`A ⟶ R ⟶ K` with `K` the fraction field of `A` and `R ⟶ K` injective, then `K` is the fraction
field of `R`. -/
theorem isFractionRing_of_isScalarTower (A R K : Type*) [CommRing A] [IsDomain A] [CommRing R]
    [IsDomain R] [Field K] [Algebra A R] [Algebra A K] [Algebra R K] [IsScalarTower A R K]
    [IsFractionRing A K]
    (hinj : Function.Injective (algebraMap R K)) : IsFractionRing R K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  · have hy : (y : R) ≠ 0 := nonZeroDivisors.ne_zero y.2
    exact Ne.isUnit ((map_ne_zero_iff _ hinj).mpr hy)
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
    have hb0 : algebraMap A K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hb)
    have hbR : algebraMap A R b ≠ 0 := fun h =>
      hb0 (by rw [IsScalarTower.algebraMap_apply A R K, h, map_zero])
    refine ⟨⟨algebraMap A R a, ⟨algebraMap A R b, mem_nonZeroDivisors_of_ne_zero hbR⟩⟩, ?_⟩
    change algebraMap A K a / algebraMap A K b * algebraMap R K (algebraMap A R b) =
      algebraMap R K (algebraMap A R a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_cancel₀ _ hb0]

/-- **[Stacks, Tag 0BG0], Steps 1 and 2, algebra.** A normal local domain `B` with fraction field
`K`, essentially of finite type over a Nagata domain `A` with the same fraction field, is the
localization at a prime of an integrally closed affine blowup algebra `A[J/t]`, `t ∈ J`,
`t ≠ 0`. -/
theorem exists_affineBlowup_localization_of_essFiniteType (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsLocalRing B] [IsDomain B] [Algebra A B] (K : Type u) [Field K] [Algebra A K]
    [Algebra B K] [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K]
    [IsIntegrallyClosed B] (hN : IsNagataRing A) (hft : Algebra.EssFiniteType A B) :
    ∃ (J : Ideal A) (t : A) (_ : t ∈ J), t ≠ 0 ∧ IsIntegrallyClosed (affineBlowup J t) ∧
      ∃ (P : Ideal (affineBlowup J t)) (_ : P.IsPrime),
        Nonempty (B ≃+* Localization.AtPrime P) := by
  classical
  let β : B →ₐ[A] K := IsScalarTower.toAlgHom A B K
  have hβ : Function.Injective β := IsFractionRing.injective B K
  let Cb : Subalgebra A B := Algebra.EssFiniteType.subalgebra A B
  have hCbinj : Function.Injective (algebraMap Cb K) := by
    rw [IsScalarTower.algebraMap_eq Cb B K]
    exact hβ.comp Subtype.val_injective
  have : IsFractionRing Cb K := isFractionRing_of_isScalarTower A Cb K hCbinj
  have hCbN : IsNagataRing Cb := IsNagataRing.of_finiteType hN
  have hfin : Module.Finite Cb (integralClosure Cb K) :=
    module_finite_integralClosure_of_isNagataRing K K hCbN
  let I : Subalgebra Cb K := integralClosure Cb K
  let D : Subalgebra A K := I.restrictScalars A
  have hDfg : D.FG := by
    have : Algebra.FiniteType A I := .trans (S := Cb) inferInstance (Module.Finite.finiteType I)
    exact (Subalgebra.fg_iff_finiteType D).mpr (inferInstanceAs (Algebra.FiniteType A I))
  have hIint : IsIntegrallyClosed I :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := Cb) K (L := K)
  let eDI : D ≃+* I :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hDint : IsIntegrallyClosed D := IsIntegrallyClosed.of_equiv eDI.symm
  have hDle : D ≤ β.range := fun x hx => (IsIntegrallyClosed.isIntegral_iff (R := B) (K := K)).mp
    (IsIntegral.tower_top (R := Cb) (A := B) (show IsIntegral Cb x from hx))
  have hCbD : ∀ c : Cb, β c ∈ D := fun c => by
    have h : IsIntegral Cb (algebraMap Cb K c) := isIntegral_algebraMap
    rwa [IsScalarTower.algebraMap_apply Cb B K] at h
  let eB : B ≃ₐ[A] β.range := AlgEquiv.ofInjective β hβ
  let φ : D →ₐ[A] B := eB.symm.toAlgHom.comp (Subalgebra.inclusion hDle)
  have hφinj : Function.Injective φ := fun _ _ h =>
    Subalgebra.inclusion_injective hDle (eB.symm.injective h)
  have hφβ : ∀ c : Cb, φ ⟨β c, hCbD c⟩ = c := fun c => hβ <| by
    change β (eB.symm ⟨β c, _⟩) = β c
    exact congrArg Subtype.val (eB.apply_symm_apply ⟨β c, _⟩)
  obtain ⟨J, t, ht, ht0, ⟨e⟩⟩ := exists_algEquiv_affineBlowup_of_fg D hDfg
  refine ⟨J, t, ht, ht0, IsIntegrallyClosed.of_equiv e.toRingEquiv, ?_⟩
  let ψ : affineBlowup J t →+* B := φ.toRingHom.comp e.symm.toRingEquiv.toRingHom
  have hψinj : Function.Injective ψ := hφinj.comp e.symm.injective
  have hψe : ∀ (c : B) (hc : c ∈ Cb), ψ (e ⟨β c, hCbD ⟨c, hc⟩⟩) = c := fun c hc => by
    change φ (e.symm (e _)) = c
    rw [AlgEquiv.symm_apply_apply]
    exact hφβ ⟨c, hc⟩
  have hsurj : ∀ b : B, ∃ c s : affineBlowup J t, IsUnit (ψ s) ∧ b * ψ s = ψ c := by
    intro b
    obtain ⟨s, hs, hsu, hbs⟩ := (Algebra.essFiniteType_cond_iff A B
      (Algebra.EssFiniteType.finset A B)).mp (Algebra.EssFiniteType.isLocalization A B) b
    exact ⟨e ⟨β (b * s), hCbD ⟨b * s, hbs⟩⟩, e ⟨β s, hCbD ⟨s, hs⟩⟩, by rwa [hψe s hs],
      by rw [hψe s hs, hψe (b * s) hbs]⟩
  exact ⟨_, inferInstance, nonempty_ringEquiv_localization_of_surjective ψ hψinj hsurj⟩

end Stacks.Blowup

end
