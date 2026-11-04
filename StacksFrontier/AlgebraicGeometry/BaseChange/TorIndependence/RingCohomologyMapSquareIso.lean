module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapSecondSquare

/-!
# The base-change map of Stacks 0DJ7 along an isomorphism of commutative squares

For a morphism of commutative squares of rings `(R, A, R', A') → (R₁, A₁, R₁', A₁')` whose four
components are bijective, the base-change map of Stacks 0DJ7 of the first square at `K`, `K'`,
`φ` is invertible exactly when the one of the second square at `K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` and
the induced morphism is.  This is Stacks 0DJ8 for the one-member family of the second square.

## Main results

* `RingTheory.TorIndependence.bijective_baseChangeTensorRingMap_of_bijective`
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_of_bijective`
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-- For a commutative square `R → A`, `R → R'`, `A → A'`, `R' → A'` with `R → A` surjective and
`R' → A'` bijective, the map `A ⊗_R R' → A'` is bijective. -/
theorem bijective_baseChangeTensorRingMap_of_bijective {R A R' A' : Type u} [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R A']
    [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
    (hA : Function.Surjective (algebraMap R A)) (hA' : Function.Bijective (algebraMap R' A')) :
    Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
  have hcomp : ∀ r : R', baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
      ((1 : A) ⊗ₜ[R] r) = algebraMap R' A' r := by
    intro r
    rw [baseChangeTensorRingMap_tmul, map_one, one_mul]
  have hsurj : ∀ z : A ⊗[R] R', ∃ r : R', (1 : A) ⊗ₜ[R] r = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a r =>
      obtain ⟨s, rfl⟩ := hA a
      refine ⟨s • r, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, rfl⟩ := hx
      obtain ⟨s, rfl⟩ := hy
      exact ⟨r + s, TensorProduct.tmul_add _ _ _⟩
  refine ⟨fun z w h => ?_, fun a => ?_⟩
  · obtain ⟨r, rfl⟩ := hsurj z
    obtain ⟨s, rfl⟩ := hsurj w
    rw [hcomp, hcomp] at h
    rw [hA'.1 h]
  · obtain ⟨r, rfl⟩ := hA'.2 a
    exact ⟨(1 : A) ⊗ₜ[R] r, hcomp r⟩

section SquareIso

variable {R A R' A' R₁ A₁ R₁' A₁' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing R₁] [CommRing A₁] [CommRing R₁'] [CommRing A₁']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁] [Algebra R₁ R₁'] [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R₁'] [Algebra A' A₁']
  [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [Algebra R R₁'] [IsScalarTower R R' R₁'] [IsScalarTower R R₁ R₁']
  [Algebra A A₁'] [IsScalarTower A A' A₁'] [IsScalarTower A A₁ A₁']
  [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']

/-- **The base-change map of Stacks 0DJ7 is invariant under an isomorphism of squares.** If the
four ring maps `R → R₁`, `A → A₁`, `R' → R₁'` and `A' → A₁'` are bijective, the base-change map
of the first square at `K`, `K'`, `φ` is invertible exactly when the one of the second square at
`K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` and the induced morphism is. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_of_bijective
    (hR : Function.Bijective (algebraMap R R₁)) (hA : Function.Bijective (algebraMap A A₁))
    (hR' : Function.Bijective (algebraMap R' R₁'))
    (hA' : Function.Bijective (algebraMap A' A₁'))
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
        ((dext (algebraMap A A₁)).obj K) ((dext (algebraMap A' A₁')).obj K')
        (extendScalarsBaseChangeHom K K' φ) n) := by
  have flat : ∀ {S T : Type u} [CommRing S] [CommRing T] [Algebra S T],
      Function.Bijective (algebraMap S T) → Module.Flat S T := fun h =>
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap _ _) h).symm
  have : Module.Flat R R₁ := flat hR
  have : Module.Flat A A₁ := flat hA
  have : Module.Flat A' A₁' := flat hA'
  have hR₁' : let := (baseChangeTensorRingMap (R := R) (A := R₁) (R' := R')
      (A' := R₁')).toAlgebra; Module.Flat (R₁ ⊗[R] R') R₁' :=
    RingHom.Flat.of_bijective (bijective_baseChangeTensorRingMap_of_bijective hR.2 hR')
  refine (isIso_ringBaseChangeCohomologyMap_iff_forall_secondSquare (ι := Unit)
    (R₁ := fun _ => R₁) (A₁ := fun _ => A₁) (R₁' := fun _ => R₁') (A₁' := fun _ => A₁')
    (fun _ => hR₁') (fun q => ⟨(), ?_⟩) K K' φ n).trans ⟨fun h => h (), fun h _ => h⟩
  exact (PrimeSpectrum.isHomeomorph_comap_of_bijective hA').surjective q

end SquareIso

end RingTheory.TorIndependence

end
