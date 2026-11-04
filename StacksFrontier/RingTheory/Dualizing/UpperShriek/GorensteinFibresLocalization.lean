module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres
public import StacksFrontier.RingTheory.Dualizing.ConcentratedDualizingModule
public import StacksFrontier.RingTheory.RelativeDimension.Basic
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.GorensteinFibres

/-!
# Gorenstein fibres through localizations

For a flat homomorphism of finite type `R → A` of Noetherian rings, the relative dualizing complex
`ω^•_{A/R} = φ^!(R)` is studied after localization at a prime `q` of `A`.

## Main results

* `isGorensteinLocalRing_fiber_of_isInvertible_localization`: if the localization of `ω^•_{A/R}`
  at `q` is invertible, then the local ring of the fibre at the corresponding prime is Gorenstein.
* `exists_nontrivial_localizedModule_homology_upperShriekFunctor_unit`: some cohomology module of
  `ω^•_{A/R}` has nonzero localization at `q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- Base changing `K` to the local ring of the fibre at `Q` through the localization `B` of `A`
at `q` or through the fibre agree. -/
private theorem exists_ringHom_derivedFibreIso_localization
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime] (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization.AtPrime B q] (P : Ideal R) [P.IsPrime] (Q : Ideal (P.Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom = q)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    ∃ φ : B →+* Localization.AtPrime Q, Nonempty
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap (P.Fiber A) (Localization.AtPrime Q))).functor.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom).functor.obj K) ≅
        (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj K)) := by
  let ι : A →+* P.Fiber A := (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom
  have hunit : ∀ y : q.primeCompl, IsUnit ((algebraMap (P.Fiber A) (Localization.AtPrime Q)).comp
      ι y) := by
    intro ⟨y, hy⟩
    refine IsLocalization.map_units (M := Q.primeCompl) (Localization.AtPrime Q) ⟨ι y, ?_⟩
    change ι y ∉ Q
    intro hmem
    exact hy (hQ ▸ hmem)
  refine ⟨IsLocalization.lift (M := q.primeCompl) hunit, ⟨?_⟩⟩
  exact (derivedFibreIso ι (algebraMap _ _) _ rfl (Iso.refl _)).symm ≪≫
    derivedFibreIso (algebraMap A B) _ _ (IsLocalization.lift_comp hunit) (Iso.refl _)

/-- **Gorensteinness of a fibre at a point from invertibility of `ω^•_{A/R}` there.** Let
`φ : R → A` be a flat homomorphism of finite type of Noetherian rings, let `q` be a prime of `A`
over `P ⊆ R` and let `Q` be the corresponding prime of the fibre `A ⊗_R κ(P)`. If the
localization of `ω^•_{A/R} = φ^!(R)` at `q`, taken in any localization `B` of `A` at `q`, is an
invertible object of `D(B)`, then the local ring of the fibre at `Q` is Gorenstein.

The localization of `ω^•_{A/R}` at `q`, base changed to the local ring `L` of the fibre at `Q`, is
the localization at `Q` of the relative dualizing complex of the fibre, which is a dualizing
complex [Stacks, Tag 0BZW] (2)(b); invertibility passes along base change, and the local criterion
[Stacks, Tag 0DW9] (1)(b) applies. -/
theorem isGorensteinLocalRing_fiber_of_isInvertible_localization
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (q : Ideal A) [q.IsPrime] (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization.AtPrime B q] (P : Ideal R) [P.IsPrime] (Q : Ideal (P.Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] P.Fiber A).toRingHom = q)
    (hInv : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        B).choose
      MonoidalCategory.IsInvertible
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A B)).functor.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) :
    letI : IsNoetherianRing (P.Fiber A) := isNoetherianRing_baseChange P.ResidueField p
    IsGorensteinLocalRing (Localization.AtPrime Q) := by
  let : IsNoetherianRing (P.Fiber A) := isNoetherianRing_baseChange P.ResidueField p
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let F := P.Fiber A
  let L := Localization.AtPrime Q
  let ι : A →+* F := (Algebra.TensorProduct.includeRight : A →ₐ[R] F).toRingHom
  let K := relativeDualizing p
  let D := (totalDerivedExtensionScalars.{u, u, u} ι).functor.obj K
  have hD : IsDualizingComplex D :=
    isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field P.ResidueField
      p hflat
  obtain ⟨φ, ⟨e⟩⟩ := exists_ringHom_derivedFibreIso_localization q B P Q hQ K
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    B).choose
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory L).choose
  have hInvL : MonoidalCategory.IsInvertible
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap F L)).functor.obj D) :=
    isInvertible_of_iso e.symm
      (DerivedCategory.Invertible.isInvertible_derivedExtensionScalars φ _ hInv)
  let Dloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap F L)).obj D
  have hDloc : MonoidalCategory.IsInvertible Dloc :=
    isInvertible_of_iso
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap F L)).functor.mapIso
        ((uliftDerivedSelfIso F).app D).symm) hInvL
  have hLift :
      let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        (ULift.{u} L)).choose
      MonoidalCategory.IsInvertible
        ((StacksDraft.TorAmplitude.scalarLift.{u, u} (R := L)).mapDerivedCategory.obj Dloc) := by
    let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (ULift.{u} L)).choose
    exact isInvertible_of_iso ((scalarLiftDerivedIso.{u, u} L).app Dloc)
      (DerivedCategory.Invertible.isInvertible_derivedExtensionScalars
        (ULift.ringEquiv.symm : L ≃+* ULift.{u} L).toRingHom Dloc hDloc)
  exact (isGorensteinLocalRing_iff_isInvertible_localization D hD Q).2
    ((isInvertible_iff_scalarLift.{u, u} L Dloc).mpr hLift)


/-- **`ω^•_{A/R}` does not vanish at any prime.** Let `φ : R → A` be a flat homomorphism of finite
type of Noetherian rings and `q` a prime of `A`. Then some cohomology module of
`ω^•_{A/R} = φ^!(R)` has nonzero localization at `q`: otherwise the derived base change of
`ω^•_{A/R}` to the local ring at `q` of its fibre would vanish, while it is a dualizing complex of
that local ring ([Stacks, Tag 0BZW] (2)(b)), which is never zero. -/
theorem exists_nontrivial_localizedModule_homology_upperShriekFunctor_unit
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (q : Ideal A) [q.IsPrime] :
    ∃ i : ℤ, Nontrivial (LocalizedModule q.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  by_contra hcon
  have hsub : ∀ i : ℤ, Subsingleton (LocalizedModule q.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (relativeDualizing p))) :=
    fun i => not_nontrivial_iff_subsingleton.mp fun h => hcon ⟨i, h⟩
  let P : Ideal R := q.comap (algebraMap R A)
  obtain ⟨Q, hQprime, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q P rfl
  let : IsNoetherianRing (P.Fiber A) := isNoetherianRing_baseChange P.ResidueField p
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let F := P.Fiber A
  let L := Localization.AtPrime Q
  let B := Localization.AtPrime q
  let ι : A →+* F := (Algebra.TensorProduct.includeRight : A →ₐ[R] F).toRingHom
  let K := relativeDualizing p
  let D := (totalDerivedExtensionScalars.{u, u, u} ι).functor.obj K
  have hD : IsDualizingComplex D :=
    isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field P.ResidueField
      p hflat
  let KB := (totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj K
  have hKB : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj KB) := by
    intro i
    have e := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, u}
      (R := A) (A := B) q.primeCompl i).app K
    have hz : IsZero ((ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj KB)) := by
      refine IsZero.of_iso ?_ e
      rw [ModuleCat.isZero_iff_subsingleton]
      exact hsub i
    rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
    exact hz
  have : KB.IsGE 0 := (DerivedCategory.isGE_iff KB 0).2 fun i _ => hKB i
  have : KB.IsLE 0 := (DerivedCategory.isLE_iff KB 0).2 fun i _ => hKB i
  obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE KB 0
  have hM : IsZero M := (hKB 0).of_iso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).app M).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).mapIso eM.symm)
  have hKB0 : IsZero KB :=
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map_isZero hM).of_iso eM
  obtain ⟨φ, ⟨e⟩⟩ := exists_ringHom_derivedFibreIso_localization q B P Q hQ K
  have hzL :
      IsZero ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap F L)).obj D) :=
    (((totalDerivedExtensionScalars.{u, u, u} φ).functor.map_isZero hKB0).of_iso e).of_iso
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap F L)).functor.mapIso
        ((uliftDerivedSelfIso F).app D).symm).symm
  let : IsNoetherianRing L := IsLocalization.isNoetherianRing Q.primeCompl L inferInstance
  have hDL := isDualizingComplex_localization (B := L) Q.primeCompl D hD
  obtain ⟨i, hi⟩ := exists_not_isZero_homology _ hDL
  exact hi (Functor.map_isZero _ hzL)

end Dualizing


end
