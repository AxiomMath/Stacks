module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.RingTheory.Dualizing.InvertibleTransport
public import StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
public import StacksFrontier.RingTheory.Localization.AwayToAtPrime

/-!
# Openness of the Gorenstein locus

For a Noetherian ring admitting a dualizing complex, the primes at which the local ring is
Gorenstein form an open subset of the prime spectrum.

## Main results

* `Dualizing.isOpen_gorensteinLocus`: **[Stacks, Tag 0DW9 (1)(c)]**, the Gorenstein locus of a
  Noetherian ring with a dualizing complex is open.

## Implementation notes

Openness is checked pointwise. Near a Gorenstein prime the dualizing complex is a shifted copy of
the structure sheaf on a principal open `D(f)`
(`Dualizing.IsDualizingComplex.exists_isLocalized_iso_shift_single`), and that trivialization
transports to every prime of `D(f)`: the complex localized there is a shifted unit, hence
invertible, so the local criterion
`Dualizing.isGorensteinLocalRing_iff_isInvertible_localization` makes the local ring Gorenstein.
So `D(f)` is an open neighbourhood of the prime contained in the locus.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

/-- A functor on derived categories that agrees with `F` on complexes carries a module in degree
zero to its image under `F` in degree zero, once its value on the single complex is known. -/
private noncomputable def mapSingleIsoOfComparison
    {R : Type u} {S : Type*} [CommRing R] [CommRing S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} S) [F.Additive]
    (G : DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} S))
    (U : ModuleCat.{max u v} R)
    (e : G.obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj U)) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj U))) :
    G.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj U) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj (F.obj U) :=
  G.mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app U) ≪≫ e ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app U) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (F.obj U)).symm

/-- Extension of scalars along `f : R →+* B` carries the universe lift of `R`, placed in degree
zero, to the universe lift of `B`, placed in degree zero: it is monoidal, so it preserves units. -/
private noncomputable def derivedExtensionScalarsLiftedUnitIso
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} f).functor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
        ((ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R R))) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj
      ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)) := by
  let := f.toAlgebra
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} f
  let F := CochainComplex.DerivedTensor.extensionScalars.{u, u, v} f
  let UR := (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R R)
  let UB := (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)
  let P := (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj UR
  let : CochainComplex.IsStrictlyLE P 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P 0
  let e := asIso (D.comparison.app P)
  let eT : F.obj UR ≅ UB :=
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      ULift.moduleEquiv).trans
        ((TensorProduct.AlgebraTensorModule.rid R B B).trans ULift.moduleEquiv.symm)).toModuleIso
  exact mapSingleIsoOfComparison F D.functor UR e ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso eT

/-- Every shift of the ring in degree zero is invertible for the derived tensor product: it is
already a shifted unit on the trivial principal cover of the spectrum. -/
private theorem shiftedUnit_isInvertible {R : Type u} [CommRing R] (n : ℤ) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    MonoidalCategory.IsInvertible
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))⟦n⟧) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  apply (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit (U⟦n⟧)).1.mpr
  intro p hp
  let Rf := Localization.Away (1 : R)
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R Rf)
  let eUnit := D.functor.mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (ULift.moduleEquiv.symm.toModuleIso : ModuleCat.of R R ≅
        (ModuleCat.uliftFunctor.{u} R).obj (ModuleCat.of R R))) ≪≫
    derivedExtensionScalarsLiftedUnitIso.{u, u} (algebraMap R Rf) ≪≫
    ((DerivedCategory.singleFunctor _ 0).mapIso
      (ULift.moduleEquiv.toModuleIso :
        (ModuleCat.uliftFunctor.{u} Rf).obj (ModuleCat.of Rf Rf) ≅ ModuleCat.of Rf Rf))
  refine ⟨1, hp.one_notMem, -n, ?_⟩
  let : D.functor.CommShift ℤ := D.commShift
  exact ⟨(D.functor.commShiftIso n).app U ≪≫
    (shiftFunctor _ n).mapIso eUnit ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} Rf)).shiftIso n (-n) 0 (by omega)).app
      (ModuleCat.of Rf Rf)⟩

/-- The coefficient equivalence to the universe-lifted ring carries the universe lift of `R` in
degree zero to the lifted ring in degree zero. -/
private noncomputable def scalarLiftSingleUnitIso
    {R : Type u} [CommRing R] :
    let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)
    let G := F.mapDerivedCategory
    G.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj
      ((ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R R))) ≅
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} (ULift.{v} R)) 0).obj
      (ModuleCat.of (ULift.{v} R) (ULift.{v} R)) := by
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)
  let G := F.mapDerivedCategory
  let U := (ModuleCat.uliftFunctor.{v} R).obj (ModuleCat.of R R)
  exact mapSingleIsoOfComparison F G U (F.mapDerivedCategoryFactors.app _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (Iso.refl _)

/-- If a dualizing complex becomes a shifted copy of the structure sheaf on `D(f)`, then the local
ring at every prime of `D(f)` is Gorenstein: pushing the trivialization forward along
`A_f → A_q` makes the localized complex a shifted unit, hence invertible. -/
private theorem gorenstein_on_basicOpen_of_trivialization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : Dualizing.IsDualizingComplex K)
    (f : A) (n : ℤ)
    (hiso : Nonempty ((StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A (Localization.Away f))).obj K ≅
      ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} (Localization.Away f)) 0).obj
        ((ModuleCat.uliftFunctor.{v} (Localization.Away f)).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))))⟦-n⟧))
    (q : PrimeSpectrum A) (hq : f ∉ q.asIdeal) :
    Dualizing.IsGorensteinLocalRing (Localization.AtPrime q.asIdeal) := by
  let S := Localization.Away f
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing
    q.asIdeal.primeCompl B inferInstance
  let ψ : S →+* B := localizationAwayToAtPrime f q.asIdeal hq
  let : Algebra S B := ψ.toAlgebra
  let K' := (ModuleCat.uliftFunctor.{max u u, v} A).mapDerivedCategory.obj K
  let ecomp := (StacksDraft.Perfect.derivedExtensionScalarsComp.{u, v}
    (algebraMap A S) ψ).app K'
  have hcomp : ψ.comp (algebraMap A S) = algebraMap A B := by
    ext a
    change ψ (algebraMap A S a) = algebraMap A (Localization.AtPrime q.asIdeal) a
    simp [ψ, localizationAwayToAtPrime]
  rw [hcomp] at ecomp
  let DB := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
    (algebraMap A B)
  let DS := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} ψ
  obtain ⟨eS⟩ := hiso
  let UR := (ModuleCat.uliftFunctor.{v} S).obj (ModuleCat.of S S)
  let UB := (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)
  let eUnit := derivedExtensionScalarsLiftedUnitIso.{v, u} ψ
  let : (DS.functor).CommShift ℤ := DS.commShift
  let eShift := (DS.functor.commShiftIso (-n)).app
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} S) 0).obj UR)
  let eKB : DB.functor.obj K' ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj UB)⟦-n⟧ :=
    ecomp.symm ≪≫ DS.functor.mapIso eS ≪≫ eShift ≪≫
      (shiftFunctor _ (-n)).mapIso eUnit
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)
  let G := F.mapDerivedCategory
  let U := (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj UB
  let := Dualizing.derivedCategoryMonoidal.{u, v} B
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} B)).choose
  have hShiftU : MonoidalCategory.IsInvertible (U⟦-n⟧) := by
    apply (isInvertible_iff_scalarLift.{u, v} B (U⟦-n⟧)).mpr
    let : G.CommShift ℤ := inferInstance
    exact isInvertible_of_iso_symm
      ((G.commShiftIso (-n)).app U ≪≫
        (shiftFunctor _ (-n)).mapIso (scalarLiftSingleUnitIso.{v, u} (R := B)))
      (shiftedUnit_isInvertible.{max u v} (-n))
  exact (isGorensteinLocalRing_iff_isInvertible_localization.{u, v} K hK q.asIdeal).mpr
    (isInvertible_of_iso_symm eKB hShiftU)

/-- **Stacks Project, Tag 0DW9 (1)(c).** If a Noetherian ring admits a dualizing complex, then the
set of primes whose local ring is Gorenstein is open in the prime spectrum. -/
@[stacks 0DW9 "(1)(c)"]
theorem isOpen_gorensteinLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : Dualizing.IsDualizingComplex K) :
    IsOpen {p : PrimeSpectrum A |
      Dualizing.IsGorensteinLocalRing (Localization.AtPrime p.asIdeal)} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨f, hf, n, hiso⟩ :=
    IsDualizingComplex.exists_isLocalized_iso_shift_single K hK
      p.asIdeal (hp := hp)
  exact Filter.mem_of_superset
    ((PrimeSpectrum.basicOpen f).isOpen.mem_nhds ((PrimeSpectrum.mem_basicOpen f p).2 hf))
    fun q hq => gorenstein_on_basicOpen_of_trivialization K hK f n hiso q
      ((PrimeSpectrum.mem_basicOpen f q).mp hq)

end Dualizing
