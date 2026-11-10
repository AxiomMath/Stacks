module

public import Mathlib.Algebra.Module.FinitePresentation
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible

/-!
# Local trivialization of a dualizing complex

A dualizing complex on a Noetherian ring is, near a prime whose local ring is Gorenstein, a
shifted copy of the structure sheaf: there is an element `f` outside the prime and an integer `n`
such that the derived localization of the complex away from `f` is the free module of rank one
placed in degree `-n`.

## Main results

* `Dualizing.IsDualizingComplex.exists_isLocalized_iso_shift_single`: the local trivialization.

## Implementation notes

The argument first works over the local ring. There the local criterion
`Dualizing.isGorensteinLocalRing_iff_isInvertible_localization` makes the localized complex
invertible, hence locally a shifted unit; since the ring is local the covering element is a unit,
so the shift already holds over the local ring itself. That pins the cohomology of the localized
complex to a single degree `n`, where it is free of rank one. Both pieces of data are then spread
out: the cohomology modules are finite, so the degree-`n` trivialization lifts to an `A`-linear map
that becomes bijective away from one element, and each of the finitely many other cohomology
modules, which vanish at the prime, vanishes away from another. The product of those elements is
the `f` of the statement.

The restriction to the principal open `D(f)` is the canonical derived extension of scalars to
`Localization.Away f`, whose input module universe is independent of the ring universe.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- An object of finite injective dimension has cohomology in a bounded range of degrees: it is
represented by a complex of injectives that is zero outside finitely many degrees. -/
private theorem bounded_cohomology_of_finiteInjectiveDimension
    {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨a, b, I, _, _, _, ⟨e⟩⟩ := hK
  exact ⟨a, b, DerivedCategory.TStructure.t.isGE_of_iso e.symm a,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- At a prime whose local ring is Gorenstein, the derived localization of a dualizing complex is
invertible for the derived tensor product. -/
private theorem localized_dualizing_isInvertible
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : Ideal A) [p.IsPrime]
    (hp : Dualizing.IsGorensteinLocalRing (Localization.AtPrime p)) :
    let B := Localization.AtPrime p
    letI := Dualizing.derivedCategoryMonoidal.{u, v} B
    MonoidalCategory.IsInvertible
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A B)).obj K) := by
  let B := Localization.AtPrime p
  let := Dualizing.derivedCategoryMonoidal.{u, v} B
  exact (Dualizing.isGorensteinLocalRing_iff_isInvertible_localization
    K hK p).mp hp

/-- Transported to the universe-lifted local ring, the derived localization of a dualizing complex
at a Gorenstein prime is locally a shifted copy of the ring. -/
private theorem localized_scalarLift_isLocallyShiftedUnit
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : Ideal A) [p.IsPrime]
    (hp : Dualizing.IsGorensteinLocalRing (Localization.AtPrime p)) :
    let B := Localization.AtPrime p
    let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A B)).obj K
    let K' := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)).mapDerivedCategory.obj Kloc
    DerivedCategory.Invertible.IsLocallyShiftedUnit K' := by
  let B := Localization.AtPrime p
  let := Dualizing.derivedCategoryMonoidal.{u, v} B
  let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A B)).obj K
  let K' := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)).mapDerivedCategory.obj Kloc
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} B)).choose
  exact (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit K').1.mp <|
    (Dualizing.isInvertible_iff_scalarLift.{u, v} B Kloc).mp
      (localized_dualizing_isInvertible K hK p hp)

/-- The neighbourhood on which the localized dualizing complex is a shifted copy of the ring may be
taken principal at a unit, because the local ring has a unique maximal ideal. -/
private theorem exists_unit_local_shift
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : Ideal A) [p.IsPrime]
    (hp : Dualizing.IsGorensteinLocalRing (Localization.AtPrime p)) :
    let B := Localization.AtPrime p
    let C := ULift.{v} B
    let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A B)).obj K
    let K' := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)).mapDerivedCategory.obj Kloc
    ∃ g : C, IsUnit g ∧ ∃ n : ℤ,
      Nonempty (((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap C (Localization.Away g))).functor.obj K') ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} (Localization.Away g)) n).obj
          (ModuleCat.of (Localization.Away g) (Localization.Away g)))) := by
  let B := Localization.AtPrime p
  let C := ULift.{v} B
  let e : B ≃+* C := ULift.ringEquiv.symm
  let : IsLocalRing C := e.isLocalRing
  obtain ⟨g, hg, n, hshift⟩ := localized_scalarLift_isLocallyShiftedUnit K hK p hp
    (IsLocalRing.maximalIdeal C) (IsLocalRing.maximalIdeal.isMaximal C).isPrime
  exact ⟨g, IsLocalRing.notMem_maximalIdeal.mp hg, n, hshift⟩

/-- Localizing away from a unit changes nothing: derived extension of scalars to `R_g` agrees with
restriction of scalars along the induced isomorphism `R_g ≃+* R`. -/
private noncomputable def derivedAwayUnitIso
    {R : Type u} [CommRing R] (g : R) (hg : IsUnit g) :
    let S := Localization.Away g
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R S)).functor ≅
      (ModuleCat.restrictScalars
        (IsLocalization.atUnit R S g hg).symm.toRingHom).mapDerivedCategory := by
  let S := Localization.Away g
  let e := IsLocalization.atUnit R S g hg
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv
  let G := ModuleCat.restrictScalars e.symm.toRingHom
  let a := ModuleCat.extendRestrictScalarsAdj (algebraMap R S)
  let i : F ≅ G := a.leftAdjointUniq E.symm.toAdjunction
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj
    (algebraMap R S)).left_adjoint_additive
  letI : F.IsEquivalence := Functor.isEquivalence_of_iso i.symm
  letI : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.holdsForLocalizationAway S g)
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R S)
  haveI : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{u} R) (ComplexShape.up ℤ)) (by
        intro X Y f hf
        have : QuasiIso f := hf
        change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f))
        infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ G.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex i (ComplexShape.up ℤ)) _ ≪≫
      G.mapDerivedCategoryFactors.symm)

/-- Along the isomorphism `R ≃+* R_g` induced by a unit `g`, the localized ring placed in degree `n`
restricts to the ring itself placed in degree `n`. -/
private noncomputable def restrictScalarsSingleIso
    {R : Type u} [CommRing R] (g : R) (hg : IsUnit g) (n : ℤ) :
    let S := Localization.Away g
    (ModuleCat.restrictScalars
      (IsLocalization.atUnit R S g hg).toRingEquiv.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R) := by
  let S := Localization.Away g
  let e := IsLocalization.atUnit R S g hg
  let F := ModuleCat.restrictScalars e.toRingEquiv.toRingHom
  letI : F.Additive := inferInstance
  letI : PreservesFiniteLimits F := inferInstance
  letI : PreservesColimitsOfSize.{0, 0} F := inferInstance
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let U := ModuleCat.of S S
  let eFU : F.obj U ≅ ModuleCat.of R R :=
    ModuleCat.restrictScalarsIsoOfEquiv e.toRingEquiv
  let P : CochainComplex (ModuleCat.{u} S) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) n).obj U
  exact F.mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) n).app U) ≪≫
    F.mapDerivedCategoryFactors.app P ≪≫
    (DerivedCategory.Q (C := ModuleCat.{u} R)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app U) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) n).app (F.obj U)).symm ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).mapIso eFU

/-- An object that becomes a shifted copy of the ring after localizing away from a unit is already a
shifted copy of the ring. -/
private theorem unit_local_shift_iso
    {R : Type u} [CommRing R] (g : R) (hg : IsUnit g) (n : ℤ)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hshift : Nonempty
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap R (Localization.Away g))).functor.obj K ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away g)) n).obj
          (ModuleCat.of (Localization.Away g) (Localization.Away g)))) :
    Nonempty (K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)) := by
  let S := Localization.Away g
  let e := IsLocalization.atUnit R S g hg
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv
  let G := ModuleCat.restrictScalars e.symm.toRingHom
  let H := ModuleCat.restrictScalars e.toRingHom
  let Gd := G.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  have hGK : Gd.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S S) :=
    ((derivedAwayUnitIso g hg).app K).symm ≪≫ hshift.some
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let : Q.EssSurj := Localization.essSurj Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  obtain ⟨I, ⟨eI⟩⟩ := Functor.EssSurj.mem_essImage Q K
  let I' : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.up ℤ) := I
  let ηI :=
    (NatIso.mapHomologicalComplex.{0, u, u + 1, u, u + 1}
      E.symm.unitIso (ComplexShape.up ℤ)).app I'
  have hK : K ≅ Hd.obj (Gd.obj K) := by
    let eQ : Q.obj I ≅
        Q.obj ((E.symm.functor ⋙ E.functor).mapHomologicalComplex
          (ComplexShape.up ℤ) |>.obj I') := Q.mapIso ηI
    exact eI.symm ≪≫ eQ ≪≫
      H.mapDerivedCategoryFactors.symm.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
      Hd.mapIso (G.mapDerivedCategoryFactors.symm.app I) ≪≫
      Hd.mapIso (Gd.mapIso eI)
  exact ⟨hK ≪≫ Hd.mapIso hGK ≪≫ restrictScalarsSingleIso g hg n⟩

/-- At a Gorenstein prime, a dualizing complex localizes to an object whose cohomology is
concentrated in a single degree `n`, where it is free of rank one. -/
private theorem localized_dualizing_local_data
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : Ideal A) [p.IsPrime]
    (hp : Dualizing.IsGorensteinLocalRing (Localization.AtPrime p)) :
    let B := Localization.AtPrime p
    let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A B)).obj K
    ∃ n : ℤ,
      Kloc.IsGE n ∧ Kloc.IsLE n ∧
        Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj Kloc) ≅
          ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))) := by
  let B := Localization.AtPrime p
  let C := ULift.{v} B
  let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A B)).obj K
  obtain ⟨g, hg, n, hshift⟩ := exists_unit_local_shift K hK p hp
  let hIso := unit_local_shift_iso g hg n
    ((StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)).mapDerivedCategory.obj Kloc)
    hshift
  let K' := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)).mapDerivedCategory.obj Kloc
  have hGE' : K'.IsGE n := DerivedCategory.TStructure.t.isGE_of_iso hIso.some.symm n
  have hLE' : K'.IsLE n := DerivedCategory.TStructure.t.isLE_of_iso hIso.some.symm n
  have hGE : Kloc.IsGE n := (DerivedCategory.isGE_iff Kloc n).2 fun i hi ↦
    StacksDraft.TorAmplitude.scalarLift_reflects_isZero_homology Kloc i
      (DerivedCategory.isZero_of_isGE K' n i hi)
  have hLE : Kloc.IsLE n := (DerivedCategory.isLE_iff Kloc n).2 fun i hi ↦
    StacksDraft.TorAmplitude.scalarLift_reflects_isZero_homology Kloc i
      (DerivedCategory.isZero_of_isLE K' n i hi)
  let F := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := B)
  let eH := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n).app Kloc
  let eHsingle := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} C) n).mapIso hIso.some ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} C) n).app
      (ModuleCat.of C C)
  let eRing : C ≃+* B := ULift.ringEquiv
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv eRing
  let U := (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B)
  have eUnit : F.obj U ≅ ModuleCat.of C C := Iso.refl _
  have eModule :
      F.obj ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj Kloc) ≅
        F.obj U :=
    eH.symm ≪≫ eHsingle ≪≫ eUnit.symm
  have eHlocal :
      Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj Kloc) ≅
        U) :=
    ⟨E.unitIso.app _ ≪≫ E.inverse.mapIso eModule ≪≫ (E.unitIso.app U).symm⟩
  exact ⟨n, hGE, hLE, eHlocal⟩

/-- Cohomology commutes with derived localization at a prime: the localization of `H^n` is the
`n`-th cohomology of the derived localization. -/
private noncomputable def localizedHomologyAtPrimeIsoGeneric
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) :
    ModuleCat.of A (LocalizedModule p.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K)) ≅
      (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p))).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} (Localization.AtPrime p)) n).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap A (Localization.AtPrime p))).obj K)) := by
  let B := Localization.AtPrime p
  let U := ModuleCat.uliftFunctor.{u, v} A
  let Kbig := U.mapDerivedCategory.obj K
  let eHom := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U n).app K
  let eLoc := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
    (R := A) (A := B) p.primeCompl n).app Kbig
  let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u}
    p.primeCompl).mapIso eHom
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K
  let eULift := localizedModuleUliftIso (R := A) p.primeCompl (M := H)
  have e : (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A B)).obj K)) ≅
        ModuleCat.of A (LocalizedModule p.primeCompl H) := by
    change (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
            (algebraMap A B)).functor.obj Kbig)) ≅ _
    exact eLoc ≪≫ eLift ≪≫ eULift
  exact e.symm


/-- Cohomology commutes with derived localization: the localization of `H^n` at a submonoid `S` is
the `n`-th cohomology of the derived extension of scalars to a localization `B` of `A` at `S`. -/
private noncomputable def localizedHomologyIso
    {A : Type u} [CommRing A] (S : Submonoid A) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization S B] (K : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) :
    ModuleCat.of A (LocalizedModule S
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K)) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K)) := by
  let U := ModuleCat.uliftFunctor.{u, v} A
  let Kbig := U.mapDerivedCategory.obj K
  let eHom := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U n).app K
  let eLoc := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
    (R := A) (A := B) S n).app Kbig
  let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max v u} S).mapIso eHom
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K
  let eULift := localizedModuleUliftIso (R := A) S (M := H)
  have e : (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A B)).obj K)) ≅
        ModuleCat.of A (LocalizedModule S H) := by
    change (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
            (algebraMap A B)).functor.obj Kbig)) ≅ _
    exact eLoc ≪≫ eLift ≪≫ eULift
  exact e.symm

/-- The previous identification as an `A_f`-linear equivalence. -/
private noncomputable def localizedHomologyAwayLinearEquiv
    {A : Type u} [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{v} A)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away f)) n).obj
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.Away f))).obj K)) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) := by
  let B := Localization.Away f
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj
    ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj K)
  let N' := (ModuleCat.restrictScalars (algebraMap A B)).obj N
  let e : ↑N' ≃ₗ[A] LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) :=
    (localizedHomologyIso (.powers f) (Localization.Away f) K n).symm.toLinearEquiv
  letI : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact e.extendScalarsOfIsLocalization (Submonoid.powers f) B

/-- Localizing the universe lift of the ring away from `f` gives the universe lift of `A_f`. -/
private noncomputable def localizedAwayRegularIso
    {A : Type u} [CommRing A] (f : A) :
    LocalizedModule.Away f (ULift.{v} A) ≃ₗ[Localization.Away f]
      ULift.{v} (Localization.Away f) := by
  let B := Localization.Away f
  let eA : ULift.{v} A ≃ₗ[A] A := ULift.moduleEquiv
  let eB : B ≃ₗ[A] ULift.{v} B := ULift.moduleEquiv.symm
  let g : ULift.{v} A →ₗ[A] ULift.{v} B :=
    eB.toLinearMap.comp ((Algebra.linearMap A B).comp eA.toLinearMap)
  have hg : IsLocalizedModule (Submonoid.powers f) g := inferInstance
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) (ULift.{v} A)) g
  exact e.extendScalarsOfIsLocalization (Submonoid.powers f) B

/-- A trivialization of a finite cohomology module over `A_p` comes from an `A`-linear map that
becomes bijective after localizing away from any multiple of a suitable element outside `p`. -/
private theorem exists_homology_map_bijective_on_multiples
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (K : DerivedCategory (ModuleCat.{v} A)) (n : ℤ)
    (hFinite : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K))
    (eH : (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (Localization.AtPrime p)) n).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A (Localization.AtPrime p))).obj K) ≅
        (ModuleCat.uliftFunctor.{v} (Localization.AtPrime p)).obj
          (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    ∃ (r : A), r ∉ p ∧
      ∃ φ : ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) →ₗ[A]
          ULift.{v} A,
        ∀ t : A, r ∣ t → Function.Bijective (LocalizedModule.map (.powers t) φ) := by
  let B := Localization.AtPrime p
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K
  let : Module.Finite A H := hFinite
  let : Module.FinitePresentation A H :=
    Module.finitePresentation_iff_finite A H |>.2 hFinite
  let : Module.Finite A (ULift.{v} A) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := A) (M := A)).symm
  let : Module.FinitePresentation A (ULift.{v} A) :=
    Module.finitePresentation_iff_finite A _ |>.2 inferInstance
  let hLocal := localizedHomologyIso p.primeCompl (Localization.AtPrime p) K n ≪≫
    (ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime p))).mapIso eH
  let N' := (ModuleCat.restrictScalars (algebraMap A B)).obj
    ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  let eUB : ↑N' ≃ₗ[A] B := {
    toFun := ULift.down
    invFun := ULift.up
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; rfl
    map_add' := by intro x y; rfl
    map_smul' := by
      intro a x
      change (algebraMap A B a) • x.down = a • x.down
      rw [smul_eq_mul, Algebra.smul_def]
  }
  let gA : A →ₗ[A] ↑N' :=
    eUB.symm.toLinearMap.comp (Algebra.linearMap A B)
  have hgA : IsLocalizedModule p.primeCompl gA := inferInstance
  let eA : ULift.{v} A ≃ₗ[A] A := ULift.moduleEquiv
  let gN : ULift.{v} A →ₗ[A] ↑N' := gA.comp eA.toLinearMap
  have hgN : IsLocalizedModule p.primeCompl gN := inferInstance
  let fH := LocalizedModule.mkLinearMap p.primeCompl H
  let eLocal := hLocal.toLinearEquiv
  obtain ⟨φ, s, hφ⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (S := p.primeCompl) (f := gN) (g := eLocal.toLinearMap.comp fH)
  have hmap : IsLocalizedModule.map p.primeCompl fH gN φ = s • eLocal.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl fH gN
    rw [IsLocalizedModule.map_comp]
    simpa [LinearMap.smul_comp] using hφ
  have hbij : Function.Bijective (IsLocalizedModule.map p.primeCompl fH gN φ) := by
    rw [hmap]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units gN s)).comp
      eLocal.bijective
  obtain ⟨r, hr, hbijAll⟩ :=
    exists_bijective_map_powers p.primeCompl fH gN φ hbij
  exact ⟨r, hr, φ, hbijAll⟩

/-- A finite module that vanishes at `p` vanishes after localizing away from any multiple of a
suitable element outside `p`. -/
private theorem exists_away_subsingleton_of_local_subsingleton
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (hM : Subsingleton (LocalizedModule p.primeCompl M)) :
    ∃ r : A, r ∉ p ∧ ∀ t : A, r ∣ t →
      Subsingleton (LocalizedModule.Away t M) := by
  let fM := LocalizedModule.mkLinearMap p.primeCompl M
  let Z := ULift.{u} PUnit
  let fN : Z →ₗ[A] Z := 0
  have hN : IsLocalizedModule p.primeCompl fN :=
    ⟨fun _ ↦ (Module.End.isUnit_iff _).2
        ⟨fun x y _ ↦ Subsingleton.elim x y, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩,
      fun y ↦ ⟨(y, 1), Subsingleton.elim _ _⟩, fun _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  have hbij : Function.Bijective
      (IsLocalizedModule.map p.primeCompl fM fN (0 : M →ₗ[A] Z)) :=
    ⟨fun x y _ ↦ hM.elim x y, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨r, hr, hbij⟩ := exists_bijective_map_powers p.primeCompl fM fN
    (0 : M →ₗ[A] Z) hbij
  refine ⟨r, hr, fun t hrt => ?_⟩
  exact ⟨fun x y => (hbij t hrt).injective (Subsingleton.elim _ _)⟩

/-- On a principal neighbourhood of a prime whose local ring is Gorenstein, a dualizing complex is
a shifted copy of the free module of rank one. -/
theorem IsDualizingComplex.exists_isLocalized_iso_shift_single
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : Dualizing.IsDualizingComplex K) (p : Ideal A) [p.IsPrime]
    (hp : Dualizing.IsGorensteinLocalRing (Localization.AtPrime p)) :
    ∃ f ∉ p, ∃ n : ℤ,
      Nonempty
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap A (Localization.Away f))).obj K ≅
          ((DerivedCategory.singleFunctor
              (ModuleCat.{max u v} (Localization.Away f)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (Localization.Away f)).obj
              (ModuleCat.of (Localization.Away f) (Localization.Away f))))⟦-n⟧) := by
  classical
  let Bp := Localization.AtPrime p
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A Bp)).obj K
  obtain ⟨n, hGEp, hLEp, eHp⟩ := localized_dualizing_local_data K hK p hp
  change Kp.IsGE n at hGEp
  change Kp.IsLE n at hLEp
  obtain ⟨a, b, hGEK, hLEK⟩ :=
    bounded_cohomology_of_finiteInjectiveDimension K hK.finiteInjectiveDimension
  let Sbad := (Finset.Icc a b).erase n
  have hbad (i : ℤ) (hi : i ∈ Sbad) :
      ∃ r : A, r ∉ p ∧ ∀ t : A, r ∣ t →
        Subsingleton (LocalizedModule.Away t
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) := by
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K
    let : Module.Finite A H := hK.finiteCohomology i
    have hin : i ≠ n := (Finset.mem_erase.mp hi).1
    have hz : IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} Bp) i).obj Kp) := by
      by_cases hlt : i < n
      · exact DerivedCategory.isZero_of_isGE Kp n i hlt
      · exact DerivedCategory.isZero_of_isLE Kp n i (by omega)
    have hsub : Subsingleton (LocalizedModule p.primeCompl H) := by
      let e := localizedHomologyIso p.primeCompl Bp K i
      exact ⟨fun x y => e.toLinearEquiv.injective
        ((ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _)⟩
    exact exists_away_subsingleton_of_local_subsingleton p H hsub
  let T := Sbad.attach
  let rfun : {i : ℤ // i ∈ Sbad} → A := fun i => Classical.choose (hbad i i.property)
  let q : A := T.prod rfun
  have hq : q ∈ p.primeCompl :=
    Submonoid.prod_mem _ fun i _ ↦ (Classical.choose_spec (hbad i.1 i.2)).1
  obtain ⟨r₀, hr₀, φ, hbijAll⟩ := exists_homology_map_bijective_on_multiples
    p K n (hK.finiteCohomology n) eHp.some
  let f : A := r₀ * q
  have hf : f ∉ p := p.primeCompl.mul_mem hr₀ hq
  have hbadAway (i : {i : ℤ // i ∈ Sbad}) :
      Subsingleton (LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i.1).obj K)) := by
    let ri := rfun i
    have hri : ri ∣ q := Finset.dvd_prod_of_mem _ (Finset.mem_attach _ i)
    exact (Classical.choose_spec (hbad i.1 i.2)).2 f (dvd_mul_of_dvd_right hri r₀)
  let B := Localization.Away f
  let Kf := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A B)).obj K
  have hsubAway (i : ℤ) (hi : i ≠ n) :
      Subsingleton (LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K)) := by
    by_cases hii : i ∈ Sbad
    · exact hbadAway ⟨i, hii⟩
    · have hiIcc : i ∉ Finset.Icc a b := by
        intro hIcc
        exact hii (Finset.mem_erase.mpr ⟨hi, hIcc⟩)
      have hiOutside : i < a ∨ b < i := by
        simp only [Finset.mem_Icc, not_and, not_le] at hiIcc
        omega
      have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) := by
        rcases hiOutside with hlt | hgt
        · exact DerivedCategory.isZero_of_isGE K a i hlt
        · exact DerivedCategory.isZero_of_isLE K b i hgt
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  have hzeroAway (i : ℤ) (hi : i ≠ n) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i).obj Kf) := by
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun x y => (localizedHomologyAwayLinearEquiv f K i).injective ((hsubAway i hi).elim _ _)⟩
  have hGEf : Kf.IsGE n := (DerivedCategory.isGE_iff Kf n).2 fun i hi =>
    hzeroAway i (by omega)
  have hLEf : Kf.IsLE n := (DerivedCategory.isLE_iff Kf n).2 fun i hi =>
    hzeroAway i (by omega)
  let eMap : LocalizedModule.Away f ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} A) n).obj K) ≃ₗ[B] LocalizedModule.Away f (ULift.{v} A) :=
    LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers f) φ)
      (hbijAll f (dvd_mul_right r₀ q))
  let eModule : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj Kf ≅
      (ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B) :=
    ((localizedHomologyAwayLinearEquiv f K n).trans
      (eMap.trans (localizedAwayRegularIso f))).toModuleIso
  obtain ⟨M, ⟨eK⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Kf n
  let eHN : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).obj Kf ≅ M :=
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) n).mapIso eK ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} B) n).app M
  let eSingle := (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) n).mapIso
    (eHN.symm ≪≫ eModule)
  let eShift := ((DerivedCategory.singleFunctors (ModuleCat.{max u v} B)).shiftIso
    (-n) n 0 (by omega)).app
      ((ModuleCat.uliftFunctor.{v} B).obj (ModuleCat.of B B))
  exact ⟨f, hf, n, ⟨eK ≪≫ eSingle ≪≫ eShift.symm⟩⟩

end Dualizing
