module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.LocalizationAwayDualizing
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# A local criterion for Gorenstein rings

Over a Noetherian ring `A` carrying a dualizing complex `K`, the localization of `A` at a prime
`p` is Gorenstein exactly when the derived localization of `K` is invertible in the derived
category of `Localization.AtPrime p`.

The argument has two halves. Over a Noetherian *local* ring `B` the criterion is
`Dualizing.IsDualizingComplex.exists_iso_derivedTensorProduct_invertible` [Stacks, Tag 0A7F] in
one direction — two dualizing complexes differ by an invertible object, so if `B` itself is
Gorenstein then any dualizing complex is invertible — and in the other direction
`DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit`, which turns invertibility into
the statement that some principal localization of the complex is a shifted copy of the localized
ring; shifting that back (`Dualizing.isDualizingComplex_shift`) and gluing over the one-element
cover given by a unit (`Dualizing.isDualizingComplex_of_localizations` [Stacks, Tag 0A7H]) makes
`B` Gorenstein. The second half is the reduction of the general statement to the local one, which
is where the universes have to be moved: `Dualizing.IsGorensteinLocalRing` is stated in the ring's
own universe, while the complex being localized lives over a module universe independent of it.

## Main definitions

* `Dualizing.derivedCategoryMonoidal` — the derived tensor product as a monoidal structure on
  `D(ModuleCat.{max u v} R)`, transported from the coefficient-equivalent lifted ring `ULift.{v} R`
  along `StacksDraft.TorAmplitude.scalarLift`.
* `Dualizing.scalarLiftDerivedIso` — that coefficient equivalence agrees with derived extension of
  scalars along `ULift.ringEquiv`.

## Main results

* `Dualizing.isInvertible_iff_scalarLift` — the coefficient equivalence detects invertibility, so
  the transported monoidal structure may be used in place of the canonical one over `ULift.{v} R`.
* `Dualizing.isGorensteinLocalRing_iff_isInvertible_localization` — **[Stacks, Tag 0DW9]**, the
  local criterion itself.

## Implementation notes

`Dualizing.IsGorensteinLocalRing B` pins the module universe to `B`'s own, but the dualizing
complex `K` of the statement lives in `ModuleCat.{v} A` for a `v` unrelated to `A`'s universe, and
its localization therefore lives in `ModuleCat.{max u v} B`. The two are bridged by passing to
`ULift.{v} B`, whose own universe is already `max u v`:
`Dualizing.isGorensteinLocalRing_of_ringEquiv` transports Gorensteinness along
`B ≃+* ULift.{v} B`, and `Dualizing.isInvertible_iff_scalarLift` transports invertibility the
other way. That is the only role of the lift, and it is why
`Dualizing.derivedCategoryMonoidal` is defined by transport rather than taken directly: the
canonical derived monoidal structure of `CochainComplex.DerivedTensor` is available over
`ULift.{v} B` but not, at one universe, over `B`.

The monoidal structure appearing in the statement is `Dualizing.derivedCategoryMonoidal`, which is
`@[instance_reducible]` rather than an `instance`: a second ambient monoidal structure on a derived
category breaks instance search, so it is introduced where it is needed.

Tag 0DW9 has four statements in the Stacks Project, so its covering set spans four declarations:
part (1)(a) is `Dualizing.isGorensteinRing_iff_isInvertible_canonical`, part (1)(b) is the local
criterion below, part (1)(c) is `Dualizing.isOpen_gorensteinLocus`, and part (2) is
`Dualizing.exists_isDualizingComplex_iff_regularModule`. Each carries the tag with its clause.
`Dualizing.isGorensteinRing_iff_isInvertible` states part (1)(a) for a dualizing complex whose
module universe is larger than the ring's, where the tensor product is the transported one.

## References

* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
-/

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-- Any two derived tensor products on `D(ModuleCat.{max u v} R)` agree on each pair of objects:
both are computed by the tensor product of K-flat resolutions, which is what each one's
`comparison` isomorphism says. -/
private def derivedTensorGeneralObjIso
    {R : Type u} [CommRing R]
    (T T' : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, v} R)
    (X Y : DerivedCategory (ModuleCat.{max u v} R)) :
    (T.tensor.obj X).obj Y ≅ (T'.tensor.obj X).obj Y := by
  let Q := DerivedCategory.Q (C := ModuleCat.{max u v} R)
  let hQX : ∃ K, Nonempty (Q.obj K ≅ X) := Functor.EssSurj.mem_essImage Q X
  let hQY : ∃ L, Nonempty (Q.obj L ≅ Y) := Functor.EssSurj.mem_essImage Q Y
  let K := hQX.choose
  let L := hQY.choose
  let eK := Classical.choice hQX.choose_spec
  let eL := Classical.choice hQY.choose_spec
  let hKP := CochainComplex.KFlat.exists_kFlat_resolution K
  let hLP := CochainComplex.KFlat.exists_kFlat_resolution L
  let P := hKP.choose
  let P' := hLP.choose
  let fP := hKP.choose_spec.choose
  let fP' := hLP.choose_spec.choose
  let hP := hKP.choose_spec.choose_spec.1
  let hP' := hLP.choose_spec.choose_spec.1
  -- These two supply `IsIso (Q.map fP)`/`IsIso (Q.map fP')` to the `asIso`s below; they are
  -- load-bearing despite never being named.
  let _hfP := hKP.choose_spec.choose_spec.2.2.1
  let _hfP' := hLP.choose_spec.choose_spec.2.2.1
  let eXP : Q.obj P ≅ X := asIso (Q.map fP) ≪≫ eK
  let eYP : Q.obj P' ≅ Y := asIso (Q.map fP') ≪≫ eL
  let eT (S : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, v} R) :
      (S.tensor.obj X).obj Y ≅ Q.obj (CochainComplex.DerivedTensor.tensorComplex P P') :=
    (S.tensor.mapIso eXP.symm).app Y ≪≫
      (S.tensor.obj (Q.obj P)).mapIso eYP.symm ≪≫ S.comparison P P' hP hP'
  exact eT T ≪≫ (eT T').symm

/-- Derived tensor on modules in a universe containing the ring's, transported from
`ULift R` along the coefficient equivalence. The objects remain modules over `R`. -/
@[instance_reducible]
def derivedCategoryMonoidal (R : Type u) [CommRing R] :
    MonoidalCategory (DerivedCategory (ModuleCat.{max u v} R)) :=
  letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} R)).choose
  Monoidal.transport
    (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)).mapDerivedCategory.asEquivalence.symm

/-- The coefficient equivalence detects invertibility for the transported tensor product. -/
theorem isInvertible_iff_scalarLift (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    letI := derivedCategoryMonoidal.{u, v} R
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (ULift.{v} R)).choose
    IsInvertible K ↔ IsInvertible
      ((StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)).mapDerivedCategory.obj K) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (ULift.{v} R)).choose
  let e := (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)).mapDerivedCategory.asEquivalence
  let := derivedCategoryMonoidal.{u, v} R
  constructor
  · rintro ⟨h⟩
    refine ⟨⟨e.functor.obj h.inv, ?_, ?_⟩⟩
    · exact (e.counitIso.app _).symm ≪≫ e.functor.mapIso h.isoLeft ≪≫ e.counitIso.app _
    · exact (e.counitIso.app _).symm ≪≫ e.functor.mapIso h.isoRight ≪≫ e.counitIso.app _
  · rintro ⟨h⟩
    refine ⟨⟨e.inverse.obj h.inv, ?_, ?_⟩⟩
    · exact e.inverse.mapIso (tensorIso (Iso.refl _) (e.counitIso.app _) ≪≫ h.isoLeft)
    · exact e.inverse.mapIso (tensorIso (e.counitIso.app _) (Iso.refl _) ≪≫ h.isoRight)

/-- Extending scalars to the lifted ring agrees with its coefficient equivalence on
derived categories: the equivalence is exact, so its derived comparison is invertible. -/
def scalarLiftDerivedIso (R : Type u) [CommRing R] :
    (totalDerivedExtensionScalars.{u, max u v, max u v}
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom).functor ≅
      (StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)).mapDerivedCategory := by
  let e := (ULift.ringEquiv : ULift.{v} R ≃+* R)
  let F := ModuleCat.extendScalars.{u, max u v, max u v} e.symm.toRingHom
  let G := StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v} e
  let a := ModuleCat.extendRestrictScalarsAdj.{max u v} e.symm.toRingHom
  let i : F ≅ G := a.leftAdjointUniq E.toAdjunction
  letI : F.Additive := a.left_adjoint_additive
  letI : F.IsEquivalence := Functor.isEquivalence_of_iso i.symm
  let D := totalDerivedExtensionScalars.{u, max u v, max u v} e.symm.toRingHom
  haveI : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) (by
      intro X Y f hf
      have : QuasiIso f := hf
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map f))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ G.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex i (ComplexShape.up ℤ)) _ ≪≫
      G.mapDerivedCategoryFactors.symm)

/-- The module-universe lift of a cochain complex is degreewise `ULift.moduleEquiv`. -/
private def uliftModuleComplexIso
    {R : Type u} [CommRing R] (I : CochainComplex (ModuleCat.{v} R) ℤ) :
    ((ModuleCat.uliftFunctor.{v} R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ≅ I := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (ULift.moduleEquiv : ULift.{v} (I.X i) ≃ₗ[R] I.X i).toModuleIso) ?_
  intro i j hij
  ext x
  rfl

/-- The module-universe lift at one universe is the identity on the derived category.

`Dualizing.uliftDerivedSelfIso` is the same fact with the module universe equal to the ring's; the
module universe here is independent of the ring's, which is what the reduction to the local case
needs, and only the object-level statement is required. -/
private theorem uliftModuleDerivedIso
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{v} R)) :
    Nonempty ((ModuleCat.uliftFunctor.{v} R).mapDerivedCategory.obj K ≅ K) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{v} R)
  obtain ⟨I, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage Q K
  exact ⟨(ModuleCat.uliftFunctor.{v} R).mapDerivedCategory.mapIso e.symm ≪≫
    (ModuleCat.uliftFunctor.{v} R).mapDerivedCategoryFactors.app I ≪≫
    Q.mapIso (uliftModuleComplexIso I) ≪≫ e⟩

/-- Derived localization away from `f` carries the ring, in degree zero, to the localized ring, in
degree zero: extension of scalars is monoidal, so it carries the unit to the unit. -/
private def localizationAwayUnitIso
    {R : Type u} [CommRing R] (f : R) :
    (StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} f).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 0).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f)) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization.Away f))
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj
    (algebraMap R (Localization.Away f))).left_adjoint_additive
  letI : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.Flat.holdsForLocalizationAway (Localization.Away f) f)
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap R (Localization.Away f))).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  change F.mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅ _
  exact F.mapDerivedCategory.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app (ModuleCat.of R R)) ≪≫
    F.mapDerivedCategoryFactors.app (𝟙_ _) ≪≫
    (DerivedCategory.Q (C := ModuleCat.{u} (Localization.Away f))).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app
        (ModuleCat.of R R)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (Localization.Away f)) 0).app
      (F.obj (ModuleCat.of R R))).symm ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 0).mapIso
      (Functor.Monoidal.εIso F).symm

/-- The local criterion in the ring's own universe: a Noetherian local ring is Gorenstein exactly
when a dualizing complex over it is invertible.

Forwards this is uniqueness of dualizing complexes [Stacks, Tag 0A7F]: the ring in degree zero is
itself dualizing, so it differs from the given complex by an invertible object, and the unit of the
canonical derived monoidal structure is the ring in degree zero. Backwards, invertibility localizes
the complex to a shifted copy of the localized ring on a principal neighbourhood of the maximal
ideal; that neighbourhood is the whole ring, because the element it is generated by misses the
maximal ideal and is therefore a unit. -/
private theorem local_criterion_native
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (Kloc : DerivedCategory (ModuleCat.{u} B))
    (hKloc : IsDualizingComplex Kloc) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    IsGorensteinLocalRing B ↔ MonoidalCategory.IsInvertible Kloc := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  constructor
  · intro hG
    have hU : IsDualizingComplex U := hG
    obtain ⟨T, m, hdata, L, hL, hKL⟩ :=
      @IsDualizingComplex.exists_iso_derivedTensorProduct_invertible.{u, u}
        B inferInstance inferInstance Kloc U hKloc hU
    rcases hKL with ⟨eKU⟩
    let : MonoidalCategory (DerivedCategory (ModuleCat.{u} B)) :=
      (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    let : SymmetricCategory (DerivedCategory (ModuleCat.{u} B)) :=
      (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose_spec.choose
    let eTensorCan :=
      (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        B).choose_spec.choose_spec.choose
    let UCan : (𝟙_ (DerivedCategory (ModuleCat.{u} B))) ≅ U := by
      let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B
      exact (T.rightUnitor.app (𝟙_ (DerivedCategory (ModuleCat.{u} B)))).symm ≪≫
        (((eTensorCan.app (𝟙_ (DerivedCategory (ModuleCat.{u} B)))).app U).symm ≪≫
          leftUnitor U)
    have eProductCan : (𝟙_ (DerivedCategory (ModuleCat.{u} B))) ≅ Kloc ⊗ L :=
      UCan ≪≫ eKU ≪≫
        derivedTensorGeneralObjIso T
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B).toGeneral Kloc L ≪≫
        ((eTensorCan.app Kloc).app L).symm
    exact ⟨{
      inv := L
      isoLeft := eProductCan.symm
      isoRight := (β_ L Kloc) ≪≫ eProductCan.symm
    }⟩
  · intro hInv
    have hLoc : DerivedCategory.Invertible.IsLocallyShiftedUnit Kloc :=
      (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit Kloc).1.mp hInv
    obtain ⟨f, hf, n, hshift⟩ := hLoc (IsLocalRing.maximalIdeal B)
      (IsLocalRing.maximalIdeal.isMaximal B).isPrime
    have hfunit : IsUnit f := IsLocalRing.notMem_maximalIdeal.mp hf
    have hAway : IsDualizingComplex
        ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} f).obj Kloc) :=
      isDualizingComplex_localizationAway f Kloc hKloc
    have hDshift : IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
      isDualizingComplex_of_iso hshift.some
        (isDualizingComplex_of_iso
          ((DerivedCategory.Invertible.localizationAwayIso.{u, u} f).app Kloc).symm hAway)
    have hURf : IsDualizingComplex
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 0).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
      isDualizingComplex_of_iso
        (((DerivedCategory.singleFunctors (ModuleCat.{u} (Localization.Away f))).shiftIso
            n 0 n (by omega)).app
          (ModuleCat.of (Localization.Away f) (Localization.Away f)))
        (isDualizingComplex_shift _ hDshift n)
    have hspan : Ideal.span (Set.range (fun _ : Unit => f)) = ⊤ := by
      simpa using (Ideal.span_singleton_eq_top.mpr hfunit)
    exact isDualizingComplex_of_localizations (fun _ : Unit => f) U hspan
      (fun _ => isDualizingComplex_of_iso (localizationAwayUnitIso (R := B) f).symm hURf)

/-- A coefficient equivalence preserves a dualizing complex. Here it is computed as
localization at the trivial submonoid, so the existing localization theorem applies. -/
private theorem dualizing_scalarLift
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsDualizingComplex K) :
    letI := isNoetherianRing_of_ringEquiv R
      (ULift.ringEquiv.symm : R ≃+* ULift.{v} R)
    IsDualizingComplex
      ((StacksDraft.TorAmplitude.scalarLift.{u, v} (R := R)).mapDerivedCategory.obj K) := by
  let e := (ULift.ringEquiv.symm : R ≃+* ULift.{v} R)
  let := e.toRingHom.toAlgebra
  let : IsLocalization (⊥ : Submonoid R) (ULift.{v} R) :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro _ ⟨r, hr, rfl⟩
      obtain rfl : r = 1 := Submonoid.mem_bot.mp hr
      simpa only [map_one] using (IsUnit.submonoid (ULift.{v} R)).one_mem) e.bijective
  let := isNoetherianRing_of_ringEquiv R e
  exact isDualizingComplex_of_iso
    ((totalDerivedExtensionScalars.{u, max u v, max u v} e.toRingHom).functor.mapIso
      (uliftModuleDerivedIso K).some ≪≫ (scalarLiftDerivedIso.{u, v} R).app K)
    (isDualizingComplex_localization (B := ULift.{v} R) (⊥ : Submonoid R) K hK)

/-- **Stacks Project, Tag 0DW9 (1)(b).** The localization of a Noetherian
ring at a prime is Gorenstein if and only if the localization of a dualizing complex
is invertible in the derived category of the localized ring. -/
@[stacks 0DW9 "(1)(b)"]
theorem isGorensteinLocalRing_iff_isInvertible_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K)
    (p : Ideal A) [p.IsPrime] :
    let B := Localization.AtPrime p
    letI := derivedCategoryMonoidal.{u, v} B
    IsGorensteinLocalRing B ↔
      MonoidalCategory.IsInvertible
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A B)).obj K) := by
  let B := Localization.AtPrime p
  let C := ULift.{v} B
  let e : B ≃+* C := ULift.ringEquiv.symm
  let := isNoetherianRing_of_ringEquiv B e
  let : IsLocalRing C := e.isLocalRing
  let Kloc := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A B)).obj K
  exact (Iff.intro (isGorensteinLocalRing_of_ringEquiv e.symm)
      (isGorensteinLocalRing_of_ringEquiv e)).trans
    ((local_criterion_native C _ (dualizing_scalarLift Kloc
      (isDualizingComplex_localization p.primeCompl K hK))).trans
    (isInvertible_iff_scalarLift.{u, v} B Kloc).symm)

end Dualizing

end
