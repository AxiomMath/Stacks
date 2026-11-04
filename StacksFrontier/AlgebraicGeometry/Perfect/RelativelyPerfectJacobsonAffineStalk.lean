module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonStalks
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.AffineAvatar
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.Homology.RelativelyPerfect.JacobsonFibre

/-!
# Derived stalks over the base on an affine chart

For a morphism of schemes `f : X ⟶ S` and a point `x` of `X`, the derived stalk of an object `E`
of `D(𝒪_X)` at `x`, read over the local ring `𝒪_{S, f x}`, is computed here in two situations.

* Across an open immersion `j : V ⟶ X`: the derived stalk of the derived pullback of `E` at `y`,
  read over the base along `j ≫ f`, is the derived stalk of `E` at `j y`.
* On `Spec A` over `Spec R`: the derived stalk at a prime `q` of the sheaf `M̃^•` associated to a
  complex of `A`-modules is the localisation `M_q`, read over `R_{q ∩ R}`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings`:
  the derived stalk over the local ring and over the `RingCat`-valued stalk of the structure sheaf
  define the same Tor amplitude over the base.
* `AlgebraicGeometry.derivedStalkOverBaseDerivedPullbackIso`: the open-immersion statement.
* `AlgebraicGeometry.exists_derivedStalkOverBase_tilde_iso`: the affine statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### The two spellings of the derived stalk over the base -/

/-- **The two spellings of the derived stalk over the base define the same Tor amplitude.** For a
morphism `f : X ⟶ S`, a point `x` of `X` and an object `E` of `D(𝒪_X)`, the derived stalk of `E`
over the local ring `𝒪_{X, x}`, read over `𝒪_{S, f x}` along the stalk map, has Tor amplitude in
`[a, b]` exactly when the derived stalk over the `RingCat`-valued stalk of the structure sheaf,
read over `𝒪_{S, f x}` along the stalk map and the comparison of the two stalk rings, does. -/
theorem Scheme.Hom.hasTorAmplitudeCanonical_derivedStalk_iff_structureSheafOfRings
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (a b : ℤ) :
    HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
          ((derivedStalkFunctor x).obj E)) a b ↔
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base x)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
              (f.stalkMap x).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E)) a b := by
  let e : (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor x).obj E) ≅
      (ModuleCat.restrictScalars.{u}
          ((SemilinearStalk.commStalkRingEquiv X.presheaf x).symm.toRingHom.comp
            (f.stalkMap x).hom)).mapDerivedCategory.obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafOfRings.{u} X.toRingedSpace) x).mapDerivedCategory.obj E) :=
    (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.mapIso
        ((derivedStalkSpellingFunctorIso x).app E) ≪≫
      PseudoCoherence.restrictScalarsCompObjIso (f.stalkMap x).hom
        (ringCatStalkRingEquiv x).symm.toRingHom
        ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x).obj E)
  exact ⟨fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b h,
    fun h => BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e.symm a b h⟩

/-! ### Across an open immersion -/

/-- **The derived stalk over the base across an open immersion.** For an open immersion
`j : V ⟶ X`, a morphism `f : X ⟶ S`, an object `E` of `D(𝒪_X)` and a point `y` of `V`, the
derived stalk at `y` of the derived pullback of `E` along `j`, read over `𝒪_{S, f (j y)}` along
the stalk map of `j ≫ f`, is the derived stalk of `E` at `j y`, read along the stalk map of `f`.

The stalk of a derived pullback is the derived extension of scalars along the stalk map of `j`,
which is a ring isomorphism, and restricting scalars along it undoes that extension. -/
def derivedStalkOverBaseDerivedPullbackIso {X S V : Scheme.{u}} (f : X ⟶ S) (j : V ⟶ X)
    [IsOpenImmersion j] (E : DerivedCategory X.Modules) (y : V) :
    (ModuleCat.restrictScalars ((j ≫ f).stalkMap y).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor y).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            j.toLRSHom.toShHom).obj E)) ≅
      (ModuleCat.restrictScalars (f.stalkMap (j.base y)).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor (j.base y)).obj E) :=
  let e := stalkRingEquivOfIsOpenImmersion j y
  let σ := (f.stalkMap (j.base y)).hom
  have hτ : ((j ≫ f).stalkMap y).hom = e.toRingHom.comp σ :=
    Stacks.ModuleSkyscraper.stalkMap_hom_comp j f y
  (ModuleCat.restrictScalars ((j ≫ f).stalkMap y).hom).mapDerivedCategory.mapIso
      ((derivedPullbackStalkIso j y).app E) ≪≫
    eqToIso (congrArg (fun φ : S.presheaf.stalk (f.base (j.base y)) →+* V.presheaf.stalk y =>
      (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} e.toRingHom).functor.obj
          ((derivedStalkFunctor (j.base y)).obj E))) hτ) ≪≫
    (PseudoCoherence.restrictScalarsCompObjIso σ e.toRingHom _).symm ≪≫
    (ModuleCat.restrictScalars σ).mapDerivedCategory.mapIso
      ((totalDerivedExtendRestrictScalarsSelfIso.{u, u} e).app _)

/-! ### On an affine scheme over an affine base -/

/-- The derived stalk over the base of the class of `M̃^•` at a prime `q`, for the morphism of
spectra of a ring map `R → A`: it is the localisation `M_q` read over `R_{q ∩ R}`, up to the
identification of the local ring of `Spec R` with `R_{q ∩ R}`. -/
def tildeDerivedStalkOverBaseIso {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (w : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
    (ModuleCat.restrictScalars
        ((AffineRelativeTorAmplitude.specMap R A).stalkMap w).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor (X := Spec (CommRingCat.of A)) w).obj
          (DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex (R := CommRingCat.of A) M))) ≅
      (ModuleCat.restrictScalars
          (AffineRelativeTorAmplitude.baseStalkRingEquiv R A w).toRingHom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((CochainComplex.restrictScalars
            (algebraMap (Localization.AtPrime (w.asIdeal.under R))
              (Localization.AtPrime w.asIdeal))).obj
            ((CochainComplex.extendScalars
              (algebraMap A (Localization.AtPrime w.asIdeal))).obj M))) :=
  let : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
  (relativeStalkComplexDerivedIso (AffineRelativeTorAmplitude.specMap R A)
      (Stacks.AffineTilde.tildeComplex (R := CommRingCat.of A) M) w).symm ≪≫
    DerivedCategory.Q.mapIso (AffineRelativeTorAmplitude.relativeStalkComplexTildeIso R A w M) ≪≫
    ((ModuleCat.restrictScalars
      (AffineRelativeTorAmplitude.baseStalkRingEquiv R A w).toRingHom).mapDerivedCategoryFactors.app
        _).symm

/-- **The derived stalk over the base of an associated sheaf.** Let `g : Spec A ⟶ Spec R` be the
morphism of a ring map `R → A`, let `M` be a complex of `A`-modules and `F` an object of
`D(𝒪_{Spec A})` isomorphic to the class of `M̃^•`. At a prime `q` of `A`, the derived stalk of `F`
read over the local ring of `Spec R` along the stalk map of `g` is, up to an identification of
that local ring with `R_{q ∩ R}`, the localisation `M_q` read over `R_{q ∩ R}`. -/
theorem exists_derivedStalkOverBase_tilde_iso {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (hg : g = AffineRelativeTorAmplitude.specMap R A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (F : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (eF : DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex (R := CommRingCat.of A) M) ≅ F)
    (w : PrimeSpectrum A) :
    letI : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
    ∃ ε : (Spec (CommRingCat.of R)).presheaf.stalk (g.base w) ≃+*
        Localization.AtPrime (w.asIdeal.under R),
      Nonempty ((ModuleCat.restrictScalars (g.stalkMap w).hom).mapDerivedCategory.obj
          ((derivedStalkFunctor (X := Spec (CommRingCat.of A)) w).obj F) ≅
        (ModuleCat.restrictScalars ε.toRingHom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj
            ((CochainComplex.restrictScalars
              (algebraMap (Localization.AtPrime (w.asIdeal.under R))
                (Localization.AtPrime w.asIdeal))).obj
              ((CochainComplex.extendScalars
                (algebraMap A (Localization.AtPrime w.asIdeal))).obj M)))) := by
  subst hg
  exact ⟨AffineRelativeTorAmplitude.baseStalkRingEquiv R A w,
    ⟨(ModuleCat.restrictScalars
        ((AffineRelativeTorAmplitude.specMap R A).stalkMap w).hom).mapDerivedCategory.mapIso
      ((derivedStalkFunctor (X := Spec (CommRingCat.of A)) w).mapIso eF.symm) ≪≫
      tildeDerivedStalkOverBaseIso M w⟩⟩

/-! ### Through an affine chart -/

section Chart

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
  (hι : ι ≫ f = AffineRelativeTorAmplitude.specMap R A)
  (E : DerivedCategory X.Modules) (M : CochainComplex (ModuleCat.{u} A) ℤ)
  (eF : DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex (R := CommRingCat.of A) M) ≅
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback ι.toLRSHom.toShHom).obj E)

include hι eF in
/-- **Tor amplitude over the base at a point of an affine chart.** Let `ι : Spec A ⟶ X` be an open
immersion over `Spec R` and let the derived pullback of `E` along `ι` be the class of `M̃^•`. If
the localisation of `M` at a prime `q` of `A` has Tor amplitude in `[a, b]` over `R_{q ∩ R}`, then
the derived stalk of `E` at `ι q`, read over the local ring of `Spec R`, has Tor amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeCanonical_derivedStalk_of_hasTorAmplitudeAt (z : X) (w : PrimeSpectrum A)
    (hw : ι.base w = z) (a b : ℤ)
    (h : HasTorAmplitudeAt R M w.asIdeal a b) :
    HasTorAmplitudeCanonical (ToType ((Spec (CommRingCat.of R)).presheaf.stalk (f.base z)))
      ((ModuleCat.restrictScalars (f.stalkMap z).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor z).obj E)) a b := by
  subst hw
  let : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
  obtain ⟨ε, ⟨e⟩⟩ := exists_derivedStalkOverBase_tilde_iso (ι ≫ f) hι M _ eF w
  have h₁ := (AffineRelativeTorAmplitude.hasTorAmplitudeCanonical_iff_hasTorAmplitude0DJF
    _ a b).mpr h
  have h₂ := (Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff ε _ a b).mpr h₁
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    (e.symm ≪≫ derivedStalkOverBaseDerivedPullbackIso f ι E w) a b h₂

include hι eF in
/-- **The derived fibre at a point of an affine chart.** Let `ι : Spec A ⟶ X` be an open immersion
over `Spec R` and let the derived pullback of `E` along `ι` be the class of `M̃^•`. Let `q` be a
prime of `A` with `ι q = z`, and let `c` be a ring map out of the local ring of `Spec R` at a point
`s` equal to `f z`. If the derived base change along `c` of the derived stalk of `E` at `z`, read
over that local ring, has Tor amplitude in `[a, b]`, then so has the derived base change of the
localisation `M_q`, read over `R_{q ∩ R}`, along `c` precomposed with an identification of
`R_{q ∩ R}` with the local ring at `s`. -/
theorem exists_hasTorAmplitudeCanonical_derivedFibre_tilde (z : X) (w : PrimeSpectrum A)
    (hw : ι.base w = z) {s : Spec (CommRingCat.of R)} (hpt : s = f.base z)
    {R₀ : Type u} [CommRing R₀] (c : (Spec (CommRingCat.of R)).presheaf.stalk s →+* R₀)
    (a b : ℤ)
    (hFS : HasTorAmplitudeCanonical R₀
      ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj
        ((ModuleCat.restrictScalars
            (((Spec (CommRingCat.of R)).presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫
              f.stalkMap z).hom).mapDerivedCategory.obj
          ((derivedStalkFunctor z).obj E))) a b) :
    letI : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
    ∃ ε : (Spec (CommRingCat.of R)).presheaf.stalk s ≃+* Localization.AtPrime (w.asIdeal.under R),
      HasTorAmplitudeCanonical R₀
        ((totalDerivedExtensionScalars.{u, u, u} (c.comp ε.symm.toRingHom)).functor.obj
          ((ModuleCat.restrictScalars
            (algebraMap (Localization.AtPrime (w.asIdeal.under R))
              (Localization.AtPrime w.asIdeal))).mapDerivedCategory.obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization.AtPrime w.asIdeal))).functor.obj
                (DerivedCategory.Q.obj M)))) a b := by
  subst hw
  let : Algebra (Localization.AtPrime (w.asIdeal.under R)) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under R) w.asIdeal
  obtain ⟨ε, ⟨e⟩⟩ := exists_derivedStalkOverBase_tilde_iso (ι ≫ f) hι M _ eF w
  let sc := ((Spec (CommRingCat.of R)).presheaf.stalkCongr (Inseparable.of_eq hpt))
  let scE := sc.commRingCatIsoToRingEquiv
  let ε' := scE.trans ε
  let σ := (f.stalkMap (ι.base w)).hom
  let Rp := Localization.AtPrime (w.asIdeal.under R)
  let Aq := Localization.AtPrime w.asIdeal
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A Aq)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Aq w.asIdeal.primeCompl))
  let Y' := DerivedCategory.Q.obj ((CochainComplex.restrictScalars (algebraMap Rp Aq)).obj
    ((CochainComplex.extendScalars (algebraMap A Aq)).obj M))
  let eY : (ModuleCat.restrictScalars (algebraMap Rp Aq)).mapDerivedCategory.obj
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A Aq)).functor.obj
        (DerivedCategory.Q.obj M)) ≅ Y' :=
    (ModuleCat.restrictScalars (algebraMap Rp Aq)).mapDerivedCategory.mapIso
        ((Dualizing.totalDerivedExtensionScalarsIsoExtendScalars (algebraMap A Aq)).app _ ≪≫
          (ModuleCat.extendScalars.{u, u, u} (algebraMap A Aq)).mapDerivedCategoryFactors.app M) ≪≫
      (ModuleCat.restrictScalars (algebraMap Rp Aq)).mapDerivedCategoryFactors.app _
  let eObj : (ModuleCat.restrictScalars (sc.hom ≫ f.stalkMap (ι.base w)).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor (ι.base w)).obj E) ≅
      (ModuleCat.restrictScalars ε'.toRingHom).mapDerivedCategory.obj Y' :=
    (PseudoCoherence.restrictScalarsCompObjIso sc.hom.hom σ _).symm ≪≫
      (ModuleCat.restrictScalars sc.hom.hom).mapDerivedCategory.mapIso
        ((derivedStalkOverBaseDerivedPullbackIso f ι E w).symm ≪≫ e) ≪≫
      PseudoCoherence.restrictScalarsCompObjIso sc.hom.hom ε.toRingHom Y'
  refine ⟨ε', BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b hFS⟩
  exact (totalDerivedExtensionScalars.{u, u, u} c).functor.mapIso eObj ≪≫
    PseudoCoherence.totalDerivedExtensionScalarsRestrictScalarsIso ε' c Y' ≪≫
    (totalDerivedExtensionScalars.{u, u, u} (c.comp ε'.symm.toRingHom)).functor.mapIso eY.symm

end Chart

end AlgebraicGeometry

end
