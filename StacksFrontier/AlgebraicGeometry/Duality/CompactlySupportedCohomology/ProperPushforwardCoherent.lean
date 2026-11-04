module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTriangulated
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence

/-!
# Proper pushforward on bounded coherent derived categories

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes. The derived direct image `Rf_*`
carries `D^b_{Coh}(𝒪_X)` into `D^b_{Coh}(𝒪_Y)` ([Stacks, Tag 08E2], whose input is the coherence
of higher direct images, [Stacks, Tag 02O5]), so it restricts to a triangulated functor

`Rf_* : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_Y)`.

For an open `V ⊆ Y` with `U = f⁻¹(V)` and `g : U ⟶ V` the restriction of `f`, restricting to `V`
commutes with it: `(Rf_* K)|_V ≅ Rg_*(K|_U)`, by [Stacks, Tag 08FE].

## Main definitions

* `AlgebraicGeometry.properPushforwardBoundedCoherent`: `Rf_*` on `D^b_{Coh}`.
* `AlgebraicGeometry.properPushforwardRestrictIso`: the identification
  `(Rf_* K)|_V ≅ Rg_*(K|_U)`.
* `AlgebraicGeometry.derivedPushforwardModulesPlusIso`: on bounded below objects `Rf_*` is the
  bounded below derived direct image `Rf_*^+`.
* `AlgebraicGeometry.homologyDerivedPushforwardSingleIso`: `H^q(Rf_*(M[-p])) ≅ R^{q-p} f_* M`,
  naturally in the `𝒪_X`-module `M`.

## Main results

* `AlgebraicGeometry.hasCoherentBoundedDirectImages_of_isProper`: the higher direct images of a
  coherent module along a proper morphism to a Noetherian scheme are coherent and vanish in large
  degrees.
* `AlgebraicGeometry.mem_boundedCoherentDerived_derivedPushforward`: `Rf_*` preserves
  `D^b_{Coh}`.

## References

* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The higher direct images of a coherent module along a proper morphism** to a Noetherian
scheme are coherent ([Stacks, Tag 02O5]) and vanish in large degrees ([Stacks, Tag 01XJ]). -/
public theorem hasCoherentBoundedDirectImages_of_isProper [IsNoetherian Y] [IsProper f]
    (M : X.Modules) [M.IsCoherent] :
    Stacks.AlgebraicGeometry.ProperSupportCoherent.HasCoherentBoundedDirectImages f M := by
  refine ⟨fun p => ?_, ?_⟩
  · rcases lt_or_ge p 0 with hp | hp
    · exact (coherentInModules Y).prop_of_isZero
        (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f M p hp)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp).symm⟩
      exact ProperCoherenceWitness.higherDirectImageIsCoherent X Y f inferInstance
        inferInstance M inferInstance n
  · obtain ⟨N, hN⟩ :=
      Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward f
    exact ⟨N, fun p hp => hN p hp M (isQuasicoherent_of_isCoherent M)⟩

/-- **`Rf_*` preserves `D^b_{Coh}`** for a proper morphism to a Noetherian scheme: this is
[Stacks, Tag 08E2], every coherent module having proper support. -/
public theorem mem_boundedCoherentDerived_derivedPushforward [IsNoetherian Y] [IsProper f]
    (E : DerivedCategory X.Modules) (hE : boundedCoherentDerived X E) :
    boundedCoherentDerived Y (derivedPushforwardModules f |>.obj E) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hE
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).mpr fun i hi => ha i hi
  have hLE : E.IsLE (a + (((b - a).toNat : ℕ) : ℤ)) :=
    (DerivedCategory.isLE_iff E _).mpr fun i hi => hb i (by omega)
  open Stacks.AlgebraicGeometry.ProperSupportCoherent in
  exact derivedCategoryBBounded_derivedPushforward_of_bounded
    f (b - a).toNat a E (fun j _ => by
      have : ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent := hc j
      exact hasCoherentBoundedDirectImages_of_isProper f _) hGE hLE

/-- **`Rf_* : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_Y)`** for a proper morphism `f` to a Noetherian
scheme: the derived direct image, which preserves bounded coherent objects by
`AlgebraicGeometry.mem_boundedCoherentDerived_derivedPushforward`. -/
public abbrev properPushforwardBoundedCoherent [IsNoetherian Y] [IsProper f] :
    BoundedCoherentDerived X ⥤ BoundedCoherentDerived Y :=
  (boundedCoherentDerived Y).lift ((boundedCoherentDerived X).ι ⋙ derivedPushforwardModules f)
    fun E => mem_boundedCoherentDerived_derivedPushforward f E.obj E.property

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-- **[Stacks, Tag 08FE] for an open of the target.** For `V ⊆ Y` open, `U = f⁻¹(V)` and
`g = f|_U : U ⟶ V`, restricting the derived direct image to `V` is the derived direct image along
`g` of the restriction to `U`: `(Rf_* K)|_V ≅ Rg_*(K|_U)`. -/
public def derivedPushforwardRestrictIso [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens) :
    derivedPushforwardModules f ⋙ (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).mapDerivedCategory ⋙
        derivedPushforwardModules (f ∣_ V) := by
  let i := (f ⁻¹ᵁ V).ι
  let j := V.ι
  let g := f ∣_ V
  have hsq : IsPullback i g f j := (isPullback_morphismRestrict f V).flip
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  have hiR : Ri.IsRightDerivedFunctor Fi.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Ri Fi.mapDerivedCategoryFactorsh
  have hjR : Rj.IsRightDerivedFunctor Fj.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Rj Fj.mapDerivedCategoryFactorsh
  let e : derivedPushforwardModules f ⋙ Rj ≅ Ri ⋙ derivedPushforwardModules g :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      f.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom _ _
      (isPullback_toShHom i g f j hsq) _ _ _ _
      (derivedPushforwardModules f) (derivedPushforwardModules g) Ri Rj
      (derivedPushforwardModulesUnit f) (derivedPushforwardModulesUnit g)
      Fi.mapDerivedCategoryFactorsh.inv Fj.mapDerivedCategoryFactorsh.inv
      (derivedPushforwardModules_isRightDerivedFunctor f)
      (derivedPushforwardModules_isRightDerivedFunctor g) hiR hjR
  exact Functor.isoWhiskerLeft _
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback j)) ≪≫ e ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorIsoPullback i)).symm _

/-- **Restriction to an open of the target commutes with `Rf_*` on `D^b_{Coh}`.** For `V ⊆ Y`
open, `U = f⁻¹(V)` and `g = f|_U : U ⟶ V`, `(Rf_* K)|_V ≅ Rg_*(K|_U)` naturally in `K` in
`D^b_{Coh}(𝒪_X)`; this is `AlgebraicGeometry.derivedPushforwardRestrictIso` read in the full
subcategories `D^b_{Coh}`. -/
public def properPushforwardRestrictIso [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    (V : Y.Opens) :
    properPushforwardBoundedCoherent f ⋙ restrictBoundedCoherentLift V.ι ≅
      restrictBoundedCoherentLift (f ⁻¹ᵁ V).ι ⋙ properPushforwardBoundedCoherent (f ∣_ V) :=
  NatIso.ofComponents
    (fun K => (boundedCoherentDerived V).fullyFaithfulι.preimageIso
      ((derivedPushforwardRestrictIso f V).app K.obj))
    (fun {K L} φ => (boundedCoherentDerived V).ι.map_injective (by
      simpa using (derivedPushforwardRestrictIso f V).hom.naturality
        ((boundedCoherentDerived X).ι.map φ)))

section PlusComparison

variable [QuasiCompact f] [QuasiSeparated f]

/-- Degreewise direct image of a bounded below complex of `𝒪_X`-modules, read in `D(𝒪_Y)`. -/
public abbrev plusPushforwardToDerived :
    HomotopyCategory.Plus X.Modules ⥤ DerivedCategory Y.Modules :=
  HomotopyCategory.Plus.ι _ ⋙ (Scheme.Modules.pushforward f).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The comparison `f_*K ⟶ Rf_*^+K` for a bounded below complex `K`, read in `D(𝒪_Y)`. -/
public def plusPushforwardUnitPlus :
    plusPushforwardToDerived f ⟶ DerivedCategory.Plus.Qh ⋙
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerRight (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι

/-- The comparison `f_*K ⟶ Rf_*K` for a bounded below complex `K`. -/
public def plusPushforwardUnitBig :
    plusPushforwardToDerived f ⟶ DerivedCategory.Plus.Qh ⋙
      (DerivedCategory.Plus.ι ⋙ derivedPushforwardModules f) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι _) (derivedPushforwardModulesUnit f)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- `Rf_*^+` followed by `D⁺(𝒪_Y) ⥤ D(𝒪_Y)` is a right derived functor of degreewise `f_*` on
`K⁺(𝒪_X)`: its comparison map is invertible on bounded below complexes of injective modules. -/
public theorem isRightDerivedFunctor_plusPushforwardUnitPlus :
    ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).IsRightDerivedFunctor (plusPushforwardUnitPlus f)
      (HomotopyCategory.Plus.quasiIso X.Modules) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusPushforwardToDerived f)).isRightDerivedFunctor_of_isIso
    (plusPushforwardUnitPlus f) (fun Z => by
      have h : IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app
          ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj Z)) :=
        (HomotopyCategory.Plus.localizerMorphism_derives
            ((Scheme.Modules.pushforward f).mapHomotopyCategoryPlus ⋙
              DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit Z
      exact @Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Plus.ι _ h)

omit [QuasiCompact f] [QuasiSeparated f] in
/-- `D⁺(𝒪_X) ⥤ D(𝒪_X)` followed by `Rf_*` is a right derived functor of degreewise `f_*` on
`K⁺(𝒪_X)`: a bounded below complex of injective modules is K-injective, and K-injective complexes
compute `Rf_*`. -/
public theorem isRightDerivedFunctor_plusPushforwardUnitBig :
    (DerivedCategory.Plus.ι ⋙ derivedPushforwardModules f).IsRightDerivedFunctor
      (plusPushforwardUnitBig f) (HomotopyCategory.Plus.quasiIso X.Modules) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (plusPushforwardToDerived f)).isRightDerivedFunctor_of_isIso
    (plusPushforwardUnitBig f) (fun Z => by
      obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff
        ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj Z).obj.as).1
        ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj Z).2
      have := hn
      have hKI : CochainComplex.IsKInjective
          ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj Z).obj.as :=
        CochainComplex.isKInjective_of_injective _ n
      have hI : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
          IsIso ((derivedPushforwardModulesUnit f).app
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) :=
        fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI
      exact hI _ hKI)

/-- **`Rf_*` on bounded below objects is the bounded below derived direct image**: for a
quasi-compact and quasi-separated `f`, the bounded below right derived functor `Rf_*^+` of `f_*`
followed by `D⁺(𝒪_Y) ⥤ D(𝒪_Y)` is isomorphic to `D⁺(𝒪_X) ⥤ D(𝒪_X)` followed by `Rf_*`. Both are
right derived functors of degreewise `f_*` on `K⁺(𝒪_X)`, since bounded below complexes of
injective modules are K-injective, and the isomorphism is the uniqueness of right derived
functors. -/
public def derivedPushforwardModulesPlusIso :
    (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ derivedPushforwardModules f :=
  have := isRightDerivedFunctor_plusPushforwardUnitPlus f
  have := isRightDerivedFunctor_plusPushforwardUnitBig f
  Functor.rightDerivedUnique _ _ (plusPushforwardUnitPlus f) (plusPushforwardUnitBig f)
    (HomotopyCategory.Plus.quasiIso X.Modules)

end PlusComparison

/-- **`H^q(Rf_*(M[-p])) ≅ R^{q-p} f_* M`, naturally in `M`.** For a quasi-compact and
quasi-separated morphism `f : X ⟶ Y` and integers `p` and `q`, the `q`-th cohomology sheaf of the
derived direct image of an `𝒪_X`-module `M` placed in degree `p` is the higher direct image
`R^{q-p} f_* M`. The complex `M[-p]` is the shift by `-p` of `M` placed in degree `0`, `Rf_*`
commutes with shifts, and on bounded below objects `Rf_*` is the bounded below derived direct
image, whose cohomology on `M` placed in degree `0` is the higher direct image. -/
public def homologyDerivedPushforwardSingleIso [QuasiCompact f] [QuasiSeparated f] (p q : ℤ) :
    DerivedCategory.singleFunctor X.Modules p ⋙ derivedPushforwardModules f ⋙
      DerivedCategory.homologyFunctor Y.Modules q ≅
      (Scheme.Modules.pushforward f).rightDerivedPlus (q - p) :=
  Functor.isoWhiskerRight ((DerivedCategory.singleFunctors X.Modules).shiftIso (-p) p 0
      (by omega)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((derivedPushforwardModules f).commShiftIso (-p)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((DerivedCategory.homologyFunctor Y.Modules 0).shiftIso (-p) q
        (q - p) (by omega))) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso X.Modules 0).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (derivedPushforwardModulesPlusIso f).symm _ ≪≫
      Functor.associator _ _ _)

end AlgebraicGeometry

end
