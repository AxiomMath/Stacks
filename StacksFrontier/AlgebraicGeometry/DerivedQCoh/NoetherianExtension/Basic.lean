module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.SectionExtension
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Grothendieck
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasquePushforwardVanishing
public import StacksCore.Tactic.StacksAttribute

/-!
# The right derived extension of direct image on quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of Noetherian schemes. Direct image preserves quasi-coherence, so
it restricts to a functor `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. The category `QCoh(𝒪_X)` is
Grothendieck abelian, so every complex of quasi-coherent modules admits a K-injective
resolution and `f_*` has a total right derived functor
`Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`.

[Stacks, Tag 09T3] asserts in addition that `Φ` is compatible with the derived direct image of
all modules: the square whose horizontal arrows are `Φ` and `Rf_*`, and whose vertical arrows
are the comparison functors `D(QCoh(𝒪_•)) ⥤ D_QCoh(𝒪_•)` of [Stacks, Tag 06VT], commutes.

Commutativity is the canonical identification of two right derived functors of one functor.
Both composites of the square derive `K(QCoh(𝒪_X)) ⥤ D(𝒪_Y)`, termwise direct image followed
by forgetting quasi-coherence: the composite through `Rf_*` because its derivation unit is
invertible on complexes of injective quasi-coherent modules — those are flasque by
[Stacks, Tag 09T2], hence acyclic for `f_*` by [Stacks, Tag 09T0], so [Stacks, Tag 0G9N]
applies — and the composite through `Φ` because the derivation unit of `Φ` is invertible on
K-injective complexes. A natural transformation on `D(QCoh(𝒪_X))` which is invertible at the
complexes with injective terms is invertible at every K-injective complex, since a
quasi-isomorphism between K-injective complexes is a homotopy equivalence. The two right
derived functors are then identified by `CategoryTheory.Functor.rightDerivedUnique`.

## Main definitions

* `AlgebraicGeometry.noetherianPushforwardExtension`: the right derived extension `Φ`.
* `AlgebraicGeometry.noetherianPushforwardExtensionUnit`: its derivation unit.
* `AlgebraicGeometry.noetherianPushforwardExtensionComparison`: the commuting square, as a
  natural isomorphism.

## Main results

* `AlgebraicGeometry.noetherianPushforwardExtension_isRightDerivedFunctor`: `Φ` is a total
  right derived functor of direct image on quasi-coherent modules.
* `AlgebraicGeometry.rightAcyclic_pushforward_of_isFlasque`: a flasque sheaf of modules is
  right acyclic for direct image, along any morphism of schemes.
* `AlgebraicGeometry.rightAcyclic_pushforward_of_injective_quasicoherent`: an injective
  quasi-coherent module on a Noetherian scheme is right acyclic for direct image.

## Implementation notes

The square is stated after the fully faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, so that the
derived direct image may be an arbitrary right derived functor of direct image on *all*
modules rather than one already known to restrict to the complexes with quasi-coherent
cohomology. That inclusion being fully faithful, this is the same assertion as the
commutativity of the square drawn in the source.

The square is a natural isomorphism as data, built as the canonical comparison of two right
derived functors; its existence is not merely asserted. It cannot be an equality: the derived
direct image enters as an arbitrary model, and the two composites are built out of it by
different routes.

`CategoryTheory.HasDerivedCategory.standard` is installed with a raised priority for the reason
recorded in `StacksFrontier/AlgebraicGeometry/DerivedAcyclic/Pushforward.lean`: the import closure
carries the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a
global instance, and with the two in play at equal priority instance search no longer resolves
`HasDerivedCategory.{u + 1} X.Modules`. [Stacks, Tag 0G9N] is stated in the standard model, so
that is the model here.

The category of `𝒪_X`-modules has two definitionally equal but syntactically distinct
spellings, `AlgebraicGeometry.Scheme.Modules X` and `SheafOfModules X.ringCatSheaf`. Instance
search does not cross the two, so the construction of the square names the inclusion of
quasi-coherent modules at the first spelling, with its exactness and additivity supplied there.

## References

* [Stacks Project, Tag 09T3](https://stacks.math.columbia.edu/tag/09T3)
* [Stacks Project, Tag 09T2](https://stacks.math.columbia.edu/tag/09T2)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived (derivedQuasicoherentComparison
  derivedQuasicoherentComparisonCompι)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- Every complex of quasi-coherent modules on a scheme admits a quasi-isomorphism to a
K-injective complex of quasi-coherent modules. -/
theorem exists_quasiIso_isKInjective_quasicoherentModules (X : Scheme.{u})
    (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ) :
    ∃ (I : CochainComplex (Scheme.QuasicoherentModules X) ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor _).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion _).app K, inferInstance, inferInstance⟩

/-- Termwise pushforward of complexes of quasi-coherent modules, followed by the localization
to the derived category of the target. -/
abbrev quasicoherentPushforwardToDerivedCategory {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    HomotopyCategory (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y) :=
  (quasicoherentPushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Termwise direct image of quasi-coherent modules has a pointwise right derived functor:
`QCoh(𝒪_X)` is Grothendieck abelian, so every complex has a K-injective resolution. -/
instance quasicoherentPushforwardToDerivedCategory_hasPointwiseRightDerivedFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (quasicoherentPushforwardToDerivedCategory f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1}
    (quasicoherentPushforwardToDerivedCategory f)
    (exists_quasiIso_isKInjective_quasicoherentModules X)).1

/-- The right derived extension `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` of direct image on
quasi-coherent modules, for a morphism of Noetherian schemes: the total right derived functor
of termwise direct image.

This is the functor of [Stacks, Tag 09T3]; the compatibility with derived direct image that
the source asserts of it is
`AlgebraicGeometry.noetherianPushforwardExtensionComparison`. -/
@[stacks 09T3]
def noetherianPushforwardExtension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] :
    DerivedCategory (Scheme.QuasicoherentModules X) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Y) :=
  (quasicoherentPushforwardToDerivedCategory f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))

/-- The derivation unit of `AlgebraicGeometry.noetherianPushforwardExtension`: the canonical
comparison from termwise direct image of complexes of quasi-coherent modules to the right
derived extension. -/
def noetherianPushforwardExtensionUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] :
    quasicoherentPushforwardToDerivedCategory f ⟶
      DerivedCategory.Qh ⋙ noetherianPushforwardExtension f :=
  (quasicoherentPushforwardToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.noetherianPushforwardExtension` is a total right derived functor of
direct image on quasi-coherent modules, with
`AlgebraicGeometry.noetherianPushforwardExtensionUnit` as its derivation unit. -/
@[stacks 09T3]
instance noetherianPushforwardExtension_isRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] :
    (noetherianPushforwardExtension f).IsRightDerivedFunctor
      (noetherianPushforwardExtensionUnit f)
      (HomotopyCategory.quasiIso (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor
    ((quasicoherentPushforwardToDerivedCategory f).totalRightDerived DerivedCategory.Qh _)
    ((quasicoherentPushforwardToDerivedCategory f).totalRightDerivedUnit
      DerivedCategory.Qh _) _)

/-- **A flasque sheaf of modules on a scheme is right acyclic for direct image.** Direct image
is left exact, and the positive higher direct images of a flasque sheaf of modules vanish by
[Stacks, Tag 09T0], so the acyclicity criterion [Stacks, Tag 015C] applies.

[Stacks, Tag 09T0] is stated for a morphism of ringed spaces; this is the same statement read
for the underlying morphism of the ringed spaces of two schemes. -/
theorem rightAcyclic_pushforward_of_isFlasque {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)] :
    (Scheme.Modules.pushforward f).rightAcyclic M := by
  have hfin : PreservesFiniteLimits (Scheme.Modules.pushforward f) := inferInstance
  refine (((Scheme.Modules.pushforward f).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    M).2 hfin).mpr fun i hi => ?_
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf
      (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)).obj M) :=
    inferInstanceAs (TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
  change IsZero (((RingedSpaceModuleAdjunction.modulePushforward
    (X := X.toLocallyRingedSpace.toRingedSpace) (Y := Y.toLocallyRingedSpace.toRingedSpace)
      f.toLRSHom.toShHom).rightDerivedPlus i).obj M)
  exact Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    f.toLRSHom.toShHom M i hi

/-- An injective object of the category of quasi-coherent modules on a Noetherian scheme is
right acyclic for direct image along any morphism of schemes: such an object is flasque by
[Stacks, Tag 09T2], and a flasque sheaf of modules is right acyclic for direct image. -/
theorem rightAcyclic_pushforward_of_injective_quasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] (J : Scheme.QuasicoherentModules X) [Injective J] :
    (Scheme.Modules.pushforward f).rightAcyclic J.obj :=
  have := isFlasque_of_injective_quasicoherent X J
  rightAcyclic_pushforward_of_isFlasque f J.obj

/-- A natural transformation of functors on the homotopy category of complexes of
quasi-coherent modules is invertible at every K-injective complex as soon as it is invertible
at the complexes with injective terms. -/
theorem isIso_app_quotient_of_isKInjective_of_termwise_injective {X : Scheme.{u}}
    {H : Type*} [Category* H]
    {F₁ F₂ : HomotopyCategory (Scheme.QuasicoherentModules X) (ComplexShape.up ℤ) ⥤ H}
    (τ : F₁ ⟶ F₂)
    (hτ : ∀ K : CochainComplex (Scheme.QuasicoherentModules X) ℤ, (∀ n, Injective (K.X n)) →
      IsIso (τ.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (I : CochainComplex (Scheme.QuasicoherentModules X) ℤ) (hI : I.IsKInjective) :
    IsIso (τ.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have : ((𝟭 (CochainComplex (Scheme.QuasicoherentModules X) ℤ)).obj I).IsKInjective := hI
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion _).app I
  have : IsIso ((HomotopyCategory.quotient (Scheme.QuasicoherentModules X)
      (ComplexShape.up ℤ)).map ι) :=
    HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _
      ((CochainComplex.IsKInjective.quasiIso_iff ι).1 inferInstance)
  exact (τ.isIso_app_iff_of_iso (asIso ((HomotopyCategory.quotient _ _).map ι))).2
    (hτ _ fun _ => inferInstance)

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y]
  (RF : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
  (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

omit [IsNoetherian Y] in
/-- The derivation unit of a right derived direct image is invertible at a complex of
quasi-coherent modules with injective terms: such a complex is termwise quasi-coherent and
termwise right acyclic for direct image, so [Stacks, Tag 0G9N] applies. -/
theorem isIso_rightDerivedUnit_app_of_termwise_injective_quasicoherent
    (K : CochainComplex (Scheme.QuasicoherentModules X) ℤ) (hK : ∀ n, Injective (K.X n)) :
    IsIso (α.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj
      (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))) :=
  isIso_to_rightDerived_of_termwise_acyclic f _ (fun n => (K.X n).2)
    (fun n => have := hK n
      rightAcyclic_pushforward_of_injective_quasicoherent f (K.X n)) RF α

/-- **The commuting square of [Stacks, Tag 09T3].** For a morphism of Noetherian schemes the
derived extension of direct image on quasi-coherent modules agrees, under the comparison
functors `D(QCoh(𝒪_•)) ⥤ D_QCoh(𝒪_•)`, with any right derived direct image of all modules.

The isomorphism is the canonical one: both composites are right derived functors of the single
functor `K(QCoh(𝒪_X)) ⥤ D(𝒪_Y)` given by termwise direct image followed by forgetting
quasi-coherence, so they are identified by the uniqueness of right derived functors. -/
@[stacks 09T3]
def noetherianPushforwardExtensionComparison :
    derivedQuasicoherentComparison X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RF ≅
      noetherianPushforwardExtension f ⋙ derivedQuasicoherentComparison Y ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let Q := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let C := Scheme.QuasicoherentModules X
  let D := Scheme.QuasicoherentModules Y
  let I : C ⥤ X.Modules := P.ι
  let J : D ⥤ Y.Modules := Q.ι
  let F : C ⥤ D := quasicoherentPushforward f
  let G : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  let : I.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
  let : J.Additive := CategoryTheory.Functor.fullSubcategoryInclusion_additive _
  let : PreservesFiniteLimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits X
  let : PreservesFiniteColimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits X
  let : PreservesFiniteLimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits Y
  let : PreservesFiniteColimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits Y
  let : F.Additive := quasicoherentPushforward_additive f
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso C c
  let QC := DerivedCategory.Qh (C := C)
  let QD := DerivedCategory.Qh (C := D)
  let QX := DerivedCategory.Qh (C := X.Modules)
  let QY := DerivedCategory.Qh (C := Y.Modules)
  let FH := F.mapHomotopyCategory c
  let JH := J.mapHomotopyCategory c
  let IH := I.mapHomotopyCategory c
  let GH := G.mapHomotopyCategory c
  let Φ := noetherianPushforwardExtension f
  let η := noetherianPushforwardExtensionUnit f
  let L : DerivedCategory C ⥤ DerivedCategory Y.Modules := I.mapDerivedCategory ⋙ RF
  let R : DerivedCategory C ⥤ DerivedCategory Y.Modules := Φ ⋙ J.mapDerivedCategory
  let eSourceHC : FH ⋙ JH ≅ IH ⋙ GH :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ J)) c ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ G)) c).symm
  let αL : (FH ⋙ JH) ⋙ QY ⟶ QC ⋙ L :=
    (Functor.isoWhiskerRight eSourceHC QY).hom ≫
      (Functor.associator IH GH QY).hom ≫
      Functor.whiskerLeft IH α ≫
      (Functor.associator IH QX RF).inv ≫
      Functor.whiskerRight I.mapDerivedCategoryFactorsh.inv RF ≫
      (Functor.associator QC I.mapDerivedCategory RF).hom
  let αR : (FH ⋙ JH) ⋙ QY ⟶ QC ⋙ R :=
    (Functor.associator FH JH QY).hom ≫
      Functor.whiskerLeft FH J.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator FH QD J.mapDerivedCategory).inv ≫
      Functor.whiskerRight η J.mapDerivedCategory ≫
      (Functor.associator QC Φ J.mapDerivedCategory).hom
  have hαL : ∀ K : CochainComplex C ℤ, K.IsKInjective →
      IsIso (αL.app ((HomotopyCategory.quotient C c).obj K)) := by
    intro K₀ hK₀
    refine isIso_app_quotient_of_isKInjective_of_termwise_injective αL ?_ K₀ hK₀
    intro K hK
    have : IsIso (α.app (IH.obj ((HomotopyCategory.quotient C c).obj K))) :=
      (α.isIso_app_iff_of_iso ((Functor.mapHomotopyCategoryFactors I c).app K)).2
        (isIso_rightDerivedUnit_app_of_termwise_injective_quasicoherent f RF α K hK)
    dsimp [αL]
    infer_instance
  have hαR : ∀ K : CochainComplex C ℤ, K.IsKInjective →
      IsIso (αR.app ((HomotopyCategory.quotient C c).obj K)) := by
    intro K hK
    have : IsIso (η.app ((HomotopyCategory.quotient C c).obj K)) :=
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
          u, u + 1, u + 1, u + 1, u + 1, u + 1}
        (quasicoherentPushforwardToDerivedCategory f)
        (exists_quasiIso_isKInjective_quasicoherentModules X)).2
          DerivedCategory.Qh Φ η K hK
    dsimp [αR]
    infer_instance
  let : L.IsRightDerivedFunctor αL W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      (exists_quasiIso_isKInjective_quasicoherentModules X) _ L αL hαL
  let : R.IsRightDerivedFunctor αR W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      (exists_quasiIso_isKInjective_quasicoherentModules X) _ R αR hαR
  exact Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι X) RF ≪≫
    Functor.rightDerivedUnique L R αL αR W ≪≫
    (Functor.isoWhiskerLeft Φ (derivedQuasicoherentComparisonCompι Y)).symm

end Comparison

end AlgebraicGeometry

end
