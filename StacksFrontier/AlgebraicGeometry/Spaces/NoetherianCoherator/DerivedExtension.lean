module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# The right derived extension of the direct image on quasi-coherent modules

Let `f : X ⟶ Y` be a morphism of algebraic spaces whose direct image preserves
quasi-coherence.  The category `QCoh(𝒪_X)` is Grothendieck abelian (Stacks 077V), so every
complex of quasi-coherent modules has a K-injective resolution (Stacks 079P), and the direct image
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` has a total right derived functor
`Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`.

This file builds `Φ`, and reduces the commutativity of the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶^{Rf_*} D(𝒪_Y)`,
`D(QCoh(𝒪_X)) ⟶^{Φ} D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y) ⟶ D(𝒪_Y)`

to the invertibility of the comparison `f_* I ⟶ Rf_* I` at complexes `I` of quasi-coherent modules
with injective terms.  Both composites of the square are then right derived functors of the one
functor `K(QCoh(𝒪_X)) ⥤ D(𝒪_Y)` given by termwise direct image followed by forgetting
quasi-coherence, and they are identified by the uniqueness of right derived functors.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentPushforwardExtension`: the right derived extension `Φ`.
* `AlgebraicGeometry.Space.quasicoherentPushforwardExtensionUnit`: its derivation unit.
* `AlgebraicGeometry.Space.quasicoherentPushforwardExtensionComparison`: the square, as a natural
  isomorphism, given the invertibility of `f_* I ⟶ Rf_* I` on complexes with injective terms.

## Implementation notes

The square is stated after the fully faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, so that `Rf_*`
may be an arbitrary right derived functor of the direct image of all modules; this is the same
arrangement as `AlgebraicGeometry.Space.derivedQuasicoherentComparisonSquare`.  The comparison
functors are those of Stacks 08F1,
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse`, which is stated in the
standard model of the derived categories; that is why this file installs
`HasDerivedCategory.standard`, as the file of Stacks 08F1 does.

## References

* [Stacks Project, Tag 09TM](https://stacks.math.columbia.edu/tag/09TM)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every complex of quasi-coherent modules on an algebraic space admits a quasi-isomorphism to a
K-injective complex of quasi-coherent modules (Stacks 079P, `QCoh(𝒪_Z)` being Grothendieck
abelian by Stacks 077V). -/
theorem exists_quasiIso_isKInjective_quasicoherentSheaves (Z : AlgebraicSpaces B S hS)
    (K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ℤ) :
    ∃ (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ℤ) (q : K ⟶ I),
      I.IsKInjective ∧ QuasiIso q :=
  have := quasicoherentSheaves_isGrothendieckAbelian B S hS Z.1 Z.2
  Stacks.Injectives.exists_kInjective_resolution_of_grothendieck K

/-- A natural transformation of functors on the homotopy category of complexes of
quasi-coherent modules is invertible at every K-injective complex as soon as it is invertible at
the complexes with injective terms: a K-injective complex is homotopy equivalent to its chosen
K-injective resolution, whose terms are injective. -/
theorem isIso_app_quotient_quasicoherentSheaves_of_isKInjective_of_termwise_injective
    (Z : AlgebraicSpaces B S hS) {H : Type*} [Category* H]
    {F₁ F₂ : HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ) ⥤ H}
    (τ : F₁ ⟶ F₂)
    (hτ : ∀ K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ℤ,
      (∀ n, Injective (K.X n)) →
        IsIso (τ.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ℤ) (hI : I.IsKInjective) :
    IsIso (τ.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have := quasicoherentSheaves_isGrothendieckAbelian B S hS Z.1 Z.2
  have := hI
  have : ((𝟭 (CochainComplex (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ℤ)).obj I).IsKInjective :=
    hI
  have hq : IsIso ((HomotopyCategory.quotient (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2)
      (ComplexShape.up ℤ)).map
        ((Stacks.Injectives.kInjectiveResolutionInclusion _).app I)) :=
    HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _
      ((CochainComplex.IsKInjective.quasiIso_iff
        ((Stacks.Injectives.kInjectiveResolutionInclusion _).app I)).1 inferInstance)
  exact (τ.isIso_app_iff_of_iso (asIso ((HomotopyCategory.quotient _ _).map
    ((Stacks.Injectives.kInjectiveResolutionInclusion _).app I)))).2
      (hτ _ fun _ => inferInstance)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hpush : PushforwardPreservesQuasicoherence B S hS f)

/-- Termwise direct image of complexes of quasi-coherent modules, followed by the localization
to the derived category of the target. -/
abbrev quasicoherentPushforwardToDerivedCategory :
    HomotopyCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) :=
  (quasicoherentPushforward B S hS f hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- Termwise direct image of quasi-coherent modules has a pointwise right derived functor:
`QCoh(𝒪_X)` is Grothendieck abelian, so every complex has a K-injective resolution. -/
instance quasicoherentPushforwardToDerivedCategory_hasPointwiseRightDerivedFunctor :
    (quasicoherentPushforwardToDerivedCategory B S hS f hpush).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (quasicoherentPushforwardToDerivedCategory B S hS f hpush)
    (exists_quasiIso_isKInjective_quasicoherentSheaves B S hS X)).1

/-- The right derived extension `Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` of the direct image on
quasi-coherent modules: the total right derived functor of termwise direct image. -/
def quasicoherentPushforwardExtension :
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) :=
  (quasicoherentPushforwardToDerivedCategory B S hS f hpush).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- The derivation unit of `AlgebraicGeometry.Space.quasicoherentPushforwardExtension`. -/
def quasicoherentPushforwardExtensionUnit :
    quasicoherentPushforwardToDerivedCategory B S hS f hpush ⟶
      DerivedCategory.Qh ⋙ quasicoherentPushforwardExtension B S hS f hpush :=
  (quasicoherentPushforwardToDerivedCategory B S hS f hpush).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- `AlgebraicGeometry.Space.quasicoherentPushforwardExtension` is a total right derived functor
of the direct image on quasi-coherent modules, with derivation unit
`AlgebraicGeometry.Space.quasicoherentPushforwardExtensionUnit`. -/
instance quasicoherentPushforwardExtension_isRightDerivedFunctor :
    (quasicoherentPushforwardExtension B S hS f hpush).IsRightDerivedFunctor
      (quasicoherentPushforwardExtensionUnit B S hS f hpush)
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor
    ((quasicoherentPushforwardToDerivedCategory B S hS f hpush).totalRightDerived
      DerivedCategory.Qh _)
    ((quasicoherentPushforwardToDerivedCategory B S hS f hpush).totalRightDerivedUnit
      DerivedCategory.Qh _) _)

section Comparison

variable (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

/-- **The square of the derived extension, given that complexes with injective terms compute
the derived direct image.**  If the derivation unit `f_* K ⟶ Rf_* K` is invertible at every
complex `K` of quasi-coherent `𝒪_X`-modules whose terms are injective objects of `QCoh(𝒪_X)`,
then the comparison functors of Stacks 08F1 carry the derived extension `Φ` of
`f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` to `Rf_*`.

The isomorphism is the canonical one: both composites are right derived functors of the functor
`K(QCoh(𝒪_X)) ⥤ D(𝒪_Y)` given by termwise direct image followed by forgetting quasi-coherence. -/
def quasicoherentPushforwardExtensionComparison
    (hinj : ∀ K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ℤ,
      (∀ n, Injective (K.X n)) →
        IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
          (ComplexShape.up ℤ)).obj
            (((quasicoherentSheavesι B S hS X).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)))) :
    quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙ RF ≅
      quasicoherentPushforwardExtension B S hS f hpush ⋙
        quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι := by
  let C := QuasicoherentSheaves.{u, u} B S hS X.1 X.2
  let D := QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2
  let I : C ⥤ Modules.{u, u} B S hS X.1 X.2 := quasicoherentSheavesι B S hS X
  let J : D ⥤ Modules.{u, u} B S hS Y.1 Y.2 := quasicoherentSheavesι B S hS Y
  let F : C ⥤ D := quasicoherentPushforward B S hS f hpush
  let G := modulePushforward B S hS f
  let c := ComplexShape.up ℤ
  let W := HomotopyCategory.quasiIso C c
  let QC := DerivedCategory.Qh (C := C)
  let QD := DerivedCategory.Qh (C := D)
  let QX := DerivedCategory.Qh (C := Modules.{u, u} B S hS X.1 X.2)
  let QY := DerivedCategory.Qh (C := Modules.{u, u} B S hS Y.1 Y.2)
  let FH := F.mapHomotopyCategory c
  let JH := J.mapHomotopyCategory c
  let IH := I.mapHomotopyCategory c
  let GH := G.mapHomotopyCategory c
  let Φ := quasicoherentPushforwardExtension B S hS f hpush
  let η := quasicoherentPushforwardExtensionUnit B S hS f hpush
  let L : DerivedCategory C ⥤ DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
    I.mapDerivedCategory ⋙ RF
  let R : DerivedCategory C ⥤ DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
    Φ ⋙ J.mapDerivedCategory
  let eSourceHC : FH ⋙ JH ≅ IH ⋙ GH :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ J)) c ≪≫
      (Functor.mapHomotopyCategoryCompIso
        (quasicoherentPushforwardCompιIso B S hS f hpush).symm c).symm
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
    refine isIso_app_quotient_quasicoherentSheaves_of_isKInjective_of_termwise_injective
      B S hS X αL ?_ K₀ hK₀
    intro K hK
    have : IsIso (α.app (IH.obj ((HomotopyCategory.quotient C c).obj K))) :=
      (α.isIso_app_iff_of_iso ((Functor.mapHomotopyCategoryFactors I c).app K)).2 (hinj K hK)
    dsimp [αL]
    infer_instance
  have hαR : ∀ K : CochainComplex C ℤ, K.IsKInjective →
      IsIso (αR.app ((HomotopyCategory.quotient C c).obj K)) := by
    intro K hK
    have : IsIso (η.app ((HomotopyCategory.quotient C c).obj K)) :=
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
          u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (quasicoherentPushforwardToDerivedCategory B S hS f hpush)
        (exists_quasiIso_isKInjective_quasicoherentSheaves B S hS X)).2
          DerivedCategory.Qh Φ η K hK
    dsimp [αR]
    infer_instance
  let : L.IsRightDerivedFunctor αL W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      (exists_quasiIso_isKInjective_quasicoherentSheaves B S hS X) _ L αL hαL
  let : R.IsRightDerivedFunctor αR W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      (exists_quasiIso_isKInjective_quasicoherentSheaves B S hS X) _ R αR hαR
  exact Functor.isoWhiskerRight (quasicoherentDerivedComparisonCompιIso B S hS X.1 X.2) RF ≪≫
    Functor.rightDerivedUnique L R αL αR W ≪≫
    (Functor.isoWhiskerLeft Φ (quasicoherentDerivedComparisonCompιIso B S hS Y.1 Y.2)).symm

end Comparison

end AlgebraicGeometry.Space

end
