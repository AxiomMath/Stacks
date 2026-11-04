module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedPushforwardPerfect
public import StacksFrontier.CategoryTheory.Triangulated.SupportedGlue
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps

/-!
# The étale derived direct image and supports on an elementary distinguished square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` and `P = U ×_X V`. This file defines the derived direct image `Rf_*` along a morphism of
algebraic spaces and proves that an object of `D(𝒪_V)` vanishing on `P` is supported on the
preimage of `|X| \ |U|`.

## Main definitions

* `AlgebraicGeometry.Space.etaleDerivedPushforward`: the unbounded derived direct image `Rf_*`
  along a morphism of algebraic spaces, the total right derived functor of `f_*`.
* `AlgebraicGeometry.Space.etaleDerivedPushforwardAdjunction`: for `f` étale, derived restriction
  `(-)|_X` is left adjoint to `Rf_*`.

## Main results

* `AlgebraicGeometry.Space.cohomologySupportedOn_of_isZero_edsDerivedRestrictSnd`: an object of
  `D(𝒪_V)` vanishing on `U ×_X V` is supported on `j⁻¹(|X| \ |U|)`.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}

/-- The unbounded derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` along a morphism of algebraic
spaces: the total right derived functor of the degreewise direct image. -/
noncomputable abbrev etaleDerivedPushforward (f : X ⟶ Y) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) :=
  haveI := hasRightDerivedFunctor_modulePushforward B S hS f
  ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))

/-- For an étale morphism `f`, derived restriction along `f` is left adjoint to the derived
direct image `Rf_*`. -/
noncomputable def etaleDerivedPushforwardAdjunction (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ⊣
      etaleDerivedPushforward B S hS f :=
  haveI := hasRightDerivedFunctor_modulePushforward B S hS f
  Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
    (etaleModulePullbackAdjunction B S hS f hf) _
    (((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_modules B S hS X.1 X.2)

end Pushforward

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The points of `V` lying over `U` are the points of `U ×_X V`. -/
theorem preimage_range_pointsMap_edsEtaleHom :
    pointsMap B S hS V fV ⁻¹' Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) =
      Set.range (pointsMap B S hS (edsInter B S hS hsq).1 (edsSnd B S hS hsq).hom) := by
  rw [← Set.image_univ, preimage_image_pointsMap_of_isPullback B S hS
    (IsPullback.of_hasPullback Uo.ι fV) Set.univ, Set.preimage_univ, Set.image_univ]
  rfl

/-- An object of `D(𝒪_V)` whose restriction to `U ×_X V` vanishes is supported on `j⁻¹T`, where
`T = |X| \ |U|`. -/
theorem cohomologySupportedOn_of_isZero_edsDerivedRestrictSnd
    (M : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hM : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)).mapDerivedCategory.obj M)) :
    CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) M := by
  intro n x hx hxU
  have hxU' : x ∈ pointsMap B S hS V fV ⁻¹' Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) :=
    hxU
  rw [preimage_range_pointsMap_edsEtaleHom B S hS hsq] at hxU'
  obtain ⟨p, rfl⟩ := hxU'
  have hj := isEtale_edsSnd B S hS hsq
  have hH : IsZero ((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) hj).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) n).obj M)) :=
    IsZero.of_iso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsInter B S hS hsq).1
        (edsInter B S hS hsq).2) n).map_isZero hM)
      (((etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) hj).mapDerivedCategoryHomologyIso
        n).app _).symm
  have hsupp := supportOfSheaf_toSheaf_etaleModulePullback B S hS (edsSnd B S hS hsq) hj
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) n).obj M)
  rw [(supportOfSheaf_eq_empty_iff_isZero B S hS (edsInter B S hS hsq) _).2 hH] at hsupp
  have : p ∈ pointsMap B S hS (edsInter B S hS hsq).1 (edsSnd B S hS hsq).hom ⁻¹'
      supportOfSheaf B S hS (edsEtale B S hS hsq).1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2) n).obj M)) := hx
  rw [← hsupp] at this
  exact this

end Square

end AlgebraicGeometry.Space

end
