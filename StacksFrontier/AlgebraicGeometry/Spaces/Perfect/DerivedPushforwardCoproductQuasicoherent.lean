module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardCoproductInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts

/-!
# Direct sums in `D_QCoh` and derived direct images: reduction to affine étale objects

Let `x : X ⟶ Z` be a morphism of algebraic spaces over a scheme `S` with `X` quasi-compact and
quasi-separated, and let `G : D(𝒪_Z) ⥤ 𝒯` be exact. This file specializes the induction of
`AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_affine` to families of
objects with quasi-coherent cohomology: `G ∘ Rx_*` commutes with their direct sums as soon as it
does on every affine `Y` étale over `X`. This is the reduction step of [Stacks, Tag 08FB].

## Main results

* `AlgebraicGeometry.Space.isIso_sigmaComparison_etaleModulePullback_mapDerivedCategory`: étale
  restriction commutes with direct sums in the derived category.
* `AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_affine_quasicoherent`: the
  reduction; stability of `D_QCoh` under étale restriction is Stacks 08F4.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The localization functor of `𝒪_Y`-modules preserves direct sums indexed in the universe of
the schemes (Stacks 07D9). -/
theorem preservesColimitsOfShape_discrete_derivedCategoryQ_modules (Y : AlgebraicSpaces B S hS)
    (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := Modules.{u, u} B S hS Y.1 Y.2)) :=
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  CochainComplex.KFlat.CoproductBridge.derivedCategory_Q_preservesCoproductsOfShape _
    ⟨inferInstance, fun _ => ⟨inferInstance, inferInstance⟩⟩ J

/-- `D(𝒪_Y)` has direct sums indexed in the universe of the schemes (Stacks 07D9). -/
theorem hasCoproducts_derivedCategory_modules (Y : AlgebraicSpaces B S hS) :
    HasCoproducts.{u} (DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) := fun J => by
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  have := preservesColimitsOfShape_discrete_derivedCategoryQ_modules B S hS Y J
  refine ⟨fun F => ?_⟩
  let K : Discrete J ⥤ CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ :=
    Discrete.functor fun j => DerivedCategory.Q.objPreimage (F.obj ⟨j⟩)
  exact hasColimit_of_iso (F := K ⋙ DerivedCategory.Q)
    (Discrete.natIso fun j => (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm)

attribute [local instance] hasCoproducts_derivedCategory_modules

section Quasicoherent

/-- **Étale restriction commutes with direct sums in the derived category**: for an étale
`e : Y ⟶ W` the functor `D(𝒪_W) ⥤ D(𝒪_Y)` induced by the exact restriction `e^*` preserves the
direct sum of any family indexed in the universe of the schemes. -/
theorem isIso_sigmaComparison_etaleModulePullback_mapDerivedCategory
    {Y W : AlgebraicSpaces B S hS} (e : Y ⟶ W) (he : IsEtale B S hS e.hom) {J : Type u}
    (K : J → DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    IsIso (sigmaComparison (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory K) := by
  have := isGrothendieckAbelian_modules B S hS W.1 W.2
  have := preservesColimitsOfShape_discrete_derivedCategoryQ_modules B S hS W J
  have := preservesColimitsOfShape_discrete_derivedCategoryQ_modules B S hS Y J
  have := preservesColimitsOfSize_etaleModulePullback B S hS e he
  have : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q ⋙ (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso
      (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategoryFactors).2 inferInstance
  have := preservesColimitsOfShape_discrete_of_essSurj_comp DerivedCategory.Q
    (etaleModulePullback.{u, u} B S hS e he).mapDerivedCategory J
  exact isIso_sigmaComparison_of_preservesColimit _ K inferInstance

/-- **Direct sums of complexes with quasi-coherent cohomology and derived direct images, by
induction on quasi-compact quasi-separated étale objects.** Let `x : X ⟶ Z` with `X`
quasi-compact and quasi-separated and `G : D(𝒪_Z) ⥤ 𝒯` exact. If for every affine `Y` étale
over `X` along `y`, and every right derived functor `R` of `(y ≫ x)_*`, the functor `G ∘ R`
commutes with direct sums of families in `D_QCoh(𝒪_Y)`, then so does `G ∘ R` for every right
derived functor `R` of `x_*`, on families in `D_QCoh(𝒪_X)`. -/
theorem isIso_sigmaComparison_derivedPushforward_of_affine_quasicoherent
    {T : Type*} [Category T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] (J : Type u)
    [HasCoproductsOfShape J T] (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Z : AlgebraicSpaces B S hS} (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (x : X ⟶ Z)
    (G : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ T) [G.Additive]
    [G.CommShift ℤ] [G.IsTriangulated]
    (haff : ∀ (Y : AlgebraicSpaces B S hS) (y : Y ⟶ X), IsEtale B S hS y.hom →
      IsAffineSpace B S hS Y.1 → ∀ K : J → DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      (∀ j, DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
        (K j)) →
      ∀ (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
          DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
        (α : (modulePushforward B S hS (y ≫ x)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor α
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) →
        IsIso (sigmaComparison (R ⋙ G) K))
    (K : J → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ j, DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
        (K j))
    (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (α : (modulePushforward B S hS x).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    IsIso (sigmaComparison (R ⋙ G) K) :=
  isIso_sigmaComparison_derivedPushforward_of_affine B S hS J hZ hXqc hXqs x G
    (fun Y K => ∀ j, DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
        (K j))
    (fun e he K hK j => derivedQuasicoherent_etaleModulePullback B S hS e he (K j) (hK j))
    (fun e he K _ => isIso_sigmaComparison_etaleModulePullback_mapDerivedCategory B S hS e he K)
    haff K hK R α

end Quasicoherent

end AlgebraicGeometry.Space

end
