module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsCoproductsAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition

/-!
# Cohomology of a quasi-compact quasi-separated algebraic space commutes with direct sums

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `RΓ` be a
right derived functor of the global sections `Γ(X, −) : Mod(𝒪_X) ⥤ Ab`. Then `RΓ` commutes with
direct sums of objects of `D_QCoh(𝒪_X)`. This is [Stacks, Tag 08FB] for the morphism from `X` to
a point (the direct image to a point being global sections), and it is the input of
[Stacks, Tag 08IN] in the proof of [Stacks, Tag 0D3F].

The proof is the source's induction:
`AlgebraicGeometry.Space.isIso_sigmaComparison_derivedPushforward_of_affine_quasicoherent`
(the induction principle of Stacks 08GP run along the relative Mayer–Vietoris triangles of
Stacks 08JK) reduces it to `RΓ(X, y_* −)` for affine `Y` étale over `X`, which is
`Space.isIso_sigmaComparison_rightDerived_pushforwardGlobalSections_of_isAffineSpace`;
that a composite `RΓ ∘ Ry_*` is a right derived functor of `Γ(X, y_* −)` holds because `y_*` has an
exact left adjoint, so preserves K-injective complexes.

## Main results

* `AlgebraicGeometry.Space.isRightDerivedFunctor_comp_derivedPushforward`: `RΓ ∘ Ry_*` is a right
  derived functor of `Γ(X, y_* −)`, for `y` étale.
* `AlgebraicGeometry.Space.isIso_sigmaComparison_rightDerived_baseRingGlobalSections`: the
  direct-sum statement.

## References

* [Stacks Project, Tag 08FB](https://stacks.math.columbia.edu/tag/08FB)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unit exhibiting `Rw ∘ Ry_*` as a right derived functor of `y_* ⋙ w`: the unit of `Rw`
at the image of `y_*`, followed by `Rw` applied to the unit of `Ry_*`. -/
def pushforwardCompRightDerivedUnit {Y Z : AlgebraicSpaces B S hS} (y : Y ⟶ Z) {T : Type*}
    [Category* T] [Abelian T] (w : Modules.{u, u} B S hS Z.1 Z.2 ⥤ T) [w.Additive]
    (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αR : (modulePushforward B S hS y).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (Rw : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ DerivedCategory T)
    (αw : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw) :
    (modulePushforward B S hS y ⋙ w).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ (R ⋙ Rw) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (modulePushforward B S hS y ⋙ w))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePushforward B S hS y).mapHomotopyCategory (ComplexShape.up ℤ))
      αw ≫
    Functor.whiskerRight αR Rw

/-- **A right derived functor of `w` after one of `y_*` is one of `y_* ⋙ w`**, for `y` étale:
the unit is invertible at every K-injective complex `I`, because `y_* I` is K-injective (`y_*`
has the exact left adjoint `y^*`, Stacks 08BJ). -/
theorem isRightDerivedFunctor_comp_derivedPushforward {Y Z : AlgebraicSpaces B S hS} (y : Y ⟶ Z)
    (hy : IsEtale B S hS y.hom) {T : Type*} [Category* T] [Abelian T]
    (w : Modules.{u, u} B S hS Z.1 Z.2 ⥤ T) [w.Additive]
    (R : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (αR : (modulePushforward B S hS y).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (Rw : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤ DerivedCategory T)
    (αw : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw)
    [Rw.IsRightDerivedFunctor αw
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))] :
    (R ⋙ Rw).IsRightDerivedFunctor (pushforwardCompRightDerivedUnit B S hS y w R αR Rw αw)
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Y.1 Y.2) :=
    isGrothendieckAbelian_modules B S hS Y.1 Y.2
  refine Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ DerivedCategory.Qh (R ⋙ Rw) _ fun I hI ↦ ?_
  have hR : IsIso (αR.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((modulePushforward B S hS y).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)).2
          DerivedCategory.Qh R αR I hI
  have hyI : CochainComplex.IsKInjective
      (((modulePushforward B S hS y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact (modulePushforward B S hS y)
      (etaleModulePullback.{u, u} B S hS y hy) (etaleModulePullbackAdjunction B S hS y hy) I
  have hw : IsIso (αw.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((modulePushforward B S hS y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2)).2
        DerivedCategory.Qh Rw αw _ hyI
  dsimp only [pushforwardCompRightDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  have : IsIso (αw.app (((modulePushforward B S hS y).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := hw
  infer_instance

/-- The direct image along the identity, on homotopy categories, followed by the localization,
is the localization. -/
def pushforwardIdMapHomotopyCategoryIso (X : AlgebraicSpaces B S hS) :
    (modulePushforward B S hS (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ≅ DerivedCategory.Qh ⋙ 𝟭 _ :=
  Functor.isoWhiskerRight
    ({ hom := NatTrans.mapHomotopyCategory (modulePushforwardIdIso B S hS X).hom _
       inv := NatTrans.mapHomotopyCategory (modulePushforwardIdIso B S hS X).inv _
       hom_inv_id := by
         rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
           NatTrans.mapHomotopyCategory_id]
       inv_hom_id := by
         rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
           NatTrans.mapHomotopyCategory_id] } ≪≫
      Functor.mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- **Stacks 08FB for the morphism from a quasi-compact quasi-separated algebraic space to a
point.** Let `X` be a quasi-compact and quasi-separated algebraic space over `S`, and let `RΓ` be
a right derived functor of the global sections `Γ(X, −) : Mod(𝒪_X) ⥤ Ab` (read on the model of
the small étale site through any ring map `φ : R →+* Γ(X, 𝒪_X)`). Then `RΓ` commutes with the
direct sum of every family of objects of `D(𝒪_X)` with quasi-coherent cohomology. -/
theorem isIso_sigmaComparison_rightDerived_baseRingGlobalSections
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)
    (RΓ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : (baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    {J : Type u} (K : J → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ j, qcohDerivedProp B S hS X (K j)) :
    IsIso (sigmaComparison RΓ K) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  let _ := Functor.IsRightDerivedFunctor.commShift RΓ α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : RΓ.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor _ RΓ α
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    AddCommGrpCat.{u} J
  have : (𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))).IsRightDerivedFunctor
      (pushforwardIdMapHomotopyCategoryIso B S hS X).hom
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
      _ DerivedCategory.Qh _ _ fun _ _ ↦ inferInstance
  exact isIso_sigmaComparison_derivedPushforward_of_affine_quasicoherent B S hS J hZ hXqc hXqs
    (𝟙 X) RΓ
    (fun Y y hy hY K hK R αR _ ↦
      have := isRightDerivedFunctor_comp_derivedPushforward B S hS (y ≫ 𝟙 X)
        (by simpa using hy) (baseRingGlobalSectionsAddCommGrp B S hS X φ) R αR RΓ α
      isIso_sigmaComparison_rightDerived_pushforwardGlobalSections_of_isAffineSpace B S hS
        (y ≫ 𝟙 X) φ hY (R ⋙ RΓ)
        (pushforwardCompRightDerivedUnit B S hS (y ≫ 𝟙 X)
          (baseRingGlobalSectionsAddCommGrp B S hS X φ) R αR RΓ α) K hK)
    K hK (𝟭 _) (pushforwardIdMapHomotopyCategoryIso B S hS X).hom

end AlgebraicGeometry.Space

end
