module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSmallModel
public import StacksFrontier.Deformation.AlgebraExtension.PushoutEquivalence
public import StacksFrontier.Deformation.AlgebraExtension.PushoutRestriction

/-!
# Pushout of square-zero extensions on a quasi-compact quasi-separated algebraic space

Let `f : X ⟶ B` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated, and
let `φ : ℱ ⟶ 𝒢` be a morphism of `𝒪_X`-modules with `DQ_X(φ)` an isomorphism, where `DQ_X` is the
right adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` of [Stacks Project, Tag 0CR4]. Then pushout along `φ`
is an equivalence between the categories of extensions `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` and
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_B`-algebras on `X_étale`, as soon as `NL_{X/B}` lies in
`D_QCoh(𝒪_X)`. This is [Stacks Project, Tag 0D3P], with the quasi-coherence of `NL_{X/B}`
(the quasi-coherence clause of [Stacks Project, Tag 0D0Y]) as its one input.

## The proof

The source's proof runs on a site whose objects, rings and modules share one universe, which is
`Deformation.AlgebraExtension.isEquivalence_pushoutFunctor_of_isIso_rightAdjoint_map`. The small
étale site of `X` has its objects in `Type (u + 1)`; it is replaced by its model
`AlgebraicGeometry.Space.smallEtaleModelRingedTopos` in `Type u`:

* restriction to the model is an equivalence of extension categories
  (`Deformation.AlgebraExtension.isEquivalence_siteRestriction`), and commutes with pushout
  (`Deformation.AlgebraExtension.IsPushoutFunctor.isEquivalence_of_restrict`);
* restriction of modules to the model is an equivalence (the Comparison Lemma,
  `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv`), hence so is the induced functor
  `Φ` of derived categories, and `Φ` carries the maps `Ext^i(NL, ℱ) ⟶ Ext^i(NL, 𝒢)` on the model
  to the maps `Ext^i(Φ NL, ℱ) ⟶ Ext^i(Φ NL, 𝒢)` on `X`;
* those are bijective because `Φ NL` lies in `D_QCoh(𝒪_X)` and `DQ_X(φ)` is an isomorphism
  (`ObjectProperty.bijective_comp_shift_map_of_isIso_rightAdjoint_map`).

`NL_{X/B}` enters as the naive cotangent complex of `f⁻¹𝒪_B ⟶ 𝒪_X` restricted to the model,
carried back to `D(𝒪_X)` by `Φ`.

## Main definitions

* `AlgebraicGeometry.Space.modelNaiveCotangentComplex`: `NL_{X/Y}` on the model.
* `AlgebraicGeometry.Space.modelDerivedFunctor`: the equivalence `D(𝒪_model) ⥤ D(𝒪_X)`.

## Main results

* `CategoryTheory.Functor.FullyFaithful.bijective_comp_of_arrowIso`: bijectivity of
  post-composition transported along a fully faithful functor.
* `AlgebraicGeometry.Space.modelDerivedFunctorSingleShiftIso`: the comparison of shifted
  complexes concentrated in degree `0` under `D(𝒪_model) ⥤ D(𝒪_X)`.
* `AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map`: pushout
  along `φ` is an equivalence once `NL_{X/Y}` lies in `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.AlgebraExtension

universe u

/-- Post-composition with an arrow is bijective on the homs out of an object once it is so after
a fully faithful functor, up to an isomorphism of arrows. -/
theorem CategoryTheory.Functor.FullyFaithful.bijective_comp_of_arrowIso {𝒞 𝒟 : Type*}
    [Category 𝒞] [Category 𝒟] {Φ : 𝒞 ⥤ 𝒟} (hΦ : Φ.FullyFaithful) {K M N : 𝒞} (g : M ⟶ N)
    {M' N' : 𝒟} (g' : M' ⟶ N') (w : Arrow.mk (Φ.map g) ≅ Arrow.mk g')
    (h : Function.Bijective (fun ξ : Φ.obj K ⟶ M' => ξ ≫ g')) :
    Function.Bijective (fun ξ : K ⟶ M => ξ ≫ g) := by
  have : IsIso w.hom.left := (Arrow.leftFunc.mapIso w).isIso_hom
  have : IsIso w.hom.right := (Arrow.rightFunc.mapIso w).isIso_hom
  have hp : Function.Bijective (fun ξ : K ⟶ M => Φ.map ξ ≫ w.hom.left) :=
    (bijective_comp_of_isIso w.hom.left).comp (hΦ.map_bijective K M)
  have hq : Function.Bijective (fun η : K ⟶ N => Φ.map η ≫ w.hom.right) :=
    (bijective_comp_of_isIso w.hom.right).comp (hΦ.map_bijective K N)
  have key : (fun η : K ⟶ N => Φ.map η ≫ w.hom.right) ∘ (fun ξ : K ⟶ M => ξ ≫ g) =
      (fun ξ : Φ.obj K ⟶ M' => ξ ≫ g') ∘ (fun ξ : K ⟶ M => Φ.map ξ ≫ w.hom.left) := by
    funext ξ
    change Φ.map (ξ ≫ g) ≫ w.hom.right = (Φ.map ξ ≫ w.hom.left) ≫ g'
    rw [Φ.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact w.hom.w.symm
  exact (Function.Bijective.of_comp_iff' hq _).1 (key ▸ h.comp hp)

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-- The base ring `f⁻¹𝒪_Y` of the extensions of the situation of [Stacks Project, Tag 0D3P]. -/
abbrev inverseImageBase : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
    (smallEtaleRingedTopos B S hS Y).O

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev inverseImageBaseMap : inverseImageBase B S hS f ⟶ structureSheaf B S hS X.1 X.2 :=
  (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- The comparison of the small étale site of `X` with its model, as an equivalence. -/
abbrev modelEquiv (X : AlgebraicSpaces B S hS) := smallEtaleModelEquiv B S hS X

/-- `f⁻¹𝒪_Y ⟶ 𝒪_X` restricted to the model of the small étale site of `X`. -/
abbrev modelBaseMap :=
  (ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).map
    (inverseImageBaseMap B S hS f)

/-- **The naive cotangent complex `NL_{X/Y}` on the model** of the small étale site of `X`: the
naive cotangent complex of the restriction of `f⁻¹𝒪_Y ⟶ 𝒪_X` to the model. -/
abbrev modelNaiveCotangentComplex :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} (smallEtaleModelTopology B S hS X.1) _ _
    (modelBaseMap B S hS f)

variable (X) in
/-- The sheaves of modules over the structure sheaf of the model of the small étale site of
`X`. -/
abbrev RestrictedModelModules :=
  SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
      (structureSheaf B S hS X.1 X.2)))

variable (X) in
/-- The Comparison Lemma `AlgebraicGeometry.Space.smallEtaleModelModulesEquiv`, with its target
written as the modules over the restricted structure sheaf. -/
abbrev modelModulesEquiv : Modules.{u, u} B S hS X.1 X.2 ≌ RestrictedModelModules B S hS X :=
  smallEtaleModelModulesEquiv B S hS X

/-- The functor of the Comparison Lemma `AlgebraicGeometry.Space.modelModulesEquiv` is additive,
being a pushforward of sheaves of modules. -/
instance modelModulesEquiv_functor_additive : (modelModulesEquiv B S hS X).functor.Additive :=
  Stacks.SheafOfModules.pushforward_additive _

variable (X) in
/-- The equivalence `D(𝒪_model) ⥤ D(𝒪_X)` induced by the Comparison Lemma. -/
abbrev modelDerivedFunctor :=
  (modelModulesEquiv B S hS X).inverse.mapDerivedCategory

/-- Restricting a module to the model, applying `D(-)` and coming back to `X` is the identity on
complexes concentrated in degree `0`. -/
def modelDerivedFunctorSingleIso :
    (modelModulesEquiv B S hS X).functor ⋙
        DerivedCategory.singleFunctor _ 0 ⋙ modelDerivedFunctor B S hS X ≅
      DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 :=
  Functor.isoWhiskerLeft (modelModulesEquiv B S hS X).functor
      ((modelModulesEquiv B S hS X).inverse.mapDerivedCategorySingleFunctor 0) ≪≫
    Functor.isoWhiskerRight (modelModulesEquiv B S hS X).unitIso.symm
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0) ≪≫
    Functor.leftUnitor _

/-- The shifted form of `AlgebraicGeometry.Space.modelDerivedFunctorSingleIso`. -/
def modelDerivedFunctorSingleShiftIso (i : ℤ) :
    (modelModulesEquiv B S hS X).functor ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        shiftFunctor _ i ⋙ modelDerivedFunctor B S hS X ≅
      DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0 ⋙ shiftFunctor _ i :=
  Functor.isoWhiskerLeft ((modelModulesEquiv B S hS X).functor ⋙
      DerivedCategory.singleFunctor _ 0) ((modelDerivedFunctor B S hS X).commShiftIso i) ≪≫
    Functor.isoWhiskerRight (modelDerivedFunctorSingleIso B S hS) (shiftFunctor _ i)

/-- The functor `AlgebraicGeometry.Space.modelDerivedFunctor` on derived categories induced by the
Comparison Lemma is fully faithful, being an equivalence. -/
theorem modelDerivedFunctor_fullyFaithful :
    Nonempty (modelDerivedFunctor B S hS X).FullyFaithful := by
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence
    (modelModulesEquiv B S hS X).inverse
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- **[Stacks Project, Tag 0D3P], with the quasi-coherence of `NL_{X/Y}` as its input.** Let
`f : X ⟶ Y` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated, let
`φ : ℱ ⟶ 𝒢` be a morphism of `𝒪_X`-modules (not necessarily quasi-coherent) with
`DQ_X(ℱ) ⟶ DQ_X(𝒢)` an isomorphism, and let `F` be pushout along `φ`, from extensions
`0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_Y`-algebras to extensions by `𝒢`, given by its universal
property. If `NL_{X/Y}` lies in `D_QCoh(𝒪_X)`, then `F` is an equivalence of categories.

`NL_{X/Y}` is the naive cotangent complex of `f⁻¹𝒪_Y ⟶ 𝒪_X` formed on the `Type u` model of the
small étale site of `X` and carried to `D(𝒪_X)` by the Comparison Lemma; its membership in
`D_QCoh(𝒪_X)` is the quasi-coherence clause of [Stacks Project, Tag 0D0Y], which the source cites
and which is the one input taken here. -/
theorem isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {M N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : M ⟶ N)
    {F : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M ⥤
      AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) N}
    (hF : IsPushoutFunctor.{u, u + 1, u} (a := inverseImageBaseMap B S hS f) φ F)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)))
    (hNL : qcohDerivedProp B S hS X ((modelDerivedFunctor B S hS X).obj
      (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f)))) :
    F.IsEquivalence := by
  have := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
  obtain ⟨hΦ⟩ := modelDerivedFunctor_fullyFaithful B S hS (X := X)
  let K := smallEtaleModelTopology B S hS X.1
  let e := modelEquiv B S hS X
  let a' := modelBaseMap B S hS f
  let φ' := (moduleRes K e.inverse (structureSheaf B S hS X.1 X.2)).map φ
  have h0 : Function.Bijective
      (fun ξ : DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f) ⟶
      (DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).obj
        ((moduleRes K e.inverse (structureSheaf B S hS X.1 X.2)).obj M) =>
      ξ ≫ (DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).map φ') :=
    hΦ.bijective_comp_of_arrowIso _
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)
      (Arrow.isoOfNatIso (modelDerivedFunctorSingleIso B S hS) (Arrow.mk φ))
      ((qcohDerivedProp B S hS X).bijective_comp_of_isIso_rightAdjoint_map hNL _)
  have h1 : Function.Bijective
      (fun ξ : DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f) ⟶
      ((DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).obj
        ((moduleRes K e.inverse (structureSheaf B S hS X.1 X.2)).obj M))⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor (RestrictedModelModules B S hS X) 0).map φ')⟦(1 : ℤ)⟧') :=
    hΦ.bijective_comp_of_arrowIso _
      (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ)⟦(1 : ℤ)⟧')
      (Arrow.isoOfNatIso (modelDerivedFunctorSingleShiftIso B S hS 1) (Arrow.mk φ))
      ((qcohDerivedProp B S hS X).bijective_comp_shift_map_of_isIso_rightAdjoint_map hNL _ 1)
  have hP := isPushoutFunctor_pushoutFunctor a' φ'
  have : (pushoutFunctor a' φ').IsEquivalence :=
    hP.isEquivalence (by with_reducible exact h0) (by with_reducible exact h1)
  have := isEquivalence_siteRestriction K e (inverseImageBaseMap B S hS f) M
  have := isEquivalence_siteRestriction K e (inverseImageBaseMap B S hS f) N
  exact hF.isEquivalence_of_restrict (c := idRingComparison K e _)
    (cM := idModuleComparison K e _ M) (cN := idModuleComparison K e _ N) (fun _ _ => rfl) hP

end AlgebraicGeometry.Space

end
