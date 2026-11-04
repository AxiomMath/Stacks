module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# Cohomology and base change for proper morphisms of finite presentation

For `f : X ⟶ Y` proper and of finite presentation, Stacks 0CTM: (1) if `f` is flat and `E` is a
perfect object of `D(𝒪_X)`, then `Rf_*E` is perfect and its formation commutes with arbitrary
base change; (2) if `𝒢` is an `𝒪_X`-module of finite presentation, flat over `Y`, then `Rf_*𝒢`
is perfect and its formation commutes with arbitrary base change. Both are instances of
Stacks 0A1P and 0A1K. With Stacks 0D20 this gives Stacks 0E6A.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat`: Stacks 0CTM, part (1).
* `isPerfect_derivedModulePushforward_single_and_isIso_baseChange`: Stacks 0CTM, part (2).
* `exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_of_isProper`: Stacks 0E6A, the
  locus where `Rf_{T,*}𝓕_T` is finite locally free of rank `r` in degree `i`.

## Implementation notes

The source's part (2) asks `𝒢` to be flat over the base scheme `S`. That reading is false: for
`f` the identity of a nodal curve over a field `k = S` and `𝒢` the skyscraper at the node,
`𝒢` is flat over `S` but `Rf_*𝒢 = 𝒢` is not perfect (the declaration docstring gives the affine
form of this example). The proof (through Stacks 0A1P) uses flatness over `Y`, which is what
part (2) states here.

In part (2) the base change is to `Rf'_*((g')^*𝒢)` with the underived pullback `(g')^*𝒢`, the
form of Stacks 0A1K: since `f` need not be flat, `L(g')^*𝒢` and `(g')^*𝒢` differ in general.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- global `HasDerivedCategory` instances in scope here (`Homology/DerivedCategory/LocallySmall` and
-- others) compete with the standard model in which the derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent
attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0CTM, part (1).** Let `f : X ⟶ Y` be proper, flat and of finite presentation, and
let `E ∈ D(𝒪_X)` be perfect. Then `Rf_*E` is perfect, and its formation commutes with arbitrary
base change: for every cartesian square the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an
isomorphism. -/
theorem isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat (f : X ⟶ Y)
    (hfp : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
        ((derivedModulePushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  refine ⟨?_, fun g f' g' sq =>
    isIso_smallEtaleDerivedBaseChangeMap_of_isFlat sq hf.2.1 hf.2.2 hfl E
      (qcohDerived_of_isPerfect_derivedCategoryB X E hE)⟩
  have h := isPerfect_derivedModulePushforward_derivedTensor_single f hf E hE
    (structureSheafModule B S hS X) inferInstance
    (isFlatOver_structureSheafModule B S hS f hfl)
    (hasProperSupport_structureSheafModule B S hS f hfp _)
  exact isPerfect_of_iso B S hS h ((derivedModulePushforward B S hS f).mapIso
    ((smallEtaleDerivedTensorProduct B S hS X).unitNatIso.app E))

/-- **Stacks 0CTM, part (2).** Let `f : X ⟶ Y` be proper and of finite presentation, and let `𝒢`
be an `𝒪_X`-module of finite presentation, flat over `Y`. Then `Rf_*𝒢` is perfect, and its
formation commutes with arbitrary base change: for every cartesian square the map
`Lg^*Rf_*𝒢 ⟶ Rf'_*((g')^*𝒢)` is an isomorphism.

The source asks `𝒢` to be flat over the base scheme `S`, which is false: for `S = Spec k`,
`X = Y = Spec A` with `A = k[x, y]/(xy)`, `f = id` and `𝒢 = A/(x)`, the module `𝒢` is of finite
presentation and flat over `k`, but `Rf_*𝒢 = A/(x)` has infinite projective dimension over `A`,
so it is not perfect. The corrected hypothesis, used here, is that `𝒢` is flat over `Y`. -/
theorem isPerfect_derivedModulePushforward_single_and_isIso_baseChange (f : X ⟶ Y)
    (hfp : IsProper B S hS f.hom) (hf : IsFinitePresentation B S hS f.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hGfp : G.IsFinitePresentation) (hGflat : IsFlatOver B S hS X.2 f.hom G) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
        ((derivedModulePushforward B S hS f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G)) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedBaseChangeComp B S hS f g f' g' sq.w
          (DerivedCategory.Q.obj ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
              (ComplexShape.up ℤ) 0).obj G))
          _ (smallEtaleDerivedModulePullbackQComparison g' ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
              (ComplexShape.up ℤ) 0).obj G))) := by
  have hG0 : ∀ n, n ≠ 0 → IsZero (((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
        (ComplexShape.up ℤ) 0).obj G).X n) :=
    fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  refine ⟨?_, fun g f' g' sq => ?_⟩
  · have h := isPerfect_derivedModulePushforward_derivedTensor_single f hf _ (isPerfect_unit X) G
      hGfp hGflat (hasProperSupport_of_isFinitePresentation B S hS f hfp _ G (hM := hGfp))
    exact isPerfect_of_iso B S hS h ((derivedModulePushforward B S hS f).mapIso
      ((smallEtaleDerivedTensorProduct B S hS X).leftUnitor.app _))
  refine isIso_smallEtaleDerivedBaseChangeComp_modulePullbackQComparison_of_isFlatOver B S hS sq
    hf.2.1 hf.2.2 _ ⟨0, fun i hi => hG0 i (by omega)⟩ (fun n => ?_) (fun n => ?_)
  · obtain rfl | hn := eq_or_ne n 0
    · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm
        (isQuasicoherentOnSite_of_isFinitePresentation G hGfp)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero (hG0 n hn)
  · obtain rfl | hn := eq_or_ne n 0
    · exact IsFlatOver.of_iso B S hS _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm hGflat
    · exact isFlatOver_of_isZero B S hS _ (hG0 n hn)

/-- **Stacks 0E6A.** Let `f : X ⟶ Y` be proper, flat and of finite presentation, and let `𝓕` be
an `𝒪_X`-module of finite presentation, flat over `Y`. For `i, r ∈ ℤ` there is an open subspace
`V ⊆ Y` such that `g : T ⟶ Y` factors through `V` exactly when `Rf_{T,*}𝓕_T` is a finite locally
free module of rank `r` placed in degree `i`. -/
theorem exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_of_isProper
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i r : ℤ) :
    ∃ V : OpenSubspaces B S hS Y.1, ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y),
      (∃ h : T ⟶ openSubspaceAsSpace B S hS V, h ≫ openSubspaceImmersion B S hS V = g) ↔
        IsFiniteLocallyFreeOfIntRankInDegree B S hS T
          ((derivedModulePushforward B S hS (pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (pullback f g))) 0).obj
              ((modulePullback B S hS (pullback.fst f g)).obj F))) i r :=
  have := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_derivedModulePushforward f hfl
    hfp.2.1 hfp.2.2 F hF i r
    (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp F hFfp hF).1

end AlgebraicGeometry.Space

end
