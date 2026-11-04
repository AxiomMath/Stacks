module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleFunctorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteOfIsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteEquivalenceFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# Finite presentation of the comparison `𝓕 ↦ 𝓕^a` on a represented algebraic space

For an object `U` of the big fppf site, a quasi-coherent module `𝓕` on the scheme underlying `U`
is of finite presentation exactly when the `𝒪`-module `𝓕^a` on the small étale site of the
algebraic space `h_U` is of finite presentation on the site (Stacks 03DL(7)).

## Main results

* `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_obj`: `𝓕^a` is of finite
  presentation on the small étale site of a scheme.
* `isFinitePresentationOnSite_representedModuleFunctor_obj` and
  `isFinitePresentation_of_isFinitePresentationOnSite_representedModuleFunctor_obj` (in the
  namespace `AlgebraicGeometry.Space`): the two directions on the represented algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- Abelian presheaves on the slices of the small étale site of a scheme, spelled through its
ringed topos, have a sheafification. -/
instance hasWeakSheafify_over_ringedTopos (V : (ringedTopos B X hX).C) :
    HasWeakSheafify ((ringedTopos B X hX).J.over V) AddCommGrpCat.{u} := by
  let V' : SmallEtale B X hX := V
  have : EssentiallySmall.{u} (Over V') :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 (SmallEtale B X hX)) V'))
  have : HasSheafify ((topology B X hX).over V') AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  exact inferInstanceAs (HasWeakSheafify ((topology B X hX).over V') AddCommGrpCat.{u})

/-- The local equivalences of abelian presheaves on the slices of the small étale site of a
scheme are the locally bijective morphisms. -/
instance wEqualsLocallyBijective_over_ringedTopos (V : (ringedTopos B X hX).C) :
    ((ringedTopos B X hX).J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let V' : SmallEtale B X hX := V
  have : EssentiallySmall.{u} (Over V') :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 (SmallEtale B X hX)) V'))
  exact inferInstanceAs (((topology B X hX).over V').WEqualsLocallyBijective AddCommGrpCat.{u})

/-- For `𝓕` of finite presentation on a scheme, `𝓕^a` is of finite presentation on the small
étale site of the scheme. -/
theorem isFinitePresentation_associatedModule_obj (M : X.Modules) [hM : M.IsFinitePresentation] :
    ((associatedModule B X hX).obj M).IsFinitePresentation :=
  have : SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedTopos.O)) M := hM
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso ((assocIso B X hX).app M)
    (Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules
      (toZariskiAbstractRingedToposHom B X hX).toRingedToposModulesHom M)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The comparison of the small étale sites of the scheme underlying `U` and of `h_U` preserves
finite presentation. -/
theorem isFinitePresentation_representedSmallEtaleModuleEquivalence_functor_obj
    (N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (hN : N.IsFinitePresentation) :
    ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj N).IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_reindexEquivalence_functor_obj
    (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (J := representedSchemeSmallEtaleTopology B S hS U)
    (_root_.AlgebraicGeometry.SmallEtale.ringedTopos (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).O N hN

/-- For a quasi-coherent `𝓕` of finite presentation on the scheme underlying `U`, `𝓕^a` is of
finite presentation on the small étale site of `h_U` (Stacks 03DL(7)). -/
theorem isFinitePresentationOnSite_representedModuleFunctor_obj
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    [M.obj.IsFinitePresentation] :
    ((representedModuleFunctor B S hS U).obj M).IsFinitePresentationOnSite := by
  have h := isFinitePresentation_representedSmallEtaleModuleEquivalence_functor_obj B S hS U _
    (_root_.AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_obj
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M.obj)
  exact @Stacks.Sheaves.FinitePresentation.isFinitePresentationOnSite_of_isFinitePresentation
    (smallEtaleRingedTopos B S hS (schemeSpace U)) _ _ _ _ _ _ _
    ((representedModuleFunctor B S hS U).obj M) h

/-- Conversely, `𝓕` is of finite presentation when `𝓕^a` is of finite presentation on the small
étale site of `h_U`. -/
theorem isFinitePresentation_of_isFinitePresentationOnSite_representedModuleFunctor_obj
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    (h : ((representedModuleFunctor B S hS U).obj M).IsFinitePresentationOnSite) :
    M.obj.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation _).prop_of_iso
    (representedZariskiRestriction_representedQuasicoherentIso B S hS U M.obj M.property)
    (isFinitePresentation_restrictToChart B S hS (schemeSpace U)
      ((representedModuleFunctor B S hS U).obj M)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).property h
      (selfChart B S hS U))

end AlgebraicGeometry.Space

end
