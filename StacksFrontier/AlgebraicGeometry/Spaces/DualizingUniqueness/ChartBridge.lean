module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingUniqueness.Model
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPullbackRestrictionIdentification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceEquivalenceOfIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleOfLocalShift

/-!
# Restriction to a slice of the equi-universe model is restriction to an étale chart
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- An exact functor carries an isomorphism with a shift to an isomorphism with a shift. -/
theorem nonempty_mapDerivedCategory_iso_shift {C₁ C₂ : Type*} [Category C₁] [Abelian C₁]
    [Category C₂] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A A' : DerivedCategory C₁} {n : ℤ} (e : A' ≅ A⟦n⟧) :
    Nonempty (F.mapDerivedCategory.obj A' ≅ (F.mapDerivedCategory.obj A)⟦n⟧) :=
  ⟨F.mapDerivedCategory.mapIso e ≪≫ (F.mapDerivedCategory.commShiftIso n).app A⟩

/-- An equivalence of abelian categories reflects isomorphisms with a shift on derived
categories. -/
theorem nonempty_iso_shift_of_equivalence {C₁ C₂ : Type*} [Category C₁] [Abelian C₁]
    [Category C₂] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (E : C₁ ≌ C₂) [E.functor.Additive]
    {A A' : DerivedCategory C₁} {n : ℤ}
    (e : E.functor.mapDerivedCategory.obj A' ≅ (E.functor.mapDerivedCategory.obj A)⟦n⟧) :
    Nonempty (A' ≅ A⟦n⟧) := by
  have hE := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory_functor E
  let ED := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E
  have e' : ED.functor.obj A' ≅ ED.functor.obj (A⟦n⟧) := by
    rw [hE]
    exact e ≪≫ ((E.functor.mapDerivedCategory.commShiftIso n).app A).symm
  exact ⟨ED.fullyFaithfulFunctor.preimageIso e'⟩

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

/-- Restriction to an étale chart is restriction to the slice at the chart, read through the
comparison equivalence of Stacks 04M0. -/
def chartPullbackSliceIso (c : SmallEtale B S hS X.1) :
    etaleModulePullback B S hS (chartToSpace B S hS X c) (isEtale_chartToSpace B S hS X c) ≅
      SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c ⋙
        (chartModuleSliceEquiv B S hS X c).functor :=
  (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X c)
    (isEtale_chartToSpace B S hS X c)).symm ≪≫ chartModuleRestrictionSliceIso B S hS X c

/-- **A shift on an étale chart is a shift on the slice at the chart.** -/
theorem nonempty_over_iso_shift_of_chart (c : SmallEtale B S hS X.1) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureRingSheaf B S hS X))
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (yoneda.obj c.obj.left) (isAlgebraicSpace_yoneda B S hS c.obj.left))
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} ((structureRingSheaf B S hS X).over c))
    ∀ (K K' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ)
      (_ : (representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
        (isEtale_chartToSpace B S hS X c)).obj K' ≅
      ((representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
        (isEtale_chartToSpace B S hS X c)).obj K)⟦n⟧),
    Nonempty ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
        c).mapDerivedCategory.obj K' ≅
      ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c).mapDerivedCategory.obj
        K)⟦n⟧) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureRingSheaf B S hS X))
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (yoneda.obj c.obj.left) (isAlgebraicSpace_yoneda B S hS c.obj.left))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((structureRingSheaf B S hS X).over c))
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (chartSpace B S hS X c).1 (chartSpace B S hS X c).2)
  intro K K' n e
  have := etaleModulePullback_additive.{u, u} B S hS (chartToSpace B S hS X c)
    (isEtale_chartToSpace B S hS X c)
  have := preservesFiniteLimits_etaleModulePullback B S hS (chartToSpace B S hS X c)
    (isEtale_chartToSpace B S hS X c)
  have := preservesFiniteColimits_etaleModulePullback B S hS (chartToSpace B S hS X c)
    (isEtale_chartToSpace B S hS X c)
  have : (chartModuleSliceEquiv B S hS X c).functor.Additive := ⟨rfl⟩
  have : (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c).Additive := ⟨rfl⟩
  let φ : (⟨yoneda.obj c.obj.left, isAlgebraicSpace_yoneda B S hS c.obj.left⟩ :
      AlgebraicSpaces B S hS) ⟶ X := ObjectProperty.homMk c.obj.hom
  have := etaleModulePullback_additive.{u, u} B S hS φ (isEtale_chartToSpace B S hS X c)
  have := preservesFiniteLimits_etaleModulePullback B S hS φ (isEtale_chartToSpace B S hS X c)
  have := preservesFiniteColimits_etaleModulePullback B S hS φ
    (isEtale_chartToSpace B S hS X c)
  have ι : ∀ L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      Nonempty ((representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
        (isEtale_chartToSpace B S hS X c)).obj L ≅
        (chartModuleSliceEquiv B S hS X c).functor.mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c).mapDerivedCategory.obj
            L)) := by
    intro L
    let K₀ := DerivedCategory.Q.objPreimage L
    let eK := DerivedCategory.Q.objObjPreimageIso L
    let ε := chartPullbackSliceIso B S hS X c
    let cpx : ((etaleModulePullback.{u, u} B S hS φ
        (isEtale_chartToSpace B S hS X c)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀ ≅
        ((chartModuleSliceEquiv B S hS X c).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀) :=
      HomologicalComplex.Hom.isoOfComponents (fun i => ε.app (K₀.X i))
        (fun i j _ => (ε.hom.naturality (K₀.d i j)).symm)
    exact ⟨(representedChartDerivedRestriction B S hS X.2 c.obj.left c.obj.hom
        (isEtale_chartToSpace B S hS X c)).mapIso eK.symm ≪≫
      (etaleModulePullback.{u, u} B S hS φ
        (isEtale_chartToSpace B S hS X c)).mapDerivedCategoryFactors.app K₀ ≪≫
      DerivedCategory.Q.mapIso cpx ≪≫
      ((chartModuleSliceEquiv B S hS X c).functor.mapDerivedCategoryFactors.app _).symm ≪≫
      (chartModuleSliceEquiv B S hS X c).functor.mapDerivedCategory.mapIso
        (((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
          c).mapDerivedCategoryFactors.app K₀).symm ≪≫
          (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) c).mapDerivedCategory.mapIso
            eK)⟩
  obtain ⟨ι₁⟩ := ι K'
  obtain ⟨ι₂⟩ := ι K
  exact nonempty_iso_shift_of_equivalence (chartModuleSliceEquiv B S hS X c)
    (ι₁.symm ≪≫ e ≪≫ (shiftFunctor _ n).mapIso ι₂)

/-- The slice of the equi-universe model at `V` and the slice of the small étale site at the image
of `V` carry equivalent categories of modules. -/
def modelSliceModulesEquiv (V : (smallEtaleModelRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over
        ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)) ≌
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleModelRingedSite B S hS X.1 X.2).O).over V) :=
  Stacks.SheafOfModules.InternalHom.siteEquivModulesOverOfIso
    (J := smallEtaleModelTopology B S hS X.1) (K := SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquivalence B S hS X.1 :
      (smallEtaleModelRingedSite B S hS X.1 X.2).C ≌ SmallEtale B S hS X.1)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O)
    (R := structureRingSheaf B S hS X) (𝟙 _) (hφ := IsIso.id _) V

/-- Transport to the model followed by restriction to the slice at `V` is restriction to the slice
at the image of `V` followed by the slice comparison. Both are reindexing of sections along the
same functor `Over V ⥤ SmallEtale X`. -/
def modelRestrictionIso (V : (smallEtaleModelRingedSite B S hS X.1 X.2).C) :
    (modulesEquivModelModules B S hS X.1 X.2).functor ⋙
        SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS X.1 X.2).O) V ≅
      SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
          ((smallEtaleModelEquivalence B S hS X.1).functor.obj V) ⋙
        (modelSliceModulesEquiv B S hS X V).functor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **A shift on the slice at the image of `V` is a shift on the slice of the model at `V`.** -/
theorem nonempty_restrictDer_iso_shift_of_over (V : (smallEtaleModelRingedSite B S hS X.1 X.2).C) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureRingSheaf B S hS X))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} ((structureRingSheaf B S hS X).over
      ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)))
    ∀ (K K' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ)
      (_ : (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
          ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapDerivedCategory.obj K' ≅
      ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
          ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapDerivedCategory.obj K)⟦n⟧),
    Nonempty ((RingedSite.InvertibleDerived.restrictDer (smallEtaleModelRingedSite B S hS X.1 X.2)
        V).obj ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K') ≅
      ((RingedSite.InvertibleDerived.restrictDer (smallEtaleModelRingedSite B S hS X.1 X.2)
        V).obj ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj K))⟦n⟧) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureRingSheaf B S hS X))
  let := HasDerivedCategory.standard (SheafOfModules.{u} ((structureRingSheaf B S hS X).over
    ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)))
  let := HasDerivedCategory.standard (ModelModules B S hS X.1 X.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O).over V))
  intro K K' n e
  have := additive_modulesEquivModelModules_functor B S hS X.1 X.2
  have : (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
      ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).Additive := ⟨rfl⟩
  have : (modelSliceModulesEquiv B S hS X V).functor.Additive := ⟨rfl⟩
  have ι : ∀ L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      Nonempty ((RingedSite.InvertibleDerived.restrictDer
          (smallEtaleModelRingedSite B S hS X.1 X.2) V).obj
            ((modelDerivedEquivalence B S hS X.1 X.2).functor.obj L) ≅
        (modelSliceModulesEquiv B S hS X V).functor.mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
            ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapDerivedCategory.obj
              L)) := by
    intro L
    let K₀ := DerivedCategory.Q.objPreimage L
    let eK := DerivedCategory.Q.objObjPreimageIso L
    let ε := modelRestrictionIso B S hS X V
    let cpx : ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS X.1 X.2).O) V).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((modulesEquivModelModules B S hS X.1 X.2).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀) ≅
        ((modelSliceModulesEquiv B S hS X V).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
            ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀) :=
      HomologicalComplex.Hom.isoOfComponents (fun i => ε.app (K₀.X i))
        (fun i j _ => (ε.hom.naturality (K₀.d i j)).symm)
    exact ⟨(RingedSite.InvertibleDerived.restrictDer (smallEtaleModelRingedSite B S hS X.1 X.2)
        V).mapIso (((modulesEquivModelModules B S hS X.1 X.2).functor.mapDerivedCategory.mapIso
          eK.symm) ≪≫
          (modulesEquivModelModules B S hS X.1 X.2).functor.mapDerivedCategoryFactors.app K₀) ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleModelRingedSite B S hS X.1 X.2).O) V).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso cpx ≪≫
      ((modelSliceModulesEquiv B S hS X V).functor.mapDerivedCategoryFactors.app _).symm ≪≫
      (modelSliceModulesEquiv B S hS X V).functor.mapDerivedCategory.mapIso
        (((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
          ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapDerivedCategoryFactors.app
            K₀).symm ≪≫
          (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X)
            ((smallEtaleModelEquivalence B S hS X.1).functor.obj V)).mapDerivedCategory.mapIso eK)⟩
  obtain ⟨ι₁⟩ := ι K'
  obtain ⟨ι₂⟩ := ι K
  obtain ⟨e'⟩ := nonempty_mapDerivedCategory_iso_shift (modelSliceModulesEquiv B S hS X V).functor e
  exact ⟨ι₁ ≪≫ e' ≪≫ (shiftFunctor _ n).mapIso ι₂.symm⟩

end AlgebraicGeometry.Space
