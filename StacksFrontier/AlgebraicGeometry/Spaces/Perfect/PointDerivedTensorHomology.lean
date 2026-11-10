module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSiteTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightNaturality

/-!
# The derived tensor product over the point computed by a complex of flat modules

Let `R` be a commutative ring and `(pt, R)` the punctual ringed topos, whose modules are the
`R`-modules (`AlgebraicGeometry.Space.baseRingPointModulesEquiv`). For a bounded above complex
`K` of flat `R`-modules, carried to the point as `K'`, the canonical derived tensor product of the
point computes `Hⁱ(K ⊗_R N)`:

  `Hⁱ(K ⊗_R N) ≅ Hⁱ(K' ⊗^L N[0])`, naturally in the `R`-module `N`.

Indeed `K'` is K-flat (Stacks 06YQ: a bounded above complex of flat modules, and a module on the
point is flat when its sections are), so `K' ⊗^L N[0]` is the total tensor complex
`Tot(K' ⊗ N[0])`, which is `K' ⊗ N` degreewise; on sections over the point that is `K ⊗_R N`.

## Main results

* `AlgebraicGeometry.Space.kFlat_pointModules_of_flat`: `K'` is K-flat.
* `AlgebraicGeometry.Space.pointTensorDegreewiseIso`: `K ⊗_R N ≅ Γ(pt, K' ⊗ N)` degreewise.
* `AlgebraicGeometry.Space.pointTensorComplexIso`: `Tot(K ⊗_R N[0]) ≅ Γ(pt, Tot(K' ⊗ N[0]))`,
  naturally in `N`.
* `AlgebraicGeometry.Space.pointDerivedTensorHomologyIso`: `Hⁱ(K ⊗_R N) ≅ Hⁱ(K' ⊗^L N[0])`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance high] sheafTensor_additive_ringedSite sheafTensor_obj_additive_ringedSite
  hasMapBifunctor_sheafTensor_ringedSite

variable {R : Type u} [CommRing R]

/-- **A bounded above complex of flat `R`-modules is K-flat on the point** (Stacks 06YQ): its
terms are flat sheaves of modules, their sections being flat modules. -/
theorem kFlat_pointModules_of_flat (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] (hK : ∀ i, Module.Flat R (K.X i)) :
    Stacks.SheafOfModules.IsKFlat (pointRingedTopos (CommRingCat.of R)).O
      (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  refine Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat _ _ ⟨b, ?_⟩
    fun i => Stacks.PointRingedSite.isFlat_of_flat_ev _ _ (hK i)
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (baseRingPointModulesEquiv (R := R)).inverse.map_isZero
    (CochainComplex.isZero_of_isStrictlyLE K b i hi)

section TensorComplex

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The tensor product of sheaves of modules on the point, with its universes pinned. -/
abbrev pointSheafTensor :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (pointRingedTopos (CommRingCat.of R)).O

/-- **Degreewise, `K ⊗_R N` is the sections over the point of `K' ⊗ N`**, `K'` and `N` carried
to the point. -/
def pointTensorDegreewiseIso (N : ModuleCat.{u} R) :
    (((curriedTensor (ModuleCat.{u} R)).flip.obj N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ≅
      ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((pointSheafTensor (R := R)).flip.obj
          ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun p => Stacks.PointRingedSite.evSheafTensorIso (CommRingCat.of R)
      ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p))
      ((baseRingPointModulesEquiv (R := R)).inverse.obj N))
    (fun p q _ => (Stacks.PointRingedSite.evSheafTensorIso_hom_naturality_left (CommRingCat.of R)
        ((baseRingPointModulesEquiv (R := R)).inverse.map (K.d p q))
        ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).symm)).symm

/-- `AlgebraicGeometry.Space.pointTensorDegreewiseIso` is natural in the module. -/
@[reassoc]
theorem pointTensorDegreewiseIso_hom_naturality {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).flip.map g)
        (ComplexShape.up ℤ)).app K ≫ (pointTensorDegreewiseIso K N').hom =
      (pointTensorDegreewiseIso K N).hom ≫
        ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
            ((pointSheafTensor (R := R)).flip.map
              ((baseRingPointModulesEquiv (R := R)).inverse.map g)) (ComplexShape.up ℤ)).app
            (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  have h := Stacks.PointRingedSite.evSheafTensorIso_hom_naturality_right (CommRingCat.of R)
    ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p))
    ((baseRingPointModulesEquiv (R := R)).inverse.map g)
  have h' : (Stacks.PointRingedSite.ev (CommRingCat.of R)).obj
        ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p)) ◁
          (Stacks.PointRingedSite.ev (CommRingCat.of R)).map
            ((baseRingPointModulesEquiv (R := R)).inverse.map g) ≫
        (Stacks.PointRingedSite.evSheafTensorIso (CommRingCat.of R)
          ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p))
          ((baseRingPointModulesEquiv (R := R)).inverse.obj N')).inv =
      (Stacks.PointRingedSite.evSheafTensorIso (CommRingCat.of R)
          ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p))
          ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).inv ≫
        (Stacks.PointRingedSite.ev (CommRingCat.of R)).map
          (((pointSheafTensor (R := R)).obj
            ((baseRingPointModulesEquiv (R := R)).inverse.obj (K.X p))).map
              ((baseRingPointModulesEquiv (R := R)).inverse.map g)) :=
    ((Iso.inv_comp_eq _).mpr (((Iso.eq_comp_inv _).mpr h).trans (Category.assoc _ _ _))).symm
  exact h'

/-- **`K ⊗_R N[0]` is the sections over the point of `Tot(K' ⊗ N[0])`**, naturally in `N`, where
`K'` and `N` are carried to the point. -/
def pointTensorComplexIso :
    HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0 ⋙
        (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K ≅
      (baseRingPointModulesEquiv (R := R)).inverse ⋙
        HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙
        (Stacks.SheafOfModules.Tensor.tensorComplex (pointRingedTopos (CommRingCat.of R)).O).obj
          (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ⋙
        (baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents
    (fun N => HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R)) K N ≪≫
      pointTensorDegreewiseIso K N ≪≫
      ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (HomologicalComplex.mapBifunctorSingleRightIso
          (pointSheafTensor (R := R))
          (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).symm)
    (fun {N N'} g => by
      have hA : HomologicalComplex.mapBifunctorMap (𝟙 K)
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map g)
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) ≫
            (HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R))
              K N').hom =
          (HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R))
              K N).hom ≫
            (NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} R)).flip.map g)
              (ComplexShape.up ℤ)).app K :=
        HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_right _ K g
      have h₃ := HomologicalComplex.mapBifunctorSingleRightIso_hom_naturality_right
        (pointSheafTensor (R := R))
        (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ((baseRingPointModulesEquiv (R := R)).inverse.map g)
      have h₃' : (HomologicalComplex.mapBifunctorSingleRightIso (pointSheafTensor (R := R))
            (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).inv ≫
          HomologicalComplex.mapBifunctorMap
            (𝟙 (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
              ((baseRingPointModulesEquiv (R := R)).inverse.map g))
            (pointSheafTensor (R := R)) (ComplexShape.up ℤ) =
          (NatTrans.mapHomologicalComplex ((pointSheafTensor (R := R)).flip.map
              ((baseRingPointModulesEquiv (R := R)).inverse.map g)) (ComplexShape.up ℤ)).app
            (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
          (HomologicalComplex.mapBifunctorSingleRightIso (pointSheafTensor (R := R))
            (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)
            ((baseRingPointModulesEquiv (R := R)).inverse.obj N')).inv :=
        (Iso.inv_comp_eq _).mpr (((Iso.eq_comp_inv _).mpr h₃).trans (Category.assoc _ _ _))
      have E : HomologicalComplex.mapBifunctorMap (𝟙 K)
          ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map g)
          (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) ≫
            (HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R))
              K N').hom ≫ (pointTensorDegreewiseIso K N').hom ≫
            ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).map (HomologicalComplex.mapBifunctorSingleRightIso
                (pointSheafTensor (R := R))
                (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)
                ((baseRingPointModulesEquiv (R := R)).inverse.obj N')).inv =
          (HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R))
              K N).hom ≫ (pointTensorDegreewiseIso K N).hom ≫
            ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).map (HomologicalComplex.mapBifunctorSingleRightIso
                (pointSheafTensor (R := R))
                (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)
                ((baseRingPointModulesEquiv (R := R)).inverse.obj N)).inv ≫
            ((baseRingPointModulesEquiv (R := R)).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).map (HomologicalComplex.mapBifunctorMap
                (𝟙 (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K))
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
                  ((baseRingPointModulesEquiv (R := R)).inverse.map g))
                (pointSheafTensor (R := R)) (ComplexShape.up ℤ)) := by
        rw [reassoc_of% hA, pointTensorDegreewiseIso_hom_naturality_assoc, ← Functor.map_comp,
          ← h₃', Functor.map_comp]
      exact E)

/-- The derived tensor product over the point. -/
abbrev pointDerivedTensor :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
    (pointRingedTopos (CommRingCat.of R)).O

/-- **Against a K-flat complex, the derived tensor product over the point is the total tensor
complex**, naturally in the other factor (Stacks 06YU). -/
def pointDerivedTensorQIso
    (L : CochainComplex (pointRingedTopos (CommRingCat.of R)).Modules ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat (pointRingedTopos (CommRingCat.of R)).O L) :
    (Stacks.SheafOfModules.Tensor.tensorComplex (pointRingedTopos (CommRingCat.of R)).O).obj L ⋙
        DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (pointDerivedTensor (R := R)).obj (DerivedCategory.Q.obj L) :=
  NatIso.ofComponents
    (fun M => ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (pointRingedTopos (CommRingCat.of R)).O).comparisonLeft L M hL).symm)
    (fun {M M'} g => by
      have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (pointRingedTopos (CommRingCat.of R)).O).comparisonLeft_naturality (𝟙 L) g hL hL
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.id_comp] at h
      exact ((Iso.inv_comp_eq _).mpr (((Iso.eq_comp_inv _).mpr h).trans
        (Category.assoc _ _ _))).symm)

/-- **`Hⁱ(K ⊗_R N) ≅ Hⁱ(K' ⊗^L N[0])` for a bounded above complex `K` of flat `R`-modules**,
naturally in the `R`-module `N`, where `K'` is `K` carried to the point and `⊗^L` is the derived
tensor product of the punctual ringed topos. -/
def pointDerivedTensorHomologyIso (b : ℤ) [K.IsStrictlyLE b] (hK : ∀ i, Module.Flat R (K.X i))
    (i : ℤ) :
    HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0 ⋙
        (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i ≅
      (baseRingPointModulesEquiv (R := R)).inverse ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        (pointDerivedTensor (R := R)).obj (DerivedCategory.Q.obj
          (((baseRingPointModulesEquiv (R := R)).inverse.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) ⋙
        (pointDerivedEquiv (R := R)).functor ⋙ DerivedCategory.homologyFunctor _ i :=
  let e := baseRingPointModulesEquiv (R := R)
  let K' := (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let G := e.functor.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R) i
  let s' := HomologicalComplex.single (pointRingedTopos (CommRingCat.of R)).Modules
    (ComplexShape.up ℤ) 0
  let tC :=
    (Stacks.SheafOfModules.Tensor.tensorComplex (pointRingedTopos (CommRingCat.of R)).O).obj K'
  let eC := e.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  (Functor.associator (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0)
      ((curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K) H).symm ≪≫
    Functor.isoWhiskerRight (pointTensorComplexIso K) H ≪≫
    Functor.associator e.inverse (s' ⋙ tC ⋙ eC) H ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.associator s' (tC ⋙ eC) H ≪≫
      Functor.isoWhiskerLeft s' (Functor.associator tC eC H)) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerLeft s' (Functor.isoWhiskerLeft tC
      (Functor.isoWhiskerLeft eC (DerivedCategory.homologyFunctorFactors _ i).symm ≪≫
        (Functor.associator eC DerivedCategory.Q
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i)).symm ≪≫
        Functor.isoWhiskerRight (e.functor.mapDerivedCategoryFactors).symm
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i) ≪≫
        Functor.associator DerivedCategory.Q e.functor.mapDerivedCategory
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i)))) ≪≫
    Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerLeft s'
      ((Functor.associator tC DerivedCategory.Q G).symm ≪≫
        Functor.isoWhiskerRight (pointDerivedTensorQIso K' (kFlat_pointModules_of_flat K b hK)) G ≪≫
        Functor.associator DerivedCategory.Q ((pointDerivedTensor (R := R)).obj
          (DerivedCategory.Q.obj K')) G)) ≪≫
    Functor.isoWhiskerLeft e.inverse ((Functor.associator s' DerivedCategory.Q _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0).symm
        ((pointDerivedTensor (R := R)).obj (DerivedCategory.Q.obj K') ⋙ G))

end TensorComplex

end AlgebraicGeometry.Space

end
