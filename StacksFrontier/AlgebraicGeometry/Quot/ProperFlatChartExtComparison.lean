module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartTildePullback
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexShortExact

/-!
# The coefficient `𝒪_X[0] ⊗ f^*(M~[0])` of 08JR at a chart of `Spaces'_{fp, flat, proper}`

Let `x` be a flat, proper, finitely presented algebraic space `f : X → Spec A`. At
`𝒢^• = 𝒪_X[0]` and `ℱ = M~`, the complex `𝒢^• ⊗ f^*ℱ` of [Stacks, Tag 08JR]
(`AlgebraicGeometry.Space.tensorPullbackComplex`) is `(𝒪_X ⊗_A M)[0]`, naturally in the
`A`-module `M`.

The identification is first made for an arbitrary additive bifunctor `F : 𝒜 ⥤ ℬ ⥤ 𝒟`, an object
`U` of `𝒜` and a functor `T` with `F(U, T(−)) ≅ P`
(`CochainComplex.KFlatBifunctor.singleSingleIso`): the total complex of `U[0]` and `T(M)[0]` is
the termwise complex (`CochainComplex.KFlatBifunctor.totalSingleIso`), which is `F(U, T(M))[0]`.
It is then read at `F = 𝒪_X ⊗ f^*(−)`, `U = 𝒪_X`, `T = (−)~` and
`P = 𝒪_X ⊗_A −` (`AlgebraicGeometry.Space.ProperFlatLift.chartTensorPullbackTildeIso`).

## Main definitions

* `CochainComplex.KFlatBifunctor.singleSingleIso`: `Tot F(U[0], T(M)[0]) ≅ P(M)[0]`.
* `AlgebraicGeometry.Space.ProperFlatLift.chartCoefficientIso`:
  `𝒪_X[0] ⊗ f^*(M~[0]) ≅ (𝒪_X ⊗_A M)[0]`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.chartCoefficientIso_hom_naturality`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Two complexes concentrated in degree `0` -/

namespace HomologicalComplex

variable {ι : Type*} {V W : Type*} [Category V] [Category W] [HasZeroMorphisms V]
  [HasZeroMorphisms W] [HasZeroObject V] [HasZeroObject W] (c : ComplexShape ι) [DecidableEq ι]
  (j : ι)

/-- The comparison `F(X[j]) ≅ F(X)[j]` is natural in the functor `F`. -/
theorem singleMapHomologicalComplex_hom_app_naturality_functor {F G : V ⥤ W}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G) (U : V) :
    (NatTrans.mapHomologicalComplex τ c).app ((single V c j).obj U) ≫
        (singleMapHomologicalComplex G c j).hom.app U =
      (singleMapHomologicalComplex F c j).hom.app U ≫ (single W c j).map (τ.app U) := by
  apply to_single_hom_ext
  rw [comp_f, comp_f, NatTrans.mapHomologicalComplex_app_f,
    singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_hom_app_self,
    single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (τ.naturality_assoc _ _).symm

end HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {𝒜 ℬ 𝒟 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒟] [Category 𝒞]
  [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒟] (F : 𝒜 ⥤ ℬ ⥤ 𝒟) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex 𝒜 (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex ℬ (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  (U : 𝒜) {T : 𝒞 ⥤ ℬ} {P : 𝒞 ⥤ 𝒟} (ν : T ⋙ F.obj U ≅ P)

/-- The functor `F(−, N)` preserves zero morphisms. -/
instance flip_obj_preservesZeroMorphisms (N : ℬ) : (F.flip.obj N).PreservesZeroMorphisms where
  map_zero _ _ := by rw [Functor.flip_obj_map, Functor.map_zero, NatTrans.app_zero]

/-- The termwise complex `p ↦ F(U[0]^p, N)` of `U[0]` is `F(U, N)[0]`. -/
def rowComplexSingleIso (N : ℬ) :
    rowComplex F ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj U) N ≅
      (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).obj ((F.obj U).obj N) :=
  (HomologicalComplex.singleMapHomologicalComplex (F.flip.obj N) (ComplexShape.up ℤ) 0).app U

omit [Abelian ℬ] [∀ X, (F.obj X).Additive] [∀ (K₁ : HomologicalComplex 𝒜 (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex ℬ (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- `rowComplexSingleIso` is natural in `N`. -/
theorem rowComplexSingleIso_hom_naturality {N N' : ℬ} (q : N ⟶ N') :
    rowComplexMapRight F ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj U) q ≫
        (rowComplexSingleIso F U N').hom =
      (rowComplexSingleIso F U N).hom ≫
        (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map ((F.obj U).map q) :=
  HomologicalComplex.singleMapHomologicalComplex_hom_app_naturality_functor
    (ComplexShape.up ℤ) 0 (F.flip.map q) U

/-- **`Tot F(U[0], T(M)[0]) ≅ P(M)[0]`** for `ν : F(U, T(−)) ≅ P`: the total complex is the
termwise complex `p ↦ F(U[0]^p, T(M))`, which is `F(U, T(M))[0]`. -/
def singleSingleIso (M : 𝒞) :
    HomologicalComplex.mapBifunctor ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0).obj U)
        ((HomologicalComplex.single ℬ (ComplexShape.up ℤ) 0).obj (T.obj M)) F (ComplexShape.up ℤ) ≅
      (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).obj (P.obj M) :=
  totalSingleIso F _ (T.obj M) ≪≫ rowComplexSingleIso F U (T.obj M) ≪≫
    (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).mapIso (ν.app M)

/-- **`singleSingleIso` is natural.** -/
theorem singleSingleIso_hom_naturality {M N : 𝒞} (g : M ⟶ N) :
    HomologicalComplex.mapBifunctorMap (𝟙 _)
        ((HomologicalComplex.single ℬ (ComplexShape.up ℤ) 0).map (T.map g)) F
        (ComplexShape.up ℤ) ≫ (singleSingleIso F U ν N).hom =
      (singleSingleIso F U ν M).hom ≫
        (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map (P.map g) := by
  have h₃ : (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map ((F.obj U).map (T.map g)) ≫
      (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map (ν.hom.app N) =
      (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map (ν.hom.app M) ≫
        (HomologicalComplex.single 𝒟 (ComplexShape.up ℤ) 0).map (P.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (ν.hom.naturality g)
  simp only [singleSingleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% (totalSingleIso_hom_naturality_right F _ (T.map g)),
    reassoc_of% (rowComplexSingleIso_hom_naturality F U (T.map g)), h₃]

end CochainComplex.KFlatBifunctor

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- One standard-model line, scoped to this file: the base declaration
-- `AlgebraicGeometry.Space.tensorPullbackComplex` and the instances it is used with in
-- `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/TensorPullbackComplexShortExact.lean` are stated
-- in the model `HasDerivedCategory.standard`.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)

attribute [local instance high] smallEtaleModules_abelian
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

/-- `tensorPullbackComplex` at `𝒪_X[0]`, on a map of modules placed in degree `0`, is the map of
total complexes of `tensorPullbackBifunctor`. -/
theorem tensorPullbackComplex_map_single
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      (schemeSpace (algebraOver A B S hS toS hA)))} (q : N ⟶ N') :
    (tensorPullbackComplex (chartStructureMap x hx) (structureSingleComplex x.obj.obj.left)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q) =
      HomologicalComplex.mapBifunctorMap (𝟙 _)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q)
        (tensorPullbackBifunctor (chartStructureMap x hx)) (ComplexShape.up ℤ) :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

/-- **`𝒪_X[0] ⊗ f^*(M~[0]) ≅ (𝒪_X ⊗_A M)[0]`**: `CochainComplex.KFlatBifunctor.singleSingleIso`
at `𝒪_X ⊗ f^*(−)` and `𝒪_X ⊗ f^*(M~) ≅ 𝒪_X ⊗_A M`. -/
def chartCoefficientIso (M : ModuleCat.{u} A) :
    (tensorPullbackComplex (chartStructureMap x hx) (structureSingleComplex x.obj.obj.left)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((affineBaseTilde A B S hS toS hA).obj M)) ≅
      (HomologicalComplex.single (SheafOfModules.{u}
          (ringedToposStructureRingSheaf B S hS x.obj.obj.left)) (ComplexShape.up ℤ) 0).obj
        ((chartTensorModule x hx).obj M) :=
  CochainComplex.KFlatBifunctor.singleSingleIso (tensorPullbackBifunctor (chartStructureMap x hx))
    (SheafOfModules.unit _) (chartTensorPullbackTildeIso x hx) M

/-- **`chartCoefficientIso` is natural in the `A`-module `M`.** -/
theorem chartCoefficientIso_hom_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    (tensorPullbackComplex (chartStructureMap x hx) (structureSingleComplex x.obj.obj.left)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((affineBaseTilde A B S hS toS hA).map g)) ≫ (chartCoefficientIso x hx N).hom =
      (chartCoefficientIso x hx M).hom ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((chartTensorModule x hx).map g) := by
  rw [tensorPullbackComplex_map_single]
  exact CochainComplex.KFlatBifunctor.singleSingleIso_hom_naturality
    (tensorPullbackBifunctor (chartStructureMap x hx)) (SheafOfModules.unit _)
    (chartTensorPullbackTildeIso x hx) g

end AlgebraicGeometry.Space.ProperFlatLift

end
