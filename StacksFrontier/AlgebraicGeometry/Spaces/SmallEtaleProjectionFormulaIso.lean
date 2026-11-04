module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The projection formula for algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces and
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
a cartesian square with `g` étale and representable.  By the hexagon of Stacks 0E48 the pullback
along `g` of the projection formula map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is, up to the
isomorphisms of Stacks 07A4 and the étale base change isomorphisms, the projection formula map of
`f'` at `L(g')^*E` and `Lg^*K`.  This is the step "we may work étale locally on `Y`" of the proof
of Stacks 08IN.

## Main results

* `AlgebraicGeometry.Space.isIso_map_smallEtaleProjectionFormulaMap_iff`
* `AlgebraicGeometry.Space.isIso_smallEtaleProjectionFormulaMap`: Stacks 08IN.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace Stacks.CategoryTheory

/-- In a commutative hexagon `a ≫ b ≫ c = d ≫ e ≫ k` whose edges `a`, `b`, `e`, `k` are
invertible, `d` is invertible if and only if `c` is. -/
theorem isIso_iff_isIso_of_comp₃_eq {C : Type*} [Category C] {P Q R T U V : C} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : R ⟶ T} {d : P ⟶ U} {e : U ⟶ V} {k : V ⟶ T}
    (h : a ≫ b ≫ c = d ≫ e ≫ k) (ha : IsIso a) (hb : IsIso b) (he : IsIso e) (hk : IsIso k) :
    IsIso d ↔ IsIso c := by
  constructor
  · intro hd
    have : IsIso (a ≫ b ≫ c) := by rw [h]; infer_instance
    have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a _
    exact IsIso.of_isIso_comp_left b c
  · intro hc
    have : IsIso (d ≫ e ≫ k) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right d (e ≫ k)

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- **The projection formula map is compatible with étale base change.**  For a cartesian
square whose bottom arrow `g` is étale and representable, the pullback along `g` of the
projection formula map of `f` at `(E, K)` is invertible if and only if the projection formula
map of `f'` at `(L(g')^*E, Lg^*K)` is. -/
theorem isIso_map_smallEtaleProjectionFormulaMap_iff (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso ((smallEtaleDerivedModulePullback B S hS g).map
        (smallEtaleProjectionFormulaMap B S hS f E K)) ↔
      IsIso (smallEtaleProjectionFormulaMap B S hS f'
        ((smallEtaleDerivedModulePullback B S hS g').obj E)
        ((smallEtaleDerivedModulePullback B S hS g).obj K)) := by
  have hex := Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y'))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X'))
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom E K
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w _ K)
  have h₁ := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g f' g' sq hg hrep E
  have h₂ := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g f' g' sq hg hrep
    (((smallEtaleDerivedTensor B S hS X).obj E).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj K))
  unfold smallEtaleDerivedModuleBaseChangeMap at h₁ h₂
  have h₃ : IsIso (Stacks.CategoryTheory.BaseChange.map
      (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w) E ×ₘ
        𝟙 ((smallEtaleDerivedModulePullback B S hS g).obj K)) :=
    (isIso_prod_iff _ _).mpr ⟨h₁, inferInstance⟩
  have h₄ : IsIso (𝟙 ((smallEtaleDerivedModulePullback B S hS g').obj E) ×ₘ
      (Stacks.AffineProjectionFormula.squareCompositeIso
        (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
        (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)).inv.app K) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have h₅ : IsIso (Stacks.CategoryTheory.BaseChange.map
      (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
      (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
      (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
      ((Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X)).obj
        (E, (smallEtaleDerivedModulePullback B S hS f).obj K))) := h₂
  unfold smallEtaleProjectionFormulaMap
  exact Stacks.CategoryTheory.isIso_iff_isIso_of_comp₃_eq hex inferInstance
    (Functor.map_isIso _ _) h₅ (Functor.map_isIso _ _)

/-- **Stacks 08IN.**  Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
algebraic spaces, `E ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`.  Then the projection formula map
`Rf_*(E) ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is an isomorphism. -/
@[stacks 08IN]
theorem isIso_smallEtaleProjectionFormulaMap (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : QcohDerived B S hS X E)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : QcohDerived B S hS Y K) :
    IsIso (smallEtaleProjectionFormulaMap B S hS f E K) := by
  refine isIso_of_isIso_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS Y.1) _ fun V => ?_
  have sq := isPullback_chartBaseChangeInclusion B S hS f V.1
  refine (isIso_map_smallEtaleProjectionFormulaMap_iff B S hS f (chartToSpace B S hS Y V.1)
    (chartBaseChangeProjection B S hS f V.1) (chartBaseChangeInclusion B S hS f V.1) sq
    (isEtale_chartToSpace B S hS Y V.1) (relativelyRepresentable_chartToSpace B S hS Y V.1)
    E K).2 ?_
  exact isIso_smallEtaleProjectionFormulaMap_of_isAffineSpace
    (chartBaseChangeProjection B S hS f V.1)
    (isQuasiCompact_chartBaseChangeProjection B S hS f V.1 hfqc)
    (isQuasiSeparated_chartBaseChangeProjection B S hS f V.1 hfqs)
    (isAffineSpace_chartSpace B S hS Y V.1 V.2) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
      (chartBaseChangeInclusion B S hS f V.1) E hE) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS Y V.1) K hK)

end AlgebraicGeometry.Space

end
