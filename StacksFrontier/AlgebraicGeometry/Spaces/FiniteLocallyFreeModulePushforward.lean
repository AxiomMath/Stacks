module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartSectionsProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeAffineChartBijective

/-!
# The direct image of a finite locally free module along a finite locally free morphism

Let `f : X ⟶ Y` be a finite locally free morphism of algebraic spaces over a scheme `S` (Stacks
03ZV, `AlgebraicGeometry.Space.IsFiniteLocallyFree`). The direct image of a finite locally free
`𝒪_X`-module along `f` is a finite locally free `𝒪_Y`-module.

## Main results

* `exists_affine_chartDiagram_isIso_chartLift_bijective`: over an affine étale chart `V` of `Y`
  there is an affine chart `W = V ×_Y X` of `X` over which the sections of every direct image are
  the sections over `W`.
* `module_finite_projective_chartRing_of_isFiniteLocallyFree`: for such a chart diagram, `𝒪_X(W)`
  is a finite projective `𝒪_Y(V)`-algebra.
* `isFiniteLocallyFreeOnSite_modulePushforward_of_isFiniteLocallyFree`: the direct image of a
  finite locally free module is finite locally free.

## References

* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **An affine chart above an affine chart, with bijective counit.**  For an affine `f : X ⟶ Y`
and an affine étale chart `V` of `Y` there is an affine étale chart `W` of `X` with a chart diagram
`W ⟶ V` over `f` whose cartesian form `W ⟶ V ×_Y X` is an isomorphism and over which the
canonical map `(f_*F)(V) ⟶ F(W)` is bijective for every `𝒪_X`-module `F`. -/
theorem exists_affine_chartDiagram_isIso_chartLift_bijective (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V)) :
    ∃ (W : SmallEtale B S hS X.1)
      (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom),
      IsAffine (chartScheme W) ∧ IsIso (chartLift B S hS f ⟨W, V, b, hb⟩) ∧
      ∀ F : Modules.{u, u} B S hS X.1 X.2,
        Function.Bijective (modulePushforwardCounitApp B S hS f F ⟨W, V, b, hb⟩) := by
  obtain ⟨W, b, hb, hWa, hiso⟩ := exists_affine_chart_isIso_chartLift f hf V hV
  let e : ChartDiagram B S hS X.1 Y.1 f.hom := ⟨W, V, b, hb⟩
  have hsurj : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
      (chartLift B S hS f e)).hom :=
    isSurjective_of_isIso B S hS ((SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
      (chartLift B S hS f e))
  have hpbW : IsPullback ((comparisonFunctor B S hS X).map (𝟙 W))
      ((comparisonFunctor B S hS X).map (𝟙 W)) (chartLift B S hS f e) (chartLift B S hS f e) := by
    rw [CategoryTheory.Functor.map_id]
    exact IsKernelPair.id_of_mono _
  have hk : IsSurjective B S hS
      ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map (𝟙 W))).hom := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact isSurjective_of_isIso B S hS (𝟙 _)
  exact ⟨W, b, hb, hWa, hiso, fun F => ⟨injective_modulePushforwardCounitApp f F e hsurj,
    fun p => exists_modulePushforwardCounitApp_eq f F e hsurj (𝟙 W) (𝟙 W) hpbW (𝟙 W) hk p rfl⟩⟩

/-- **The functions on the affine chart above an affine chart form a finite projective module.**
For a finite locally free `f : X ⟶ Y` and a chart diagram `d : W ⟶ V` over `f` with `V` affine
whose counit `(f_*𝒪_X)(V) ⟶ 𝒪_X(W)` is bijective, `𝒪_X(W)` is a finite projective
`𝒪_Y(V)`-algebra under pullback of functions. -/
theorem module_finite_projective_chartRing_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hV : IsAffine (chartScheme d.V))
    (hbij : Function.Bijective (modulePushforwardCounitApp B S hS f
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) d)) :
    letI := (chartDiagramPullback B S hS f d).hom.toAlgebra
    Module.Finite (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) ∧
      Module.Projective (chartRing B S hS Y.1 Y.2 d.V) (chartRing B S hS X.1 X.2 d.U) := by
  let := (chartDiagramPullback B S hS f d).hom.toAlgebra
  obtain ⟨h1, h2⟩ := module_finite_projective_sections_of_isFiniteLocallyFreeOnSite Y.2
    (pushforwardStructureModule B S hS f) hf.2 d.V hV
  let e := LinearEquiv.ofBijective (modulePushforwardCounitLinear B S hS f
    (SheafOfModules.unit _) d) hbij
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- **The direct image of a finite locally free module along a finite locally free morphism of
algebraic spaces is finite locally free.** -/
theorem isFiniteLocallyFreeOnSite_modulePushforward_of_isFiniteLocallyFree (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) (E : Modules.{u, u} B S hS X.1 X.2)
    (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePushforward B S hS f).obj E) := by
  have := SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hE
  have hq := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS f hf.1 E
    inferInstance
  refine isFiniteLocallyFreeOnSite_of_finite_projective_sections Y.2 _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hq) fun V hV => ?_
  obtain ⟨W, b, hb, hWa, -, hbij⟩ :=
    exists_affine_chartDiagram_isIso_chartLift_bijective B S hS f hf.1 V hV
  let := (chartDiagramPullback B S hS f ⟨W, V, b, hb⟩).hom.toAlgebra
  let : Module (chartRing B S hS Y.1 Y.2 V) (E.val.obj (op W)) :=
    Module.compHom _ (chartDiagramPullback B S hS f ⟨W, V, b, hb⟩).hom
  have : IsScalarTower (chartRing B S hS Y.1 Y.2 V) (chartRing B S hS X.1 X.2 W)
      (E.val.obj (op W)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hA1, hA2⟩ := module_finite_projective_chartRing_of_isFiniteLocallyFree B S hS f hf
    ⟨W, V, b, hb⟩ hV (hbij _)
  obtain ⟨hE1, hE2⟩ := module_finite_projective_sections_of_isFiniteLocallyFreeOnSite X.2 E hE W hWa
  let eE := LinearEquiv.ofBijective (modulePushforwardCounitLinear B S hS f E ⟨W, V, b, hb⟩)
    (hbij E)
  have : Module.Finite (chartRing B S hS Y.1 Y.2 V) (E.val.obj (op W)) :=
    Module.Finite.trans (chartRing B S hS X.1 X.2 W) _
  have : Module.Projective (chartRing B S hS Y.1 Y.2 V) (E.val.obj (op W)) :=
    Module.Projective.trans _ (chartRing B S hS X.1 X.2 W) _
  exact ⟨Module.Finite.equiv eE.symm, Module.Projective.of_equiv eE.symm⟩

end AlgebraicGeometry.Space

end
