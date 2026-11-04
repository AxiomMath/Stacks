module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartLocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# Derived pullback of a perfect object of an algebraic space is perfect

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `E` be a perfect
object of `D(𝒪_Y)`. Then `Lf^*E` is a perfect object of `D(𝒪_X)`, for the small étale ringed
topoi of algebraic spaces and the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`.

## Main definitions

* `AlgebraicGeometry.Space.chartSpaceHom`: the morphism of chart spaces induced by a morphism of
  the underlying objects of étale charts of two algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`: the statement above.
* `AlgebraicGeometry.Space.isPerfect_unit`: the structure sheaf of an algebraic space, placed in
  degree zero, is perfect.

## References

* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The morphism of chart spaces induced by a morphism of the underlying objects of two étale
charts of different algebraic spaces. -/
def chartSpaceHom {V : SmallEtale B S hS X.1} {W : SmallEtale B S hS Y.1}
    (q : V.1.left ⟶ W.1.left) : chartSpace B S hS X V ⟶ chartSpace B S hS Y W :=
  ObjectProperty.homMk (yoneda.map q)

/-- If a morphism `q` of the underlying objects of étale charts `V` of `X` and `W` of `Y` is
compatible with `f` and the structure morphisms, then `chartSpaceHom q` followed by the chart
morphism of `W` equals the chart morphism of `V` followed by `f`. -/
theorem chartSpaceHom_comp_chartToSpace (f : X ⟶ Y) {V : SmallEtale B S hS X.1}
    {W : SmallEtale B S hS Y.1} (q : V.1.left ⟶ W.1.left)
    (hq : yoneda.map q ≫ W.1.hom = V.1.hom ≫ f.hom) :
    chartSpaceHom q ≫ chartToSpace B S hS Y W = chartToSpace B S hS X V ≫ f :=
  ObjectProperty.hom_ext _ hq

/-- The derived pullback of a perfect object of `D(𝒪_Y)` along a morphism `f : X ⟶ Y` of
algebraic spaces is a perfect object of `D(𝒪_X)`. -/
theorem isPerfect_smallEtaleDerivedModulePullback (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS f).obj E) := by
  refine isPerfect_of_hasStrictlyPerfectModel_chart _ fun U => ?_
  let R : Presieve U := fun V _ => ∃ (W : SmallEtale B S hS Y.1) (q : V.1.left ⟶ W.1.left),
    yoneda.map q ≫ W.1.hom = V.1.hom ≫ f.hom ∧
      HasStrictlyPerfectModel B S hS
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj E)
  refine ⟨R, ?_, fun V g ⟨W, q, hq, hW⟩ => ?_⟩
  · rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro z
    obtain ⟨A₀, a₀, ha₀S, ha₀E⟩ := Y.2.exists_atlas
    let W₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a₀, ha₀E⟩
    obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ := exists_chart_over B S hS f U W₀ ha₀S z
    obtain ⟨R₀, hR₀, hR₀mod⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect E hE W₀
    obtain ⟨W', m, ⟨W'', m', m'', hm'', rfl⟩, w, hw⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS Y.1 _).1 hR₀
        (((BigFppfOver.toScheme B S hS).map q₁) z₁)
    obtain ⟨T', π, p', hp', -, w', hw'₁, -⟩ :=
      exists_chart_pullback B S hS f V₁ q₁ hq₁ (m' ≫ m'') z₁ w hw.symm
    refine ⟨T', π ≫ π₁, Sieve.le_generate R _ _ (show R (π ≫ π₁) from ⟨W', p', hp',
      (hR₀mod m'' hm'').chartRestriction m'⟩), w', ?_⟩
    rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw'₁, hz₁]
  · exact (hW.smallEtaleDerivedModulePullback_obj (chartSpaceHom q)).of_iso
      ((smallEtaleDerivedModulePullbackCompIso B S hS (chartSpaceHom q)
          (chartToSpace B S hS Y W)).app E ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS
          (chartSpaceHom_comp_chartToSpace f q hq)).app E ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS X V) f).app E).symm)

/-- The structure sheaf of an algebraic space, placed in degree zero, is a perfect object of
`D(𝒪_X)`. -/
theorem isPerfect_unit (X : AlgebraicSpaces B S hS) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj
        (SheafOfModules.unit _)) := by
  refine isPerfect_of_hasStrictlyPerfectModel_chart _ fun U => ⟨fun _ _ => True, ?_,
    fun V g _ => ?_⟩
  · have : Sieve.generate (fun _ _ => True : Presieve U) = ⊤ := by
      rw [eq_top_iff]
      intro W f _
      exact ⟨W, 𝟙 W, f, trivial, Category.id_comp f⟩
    rw [this]
    exact (SmallEtale.topology B S hS X.1).top_mem U
  · let Y := chartSpace B S hS X V
    refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)), fun j => ?_,
      ⟨0, 0, inferInstance, inferInstance⟩,
      ⟨smallEtaleDerivedModulePullbackUnitIso (chartToSpace B S hS X V) ≪≫
        (DerivedCategory.singleFunctorIsoCompQ _ 0).app _⟩⟩
    by_cases hj : j = 0
    · subst hj
      exact (isRetractOfFiniteFree_self _).of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm
    · exact ⟨0, 0, 0, (HomologicalComplex.isZero_single_obj_X _ 0 _ j hj).eq_of_src _ _⟩

end AlgebraicGeometry.Space

end
