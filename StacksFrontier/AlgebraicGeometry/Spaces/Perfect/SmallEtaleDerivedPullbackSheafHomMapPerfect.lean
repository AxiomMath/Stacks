module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect

/-!
# The map of Stacks 08I3 on algebraic spaces out of a perfect object

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `K ∈ D(𝒪_Y)` perfect and `L ∈ D(𝒪_Y)`. Then
the canonical map of Stacks 08I3,

`Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)`,

is an isomorphism. This is the statement of Stacks 08I3 / 08JP for a perfect first variable, read
on the small étale ringed topoi of algebraic spaces.

The question is étale local on `X`. Every chart `U` of `X` is covered by charts `V` whose
composite `V ⟶ X ⟶ Y` factors as `V ⟶ W ⟶ Y` through a chart `W` of `Y` on which `K` has a
strictly perfect model (the covering used for Stacks 08H6,
`AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`). For such `V`, with
`v : V ⟶ X`, `w : W ⟶ Y` and `g : V ⟶ W`, the composition law
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_comp_iff`) gives

* `c^{v ≫ f} = Lv^*(c^f) ≫ c^v` at `(Lf^*K, Lf^*L)`, where `c^v` is invertible because `v` is
  étale and `Lf^*K` is perfect
  (`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale_of_isPerfect`);
* `c^{g ≫ w} = Lg^*(c^w) ≫ c^g` at `(Lw^*K, Lw^*L)`, where `c^w` is invertible because `w` is
  étale and `K` is perfect, and `c^g` because `Lw^*K` has a strictly perfect model
  (`Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel`).

Since `v ≫ f = g ≫ w`, `Lv^*(c^f)` is invertible on every such chart, and so `c^f` is
(`Space.isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace`).

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_congr`: the map only
  depends on the morphism through its value.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect`: **the map
  of Stacks 08I3 on algebraic spaces is invertible out of a perfect object.**

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **The map of Stacks 08I3 only depends on the morphism through its value**: for `f = f'`,
the map for `f` at `(K, L)` is invertible exactly when the map for `f'` is. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_congr {f f' : X ⟶ Y} (h : f = f')
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L) ↔
      IsIso (smallEtaleDerivedPullbackSheafHomMap f' K L) := by
  subst h
  rfl

/-- **The map of Stacks 08I3 on algebraic spaces is invertible out of a perfect object.** For a
morphism `f : X ⟶ Y` of algebraic spaces, `K ∈ D(𝒪_Y)` perfect and `L ∈ D(𝒪_Y)`, the canonical
map `Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)` is an isomorphism. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L) := by
  refine isIso_of_forall_covering_isIso_smallEtaleDerivedModulePullback_chartToSpace _
    fun U => ?_
  let R : Presieve U := fun V _ => ∃ (W : SmallEtale B S hS Y.1) (q : V.1.left ⟶ W.1.left),
    yoneda.map q ≫ W.1.hom = V.1.hom ≫ f.hom ∧
      HasStrictlyPerfectModel B S hS
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj K)
  refine ⟨R, ?_, fun V g ⟨W, q, hq, hW⟩ => ?_⟩
  · rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro z
    obtain ⟨A₀, a₀, ha₀S, ha₀E⟩ := Y.2.exists_atlas
    let W₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a₀, ha₀E⟩
    obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ := exists_chart_over B S hS f U W₀ ha₀S z
    obtain ⟨R₀, hR₀, hR₀mod⟩ := exists_hasStrictlyPerfectModel_chart_of_isPerfect K hK W₀
    obtain ⟨W', m, ⟨W'', m', m'', hm'', rfl⟩, w, hw⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS Y.1 _).1 hR₀
        (((BigFppfOver.toScheme B S hS).map q₁) z₁)
    obtain ⟨T', π, p', hp', -, w', hw'₁, -⟩ :=
      exists_chart_pullback B S hS f V₁ q₁ hq₁ (m' ≫ m'') z₁ w hw.symm
    refine ⟨T', π ≫ π₁, Sieve.le_generate R _ _ (show R (π ≫ π₁) from ⟨W', p', hp',
      (hR₀mod m'' hm'').chartRestriction m'⟩), w', ?_⟩
    rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw'₁, hz₁]
  · -- the chart `v : V ⟶ X`, the chart `w : W ⟶ Y` and `chartSpaceHom q : V ⟶ W` over `f`
    have hv := isEtale_chartToSpace B S hS X V
    have hw := isEtale_chartToSpace B S hS Y W
    have hcomm := chartSpaceHom_comp_chartToSpace f q hq
    -- `c^{v ≫ f}` is invertible: it is `c^{g ≫ w}`
    have hvf : IsIso (smallEtaleDerivedPullbackSheafHomMap (chartToSpace B S hS X V ≫ f) K L) := by
      rw [← isIso_smallEtaleDerivedPullbackSheafHomMap_congr hcomm,
        isIso_smallEtaleDerivedPullbackSheafHomMap_comp_iff]
      have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale_of_isPerfect _ hw K hK L
      have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel
        (chartSpaceHom q) hW
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj L)
      infer_instance
    -- so is `Lv^*(c^f) ≫ c^v`, with `c^v` invertible
    rw [isIso_smallEtaleDerivedPullbackSheafHomMap_comp_iff] at hvf
    have := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isEtale_of_isPerfect _ hv
      ((smallEtaleDerivedModulePullback B S hS f).obj K)
      (isPerfect_smallEtaleDerivedModulePullback f K hK)
      ((smallEtaleDerivedModulePullback B S hS f).obj L)
    exact IsIso.of_isIso_comp_right _
      (smallEtaleDerivedPullbackSheafHomMap (chartToSpace B S hS X V)
        ((smallEtaleDerivedModulePullback B S hS f).obj K)
        ((smallEtaleDerivedModulePullback B S hS f).obj L))

end AlgebraicGeometry.Space

end
