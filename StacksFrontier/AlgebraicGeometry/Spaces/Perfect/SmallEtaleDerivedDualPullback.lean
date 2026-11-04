module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMapPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal

/-!
# The derived dual of a perfect object commutes with derived pullback

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `E ∈ D(𝒪_Y)` perfect. Then

`Lf^*(E^∨) ≅ (Lf^*E)^∨`,

where `E^∨ = R𝓗om(E, 𝒪_Y)` is `AlgebraicGeometry.Space.smallEtaleDerivedDual`. This is the map of
Stacks 08I3 at `L = 𝒪_Y[0]`, invertible because `E` is perfect
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect`), followed by
`Lf^*𝒪_Y[0] ≅ 𝒪_X[0]`.

The file also records the per-chart covering form of the étale locality of cohomological
amplitude: an object of `D(𝒪_X)` whose derived pullback to every chart of an étale covering of
every chart lies in `D^{≤ n}` lies itself in `D^{≤ n}`.

## Main results

* `smallEtaleDerivedModulePullbackDualIso`: `Lf^*(E^∨) ≅ (Lf^*E)^∨` for `E` perfect.
* `isLE_of_forall_covering_isLE_smallEtaleDerivedModulePullback_chartToSpace`: `D^{≤ n}` is local
  on the étale charts, in per-chart covering form.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The derived dual of a perfect object commutes with derived pullback.** For a morphism
`f : X ⟶ Y` of algebraic spaces and `E ∈ D(𝒪_Y)` perfect, `Lf^*(E^∨) ≅ (Lf^*E)^∨`: the map of
Stacks 08I3 at `(E, 𝒪_Y[0])`, followed by `Lf^*𝒪_Y[0] ≅ 𝒪_X[0]`. -/
def smallEtaleDerivedModulePullbackDualIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E) :
    (smallEtaleDerivedModulePullback B S hS f).obj (smallEtaleDerivedDual B S hS Y E) ≅
      smallEtaleDerivedDual B S hS X ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  haveI := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isPerfect f E hE
    ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)))
  asIso (smallEtaleDerivedPullbackSheafHomMap f E
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)))) ≪≫
    ((smallEtaleDerivedSheafHom B S hS X).obj
      (op ((smallEtaleDerivedModulePullback B S hS f).obj E))).mapIso
      (smallEtaleDerivedModulePullbackUnitIso f)

/-- **Cohomological amplitude `≤ n` is local on the étale charts, in per-chart covering form.**
If every chart `U` of `X` has an étale covering `{V → U}` such that the derived pullback of `K` to
each chart space `V` lies in `D^{≤ n}`, then `K` lies in `D^{≤ n}`. -/
theorem isLE_of_forall_covering_isLE_smallEtaleDerivedModulePullback_chartToSpace
    {X : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (n : ℤ)
    (h : ∀ U : SmallEtale B S hS X.1,
      ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
        ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj K).IsLE n) :
    K.IsLE n := by
  choose R hR hK using h
  refine isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (V := fun k : Σ U : SmallEtale B S hS X.1, Σ V : SmallEtale B S hS X.1,
      { g : V ⟶ U // R U g } => k.2.1) (fun W => ?_) K n fun k => hK k.1 k.2.2.1 k.2.2.2
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hR W)
  rintro Z g ⟨V, a, f, hf, rfl⟩
  exact ⟨⟨W, V, f, hf⟩, ⟨a⟩⟩

end AlgebraicGeometry.Space

end
