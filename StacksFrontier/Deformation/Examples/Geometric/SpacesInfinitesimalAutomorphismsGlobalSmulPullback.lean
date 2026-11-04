module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLinearDerivations

/-!
# Inverse image of modules carries multiplication by a function to multiplication by its pullback

Let `h : Y ⟶ X` be a morphism of algebraic spaces, `a` a global function on `X` and `b` a global
function on `Y` which is the pullback of `a`: on every commutative diagram of étale scheme charts
over `h`, pullback of regular functions along the vertical morphism carries the value of `a` to the
value of `b`.  Then for every `𝒪_X`-module `M` the inverse image along `h` of multiplication by `a`
on `M` is multiplication by `b` on `h^*M`.

Both sides are morphisms out of `h^*M`, so they are determined by their transposes along
`h^* ⊣ h_*` read through the chartwise universal property of the direct image
(`AlgebraicGeometry.Space.modulePullbackHomFMap`), whose values are the values of the morphisms on
the chart sections; on a chart section of `s` the left-hand side gives the chart section of
`a · s`, which is the pullback of `a` times the chart section of `s`.

The global function pulled back from an affine object `T` of the site along a morphism `f : X ⟶ T`
(`AlgebraicGeometry.Space.pullbackToGlobalFunctions`) is compatible in this sense with
precomposition: `chartDiagramPullback_pullbackToGlobalFunctions`.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_globalSmul_of_chartDiagramPullback`:
  `h^*(a ·) = (h^♯a) ·`.
* `AlgebraicGeometry.Space.chartDiagramPullback_pullbackToGlobalFunctions`: the pullback of a
  function from `T` along `f`, pulled back along `h`, is its pullback along `h ≫ f`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of multiplication by a global function is multiplication by its
pullback.**  For `h : Y ⟶ X`, a global function `a` on `X` and a global function `b` on `Y` whose
value on the source of every chart diagram over `h` is the pullback of the value of `a` on its
target, `h^*(a ·) = b ·` on `h^*M` for every `𝒪_X`-module `M`. -/
theorem modulePullback_map_globalSmul_of_chartDiagramPullback {X Y : AlgebraicSpaces B S hS}
    (h : Y ⟶ X)
    (a : GlobalSectionRing (structureRingSheaf B S hS X))
    (b : GlobalSectionRing (structureRingSheaf B S hS Y))
    (hab : ∀ d : ChartDiagram B S hS Y.1 X.1 h.hom,
      chartDiagramPullback B S hS h d (a.1 (op d.V)) = b.1 (op d.U))
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS h).map (globalSmul _ a M) =
      globalSmul _ b ((modulePullback B S hS h).obj M) := by
  refine ((modulePullbackAdjunction B S hS h).homEquiv _ _).injective ?_
  refine (modulePushforwardHomEquiv B S hS h _ _).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d => funext fun s => ?_)
  show (modulePullbackHomFMap B S hS h M _ ((modulePullback B S hS h).map (globalSmul _ a M))).app
      d s = (modulePullbackHomFMap B S hS h M _ (globalSmul _ b _)).app d s
  refine (modulePullbackHomFMap_app B S hS h M _ _ d s).trans
    (Eq.trans ?_ (modulePullbackHomFMap_app B S hS h M _ _ d s).symm)
  rw [modulePullbackUnitSection_eq_modulePullbackChartSection]
  refine (modulePullbackChartSection_map B S hS h M (globalSmul _ a M) d s).trans ?_
  exact (modulePullbackChartSection_smul B S hS h M d (a.1 (op d.V)) s).trans
    (congrArg (· • modulePullbackChartSection B S hS h M d s) (hab d))

/-- **The pullback of a function from an affine object of the site, pulled back along a chart
diagram, is its pullback along the composite.**  For `f : X ⟶ T` and `h : Y ⟶ X`, on a chart
diagram `d` over `h` the vertical pullback of the value of `f^♯r` on `d.V` is the value of
`(h ≫ f)^♯r` on `d.U`: both are the pullback of `r` along `d.U ⟶ d.V ⟶ T`. -/
theorem chartDiagramPullback_pullbackToGlobalFunctions {X Y : AlgebraicSpaces B S hS} (h : Y ⟶ X)
    (T : BigFppfOver B S hS) (f : X ⟶ schemeSpace T)
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (d : ChartDiagram B S hS Y.1 X.1 h.hom) :
    chartDiagramPullback B S hS h d ((pullbackToGlobalFunctions B S hS X T f r).1 (op d.V)) =
      (pullbackToGlobalFunctions B S hS Y T (h ≫ f) r).1 (op d.U) := by
  have key : d.g ≫ yoneda.preimage (d.V.1.hom ≫ f.hom) =
      yoneda.preimage (d.U.1.hom ≫ (h ≫ f).hom) := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    show yoneda.map d.g ≫ d.V.1.hom ≫ f.hom = d.U.1.hom ≫ h.hom ≫ f.hom
    rw [← Category.assoc, ← d.comm, Category.assoc]
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (d.V.1.hom ≫ f.hom))).op).hom r) =
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (d.U.1.hom ≫ (h ≫ f).hom))).op).hom r
  rw [← key, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

end AlgebraicGeometry.Space

end
