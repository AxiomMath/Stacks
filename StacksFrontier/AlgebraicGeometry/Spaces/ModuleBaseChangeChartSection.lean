module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapUnitSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators

/-!
# The base change map of a square of algebraic spaces, on the sections over an étale chart

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`
and let `K` be an `𝒪_X`-module.  `AlgebraicGeometry.Space.moduleBaseChangeMap` is the base change
map `g^*f_*K ⟶ f'_*(i^*K)` of the square.  This file computes its value on the canonical sections
of `g^*f_*K`: the sections `AlgebraicGeometry.Space.modulePullbackUnitSection` over the chart of
`Y'` of a commuting diagram `d` of étale scheme charts over `g`, which generate `g^*f_*K` locally
by `AlgebraicGeometry.Space.spanSieve_modulePullbackChart_mem`.

## Main results

* `AlgebraicGeometry.Space.val_app_modulePullbackUnitSection_moduleBaseChangeMap`: for any
  commutative square, the base change map sends the unit section of `s` at `d` to the chart
  component at `d` of the direct image along `f` of the unit along `i`, followed by the
  comparison of the two composite direct images around the square, evaluated at `s`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y)

/-- **The base change map on the canonical sections of `g^*f_*K`.**  On the chart of `Y'` of a
commuting diagram `d` of étale scheme charts over `g`, the base change map of the square carries
the unit section of a section `s` of `f_*K` to the chart component at `d` of the direct image
along `f` of the unit along `i`, followed by the comparison of the two composite direct images
around the square, applied to `s`.  The square is only required to commute. -/
theorem val_app_modulePullbackUnitSection_moduleBaseChangeMap (comm : i ≫ f = f' ≫ g)
    (K : Modules.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y'.1 Y.1 g.hom)
    (s : ((modulePushforward B S hS f).obj K).val.obj (op d.V)) :
    ((moduleBaseChangeMap f g f' i comm).app K).val.app (op d.U)
        (modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj K) d s) =
      modulePushforwardCounitApp B S hS g
          ((modulePullback B S hS i ⋙ modulePushforward B S hS f').obj K) d
        (((modulePushforward B S hS f).map
              ((modulePullbackAdjunction B S hS i).unit.app K) ≫
            (modulePushforwardSquareComparison B S hS i f' f g comm).app
              ((modulePullback B S hS i).obj K)).val.app (op d.V) s) := by
  have hu : modulePullbackUnitSection B S hS g ((modulePushforward B S hS f).obj K) d s =
      modulePushforwardCounitApp B S hS g
          ((modulePushforward B S hS f ⋙ modulePullback B S hS g).obj K) d
        (((modulePullbackAdjunction B S hS g).unit.app
          ((modulePushforward B S hS f).obj K)).val.app (op d.V) s) := rfl
  rw [hu, ← modulePushforwardCounitApp_map B S hS g
    ((moduleBaseChangeMap f g f' i comm).app K) d]
  refine congrArg (modulePushforwardCounitApp B S hS g
    ((modulePullback B S hS i ⋙ modulePushforward B S hS f').obj K) d) ?_
  exact (congrArg
    (fun a : (modulePushforward B S hS f).obj K ⟶
        (modulePushforward B S hS g).obj
          ((modulePushforward B S hS f').obj ((modulePullback B S hS i).obj K)) ↦
      a.val.app (op d.V) s)
    (unit_comp_modulePushforward_map_moduleBaseChangeMap B S hS i f' f g comm K)).symm

end AlgebraicGeometry.Space

end
