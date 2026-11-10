module

public import StacksFrontier.AlgebraicGeometry.Modules.DualSheafStalk.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact

/-!
# Naturality of the stalk of a dual and of a reflexive hull

For a morphism `f : E ⟶ F` of finitely presented `𝒪_X`-modules, the stalk at `x` of the dual
`dualMap f` is, under `dualStalkEquiv`, precomposition with the stalk map `f_x`, and the stalk at
`x` of `doubleDualMap f : E^∨∨ ⟶ F^∨∨` is, under `dualEvalEquiv`, the double `𝒪_{X,x}`-linear
transpose of `f_x`.

## Main results

* `dualStalkEquiv_stalkHom_dualMap_symm`: the stalk of `dualMap f` applied to a transported
  functional is the transport of the precomposition.
* `dualEvalEquiv_stalkHom_doubleDualMap`: the stalk of the double dual of a morphism is the
  double transpose of its stalk map.

## References

* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-- The stalk map of `dualMap f` carries the functional transported from `ψ` to the functional
transported from `ψ ∘ f_x`. -/
public theorem dualStalkEquiv_stalkHom_dualMap_symm {E F : X.Modules} [E.IsFinitePresentation]
    [F.IsFinitePresentation] (f : E ⟶ F) (x : X)
    (ψ : Module.Dual (ringStalk X.sheaf x) (modStalk F x)) :
    stalkHom (dualMap f) x ((dualStalkEquiv F x).symm ψ)
      = (dualStalkEquiv E x).symm (Module.Dual.transpose (stalkHom f x) ψ) := by
  refine (dualStalkEquiv E x).injective (LinearMap.ext fun m => ?_)
  refine (dualStalkEquiv_stalkHom_dualMap f x ((dualStalkEquiv F x).symm ψ) m).trans ?_
  refine (DFunLike.congr_fun ((dualStalkEquiv F x).apply_symm_apply ψ) (stalkHom f x m)).trans ?_
  exact (DFunLike.congr_fun
    ((dualStalkEquiv E x).apply_symm_apply (Module.Dual.transpose (stalkHom f x) ψ)) m).symm

/-- Read through `dualEvalEquiv` at `E` and at `F`, the stalk at `x` of
`doubleDualMap f : E^∨∨ ⟶ F^∨∨` is the double `𝒪_{X,x}`-linear transpose of `f_x`. -/
public theorem dualEvalEquiv_stalkHom_doubleDualMap {E F : X.Modules}
    [E.IsFinitePresentation] [F.IsFinitePresentation] [(dualSheaf E).IsFinitePresentation]
    [(dualSheaf F).IsFinitePresentation] (f : E ⟶ F) (x : X)
    (Φ : modStalk (dualSheaf (dualSheaf E)) x) :
    dualEvalEquiv F x (stalkHom (doubleDualMap f) x Φ)
      = Module.Dual.transpose (Module.Dual.transpose (stalkHom f x))
          (dualEvalEquiv E x Φ) := by
  refine LinearMap.ext fun ψ => ?_
  change dualStalkEquiv (dualSheaf F) x (stalkHom (dualMap (dualMap f)) x Φ)
      ((dualStalkEquiv F x).symm ψ)
    = dualStalkEquiv (dualSheaf E) x Φ
      ((dualStalkEquiv E x).symm (Module.Dual.transpose (stalkHom f x) ψ))
  refine (dualStalkEquiv_stalkHom_dualMap (dualMap f) x Φ ((dualStalkEquiv F x).symm ψ)).trans ?_
  exact congrArg (dualStalkEquiv (dualSheaf E) x Φ)
    (dualStalkEquiv_stalkHom_dualMap_symm f x ψ)

end Stacks.AlgebraicGeometry.ReflexiveModules

end
