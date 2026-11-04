module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Stack

/-!
# The quasi-coherent modules of finite type form a stack

The projection `p_{fg} : 𝒬𝒞oh_{fg} ⟶ (Sch/S)_fppf` from the quasi-coherent modules of finite type
on the schemes of the big fppf site over `S` satisfies the three conditions of Stacks 026F.

## Main results

* `Stacks.QCoh.finiteTypeProjection_isStack`: **Stacks 04U4**.

## Implementation notes

The passage from the stack of all quasi-coherent modules to its full subcategory of modules of
finite type is `Stacks.QCoh.isStack_finiteTypeProjection`, which takes the stack property of the
projection from all quasi-coherent modules as its input; that input is Stacks 03YM,
`Stacks.QCoh.projection_isStack`, proved in full, so the statement here assumes nothing.

## References

* [Stacks Project, Tag 04U4](https://stacks.math.columbia.edu/tag/04U4)
* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

/-- **Stacks 04U4.** The projection from the quasi-coherent modules of finite type on the schemes
of the big fppf site over `S` to that site satisfies the three conditions of Stacks 026F: it is a
fibred category, the presheaves `Mor(x, y)` are sheaves, and descent data are effective. Finite
type is preserved by the pullbacks computing the strongly cartesian arrows of Stacks 04U3 and
descends along fppf coverings (Stacks 05AZ), so Stacks 04TU passes the stack of all
quasi-coherent modules, Stacks 03YM, to its full subcategory of modules of finite type. -/
@[stacks 04U4]
theorem finiteTypeProjection_isStack (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Functor.IsStack (finiteTypeProjection B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  isStack_finiteTypeProjection B S hS (projection_isStack B S hS)

end Stacks.QCoh

end
