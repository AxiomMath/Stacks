module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeSmallStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeStackUnconditional

/-!
# A small stack of quasi-coherent modules of finite type, unconditionally (Stacks 04U6)

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FiniteTypeSmallStack` constructs the small
full subcategory `Stacks.QCoh.FiniteTypeSmall` of the quasi-coherent modules of finite type and
proves that its projection to the big fppf site of `S` is a stack granted Stacks 03YM, that the
projection from *all* quasi-coherent modules is a stack. That statement is
`Stacks.QCoh.projection_isStack`, and Stacks 04U4 built on it is
`Stacks.QCoh.finiteTypeProjection_isStack`; this file records the two clauses of Stacks 04U6
with nothing assumed.

## Main results

* `Stacks.QCoh.isStack_finiteTypeSmallProjection_unconditional`: **Stacks 04U6 (2)**, the
  restricted projection is a stack over the big fppf site of `S`.
* `Stacks.QCoh.exists_finiteTypeSmall_unconditional`: the bundled existential restating the
  source.

## References

* [Stacks Project, Tag 04U6](https://stacks.math.columbia.edu/tag/04U6)
* [Stacks Project, Tag 04U4](https://stacks.math.columbia.edu/tag/04U4)
* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04U6 (2), unconditionally.** The hypothesis of
`Stacks.QCoh.isStack_finiteTypeSmallProjection` is Stacks 03YM, and that is
`Stacks.QCoh.projection_isStack`. -/
@[stacks 04U6 "clause (2): the restricted projection is a stack over the big fppf site over S"]
theorem isStack_finiteTypeSmallProjection_unconditional :
    Functor.IsStack (finiteTypeSmallProjection B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  Functor.IsStack.fiberSkeletal (finiteTypeProjection B S hS) _
    (finiteTypeProjection_isStack B S hS)

/-- **Stacks 04U6 as the source words it, unconditionally.** The hypothesis of
`Stacks.QCoh.exists_finiteTypeSmall` is Stacks 03YM, and that is
`Stacks.QCoh.projection_isStack`. -/
theorem exists_finiteTypeSmall_unconditional :
    ∃ P : ObjectProperty (FiniteType B S hS),
      (∀ T : AlgebraicGeometry.BigFppfOver B S hS,
          Small.{u} ((Functor.restrict (finiteTypeProjection B S hS) P).Fiber T)) ∧
        P.ι.EssSurj ∧
        Functor.IsStack (Functor.restrict (finiteTypeProjection B S hS) P)
          (AlgebraicGeometry.BigFppfOver.topology B S hS) :=
  exists_finiteTypeSmall B S hS (projection_isStack B S hS)

end Stacks.QCoh

end
