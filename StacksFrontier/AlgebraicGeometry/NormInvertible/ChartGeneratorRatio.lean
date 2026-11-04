module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Recognition

/-!
# The transition units of the chart generators of a glued cocycle

Let `D` be a unit transition cocycle on a covering family `U : ι → Opens X` of a ringed space,
glued into the invertible module `D.glue`
(`Stacks.SheafOfModules.UnitTransitionCocycle.glue`). The chart generator
`D.chartGenerator hU i` is the section over `U i` whose `i`-th coordinate is one. This file
records that the transition unit of two chart generators is the transition unit of the cocycle
they came from.

Gluing and recognition are already both present:
`Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfChartGenerators` identifies a module
carrying generators with prescribed transition units as the glue, and
`Stacks.SheafOfModules.isoOfChartGenerators` compares two such modules. What was missing is the
statement that the glue is itself such a module *for its own cocycle* — without it, a cocycle
built by hand cannot be compared with anything, because nothing says what the ratios of the
sections it produces are.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.transition_self`: the transition unit from a chart
  to itself is one. This is forced by the cocycle identity and is not part of the data.
* `Stacks.SheafOfModules.UnitTransitionCocycle.generatorRatioUnit_chartGenerator`: **the ratio of
  the `j`-th and `i`-th chart generators over an open inside both charts is the transition unit
  `u_{ij}`.**

## Implementation notes

The computation is coordinatewise. A section of the glue over `V` is a family of local
coordinates indexed by the charts; the `k`-th coordinate of the `i`-th chart generator is
`u_{ik}`, the scalar action multiplies the `k`-th coordinate by the restricted scalar, and the
equation to be checked in coordinate `k` is exactly the cocycle identity
`u_{jk} u_{ij} = u_{ik}`.

The module structure on the ambient product of local coordinate rings is a `local` instance in
`StacksFrontier/AlgebraicGeometry/NormInvertible/Cocycle.lean` — as a global instance it would
compete with `Pi.module` on every product type — so it is re-enabled locally here, which is what
lets a statement mentioning `sectionsSubmodule` elaborate at all.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.UnitTransitionCocycle

attribute [local instance] sectionsProductModule

variable {X : RingedSpace.{u, u}} {ι : Type u} {U : ι → Opens X.carrier}

/-- The transition unit from a chart to itself is one: the cocycle identity for the triple
`(i, i, i)` reads `u_{ii} u_{ii} = u_{ii}`. -/
theorem transition_self (D : UnitTransitionCocycle X U) (i : ι) (V : Opens X.carrier)
    (hi : V ≤ U i) : D.transition i i V hi hi = 1 :=
  mul_right_cancel ((D.cocycle i i i V hi hi hi).trans (one_mul _).symm)

/-- The scalar action on a compatible family of local coordinates multiplies each coordinate by
the restricted scalar. -/
theorem sections_smul_val (D : UnitTransitionCocycle X U) {V : Opens X.carrier}
    (r : X.presheaf.obj (op V)) (s : D.sectionsSubmodule V) (k : ι) :
    (r • s).val k =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ U k ≤ V)).op r * s.val k := rfl

/-- **The transition unit of two chart generators of a glued cocycle is the transition unit of
the cocycle.** Over an open `V` inside both charts, the `i`-th chart generator is `u_{ij}` times
the `j`-th: in the `k`-th coordinate that equation is `u_{ik} = u_{ij} u_{jk}`, which is the
cocycle identity. -/
theorem generatorRatioUnit_chartGenerator (D : UnitTransitionCocycle X U)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (i j : ι) {V : Opens X.carrier}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    generatorRatioUnit D.glue V (generatorRestrict D.glue hj (D.chartGenerator hU j))
        (generatorRestrict D.glue hi (D.chartGenerator hU i)) =
      D.transition i j V hi hj := by
  refine generatorRatioUnit_eq _ _ _ _ _ ?_
  show (D.sectionsMap hi (D.chartSection i) : D.sectionsSubmodule V) =
    (D.transition i j V hi hj).val • D.sectionsMap hj (D.chartSection j)
  refine Subtype.ext (funext fun k => ?_)
  rw [sectionsMap_val, sections_smul_val, sectionsMap_val]
  have hVk : V ⊓ U k ≤ V := inf_le_left
  have hkk : V ⊓ U k ≤ U k := inf_le_right
  have e : ∀ (m : ι) (hm : V ≤ U m), X.presheaf.map (homOfLE (inf_le_inf_right (U k) hm)).op
        ((D.chartSection m).val k) = (D.transition m k (V ⊓ U k) (hVk.trans hm) hkk).val :=
    fun m hm => congrArg Units.val (D.restrict (i := m) (j := k) (inf_le_left : U m ⊓ U k ≤ U m)
      inf_le_right (inf_le_inf_right (U k) hm))
  have e3 : X.presheaf.map (homOfLE hVk).op (D.transition i j V hi hj).val =
      (D.transition i j (V ⊓ U k) (hVk.trans hi) (hVk.trans hj)).val :=
    congrArg Units.val (D.restrict (i := i) (j := j) hi hj hVk)
  rw [e i hi, e j hj, e3, ← D.cocycle i j k (V ⊓ U k) (hVk.trans hi) (hVk.trans hj) hkk,
    Units.val_mul, mul_comm]

end Stacks.SheafOfModules.UnitTransitionCocycle

end
