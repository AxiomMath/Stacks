module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.StalkLengthGenericPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf of an algebraic space has finite length only at a generic point

Let `X` be a locally Noetherian algebraic space over a scheme `S`, let `x̄` be a geometric point
of `X` and let `u` be a point of an étale scheme chart `W` of `X` lying over the image of `x̄`.
Then the length of `𝒪_X` at `x̄` is finite exactly when `u` is a generic point of an irreducible
component of the scheme `W`.

This is Stacks 0EE4 read at the structure sheaf of `X`.  The length of `𝒪_X` at `x̄` is the
length of the local ring `𝒪_{W, u}` over itself (Stacks 0EE1 on the chart), and for a locally
Noetherian scheme that length is finite exactly at the generic points; so the only hypothesis is
that `X` be locally Noetherian.

Two consequences are recorded.

* Away from the generic points of the chart the length is `⊤`, so a multiplicity read as its
  `ENat.toNat` is zero.
* Whether a chart point is a generic point of its chart depends only on its image in `|X|`, since
  the length at `x̄` does not.  This is the equivalence of conditions (1) and (2) of Stacks 0EE4
  at the structure sheaf.

## Main results

* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_ne_top_iff_mem_genericPoints`:
  the length of `𝒪_X` at `x̄` is finite exactly when `u` is a generic point of its chart.
* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_top_of_notMem_genericPoints`:
  away from the generic points of a chart the length is `⊤`.
* `toNat_geometricLength_structureSheafModule_eq_zero_of_notMem_genericPoints`: there its
  `ENat.toNat` is zero.
* `AlgebraicGeometry.Space.mem_genericPoints_iff_of_chartSchemeToPoints_eq`: two chart points
  with the same image in `|X|` are both generic points of their charts or neither.

## References

* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0EE4 at the structure sheaf of an algebraic space.**  Let `X` be a locally
Noetherian algebraic space, `x̄` a geometric point of `X`, and `u` a point of an étale scheme
chart `W` whose image in `|X|` is the image of `x̄`.  Then the length of `𝒪_X` at `x̄` is finite
exactly when `u` is a generic point of an irreducible component of `W`.

Positivity, the other half of the right-hand side of Stacks 0EE4, is automatic at the structure
sheaf: a local ring is nonzero. -/
@[ega "IV 4.7.7" "Case F = O_X"]
theorem geometricLength_structureSheafModule_ne_top_iff_mem_genericPoints
    (X : AlgebraicSpaces B S hS)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (xbar : GeometricPoint B S hS X.1) (W : SmallEtale B S hS X.1) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    geometricLength B S hS X xbar (structureSheafModule B S hS X) ≠ ⊤ ↔
      u ∈ genericPoints (chartScheme W) := by
  have : IsLocallyNoetherian (chartScheme W) :=
    isLocallyNoetherian_chartScheme B S hS X hLN W
  rw [geometricLength_structureSheafModule_eq_length_chartStalk B S hS X xbar W u hu]
  exact Stacks.Chow.length_stalk_ne_top_iff_mem_genericPoints (X := chartScheme W) u

/-- Away from the generic points of a chart the structure sheaf has infinite length. -/
@[ega "IV 4.7.7" "Case F = O_X"]
theorem geometricLength_structureSheafModule_eq_top_of_notMem_genericPoints
    (X : AlgebraicSpaces B S hS)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (xbar : GeometricPoint B S hS X.1) (W : SmallEtale B S hS X.1) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image)
    (hgen : u ∉ genericPoints (chartScheme W)) :
    geometricLength B S hS X xbar (structureSheafModule B S hS X) = ⊤ :=
  not_ne_iff.mp <| mt (geometricLength_structureSheafModule_ne_top_iff_mem_genericPoints B S hS X
    hLN xbar W u hu).mp hgen

/-- A multiplicity read as the `ENat.toNat` of the length of `𝒪_X` at a geometric point vanishes
when some chart point over that geometric point is not a generic point of its chart, because the
length is then `⊤` and `ENat.toNat ⊤ = 0`. -/
theorem toNat_geometricLength_structureSheafModule_eq_zero_of_notMem_genericPoints
    (X : AlgebraicSpaces B S hS)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (xbar : GeometricPoint B S hS X.1) (W : SmallEtale B S hS X.1) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image)
    (hgen : u ∉ genericPoints (chartScheme W)) :
    (geometricLength B S hS X xbar (structureSheafModule B S hS X)).toNat = 0 := by
  rw [geometricLength_structureSheafModule_eq_top_of_notMem_genericPoints B S hS X hLN
    xbar W u hu hgen]
  rfl

/-- **Conditions (1) and (2) of Stacks 0EE4 at the structure sheaf.**  Being a generic point of
its chart is a property of a chart point that depends only on its image in `|X|`: two chart
points, of possibly different charts, with the same image in `|X|` are either both generic points
or neither. -/
theorem mem_genericPoints_iff_of_chartSchemeToPoints_eq
    (X : AlgebraicSpaces B S hS)
    (hLN : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (W W' : SmallEtale B S hS X.1) (u : chartScheme W) (u' : chartScheme W')
    (huu' : chartSchemeToPoints B S hS X.1 W u = chartSchemeToPoints B S hS X.1 W' u') :
    u ∈ genericPoints (chartScheme W) ↔ u' ∈ genericPoints (chartScheme W') := by
  obtain ⟨xbar, hxbar⟩ :=
    exists_geometricRepresentative B S hS X.1 (chartSchemeToPoints B S hS X.1 W u)
  rw [← geometricLength_structureSheafModule_ne_top_iff_mem_genericPoints B S hS X hLN
      xbar W u hxbar.symm,
    ← geometricLength_structureSheafModule_ne_top_iff_mem_genericPoints B S hS X hLN
      xbar W' u' (huu'.symm.trans hxbar.symm)]

end AlgebraicGeometry.Space

end
