module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups

/-!
# Regularity, dimension and integrality along a chain of blowups at closed points

Let `X` be a Noetherian scheme which is regular of dimension two and let

`Xₙ ⟶ Xₙ₋₁ ⟶ ⋯ ⟶ X₀ = X`

be a chain of blowups at closed points, that is, a
`Stacks.ResolutionOfSurfaces.PointBlowupChain` over some set of points of `X`. Then every stage
of the chain is again Noetherian, regular and of dimension two, and is integral as soon as `X`
is.

The hypotheses under which a blowup at a closed point is formed — Noetherian, regular,
two-dimensional — are inherited by the blowup, so they hold at every stage of the chain. The
inductive step is the global form of [Stacks, Tag 0AGR],
`AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton`;
Noetherianity is `Stacks.ResolutionOfSurfaces.isNoetherian_of_pointBlowupChain`.

Integrality is a separate induction on top of the first one: the blowup of an integral scheme in
a nonzero ideal sheaf is integral ([Stacks, Tag 02ND]), and the ideal sheaf of a reduced closed
point of an integral scheme of dimension two is nonzero, so the dimension statement is what
feeds the integrality statement at each stage.

## Main results

* `Stacks.ResolutionOfSurfaces.isRegular_and_topologicalKrullDim_of_pointBlowupChain` — every
  stage of a chain of blowups at closed points of a regular Noetherian surface is regular of
  dimension two.
* `Stacks.ResolutionOfSurfaces.isRegular_of_pointBlowupChain` and
  `Stacks.ResolutionOfSurfaces.topologicalKrullDim_of_pointBlowupChain` — the two halves.
* `Stacks.ResolutionOfSurfaces.isIntegral_of_pointBlowupChain` — every stage of such a chain over
  an integral base is integral.

All four are stated for the blowup `AlgebraicGeometry.blowUp` of a quasi-coherent sheaf of ideals,
the construction in which `Stacks.ResolutionOfSurfaces.PointBlowupChain` is phrased.

## References

* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **Every stage of a chain of blowups at closed points of a regular Noetherian surface is
regular of dimension two.**

The two properties have to be carried along together: the blowup at a closed point of the next
stage can only be formed once that stage is known to be a regular surface, and the global form of
[Stacks, Tag 0AGR] delivers exactly the pair of properties it consumes. Noetherianity of the
stages is `Stacks.ResolutionOfSurfaces.isNoetherian_of_pointBlowupChain`. -/
theorem isRegular_and_topologicalKrullDim_of_pointBlowupChain {X W : Scheme.{u}}
    [IsNoetherian X] {T : Set X} {f : W ⟶ X} (hreg : IsRegular X)
    (hdim : topologicalKrullDim X = 2) (h : PointBlowupChain X T W f) :
    IsRegular W ∧ topologicalKrullDim W = 2 := by
  induction h with
  | refl => exact ⟨hreg, hdim⟩
  | step hh w hw hwT ih =>
      have := isNoetherian_of_pointBlowupChain hh
      exact isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton _ ih.1 ih.2 w hw

/-- **Every stage of a chain of blowups at closed points of a regular Noetherian surface is
regular**, the regularity half of
`Stacks.ResolutionOfSurfaces.isRegular_and_topologicalKrullDim_of_pointBlowupChain`. -/
theorem isRegular_of_pointBlowupChain {X W : Scheme.{u}} [IsNoetherian X] {T : Set X}
    {f : W ⟶ X} (hreg : IsRegular X) (hdim : topologicalKrullDim X = 2)
    (h : PointBlowupChain X T W f) : IsRegular W :=
  (isRegular_and_topologicalKrullDim_of_pointBlowupChain hreg hdim h).1

/-- **Every stage of a chain of blowups at closed points of a regular Noetherian surface has
dimension two**, the dimension half of
`Stacks.ResolutionOfSurfaces.isRegular_and_topologicalKrullDim_of_pointBlowupChain`. -/
theorem topologicalKrullDim_of_pointBlowupChain {X W : Scheme.{u}} [IsNoetherian X] {T : Set X}
    {f : W ⟶ X} (hreg : IsRegular X) (hdim : topologicalKrullDim X = 2)
    (h : PointBlowupChain X T W f) : topologicalKrullDim W = 2 :=
  (isRegular_and_topologicalKrullDim_of_pointBlowupChain hreg hdim h).2

/-- **Every stage of a chain of blowups at closed points of an integral regular Noetherian
surface is integral.**

At each stage the centre is the ideal sheaf of a reduced closed point of an integral scheme of
dimension two, hence nonzero
(`Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot`), and the blowup of an integral
scheme in a nonzero ideal sheaf is integral ([Stacks, Tag 02ND]). The dimension of the stage is
supplied by `Stacks.ResolutionOfSurfaces.topologicalKrullDim_of_pointBlowupChain`. -/
theorem isIntegral_of_pointBlowupChain {X W : Scheme.{u}} [IsNoetherian X]
    [AlgebraicGeometry.IsIntegral X] {T : Set X} {f : W ⟶ X} (hreg : IsRegular X)
    (hdim : topologicalKrullDim X = 2) (h : PointBlowupChain X T W f) :
    AlgebraicGeometry.IsIntegral W := by
  induction h with
  | refl => infer_instance
  | step hh w hw hwT ih =>
      have := ih
      exact isIntegral_blowUp _ (vanishingIdeal_singleton_ne_bot
        (topologicalKrullDim_of_pointBlowupChain hreg hdim hh) w hw)

end Stacks.ResolutionOfSurfaces

end
