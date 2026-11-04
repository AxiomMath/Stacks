module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMaps

/-!
# A birational morphism of decent algebraic spaces is dominant

A birational morphism of decent algebraic spaces over a scheme `S` whose point spaces have
finitely many irreducible components is dominant. This is **Stacks 0ACW**.

## Main results

* `AlgebraicGeometry.Space.isDominant_of_isBirational`: **Stacks 0ACW**.

## Implementation notes

Birationality, Stacks 0ACV, has two clauses, and only the first is used: the map on points
restricts to a bijection from the generic points of the irreducible components of the source
onto those of the target. The generic points of the irreducible components of a quasi-sober
space are dense in it, so the image of the map on points contains a dense set and is therefore
dense, which is dominance in the sense of Stacks 0ABL.

Beyond what birationality already assumes, what decency supplies here is quasi-sobriety of the
point space, Stacks 03K6, and that is needed only on the *target*: the source's generic points
enter only as the domain of the bijection.

## References

* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 0ABL](https://stacks.math.columbia.edu/tag/0ABL)
* [Stacks Project, Tag 0ACV](https://stacks.math.columbia.edu/tag/0ACV)
* [Stacks Project, Tag 0ACW](https://stacks.math.columbia.edu/tag/0ACW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ACW.** A birational morphism of decent algebraic spaces over `S` with finitely
many irreducible components is dominant: it maps the generic points of the irreducible
components of the source onto those of the target, and those are dense in a quasi-sober
space. -/
@[stacks 0ACW, ega "I 2.2.9" "more general"]
theorem isDominant_of_isBirational (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X)
    (hdecY : IsDecentSpace B S hS Y)
    (hfiniteX : (letI := pointTopology B S hS X
      (irreducibleComponents (points B S hS X)).Finite))
    (hfiniteY : (letI := pointTopology B S hS Y
      (irreducibleComponents (points B S hS Y)).Finite))
    {f : X ⟶ Y}
    (hf : IsBirational B S hS hX hY hdecX hdecY hfiniteX hfiniteY f) :
    IsDominant B S hS f := by
  have := quasiSober_points_of_isDecentSpace B S hS hY hdecY
  refine Dense.mono ?_ (dense_iff_closure_eq.mpr genericPoints.closure)
  intro y hy
  obtain ⟨x, -, hx⟩ :=
    (hf.bijOn B S hS hX hY hdecX hdecY hfiniteX hfiniteY).surjOn hy
  exact ⟨x, hx⟩

end AlgebraicGeometry.Space

end
