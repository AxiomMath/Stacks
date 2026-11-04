module

public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.ReducedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# Reducedness along a smooth morphism of algebraic spaces

Reducedness of an algebraic space is the étale-local property of schemes of Tag 03E6: the space
has a surjective étale atlas by a reduced scheme. The source of a smooth morphism of algebraic
spaces is reduced when its target is.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isSmooth` is reducedness of the source.

## Implementation notes

The proof is the one the source gives for local Noetherianity in Tag 04ZK, with reducedness in
place of local Noetherianity: lift a reduced surjective étale atlas `V` of the target to a
surjective étale atlas `U` of the source together with a morphism `α : U ⟶ V` of the site making
the square commute (Tag 02X1). Smoothness is the every-chart condition of Tag 03ZC, so it
applies to that square and makes the induced scheme morphism smooth; reducedness then passes to
`U` because it is local in the smooth topology (Tag 034E), via `prop_of_smooth`.

This file carries NO `@[stacks]` attribute. Tag 0GB3 has two conclusions — reducedness of the
source, and reducedness of the target of a surjective smooth morphism — and only the first is
proved here; the second is the algebraic-space form of Tag 06MI, which this library does not
have (its scheme-level form is `AlgebraicGeometry.isReduced_of_flat_of_surjective`, Tag 06QM).
A declaration proving one of two conclusions is not the covering set of the tag. Tag 0GB3 is
also outside the chapter range this work is scoped to.

## References

* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
* [Stacks Project, Tag 034E](https://stacks.math.columbia.edu/tag/034E)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GB3, reducedness of the source.** If a morphism of algebraic spaces over `S` is
smooth and its target is reduced, then its source is reduced. -/
theorem isReduced_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSmooth B S hS f)
    (hred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsReduced T) := by
  obtain ⟨V, q, hq_surj, hq_etale, hV⟩ := hred
  obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surj hq_etale
  have hsm := hf U V p q α hp_etale hq_etale hcomm.symm
  exact ⟨U, p, hp_surj, hp_etale,
    prop_of_smooth (fun T : Scheme.{u} => IsReduced T)
      ((BigFppfOver.toScheme B S hS).map α) hsm hV⟩

end AlgebraicGeometry.Space

end
