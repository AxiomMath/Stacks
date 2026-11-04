module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# An algebraic space locally of finite type over a locally Noetherian one

An algebraic space over `S` which is locally of finite type over a locally Noetherian
algebraic space is itself locally Noetherian. This is the algebraic-space form of the scheme
statement `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` of Tag 01T6.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType`.

## Implementation notes

Local Noetherianity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.Space.HasEtaleLocalProperty` of Tag 03E6 attached to
`AlgebraicGeometry.IsLocallyNoetherian`; the witness is one surjective étale chart whose
scheme has the property. Lifting the given chart of the target along the morphism, by
Tag 02X1, produces a surjective étale chart of the source together with a morphism of the
underlying schemes, and that morphism is locally of finite type because the morphism of
algebraic spaces is — the predicate of Tag 03XF being a condition on exactly such commuting
squares of charts. The scheme statement then applies on the nose.

## References

* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- An algebraic space over `S` locally of finite type over a locally Noetherian algebraic
space is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) := by
  obtain ⟨V, b, hbSurj, hbEtale, hVnoeth⟩ := hN
  obtain ⟨U, a, h, haEtale, hcomm, haSurj, -⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hbEtale
  refine ⟨U, a, haSurj hbSurj, haEtale, ?_⟩
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hVnoeth
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hf U V a b h haEtale hbEtale hcomm
  exact LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map h)

end AlgebraicGeometry.Space

end
