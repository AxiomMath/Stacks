module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Local Noetherianity along a locally finite type morphism of algebraic spaces

Local Noetherianity of an algebraic space is the étale-local property of schemes of Tag 03E6:
the space has a surjective étale atlas by a locally Noetherian scheme. If a morphism of
algebraic spaces is locally of finite type and its target is locally Noetherian, then so is
its source.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherian_of_isLocallyOfFiniteType`: the source of a
  morphism of algebraic spaces locally of finite type with locally Noetherian target is locally
  Noetherian.

## References

* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces over `S` which is locally of finite type and whose target is
locally Noetherian has locally Noetherian source. -/
@[stacks 04ZK, ega "IV 1.3.3", ega "I 6.3.7" "locally Noetherian"]
theorem isLocallyNoetherian_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hN : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  obtain ⟨V, q, hq_surj, hq_etale, hV⟩ := hN
  obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surj hq_etale
  have := hf U V p q α hp_etale hq_etale hcomm.symm
  have := hV
  exact ⟨U, p, hp_surj, hp_etale,
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).map α)⟩

end AlgebraicGeometry.Space

end
