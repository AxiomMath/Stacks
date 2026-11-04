module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# The dimension formula for a smooth morphism of algebraic spaces

For a smooth morphism of locally Noetherian algebraic spaces over `S` the dimension of the
source at a point is the dimension of the target at its image plus the relative dimension of
the morphism at that point: `dim_x(X) = dim_y(Y) + dim_x(X_y)`.

## Main results

* `AlgebraicGeometry.Space.dimensionAtPoint_eq_add_of_isSmooth` is **Stacks Tag 0AFI**.
* `AlgebraicGeometry.Space.exists_hasRelativeDimensionAt_and_dimensionAtPoint_eq_add_of_isSmooth`
  records that the relative dimension appearing there is always attained.

## Implementation notes

Local Noetherianity of an algebraic space is the étale-local property of Tag 03E6 for
`AlgebraicGeometry.IsLocallyNoetherian`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/NoetherianSpaces.lean`. The source is assumed locally
Noetherian, as in the statement of the tag, but the hypothesis is not used: by Tag 04ZK it
follows from local Noetherianity of the target and smoothness of `f`, which is how the chart
of the source is seen to be locally Noetherian below.

The relative dimension of Tag 04NM is a predicate carrying its value as an index, not a
function, so the formula is stated with the value `d` quantified and
`AlgebraicGeometry.Space.HasRelativeDimensionAt d` as a hypothesis. It is not vacuous: some
`d` always satisfies that hypothesis, by
`AlgebraicGeometry.Space.exists_hasRelativeDimensionAt`, and that is what the second statement
below records.

The proof is the source's reduction to schemes. One commuting square of surjective étale
charts `α : U ⟶ V` over `f` is obtained by Tag 02X1 from the locally Noetherian atlas of the
target; the induced morphism of schemes is smooth, being the chart morphism of a smooth
morphism, and its source is locally Noetherian because its target is. A field-valued
representative of `x` on `U` gives a pointed chart in which the relative dimension at `x` is
the local dimension of the fibre of `α` at the corresponding scheme point, by the chart
equation of Tag 04NM, and the dimensions of the two spaces are the local dimensions of `U` and
`V` at that point and its image, by the chart independence of Tag 04N5. The formula is then
Tag 0AFF for `α`.

## References

* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 0AFF](https://stacks.math.columbia.edu/tag/0AFF)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AFI.** Let `f : X ⟶ Y` be a smooth morphism of locally Noetherian algebraic
spaces over `S`. For every point `x` of `X` with image `y` in `Y` we have
`dim_x(X) = dim_y(Y) + dim_x(X_y)`, where `dim_x(X_y)` is the relative dimension `d` of `f`
at `x` in the sense of Tag 04NM. -/
@[stacks 0AFI]
public theorem dimensionAtPoint_eq_add_of_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (_hNX : HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNY : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : X ⟶ Y) (hf : IsSmooth B S hS f) {d : ℕ∞} (x : points B S hS X)
    (hd : HasRelativeDimensionAt d B S hS f x) :
    dimensionAtPoint B S hS X hX x =
      dimensionAtPoint B S hS Y hY (pointsMap B S hS X f x) + (d : WithBot ℕ∞) := by
  classical
  set T := BigFppfOver.toScheme B S hS with hT
  obtain ⟨V, b, hbSurj, hbEtale, hVnoeth⟩ := hNY
  obtain ⟨U, a, α, hsq, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have _ : IsLocallyNoetherian (T.obj V) := hVnoeth
  have _ : _root_.AlgebraicGeometry.Smooth (T.map α) :=
    hf U V a b α haEtale hbEtale hsq.symm
  have _ : LocallyOfFiniteType (T.map α) := inferInstance
  have _ : IsLocallyNoetherian (T.obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map α)
  -- a field-valued representative of `x` on the chart, and its image on the target chart
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨p, hpz⟩ := Quot.exists_rep z
  rw [← hpz] at hz
  set pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p with hpV
  have hpVmaps : pointsMap B S hS (yoneda.obj V) b (pV.class B S hS (yoneda.obj V)) =
      pointsMap B S hS X f x := by
    rw [hpV, ← pointsMap_class, ← Function.comp_apply
      (f := pointsMap B S hS (yoneda.obj V) b), ← pointsMap_comp, ← hsq, pointsMap_comp,
      Function.comp_apply, hz]
  -- the relative dimension at `x`, read on that pointed chart
  have hfibre : topologicalKrullDimAt ((T.map α).fiber ((T.map α) (schemePoint B S hS U p)))
      ((T.map α).asFiber (schemePoint B S hS U p)) = (d : WithBot ℕ∞) :=
    (hasFiberDimensionAt_ofSchemeHom_iff (T.map α) (schemePoint B S hS U p) d).mp
      (hd { U := U, V := V, a := a, b := b, h := α, a_etale := haEtale, b_etale := hbEtale
            comm := hsq.symm, representative := p
            point := IsLocalRing.closedPoint p.carrier, maps_to := hz })
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a haEtale p hz,
    dimensionAtPoint_eq_of_etale_chart B S hS Y hY _ V b hbEtale pV hpVmaps,
    hpV, schemePoint_map_yoneda B S hS α p, ← hfibre]
  exact topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber_of_smooth
    (T.map α) (schemePoint B S hS U p)

/-- **Stacks 0AFI.** The relative dimension occurring in the dimension formula for a smooth
morphism of locally Noetherian algebraic spaces always exists, so the formula is a genuine
computation of the dimension of the source at a point. -/
public theorem exists_hasRelativeDimensionAt_and_dimensionAtPoint_eq_add_of_isSmooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (hNY : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : X ⟶ Y) (hf : IsSmooth B S hS f) (x : points B S hS X) :
    ∃ d : ℕ∞, HasRelativeDimensionAt d B S hS f x ∧
      dimensionAtPoint B S hS X hX x =
        dimensionAtPoint B S hS Y hY (pointsMap B S hS X f x) + (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_hasRelativeDimensionAt B S hS hX hY f x
  exact ⟨d, hd, dimensionAtPoint_eq_add_of_isSmooth B S hS hX hY hNX hNY f hf x hd⟩

end AlgebraicGeometry.Space

end
