module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSliceCounitDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionPullbackClause
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionProjection

/-!
# Stacks 0GQD and 075K, registered on the restriction of modules to an algebraic space

Let `𝒳` be a category fibred in groupoids over `(Sch/S)_{fppf}` represented by an algebraic space
`X`. This module registers Stacks tags 0GQD and 075K on the following results.

* **Stacks 0GQD**: restriction `QCoh(𝒪_𝒳) ⟶ QCoh(𝒪_X)` to the small étale site of `X` is an
  equivalence (`AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_unconditional`),
  its quasi-inverse is `𝒢 ↦ π_X^*𝒢` (see
  `AlgebraicGeometry.Space.nonempty_inv_toSiteModules_iso_projectionModulePullback_unconditional`),
  and it is compatible with pullback
  (`AlgebraicGeometry.Space.nonempty_projectionPullbackModules_comp_iso`).
* **Stacks 075K**: `ℱ|_{F_étale} = i_F^{-1}ℱ = π_{F,*}ℱ`
  (`AlgebraicGeometry.Space.restrictionSheafFunctor_eq_restrictionToposHom_inverseImage`,
  `AlgebraicGeometry.Space.restrictionSheafFunctor_eq_projectionPushforward`), with the direct
  image `AlgebraicGeometry.Space.projectionPushforward` and its sections
  (`AlgebraicGeometry.Space.projectionPushforward_obj_obj`).

## References

* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 075K](https://stacks.math.columbia.edu/tag/075K)
-/

@[expose] public section

add_to_stacks 0GQD "the equivalence clause, with no hypothesis beyond the source's, at the \
module universe `u` and for `𝒳 : Type (u + 1)` with `Category.{u} 𝒳`.  `hres` is \
`AlgebraicGeometry.Space.restrictionPreservesQuasicoherent`, `hqcoh` is \
`AlgebraicGeometry.Space.projectionPullbackPreservesQuasicoherent`, `hunit` is \
`AlgebraicGeometry.Space.isIso_unit_moduleRestriction'`, and `hcounit` is \
`AlgebraicGeometry.Space.projectionPullbackCounitIsIso'`, the source's chart-slice argument \
over `AlgebraicGeometry.Space.chartSliceOpensAreCharts`.  The pullback clause is registered \
separately on `AlgebraicGeometry.Space.nonempty_projectionPullbackModules_comp_iso`"
  AlgebraicGeometry.Space.isEquivalence_quasicoherentRestriction_unconditional

add_to_stacks 0GQD "the quasi-inverse is the inverse image along the projection, with no \
hypothesis beyond the source's, at the module universe `u` and for `𝒳 : Type (u + 1)` with \
`Category.{u} 𝒳`"
  AlgebraicGeometry.Space.nonempty_inv_toSiteModules_iso_projectionModulePullback_unconditional

add_to_stacks 0GQD "compatibility with pullback"
  AlgebraicGeometry.Space.nonempty_projectionPullbackModules_comp_iso

add_to_stacks 075K "the direct image pi_{F,*}" AlgebraicGeometry.Space.projectionPushforward

add_to_stacks 075K "the restriction is the direct image along pi_F"
  AlgebraicGeometry.Space.restrictionSheafFunctor_eq_projectionPushforward

add_to_stacks 075K "the restriction is the inverse image along i_F"
  AlgebraicGeometry.Space.restrictionSheafFunctor_eq_restrictionToposHom_inverseImage

add_to_stacks 075K "sections of the direct image along pi_F"
  AlgebraicGeometry.Space.projectionPushforward_obj_obj

end
