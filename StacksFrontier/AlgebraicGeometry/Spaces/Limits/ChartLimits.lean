module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem

/-!
# Inverse systems whose affine charts have limits in the site

Stacks 07SF proves that a directed limit `X = lim X_i` of algebraic spaces with affine
transition morphisms is an algebraic space by choosing an affine étale chart `U_0 → X_0`,
setting `U_i = X_i ×_{X_0} U_0`, and observing that `U = lim U_i` is an affine scheme which is a
chart of `X`. Every later result on such limits uses the presentation `X = U/R` with
`U = lim U_i`. In a fixed big fppf site the scheme `lim U_i` need not lie in the site, and then
the limit sheaf need not be an algebraic space
(`AlgebraicGeometry.Space.not_forall_isAlgebraicSpace_limit_of_isAffineHom`), or it may be one
while having the wrong charts
(`AlgebraicGeometry.Space.not_forall_exists_hom_after_baseChange_of_isAlgebraicSpace_limit`).

The predicate `AlgebraicGeometry.Space.HasChartLimits` asks exactly for the source's picture:
every system of affine charts of the inverse system, in the sense of
`AlgebraicGeometry.Space.AffineChartSystem`, admits a
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge`, that is, a limit in the site which is
also the limit of the underlying schemes and which represents the base change of the limit.
It holds when the index category is smaller than the cofinality of the cutoff, and when it is
smaller than the cutoff and the base changes of the stages are uniformly bounded.

## Main definitions

* `AlgebraicGeometry.Space.HasChartLimits`: every affine chart system of the inverse system has
  a limit bridge.

## Main results

* `AlgebraicGeometry.Space.hasChartLimits_of_mk_lt_cof`: the bound `#I < cof κ` of
  `AlgebraicGeometry.Space.isAlgebraicSpace_limit` implies chart limits.
* `AlgebraicGeometry.Space.hasChartLimits_of_baseChangeSizeBounded`: so do `#I < κ` together
  with uniformly bounded base changes.
* `AlgebraicGeometry.Space.isAffineHom_limitπ_of_hasChartLimits`: Stacks 07SF, part (1), for a
  system with chart limits.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- An inverse system `D` of presheaves on the big fppf site of `S` **has chart limits** when
every system of affine charts of it admits a limit bridge: for every stage `i₀` and every
affine scheme-valued point `f₀ : U₀ ⟶ D i₀`, the affine objects representing the base changes
`D k ×_{D i₀} U₀`, `k ≥ i₀`, have a limit in the site which is also their limit as schemes and
which represents `lim D ×_{D i₀} U₀`. This is the sense in which Stacks 07SF writes
`X = lim X_i`: the charts of the limit are the limits of the charts of the stages. -/
def HasChartLimits : Prop :=
  ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
    (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
    (C : AffineChartSystem B S hS i₀ D U₀ f₀), Nonempty C.LimitBridge

variable {B S hS D}

/-- **A system indexed by a category smaller than the cofinality of the cutoff has chart
limits.** This is the bound under which Stacks 07SF is proved in
`AlgebraicGeometry.Space.isAlgebraicSpace_limit`. -/
theorem hasChartLimits_of_mk_lt_cof [IsCofiltered I] (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) : HasChartLimits B S hS D :=
  fun _ _ _ C ↦ ⟨C.limitBridge hSize hHomSize⟩

/-- **A system with uniformly bounded base changes, indexed by a category smaller than the
cutoff, has chart limits.** -/
theorem hasChartLimits_of_baseChangeSizeBounded [IsCofiltered I] {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hB : BaseChangeSizeBounded B S hS D) : HasChartLimits B S hS D :=
  fun _ _ _ C ↦ ⟨C.limitBridgeOfBaseChangeSizeBounded hSize hν hHomSize hB⟩

/-- **Stacks 07SF, part (1), for a system with chart limits.** Every projection from the limit
to a stage is affine: its base change along an affine `f₀ : U₀ ⟶ D i₀` is represented by the
limit of the charts, whose underlying scheme is affine. -/
theorem isAffineHom_limitπ_of_hasChartLimits (hD : HasChartLimits B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i : I) :
    IsAffineHom B S hS (limit.π D i) := by
  intro U₀ f₀
  obtain ⟨L⟩ := hD i U₀ f₀ (affineChartSystem B S hS i D U₀ f₀ hAffine)
  refine ⟨⟨L.cone.pt, L.isAffine_pt⟩, L.toLimit, yoneda.preimage L.toBase, ?_⟩
  rw [Functor.map_preimage]
  exact L.isPullback

end AlgebraicGeometry.Space

end
