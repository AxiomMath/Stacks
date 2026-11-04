module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps

/-!
# Limits of affine objects of the site from a bounded diagram, and bounded base changes

The declarations below accompany `StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps`.

* `AlgebraicGeometry.Scheme.DiagramBoundedBelow` bundles the hypothesis of
  `AlgebraicGeometry.Scheme.size_lt_of_isLimit_of_isAffine_of_size_le` and of the `_of_size_le`
  results of that file: one cardinal below `κ` bounding both the number of objects of the index
  and the size of every stage. It is the form in which the bound is produced for a system of
  affine charts (`AlgebraicGeometry.Space.AffineChartSystem.diagramBoundedBelow`) and carried
  along constructions on such a diagram; it is unbundled to apply those results.
* `AlgebraicGeometry.Space.HasBoundedBaseChanges`: the base changes of the later stages of an
  inverse system along the affine points of *one* stage `i₀` are bounded below the cutoff,
  together with the number of those stages. It is what the system of affine charts at `i₀`
  needs to have its limit in the site, and it has three sufficient conditions:
  `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_lt_cof` (an index small compared to the
  cofinality of the cutoff),
  `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_hasBaseChangesOfSizeLE` (transitions of
  bounded growth) and
  `AlgebraicGeometry.Space.hasBoundedBaseChanges_of_baseChangeSizeBounded`
  (`AlgebraicGeometry.Space.BaseChangeSizeBounded`, which bounds the base changes at *every*
  stage along *every* test object, with a slice of the index below the cutoff).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-! ### Bounded diagrams of schemes -/

section AffineDiagram

variable {J : Type u} [Category.{u} J]

end AffineDiagram

/-! ### Bounded cofiltered diagrams of affine objects of the big fppf site -/

section SiteDiagram

variable {J : Type u} [Category.{u} J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end SiteDiagram

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Bounded base changes -/

section BoundedBaseChanges

variable {I : Type u} [Category.{u} I]

variable (i₀ : I) (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)


/-- **Bounded base changes at a stage from uniformly bounded base changes.** If the base changes
of the stages of `D` along every test morphism are uniformly bounded
(`AlgebraicGeometry.Space.BaseChangeSizeBounded`) and the slice `Over i₀` has fewer objects than
the site's cutoff, then the base changes at `i₀` are bounded in the sense of
`AlgebraicGeometry.Space.HasBoundedBaseChanges`: the bound for an affine point `f₀` is the
maximum of `#(Over i₀)` and the bound `BaseChangeSizeBounded` gives for `f₀`.

The converse fails: `AlgebraicGeometry.Space.HasBoundedBaseChanges` speaks of one stage and of
affine test objects only, and its bound also controls the slice. -/
theorem hasBoundedBaseChanges_of_baseChangeSizeBounded (hOver : #(Over i₀) < B.cutoff)
    (hB : BaseChangeSizeBounded B S hS D) : HasBoundedBaseChanges B S hS i₀ D := fun _ f₀ =>
  let ⟨μ, hμ, hbound⟩ := hB i₀ _ f₀
  ⟨max #(Over i₀) μ, max_lt hOver hμ, le_max_left _ _,
    fun j W p q h => (hbound j W p q h).trans (le_max_right _ _)⟩

end BoundedBaseChanges

end Space

end AlgebraicGeometry

end
