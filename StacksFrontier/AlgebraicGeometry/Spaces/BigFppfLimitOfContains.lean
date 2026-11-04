module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps

/-!
# Limits in the big fppf site from containment of the limit scheme

A diagram in the big fppf site of `S` whose underlying diagram of schemes has a limit cone with
vertex contained in the site has a limit in the site, and the underlying scheme functor
preserves it.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasLimit_of_isLimit_contains`: the limit exists in the site.
* `AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_isLimit_contains`: the underlying
  scheme functor preserves it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

section SiteDiagram

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The size-bounded subcategory of schemes creates the limit of the diagram of schemes
underlying a diagram in the big fppf site of `S`, as soon as that diagram of schemes has a limit
cone whose vertex is contained in the site. -/
@[instance_reducible]
private noncomputable def createsLimitInclusionOfIsLimit (V : J ⥤ BigFppfOver B S hS)
    {c : Cone (V ⋙ BigFppfOver.toScheme B S hS)} (hc : IsLimit c) (hcont : B.Contains c.pt) :
    CreatesLimit (V ⋙ BigFppfOver.forget B S hS) B.inclusion :=
  have _hlim : HasLimit (underlyingDiagram V) := ⟨⟨⟨c, hc⟩⟩⟩
  have hsize : schemeSizeBelow B.cutoff (limit (underlyingDiagram V)) := by
    change (limit (underlyingDiagram V)).size < B.cutoff
    exact (Scheme.size_congr ((limit.isLimit (underlyingDiagram V)).conePointUniqueUpToIso
      hc)).trans_lt hcont
  Limits.createsLimitFullSubcategoryInclusion _ hsize

/-- Under the hypotheses below, the diagram has a limit in the site, preserved by the underlying
scheme functor. -/
private theorem hasLimit_and_preservesLimit_toScheme_of_isLimit_contains
    (V : J ⥤ BigFppfOver B S hS) {c : Cone (V ⋙ BigFppfOver.toScheme B S hS)} (hc : IsLimit c)
    (hcont : B.Contains c.pt) : HasLimit V ∧ PreservesLimit V (BigFppfOver.toScheme B S hS) := by
  have hconn : IsConnected J := IsCofiltered.isConnected J
  have hcr := createsLimitInclusionOfIsLimit V hc hcont
  have : HasLimit (underlyingDiagram V) := ⟨⟨⟨c, hc⟩⟩⟩
  have : HasLimit (V ⋙ BigFppfOver.forget B S hS) := hasLimit_of_created _ B.inclusion
  exact ⟨hasLimit_of_created V (Over.forget (B.obj hS)), inferInstance⟩

/-- A cofiltered diagram in the big fppf site of `S` whose diagram of schemes has a limit cone
with vertex contained in the site has a limit in the site. -/
theorem BigFppfOver.hasLimit_of_isLimit_contains (V : J ⥤ BigFppfOver B S hS)
    {c : Cone (V ⋙ BigFppfOver.toScheme B S hS)} (hc : IsLimit c) (hcont : B.Contains c.pt) :
    HasLimit V :=
  (hasLimit_and_preservesLimit_toScheme_of_isLimit_contains V hc hcont).1

/-- The underlying scheme functor preserves the limit of a cofiltered diagram in the big fppf site
of `S` whose diagram of schemes has a limit cone with vertex contained in the site. -/
theorem BigFppfOver.preservesLimit_toScheme_of_isLimit_contains (V : J ⥤ BigFppfOver B S hS)
    {c : Cone (V ⋙ BigFppfOver.toScheme B S hS)} (hc : IsLimit c) (hcont : B.Contains c.pt) :
    PreservesLimit V (BigFppfOver.toScheme B S hS) :=
  (hasLimit_and_preservesLimit_toScheme_of_isLimit_contains V hc hcont).2

end SiteDiagram

end AlgebraicGeometry

end
