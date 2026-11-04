module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChange

/-!
# The map `a_{small}^♯` of Stacks 06WC below an arrow and below its image

Let `g : 𝒳 ⥤ 𝒴` be a functor over `(Sch/S)_{fppf}` between categories fibred in groupoids and
let `φ : x' ⟶ x` be an arrow of `𝒳`.  The map `a_{small}^♯` of structure sheaves of
**Stacks 06WC** below `φ`, read through the structure functor `g ⋙ q` of `𝒳`, and the one
below `g φ`, read through `q`, are the same map.

## Main results

* `AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_of_comp`: **the map `a_{small}^♯`
  below an arrow of the source of a 1-morphism and below its image agree**, which is the
  identification the square of part (4) of Stacks 075D for presheaves of modules has to be
  formed over.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w w₂ v₂

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳]
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

section InverseImage

variable {𝒴 : Type v₂} [Category.{w₂} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids) (g : 𝒳 ⥤ 𝒴) (hgq : (g ⋙ q).IsFiberedInGroupoids)

/-- **The map `a_{small}^♯` of Stacks 06WC below an arrow `φ : x' ⟶ x` of `𝒳` and below its
image `g φ` in `𝒴` are the same map.**

Both are maps of presheaves of rings on the small étale site of the scheme below `x`, and the
scheme below `x` read through the structure functor `g ⋙ q` of the source of a 1-morphism is the
scheme below `g x` read through `q`; so the two have the same type. That they are equal is
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing` applied
twice: each is pullback of global functions along the base-change projection of the morphism of
schemes below the arrow, and `φ` and `g φ` lie over the same morphism of schemes.

This is what lets the square of part (4) of **Stacks 075D** be formed for presheaves of modules,
in `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeInverseImage.lean`: the two
maps of structure sheaves the two sides of that square are taken over are built from the
localization equivalences of **Stacks 06W0** at `x` and at `g x` and are not the same map on the
nose, but they are equal. -/
public theorem smallEtaleStructureComparison_eq_of_comp {x' x : 𝒳} (φ : x' ⟶ x) :
    smallEtaleStructureComparison B E h S hS (g ⋙ q) hgq φ τ hτ =
      smallEtaleStructureComparison B E h S hS q hq (g.map φ) τ hτ := by
  rw [smallEtaleStructureComparison_eq_smallEtaleStructureMapRing,
    smallEtaleStructureComparison_eq_smallEtaleStructureMapRing]
  rfl

end InverseImage

end AlgebraicGeometry.Stack

end
