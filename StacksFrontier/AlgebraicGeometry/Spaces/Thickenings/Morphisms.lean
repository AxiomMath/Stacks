module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Morphisms of thickenings of algebraic spaces

A morphism of thickenings of algebraic spaces over a scheme is a commutative square
`(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')`, that is a morphism in the arrow category between the two
inclusions. The inclusion of a thickening is a bijection on points, so `f` is surjective exactly
when `f'` is.

## Main results

* `AlgebraicGeometry.Space.bijective_pointsMap_ι_of_isThickening`: the inclusion of a
  thickening is a bijection on points.
* `AlgebraicGeometry.Space.isSurjective_iff_isSurjective_of_isThickening`: Stacks 09ZY,
  part (2), the surjectivity clause.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_of_isHomeomorph_pointsMap`:
  quasi-compactness of an algebraic space transfers along a morphism which is a
  homeomorphism on points.

## References

* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of a thickening of an algebraic space is a bijection on points. -/
theorem bijective_pointsMap_ι_of_isThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) :
    Function.Bijective (pointsMap B S hS G.toFunctor G.ι) :=
  ⟨pointsMap_injective_of_mono B S hS G.ι, hG.2⟩

/-- In a morphism of thickenings of algebraic spaces over `S` the
map on the closed subspaces is surjective if and only if the map on the ambient spaces is. -/
@[stacks 09ZY "surjective"]
theorem isSurjective_iff_isSurjective_of_isThickening
    {X Y : AlgebraicSpaces B S hS} {G : Subfunctor X.1} {H : Subfunctor Y.1}
    (hG : IsThickening B S hS X G) (hH : IsThickening B S hS Y H)
    (f : Arrow.mk G.ι ⟶ Arrow.mk H.ι) :
    IsSurjective B S hS f.left ↔ IsSurjective B S hS f.right := by
  have ha := bijective_pointsMap_ι_of_isThickening B S hS hG
  have hb := bijective_pointsMap_ι_of_isThickening B S hS hH
  have hcomm : pointsMap B S hS X.1 f.right ∘ pointsMap B S hS G.toFunctor G.ι =
      pointsMap B S hS H.toFunctor H.ι ∘ pointsMap B S hS G.toFunctor f.left := by
    rw [← pointsMap_comp, ← pointsMap_comp]
    exact congrArg (pointsMap B S hS G.toFunctor) f.w.symm
  show Function.Surjective (pointsMap B S hS G.toFunctor f.left) ↔
    Function.Surjective (pointsMap B S hS X.1 f.right)
  rw [← Function.Surjective.of_comp_iff' hb (pointsMap B S hS G.toFunctor f.left), ← hcomm,
    Function.Surjective.of_comp_iff _ ha.2]

/-- Quasi-compactness of an algebraic space over `S` transfers along a morphism of algebraic
spaces whose map on points is a homeomorphism. -/
theorem isQuasiCompactSpace_iff_of_isHomeomorph_pointsMap {P Q : AlgebraicSpaces B S hS}
    (k : P ⟶ Q) (hk : IsHomeomorph (pointsMap B S hS P.obj k.hom)) :
    IsQuasiCompactSpace B S hS P.obj ↔ IsQuasiCompactSpace B S hS Q.obj := by
  have e : points B S hS P.obj ≃ₜ points B S hS Q.obj :=
    hk.homeomorph (pointsMap B S hS P.obj k.hom)
  rw [isQuasiCompactSpace_iff_compactSpace_points B S hS P.obj P.property,
    isQuasiCompactSpace_iff_compactSpace_points B S hS Q.obj Q.property]
  exact ⟨fun h => have := h; e.compactSpace, fun h => have := h; e.symm.compactSpace⟩

end AlgebraicGeometry.Space

end
