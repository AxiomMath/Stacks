module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Union
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetBaseChange

/-!
# The operations on the finite part are compatible with restriction

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S`. A section of the
finite part `(X/Y)_fin` over `T` lying over `a : T ⟶ Y` restricts along a morphism
`h : T' ⟶ T`: the new section lies over `h ≫ a` and its open subspace is the preimage of the
old one under the canonical morphism `T' ×_Y X ⟶ T ×_Y X`. All of the operations of
Stacks 04PI commute with that restriction.

On points the restriction is the preimage along the canonical morphism of ambient fibre
products, so each law is the corresponding law for preimages of sets: a preimage commutes with
union, intersection, difference and symmetric difference, and sends `∅` to `∅` and the whole
space to the whole space.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartFibre.restrict`: the restriction of a section of the
  finite part along a morphism of the base.

## Main results

* `AlgebraicGeometry.Space.FinitePartFibre.pointSet_restrict`: the point set of a restriction
  is the preimage of the point set.
* `AlgebraicGeometry.Space.FinitePartFibre.restrict_star₁`,
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_star₂`,
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_star₃`,
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_star₄`,
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_add`,
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_zero` and
  `AlgebraicGeometry.Space.FinitePartFibre.restrict_one`: the four operations, the addition of
  the `F₂`-algebra, its zero and its unit in the finite case all commute with restriction.

## Implementation notes

The restriction is the preimage of the open subspace along
`AlgebraicGeometry.Space.baseChangeAmbientMap`, exactly as the restriction of a pair of
Stacks 04PC is in `AlgebraicGeometry.Space.restrictFinitePair`, of which it is the counterpart
for sections over a prescribed morphism to `Y`. Openness and finiteness of the projection are
preserved because the preimage of a subfunctor is cartesian over it and that canonical morphism
is cartesian over the morphism of the bases.

## References

* [Stacks Project, Tag 04PI](https://stacks.math.columbia.edu/tag/04PI)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped symmDiff

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace FinitePartFibre

variable {B S hS} {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  {T T' : AlgebraicSpaces B S hS} {a : T ⟶ Y}

/-- The restriction of a section of the finite part along `h : T' ⟶ T`: the preimage of its
open subspace under the canonical morphism `T' ×_Y X ⟶ T ×_Y X`, a section over `T'` lying
over `h ≫ a`. -/
def restrict (Z : FinitePartFibre B S hS f a) (h : T' ⟶ T) :
    FinitePartFibre B S hS f (h ≫ a) where
  subspace := Z.subspace.preimage (baseChangeAmbientMap B S hS f a h)
  isOpen := isOpenSubspace_preimage B S hS (baseChangeAmbientMap B S hS f a h) Z.subspace
    (isAlgebraicSpace_ambient B S hS f a) (isAlgebraicSpace_ambient B S hS f (h ≫ a)) Z.isOpen
  finite_projection :=
    isFinite_of_isPullback B S hS
      ((Subfunctor.isPullback_preimage (baseChangeAmbientMap B S hS f a h) Z.subspace).paste_vert
        (isPullback_baseChangeAmbientMap B S hS f a h)) Z.finite_projection

/-- The point set of a restriction is the preimage of the point set. -/
@[simp]
theorem pointSet_restrict (Z : FinitePartFibre B S hS f a) (h : T' ⟶ T) :
    (Z.restrict h).pointSet =
      pointsMap B S hS _ (baseChangeAmbientMap B S hS f a h) ⁻¹' Z.pointSet :=
  range_pointsMap_ι_preimage' B S hS (baseChangeAmbientMap B S hS f a h) Z.subspace

variable (hf : IsSeparated B S hS f.hom) (Z₁ Z₂ : FinitePartFibre B S hS f a) (h : T' ⟶ T)

/-- The operation `⋆₁`, the union of two sections, commutes with restriction along
`T' ⟶ T`. -/
@[stacks 04PI "star_1_commutes_with_restriction"]
theorem restrict_star₁ : (star₁ hf Z₁ Z₂).restrict h = star₁ hf (Z₁.restrict h) (Z₂.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_star₁, Set.preimage_union])

/-- The operation `⋆₂`, the intersection of two sections, commutes with restriction along
`T' ⟶ T`. -/
@[stacks 04PI "star_2_commutes_with_restriction"]
theorem restrict_star₂ : (star₂ hf Z₁ Z₂).restrict h = star₂ hf (Z₁.restrict h) (Z₂.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_star₂, Set.preimage_inter])

/-- The operation `⋆₃`, the difference `Z₁ ∖ Z₂`, commutes with restriction along
`T' ⟶ T`. -/
@[stacks 04PI "star_3_commutes_with_restriction"]
theorem restrict_star₃ : (star₃ hf Z₁ Z₂).restrict h = star₃ hf (Z₁.restrict h) (Z₂.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_star₃, Set.preimage_diff])

/-- The operation `⋆₄`, the difference `Z₂ ∖ Z₁`, commutes with restriction along
`T' ⟶ T`. -/
@[stacks 04PI "star_4_commutes_with_restriction"]
theorem restrict_star₄ : (star₄ hf Z₁ Z₂).restrict h = star₄ hf (Z₁.restrict h) (Z₂.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_star₄, Set.preimage_diff])

/-- The addition of the `F₂`-algebra, the symmetric difference of two sections, commutes with
restriction along `T' ⟶ T`. -/
@[stacks 04PI "addition_commutes_with_restriction"]
theorem restrict_add : (add hf Z₁ Z₂).restrict h = add hf (Z₁.restrict h) (Z₂.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_add, Set.preimage_symmDiff])

/-- The zero section restricts to the zero section. -/
@[stacks 04PI "zero_commutes_with_restriction"]
theorem restrict_zero : (zero Z₁).restrict h = zero (Z₁.restrict h) :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_zero, Set.preimage_empty])

/-- For `f` finite, the unit section restricts to the unit section. -/
@[stacks 04PI "unit_commutes_with_restriction"]
theorem restrict_one (hfin : IsFinite B S hS f.hom) :
    (one (a := a) hfin).restrict h = one (a := h ≫ a) hfin :=
  ext_pointSet (by simp only [pointSet_restrict, pointSet_one, Set.preimage_univ])

end FinitePartFibre


end AlgebraicGeometry.Space

end
