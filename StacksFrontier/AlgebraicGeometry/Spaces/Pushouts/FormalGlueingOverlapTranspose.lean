module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesKernel
public import StacksFrontier.CategoryTheory.Adjunction.TransposeOverSquare

/-!
# The map `f^*j_*ℋ ⟶ j'_*𝒢|_V` of a glueing triple

In Situation 0AEV a glueing triple `t = (ℋ, 𝒢, φ)` determines a map of `𝒪_Y`-modules
`f^*j_*ℋ ⟶ j'_*𝒢|_V`: the transpose under `f^* ⊣ f_*` of `j_*` of the transpose of `φ`,
followed by the comparison `j_*(f|_V)_* ⟶ f_*j'_*` conjugate to the overlap comparison of
Stacks 0AEW.  At a geometric point `ȳ` of `f⁻¹Z` its stalk, read through
`(f^*j_*ℋ)_ȳ = 𝒪_{Y,ȳ} ⊗ (j_*ℋ)_x̄`, is the map `a` of `FormalGlueing.pullbackDatum` in the
stalkwise proof of Stacks 0AF0, and what that proof needs of it is that it becomes bijective after
inverting the generators of the ideal of `Z`.  This file proves the sheaf-level input: **the map
is invertible over `V`**, since there it is `φ` up to the comparison isomorphisms and the counits
of the open immersions `j` and `j'`.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapPushforwardComparison`: the comparison
  `j_*(f|_V)_* ⟶ f_*j'_*`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.overlapTranspose`: the map of a triple.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_modulePullback_map_overlapTranspose`:
  its pullback to `V` is invertible when the structure arrow of the triple is.

## Implementation notes

The invertibility statement is written with the unfolded
`CategoryTheory.Adjunction.squareTranspose` rather than with `overlapTranspose`: matching the
two through the definition exceeds the recursion depth of the definitional check on these
module categories, whereas the unfolded form is what
`CategoryTheory.Adjunction.map_squareTranspose_comp_counit` produces.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AEW](https://stacks.math.columbia.edu/tag/0AEW)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS)

/-- The comparison `j_* ∘ (f|_V)_* ⟶ f_* ∘ j'_*` of direct images around the glueing square: the
conjugate of the inverse of the overlap comparison of Stacks 0AEW. -/
abbrev overlapPushforwardComparison :=
  conjugateEquiv ((modulePullbackAdjunction B S hS D.openImmersion).comp
      (modulePullbackAdjunction B S hS D.overlapRestriction))
    ((modulePullbackAdjunction B S hS D.ambientMorphism).comp
      (modulePullbackAdjunction B S hS D.openImmersionOver))
    D.overlapPullbackComparison.inv

/-- **The map `f^*j_*ℋ ⟶ j'_*𝒢|_V` of a glueing triple `t = (ℋ, 𝒢, φ)`**: the transpose under
`f^* ⊣ f_*` of `j_*(ℋ ⟶ (f|_V)_*𝒢|_V) ≫ (j_*(f|_V)_* ⟶ f_*j'_*)`, the first map being the
transpose of `φ`. -/
def overlapTranspose (t : D.moduleGlueingComma) :
    (modulePullback B S hS D.ambientMorphism).obj
        ((modulePushforward B S hS D.openImmersion).obj t.left) ⟶
      (modulePushforward B S hS D.openImmersionOver).obj
        ((modulePullback B S hS D.openImmersionOver).obj t.right) :=
  Adjunction.squareTranspose (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.openImmersionOver) D.overlapPullbackComparison.inv
    t.left t.hom

/-- **The map of a glueing triple is invertible over `V`** as soon as the structure arrow of the
triple is: the counits of `j^* ⊣ j_*` and `j'^* ⊣ j'_*` are invertible, the direct images along
open immersions being fully faithful. -/
theorem isIso_modulePullback_map_overlapTranspose (t : D.moduleGlueingComma) [IsIso t.hom] :
    IsIso ((modulePullback B S hS D.openImmersionOver).map
      (Adjunction.squareTranspose (modulePullbackAdjunction B S hS D.openImmersion)
        (modulePullbackAdjunction B S hS D.overlapRestriction)
        (modulePullbackAdjunction B S hS D.ambientMorphism)
        (modulePullbackAdjunction B S hS D.openImmersionOver) D.overlapPullbackComparison.inv
        t.left t.hom)) := by
  have hj := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS D.openImmersion
    D.isOpenSubspace_U.2
  have hj' := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS D.openImmersionOver
    D.isOpenSubspace_V.2
  have := hj.full
  have := hj.faithful
  have := hj'.full
  have := hj'.faithful
  have c1 : IsIso ((modulePullbackAdjunction B S hS D.openImmersion).counit.app t.left) :=
    inferInstance
  have c2 : IsIso ((modulePullbackAdjunction B S hS D.openImmersionOver).counit.app
      ((modulePullback B S hS D.openImmersionOver).obj t.right)) := inferInstance
  have c3 : IsIso D.overlapPullbackComparison.inv := Iso.isIso_inv _
  have i2 : IsIso ((modulePullback B S hS D.overlapRestriction).map
      ((modulePullbackAdjunction B S hS D.openImmersion).counit.app t.left)) :=
    Functor.map_isIso _ _
  have key := Adjunction.map_squareTranspose_comp_counit
    (modulePullbackAdjunction B S hS D.openImmersion)
    (modulePullbackAdjunction B S hS D.overlapRestriction)
    (modulePullbackAdjunction B S hS D.ambientMorphism)
    (modulePullbackAdjunction B S hS D.openImmersionOver) D.overlapPullbackComparison.inv
    t.left t.hom
  have i3 : IsIso (D.overlapPullbackComparison.inv.app
      ((modulePushforward B S hS D.openImmersion).obj t.left) ≫
      (modulePullback B S hS D.overlapRestriction).map
        ((modulePullbackAdjunction B S hS D.openImmersion).counit.app t.left) ≫ t.hom) :=
    IsIso.comp_isIso
  rw [← key] at i3
  exact IsIso.of_isIso_comp_right _
    ((modulePullbackAdjunction B S hS D.openImmersionOver).counit.app
      ((modulePullback B S hS D.openImmersionOver).obj t.right))

end AlgebraicGeometry.Space.FormalGlueingSituation

end
