module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# The functors and adjunction induced on commutative group objects

A morphism of topoi induces functors and an adjunction on the commutative group objects of its
two topoi: the inverse image preserves finite limits, its right adjoint preserves all limits, and
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts` makes both braided, so Mathlib's
`CategoryTheory.Functor.mapCommGrp` and `CategoryTheory.Adjunction.mapCommGrp` apply.

The abelian inverse image itself, and its exactness, are `CategoryTheory.Sites.abelianInverseImage`
and `CategoryTheory.Sites.abelianInverseImage_exact`.

## Main definitions

* `Stacks.Topos.AbelianInverseImage.commGrpInverseImage`, `.commGrpPushforward`,
  `.commGrpAdjunction`: the two functors and the adjunction.

## References

* [Stacks Project, Lemma 18.31.2 (Tag 04JC)](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

namespace Stacks.Topos.AbelianInverseImage

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The cartesian monoidal structure on sheaves of types given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The symmetric braiding of the cartesian monoidal structure on sheaves of types. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- The direct-image functor on commutative group objects induced by a morphism of topoi. -/
noncomputable def commGrpPushforward
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    CommGrp (Sheaf J (Type w)) ⥤ CommGrp (Sheaf K (Type w')) := by
  letI : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits f.pushforward := inferInstance
  letI : f.pushforward.Braided := .ofChosenFiniteProducts _
  exact f.pushforward.mapCommGrp

/-- The inverse-image functor on commutative group objects induced by a morphism of topoi. -/
noncomputable def commGrpInverseImage
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    CommGrp (Sheaf K (Type w')) ⥤ CommGrp (Sheaf J (Type w)) := by
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  exact f.inverseImage.mapCommGrp

/-- The adjunction on commutative group objects induced by a morphism of topoi. -/
noncomputable def commGrpAdjunction
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    commGrpInverseImage J f ⊣ commGrpPushforward J f := by
  letI : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits f.pushforward := inferInstance
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  letI : f.pushforward.Braided := .ofChosenFiniteProducts _
  letI : f.inverseImage.Braided := .ofChosenFiniteProducts _
  exact f.adj.mapCommGrp

end Stacks.Topos.AbelianInverseImage
