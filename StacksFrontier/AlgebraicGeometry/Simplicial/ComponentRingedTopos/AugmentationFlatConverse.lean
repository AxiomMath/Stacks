module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictUnit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationFlatComponent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentFlatReflect

/-!
# The converse of Stacks 0DH3: an augmentation flat on every component is flat

With the notation of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationFlat.lean`, let
`a : (Sh(𝒞_total), O) ⟶ (Sh(𝒟), O_𝒟)` be an augmentation of the total ringed topos of a
simplicial-site situation and `a_n = a ∘ g_n` its component augmentations. The forward
implication of Stacks 0DH3, that `a` flat gives every `a_n` flat, is
`CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat`. This file proves the
converse and registers the equivalence.

## The argument

Flatness of `a_n` is flatness of the inverse image of the structure map of `a` along the
component morphism of topoi
(`CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat_iff`), and flatness
of a morphism of sheaves of commutative rings is flatness of its target read as a module over
its source. The inverse image of that module along `g_n` is the corresponding module for the
inverse image of the morphism, by
`Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso`; so the hypothesis says
exactly that the inverse image on every component of `O`, as an `a^{-1}O_𝒟`-module, is flat.
That module is then flat by
`CategoryTheory.SimplicialSiteSituation.isFlat_of_forall_isFlat_componentPullbackModule`, which
is the source's "we can check this on `𝒞_n`".

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlatMap_of_forall_isFlatMap_componentInverseImage`:
  a morphism of sheaves of commutative rings on the total site whose inverse image on every
  component is flat is flat.
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat_of_forall`: **the
  converse half of Stacks 0DH3.**
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat_iff_forall`:
  **Stacks 0DH3**, the equivalence.

## Implementation notes

The universe arguments of the flatness predicates and of the inverse-image constructions are
written out. They are all the single universe of the simplicial-site situation, but several of
these constants have a section universe that appears first in an instance argument rather than
in an explicit one, so the elaborator defaults it to `0` before the expected type is consulted,
and the application then fails to typecheck rather than being inferred.

## References

* [Stacks Project, Tag 0DH3](https://stacks.math.columbia.edu/tag/0DH3)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **A morphism of sheaves of commutative rings on the total site whose inverse image on every
simplicial component is flat is flat.** Flatness of a morphism of sheaves of commutative rings is
flatness of its target as a module over its source, and the inverse image of that module is the
module of the inverse image of the morphism
(`Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso`), so this is
`CategoryTheory.SimplicialSiteSituation.isFlat_of_forall_isFlat_componentPullbackModule`. -/
theorem isFlatMap_of_forall_isFlatMap_componentInverseImage
    (R : Sheaf S.totalTopology CommRingCat.{u}) (φ : R ⟶ O)
    (h : ∀ n : SimplexCategory, SheafOfModules.IsFlatMap.{u, u, u}
      ((inverseImageCommRingFunctor (componentMorphism S n)).map φ)) :
    SheafOfModules.IsFlatMap.{u, u, u} φ := by
  refine isFlat_of_forall_isFlat_componentPullbackModule S R
    ((_root_.SheafOfModules.restrictScalars
        ((sheafCompose S.totalTopology (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
      (_root_.SheafOfModules.unit (totalRingSheafOf S O))) fun n => ?_
  have hn : SheafOfModules.IsFlat.{u, u, u, u}
      (O := pullbackCommRingSheaf.{u, u, u, u, u, u} (S.componentTopology n)
        ((componentMorphism S n).inverseImage) R)
      (Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitTarget
        ((componentMorphism S n).inverseImage) φ) := h n
  exact SheafOfModules.isFlat_of_iso.{u, u, u}
    (Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso
      ((componentMorphism S n).inverseImage) φ).symm hn

section Augmentation

variable {D : RingedTopos.{u, u, u}}
  [D.J.HasSheafCompose (forget RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (a : RingedToposHom (totalRingedTopos S O) D)

/-- **Stacks 0DH3, the converse implication.** If the augmentation `a_n` of every simplicial
component is flat, then the augmentation `a` of the total ringed topos is flat. -/
theorem componentRingedAugmentation_isFlat_of_forall
    (h : ∀ n : SimplexCategory, (componentRingedAugmentation S O a n).IsFlat) :
    a.IsFlat := by
  have hsheafify : HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1
  have hbijective : S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} S.totalTopology
  exact (SheafOfModules.isFlatMapULift_iff_isFlatMap a.fSharpInverseImage).mpr
    (isFlatMap_of_forall_isFlatMap_componentInverseImage S O _ a.fSharpInverseImage
      fun n => (componentRingedAugmentation_isFlat_iff S O a n).1 (h n))

/-- The augmentation `a` of the total ringed topos of a simplicial-site situation is flat if and
only if the augmentation `a_n` of every simplicial component is flat. -/
@[stacks 0DH3]
theorem componentRingedAugmentation_isFlat_iff_forall :
    a.IsFlat ↔ ∀ n : SimplexCategory, (componentRingedAugmentation S O a n).IsFlat :=
  ⟨fun ha n => componentRingedAugmentation_isFlat S O a ha n,
    componentRingedAugmentation_isFlat_of_forall S O a⟩

end Augmentation

end CategoryTheory.SimplicialSiteSituation

end
