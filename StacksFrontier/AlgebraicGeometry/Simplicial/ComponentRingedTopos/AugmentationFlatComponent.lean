module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationFlat

/-!
# Flatness of a component augmentation is flatness of the inverse image of the structure map

With the notation of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/AugmentationFlat.lean`: `S` is a
simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`a : (Sh(𝒞_total), O) ⟶ (Sh(𝒟), O_𝒟)` an augmentation of the total ringed topos.

The structure map of the component augmentation `a_n = a ∘ g_n` in inverse-image form is the
inverse image along `g_n` of the structure map of `a`, read between two isomorphisms
(`CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_fSharpInverseImage`).
Flatness of a morphism of sheaves of commutative rings is unchanged by composing with an
isomorphism on either side, in both directions; so flatness of `a_n` is *equivalent* to flatness
of `g_n^{-1}(a^♯)`, and not merely implied by it, which is what the forward implication of
Stacks 0DH3 uses.

This is the half of the converse of Stacks 0DH3 that is about the augmentation rather than about
the simplicial site: it turns "every `a_n` is flat" into "the inverse image of `a^♯` along every
component morphism of topoi is flat", a statement about one morphism of sheaves of commutative
rings on the total site and the family of inverse images along the component morphisms.

## Main results

* `AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso_iff`: flatness of a morphism of sheaves of
  commutative rings is *equivalent* to flatness of that morphism composed with an isomorphism on
  each side. The implication is
  `AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso`; this adds its converse, which is the
  same implication applied to the inverse isomorphisms.
* `CategoryTheory.SimplicialSiteSituation.componentRingedAugmentation_isFlat_iff`: **flatness of
  the component augmentation `a_n` is flatness of the inverse image of the structure map of `a`
  along the component morphism of topoi.**

## Implementation notes

The two sheafification facts on the component site that the unlifted flatness predicate needs are
produced here as they are in `AugmentationFlat.lean`, from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`; the private auxiliary
of that file is not in scope, and restating the two one-line applications is cheaper than
exporting it.

**What the converse of Stacks 0DH3 still needs.** With this reduction, the converse — that `a` is
flat as soon as every `a_n` is — is exactly the statement that the family of inverse images
`g_n^{-1}` jointly reflects flatness of a morphism of sheaves of commutative rings on the total
site. The joint conservativity those inverse images do have, including the reflection of
epimorphisms that the local equational criterion of Stacks 08FC part (2) consumes, is
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ComponentConservative.lean`.

## References

* [Stacks Project, Tag 0DH3](https://stacks.math.columbia.edu/tag/0DH3)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget RingCat.{u})]
  [J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Flatness of a morphism of sheaves of commutative rings composed with an isomorphism on each
side is flatness of the morphism.** One implication is
`AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso`, and the other is that implication applied
to the inverse isomorphisms, which conjugate the composite back to the morphism. -/
theorem isFlatMap_comp_iso_iff {O O' P P' : Sheaf J CommRingCat.{u}}
    (e₁ : P ≅ O) {f : O ⟶ O'} (e₂ : O' ≅ P') :
    IsFlatMap (e₁.hom ≫ f ≫ e₂.hom) ↔ IsFlatMap f := by
  refine ⟨fun h ↦ ?_, isFlatMap_comp_iso e₁ e₂⟩
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using isFlatMap_comp_iso e₁.symm e₂.symm h

end AlgebraicGeometry.SheafOfModules

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {D : RingedTopos.{u, u, u}}
  [D.J.HasSheafCompose (forget RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (a : RingedToposHom (totalRingedTopos S O) D)

/-- **Flatness of the augmentation of a simplicial component is flatness of the inverse image of
the structure map of the augmentation.** The structure map of `a_n` is the inverse image along
`g_n` of that of `a` read between two isomorphisms, and flatness of a morphism of sheaves of
commutative rings is insensitive to such a conjugation in both directions. -/
theorem componentRingedAugmentation_isFlat_iff (n : SimplexCategory) :
    (componentRingedAugmentation S O a n).IsFlat ↔
      SheafOfModules.IsFlatMap
        ((inverseImageCommRingFunctor (componentMorphism S n)).map a.fSharpInverseImage) := by
  have hsheafify : HasWeakSheafify (S.componentTopology n) AddCommGrpCat.{u} :=
    (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology n)).1
  have hbijective : (S.componentTopology n).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (S.componentTopology n)
  rw [show (componentRingedAugmentation S O a n).IsFlat ↔
      SheafOfModules.IsFlatMap (componentRingedAugmentation S O a n).fSharpInverseImage from
    SheafOfModules.isFlatMapULift_iff_isFlatMap _,
    componentRingedAugmentation_fSharpInverseImage]
  exact SheafOfModules.isFlatMap_comp_iso_iff
    (((inverseImageCommRingComp a.toToposHom (componentMorphism S n)).app D.O).symm)
    ((componentRingedTopos_restrictionIso S n).app O)

end CategoryTheory.SimplicialSiteSituation

end
