module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# The inverse-image composition comparison as a natural isomorphism

`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso` compares the iterated inverse image
of *one* sheaf of commutative rings with its inverse image along the composite. This file records
that the comparison is natural in the sheaf, in the form the inverse images of a composite of
morphisms of topoi take.

## Main definitions

* `MorphismOfTopoi.inverseImageCommRingCompIso`: the identification
  `(g ∘ f)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of functors on sheaves of commutative rings.

## Main results

* `Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_inv`: the
  companion of the existing `…_hom` lemma for the inverse comparison.

## Implementation notes

The components are the per-object comparisons, so there is no new mathematics here: what is added
is the naturality square. It is proved by forgetting commutativity — the comparison is then the
ring-valued comparison, which is the identity on sections, and
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafMap` becomes the inverse image of the
underlying morphism of sheaves of rings, so the square is an identity of functions on sections.

`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor` and `.pullbackCommRingSheaf` are made
`implicit_reducible` locally: without that the rewrite which forgets commutativity reports that
the target is not type-correct at `implicit` transparency, because
`(pullbackCommRingSheafFunctor J Φ).obj O` and `pullbackCommRingSheaf J Φ O` are interchangeable
only at default transparency.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' w'' v u v' u' v'' u''

namespace Stacks.Sheaves.ToposPullback

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [L.HasSheafCompose (forget RingCat.{w''})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : Sheaf K (Type w') ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type w'') ⥤ Sheaf K (Type w')) [PreservesFiniteProducts Ψ]
  (O : Sheaf L CommRingCat.{w''})

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Forgetting commutativity carries the inverse of the comparison of iterated inverse images to
the inverse of the ring-valued comparison. -/
lemma forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_inv :
    (Stacks.forgetCommRingSheaf J).map (pullbackCommRingSheafCompIso J K Φ Ψ O).inv =
      (pullbackRingSheafCompIso J K Φ Ψ
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := L)) O)).inv :=
  (fullyFaithfulForgetCommRingSheaf J).map_preimage _

end Stacks.Sheaves.ToposPullback

namespace MorphismOfTopoi

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local implicit_reducible] Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf MorphismOfTopoi.comp

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget RingCat.{w'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [L.HasSheafCompose (forget RingCat.{w''})]
  [L.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf L (Type w'')))

/-- The inverse image of sheaves of commutative rings along a composite morphism of topoi is the
inverse image along `g` followed by the inverse image along `f`, naturally in the sheaf. This is
the commutative-ring half of the composition comparison of Stacks 00YV. -/
noncomputable def inverseImageCommRingCompIso :
    inverseImageCommRingFunctor (g.comp f) ≅
      inverseImageCommRingFunctor g ⋙ inverseImageCommRingFunctor f :=
  NatIso.ofComponents
    (fun O ↦ (pullbackCommRingSheafCompIso J K f.inverseImage g.inverseImage O).symm)
    (fun a ↦ by
      refine (fullyFaithfulForgetCommRingSheaf J).map_injective ?_
      simp only [Functor.comp_map, Functor.map_comp, pullbackCommRingSheafFunctor_map,
        forgetCommRingSheaf_map_pullbackCommRingSheafMap, Iso.symm_hom,
        forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_inv]
      refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦ ?_))
      exact RingCat.hom_ext (RingHom.ext fun x ↦ rfl))

end MorphismOfTopoi

end
