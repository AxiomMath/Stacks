module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Inverse images of sheaves of rings compose

Let `Φ₁ : Sh(D) ⥤ Sh(C₁)` and `Φ₂ : Sh(C₁) ⥤ Sh(C₂)` be finite-product-preserving functors of
categories of sheaves of sets, as the inverse image of a morphism of topoi is. Transporting the
ring structure of a sheaf of rings `R` on `D` along `Φ₁` and then along `Φ₂` gives the same
sheaf of rings as transporting it along the composite `Φ₁ ⋙ Φ₂` in one step. This file proves
that, first for sheaves of rings and then for sheaves of commutative rings, and in both cases
packages the comparison as a natural isomorphism of the inverse-image functors.

Everything rests on one observation. The underlying sheaf of sets of
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf J₁ Φ₁ R` is `Φ₁` of the underlying sheaf of
sets of `R` *on the nose* — that is what `Stacks.Sheaves.ToposPullback.pullbackRingSheafIso`
being `Iso.refl` records — so for a finite-product-preserving functor `Ψ` to types the two types
`Ψ (Φ₁ R)` and `(Φ₁ ⋙ Ψ) R` are literally the same, and the question is only whether the
transported ring operations agree. They do, and that is already available:
`Stacks.Sheaves.ToposPushforward.ringAddObj_comp` and its siblings `ringMulObj_comp`,
`ringNegObj_comp`, `ringZeroObj_comp`, `ringOneObj_comp` say exactly that the operation
transported in two steps along `Φ₁` and then `Ψ` is the operation transported in one step along
`Φ₁ ⋙ Ψ`. Taking `Ψ` to be `Φ₂` followed by the sections functor over an object of the target
site turns those five identities into the statement that the identity map of sections is a ring
isomorphism between the two iterated inverse images, whence the comparison below.

The commutative case is read off through the fully faithful functor forgetting commutativity, as
in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposCommRingImageAdjunction.lean`: the
`forget₂`-images of the two sides are literally the iterated and the one-step inverse image of
the underlying sheaf of rings, so the ring-valued comparison has a preimage.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompRingHom` and `.pullbackRingSheafCompHom`:
  the comparison on sections over one object, and as a morphism of sheaves of rings.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafComp`: the comparison isomorphism
  `Φ₂⁻¹(Φ₁⁻¹R) ≅ (Φ₁ ⋙ Φ₂)⁻¹R` for a sheaf of rings.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafFunctorComp`: the same, as a natural
  isomorphism of inverse-image functors.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafComp` and
  `.pullbackCommRingSheafFunctorComp`: the commutative-ring analogues.

## Main results

* `Stacks.Sheaves.ToposPullback.sheafCompose_map_pullbackRingSheafComp_hom` and
  `.forget_map_pullbackCommRingSheafComp_hom`: the comparison is the identity on underlying
  sheaves of sets.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafComp_naturality` and
  `.pullbackCommRingSheafComp_naturality`: the comparison is natural in the sheaf of rings.

## Implementation notes

A single universe `ww` is used for the sections of all three topoi, because the composite
`Φ₁ ⋙ Φ₂` only exists when the middle topos is the same on both sides, and the consumers of
this file — inverse images along composable morphisms of topoi — have all three in one universe
anyway. The object and morphism universes of the three sites stay independent.

The two comparison morphisms are built directly, with the identity as the underlying map of
sections, rather than lifted from an abstract argument; that is what makes
`sheafCompose_map_pullbackRingSheafComp_hom` and the two `hom_inv_id` equations hold by `rfl`,
exactly as for the comparison with restriction in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageAdjunction.lean`.

`HasSheafCompose` for `forget RingCat`, for `forget₂ CommRingCat RingCat` and — only where the
underlying sheaf of sets of a sheaf of commutative rings is mentioned — for `forget CommRingCat`
is assumed rather than derived, exactly as in the two files this one builds on.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv₁ uu₁ vv₂ uu₂

/-! ## The comparison isomorphism for sheaves of rings -/

section RingCompIso

variable {C₁ : Type uu₁} [Category.{vv₁} C₁] {C₂ : Type uu₂} [Category.{vv₂} C₂]
  {D : Type uu} [Category.{vv} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₂.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]
  (R : Sheaf K RingCat.{ww})

/-- Over an object of the target site, the identity map of sections is a ring homomorphism from
the inverse image of `R` taken in two steps to the inverse image taken along the composite. The
four conditions are the comparisons of
`Stacks.Sheaves.ToposPushforward.ringAddObj_comp` and its siblings, taken for the functor to
types given by `Φ₂` followed by the sections functor over that object. -/
noncomputable def pullbackRingSheafCompRingHom (X : C₂ᵒᵖ) :
    (pullbackRingSheaf J₂ Φ₂ (pullbackRingSheaf J₁ Φ₁ R)).obj.obj X ⟶
      (pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R).obj.obj X :=
  letI := Sheaf.ringObjRing (pullbackRingSheaf J₁ Φ₁ R) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)
  letI := Sheaf.ringObjRing R ((Φ₁ ⋙ Φ₂) ⋙ Sheaf.sectionsFunctor J₂ X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ Stacks.Sheaves.ToposPushforward.ringAddObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y
      map_mul' := fun x y ↦ Stacks.Sheaves.ToposPushforward.ringMulObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y
      map_zero' := Stacks.Sheaves.ToposPushforward.ringZeroObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)
      map_one' := Stacks.Sheaves.ToposPushforward.ringOneObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) }

/-- The same identity, read as a ring homomorphism in the other direction. -/
noncomputable def pullbackRingSheafCompRingHomInv (X : C₂ᵒᵖ) :
    (pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R).obj.obj X ⟶
      (pullbackRingSheaf J₂ Φ₂ (pullbackRingSheaf J₁ Φ₁ R)).obj.obj X :=
  letI := Sheaf.ringObjRing (pullbackRingSheaf J₁ Φ₁ R) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)
  letI := Sheaf.ringObjRing R ((Φ₁ ⋙ Φ₂) ⋙ Sheaf.sectionsFunctor J₂ X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ (Stacks.Sheaves.ToposPushforward.ringAddObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y).symm
      map_mul' := fun x y ↦ (Stacks.Sheaves.ToposPushforward.ringMulObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y).symm
      map_zero' := (Stacks.Sheaves.ToposPushforward.ringZeroObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)).symm
      map_one' := (Stacks.Sheaves.ToposPushforward.ringOneObj_comp J₁ Φ₁ R
        (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)).symm }

/-- The comparison morphism from the inverse image of a sheaf of rings taken in two steps to
the inverse image taken along the composite. It is the identity on sections. -/
noncomputable def pullbackRingSheafCompHom :
    pullbackRingSheaf J₂ Φ₂ (pullbackRingSheaf J₁ Φ₁ R) ⟶
      pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R where
  hom :=
    { app := fun X ↦ pullbackRingSheafCompRingHom J₁ J₂ Φ₁ Φ₂ R X
      naturality := fun _ _ _ ↦ rfl }

/-- The comparison morphism in the other direction. -/
noncomputable def pullbackRingSheafCompInv :
    pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R ⟶
      pullbackRingSheaf J₂ Φ₂ (pullbackRingSheaf J₁ Φ₁ R) where
  hom :=
    { app := fun X ↦ pullbackRingSheafCompRingHomInv J₁ J₂ Φ₁ Φ₂ R X
      naturality := fun _ _ _ ↦ rfl }

/-- Inverse images of sheaves of rings compose: transporting the ring structure along `Φ₁` and
then along `Φ₂` gives the same sheaf of rings as transporting it along `Φ₁ ⋙ Φ₂` in one step.
The comparison is the identity on underlying sheaves of sets. -/
noncomputable def pullbackRingSheafComp :
    pullbackRingSheaf J₂ Φ₂ (pullbackRingSheaf J₁ Φ₁ R) ≅
      pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R where
  hom := pullbackRingSheafCompHom J₁ J₂ Φ₁ Φ₂ R
  inv := pullbackRingSheafCompInv J₁ J₂ Φ₁ Φ₂ R
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison isomorphism is the identity on underlying sheaves of sets. -/
@[simp]
lemma sheafCompose_map_pullbackRingSheafComp_hom :
    (sheafCompose J₂ (forget RingCat.{ww})).map (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R).hom =
      𝟙 (Sheaf.ringSheaf (pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R)) :=
  rfl

/-- The inverse comparison is also the identity on underlying sheaves of sets. -/
@[simp]
lemma sheafCompose_map_pullbackRingSheafComp_inv :
    (sheafCompose J₂ (forget RingCat.{ww})).map (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R).inv =
      𝟙 (Sheaf.ringSheaf (pullbackRingSheaf J₂ (Φ₁ ⋙ Φ₂) R)) :=
  rfl

/-- The comparison isomorphism is natural in the sheaf of rings. -/
lemma pullbackRingSheafComp_naturality {R₁ R₂ : Sheaf K RingCat.{ww}} (a : R₁ ⟶ R₂) :
    pullbackRingSheafMap J₂ Φ₂ (pullbackRingSheafMap J₁ Φ₁ a) ≫
        (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R₂).hom =
      (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ R₁).hom ≫ pullbackRingSheafMap J₂ (Φ₁ ⋙ Φ₂) a := by
  have h : Φ₂.map ((sheafCompose J₁ (forget RingCat.{ww})).map (pullbackRingSheafMap J₁ Φ₁ a)) =
      Φ₂.map (Φ₁.map ((sheafCompose K (forget RingCat.{ww})).map a)) :=
    congrArg (fun m ↦ Φ₂.map m) (ringSheafMap_pullbackRingSheafMap J₁ Φ₁ a)
  refine (sheafCompose J₂ (forget RingCat.{ww})).map_injective
    (Sheaf.hom_ext_sections fun X s ↦ ?_)
  exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s

/-- Inverse images of sheaves of rings compose, as a natural isomorphism of the inverse-image
functors. -/
noncomputable def pullbackRingSheafFunctorComp :
    pullbackRingSheafFunctor J₁ Φ₁ ⋙ pullbackRingSheafFunctor J₂ Φ₂ ≅
      pullbackRingSheafFunctor J₂ (Φ₁ ⋙ Φ₂) :=
  NatIso.ofComponents (fun S ↦ pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ S)
    (fun a ↦ pullbackRingSheafComp_naturality J₁ J₂ Φ₁ Φ₂ a)

end RingCompIso

/-! ## The comparison isomorphism for sheaves of commutative rings -/

section CommRingCompIso

variable {C₁ : Type uu₁} [Category.{vv₁} C₁] {C₂ : Type uu₂} [Category.{vv₂} C₂]
  {D : Type uu} [Category.{vv} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{ww})] [J₂.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (Φ₁ : Sheaf K (Type ww) ⥤ Sheaf J₁ (Type ww)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type ww) ⥤ Sheaf J₂ (Type ww)) [PreservesFiniteProducts Φ₂]

/-- Inverse images of sheaves of commutative rings compose. This is the ring-valued comparison
`Stacks.Sheaves.ToposPullback.pullbackRingSheafComp`, read back through the fully faithful
functor forgetting commutativity: the `forget₂`-images of the two sides are literally the
iterated and the one-step inverse image of the underlying sheaf of rings. -/
noncomputable def pullbackCommRingSheafComp (O : Sheaf K CommRingCat.{ww}) :
    pullbackCommRingSheaf J₂ Φ₂ (pullbackCommRingSheaf J₁ Φ₁ O) ≅
      pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O :=
  (fullyFaithfulForgetCommRingSheaf J₂).preimageIso
    (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ (SheafOfModules.Tensor.ringSheaf O))

omit [J₂.HasSheafCompose (forget RingCat.{ww})] in
/-- Forgetting commutativity carries the comparison to the ring-valued comparison. -/
@[simp]
lemma forgetCommRingSheaf_map_pullbackCommRingSheafComp_hom (O : Sheaf K CommRingCat.{ww}) :
    (Stacks.forgetCommRingSheaf J₂).map (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).hom =
      (pullbackRingSheafComp J₁ J₂ Φ₁ Φ₂ (SheafOfModules.Tensor.ringSheaf O)).hom :=
  (fullyFaithfulForgetCommRingSheaf J₂).map_preimage _

/-- The comparison isomorphism is natural in the sheaf of commutative rings. -/
lemma pullbackCommRingSheafComp_naturality {O O' : Sheaf K CommRingCat.{ww}} (a : O ⟶ O') :
    pullbackCommRingSheafMap J₂ Φ₂ (pullbackCommRingSheafMap J₁ Φ₁ a) ≫
        (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O').hom =
      (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).hom ≫
        pullbackCommRingSheafMap J₂ (Φ₁ ⋙ Φ₂) a := by
  refine (fullyFaithfulForgetCommRingSheaf J₂).map_injective ?_
  simp only [Functor.map_comp, forgetCommRingSheaf_map_pullbackCommRingSheafComp_hom,
    forgetCommRingSheaf_map_pullbackCommRingSheafMap]
  exact pullbackRingSheafComp_naturality J₁ J₂ Φ₁ Φ₂ ((Stacks.forgetCommRingSheaf K).map a)

/-- Inverse images of sheaves of commutative rings compose, as a natural isomorphism of the
inverse-image functors. -/
noncomputable def pullbackCommRingSheafFunctorComp :
    pullbackCommRingSheafFunctor J₁ Φ₁ ⋙ pullbackCommRingSheafFunctor J₂ Φ₂ ≅
      pullbackCommRingSheafFunctor J₂ (Φ₁ ⋙ Φ₂) :=
  NatIso.ofComponents (fun O ↦ pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O)
    (fun a ↦ pullbackCommRingSheafComp_naturality J₁ J₂ Φ₁ Φ₂ a)

omit [J₂.HasSheafCompose (forget RingCat.{ww})] in
/-- The comparison of the two iterated inverse images is the identity on underlying sheaves of
sets. -/
@[simp]
lemma forget_map_pullbackCommRingSheafComp_hom
    [J₂.HasSheafCompose (forget CommRingCat.{ww})] [K.HasSheafCompose (forget CommRingCat.{ww})]
    (O : Sheaf K CommRingCat.{ww}) :
    (sheafCompose J₂ (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).hom =
      𝟙 ((sheafCompose J₂ (forget CommRingCat.{ww})).obj
        (pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O)) := by
  refine Sheaf.hom_ext_sections fun X s ↦ ?_
  show RingCat.Hom.hom
    ((((Stacks.forgetCommRingSheaf J₂).map
      (pullbackCommRingSheafComp J₁ J₂ Φ₁ Φ₂ O).hom).hom.app X)) s = s
  rw [forgetCommRingSheaf_map_pullbackCommRingSheafComp_hom]
  rfl

end CommRingCompIso

end Stacks.Sheaves.ToposPullback

end
