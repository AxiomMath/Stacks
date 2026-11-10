module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image and direct image of sheaves of commutative rings

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageAdjunction.lean` builds the
adjunction `f⁻¹ ⊣ f_*` for sheaves of **rings** along a morphism of topoi. This file carries
it over to sheaves of **commutative** rings, which is the form the ringed-site vocabulary of
this development uses: `AlgebraicGeometry.RingedSite` and
  `Stacks.Sheaves.LocallyRingedTopos.RingedTopos` both carry
a structure sheaf valued in `CommRingCat`.

Two facts do all the work.

First, the inverse image of a sheaf of commutative rings along a finite-product-preserving
functor of sheaves of sets is already available as a *presheaf* of commutative rings,
`Stacks.Sheaves.RingedToposModules.inverseImageCommRingPresheaf`, whose underlying presheaf of
rings is the inverse-image presheaf of rings of Stacks 03D2 on the nose. It is a sheaf because
`forget₂ CommRingCat RingCat` is fully faithful, hence reflects limits of every size, so
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` turns the sheaf condition for the
ring-valued presheaf into the sheaf condition for the commutative-ring-valued one. No size
hypothesis relating the universes of the site to the universe of sections is needed, matching
`CategoryTheory.Presheaf.isSheaf_ringCat_of_isSheaf_forget`.

Second, `sheafCompose J (forget₂ CommRingCat RingCat)` is itself fully faithful, so a morphism
of the underlying sheaves of rings *is* a morphism of sheaves of commutative rings. That gives
the action on morphisms, the functor, and — through
`CategoryTheory.Adjunction.restrictFullyFaithful` applied to
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction` — the adjunction, with no further
computation.

The comparison with restriction along a continuous functor of sites is built directly rather
than lifted, so that it stays the identity on sections by definition: the transported ring
operations on `π⁻¹O` over `X` are the operations of `O` over `G X`, by
`CategoryTheory.Sheaf.sectionsFunctor_map_ringAddHom` and its siblings, exactly as in the
ring-valued case.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`: the inverse image of a sheaf of
  commutative rings along a finite-product-preserving functor of sheaves of sets.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafMap` and `.pullbackCommRingSheafFunctor`:
  its action on morphisms, and the functor.
* `Stacks.Sheaves.ToposPullback.restrictionCommRingIso`: for a continuous functor of sites, the
  identification of that inverse image with restriction.
* `Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` and
  `.pushforwardCommRingFunctor`: the inverse image and direct image of sheaves of commutative
  rings along a morphism of topoi.
* `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`: the adjunction between them.

## Main results

* `Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_pullbackCommRingSheaf`: the underlying
  sheaf of rings of the inverse image is the inverse image of the underlying sheaf of rings, on
  the nose.
* `Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget`: the comparison with
  restriction is the identity on underlying sheaves of sets.

## Implementation notes

`HasSheafCompose` for `forget RingCat`, for `forget₂ CommRingCat RingCat` and — only where the
underlying sheaf of sets is mentioned — for `forget CommRingCat` is assumed rather than derived,
exactly as in the ring-valued file and in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean`. For a ringed site the
`forget₂` instance is a theorem, `AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`.

The commutativity hypothesis that `inverseImageCommRingPresheaf` takes is discharged by
`commRingSheaf_mul_comm`: the sections of the underlying sheaf of rings of a sheaf of
commutative rings are, by definition, the sections of a commutative ring.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section FullyFaithful

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]

/-- Forgetting commutativity is fully faithful on sheaves, because it is fully faithful on
commutative rings. A morphism of the underlying sheaves of rings of two sheaves of commutative
rings therefore *is* a morphism of sheaves of commutative rings. -/
noncomputable def fullyFaithfulForgetCommRingSheaf :
    (sheafCompose J (forget₂ CommRingCat.{ww} RingCat.{ww})).FullyFaithful :=
  fullyFaithfulSheafCompose J (Functor.FullyFaithful.ofFullyFaithful _)

end FullyFaithful

section CommRingPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

omit [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The sections of the underlying sheaf of rings of a sheaf of commutative rings commute. -/
lemma commRingSheaf_mul_comm (O : Sheaf K CommRingCat.{ww'}) (X : Dᵒᵖ)
    (a b : (Sheaf.sectionsFunctor K X).obj (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))) :
    a * b = b * a :=
  mul_comm (G := ToType (O.obj.obj X)) a b

/-- The inverse image of a sheaf of commutative rings along a finite-product-preserving functor
of sheaves of sets. Its underlying presheaf is
`Stacks.Sheaves.RingedToposModules.inverseImageCommRingPresheaf`, and it is a sheaf because
`forget₂ CommRingCat RingCat` reflects limits. -/
noncomputable def pullbackCommRingSheaf (O : Sheaf K CommRingCat.{ww'}) :
    Sheaf J CommRingCat.{ww} :=
  ⟨inverseImageCommRingPresheaf J Φ (SheafOfModules.Tensor.ringSheaf O) (commRingSheaf_mul_comm O),
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ CommRingCat.{ww} RingCat.{ww})
      (pullbackRingSheaf J Φ (SheafOfModules.Tensor.ringSheaf O)).property⟩

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The underlying sheaf of rings of the inverse image of a sheaf of commutative rings is the
inverse image of its underlying sheaf of rings, on the nose. -/
lemma forgetCommRingSheaf_pullbackCommRingSheaf (O : Sheaf K CommRingCat.{ww'}) :
    (Stacks.forgetCommRingSheaf J).obj (pullbackCommRingSheaf J Φ O) =
      pullbackRingSheaf J Φ (SheafOfModules.Tensor.ringSheaf O) :=
  rfl

/-- The inverse image of a morphism of sheaves of commutative rings: the inverse image of the
underlying morphism of sheaves of rings, read back through full faithfulness. -/
noncomputable def pullbackCommRingSheafMap {O O' : Sheaf K CommRingCat.{ww'}} (a : O ⟶ O') :
    pullbackCommRingSheaf J Φ O ⟶ pullbackCommRingSheaf J Φ O' :=
  (fullyFaithfulForgetCommRingSheaf J).preimage
    (pullbackRingSheafMap J Φ ((Stacks.forgetCommRingSheaf K).map a))

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The underlying morphism of sheaves of rings of the inverse image of a morphism of sheaves of
commutative rings is the inverse image of its underlying morphism of sheaves of rings. -/
@[simp]
lemma forgetCommRingSheaf_map_pullbackCommRingSheafMap
    {O O' : Sheaf K CommRingCat.{ww'}} (a : O ⟶ O') :
    (Stacks.forgetCommRingSheaf J).map (pullbackCommRingSheafMap J Φ a) =
      pullbackRingSheafMap J Φ ((Stacks.forgetCommRingSheaf K).map a) :=
  (fullyFaithfulForgetCommRingSheaf J).map_preimage _

/-- The inverse image of sheaves of commutative rings along a finite-product-preserving functor
of sheaves of sets, as a functor. -/
noncomputable def pullbackCommRingSheafFunctor :
    Sheaf K CommRingCat.{ww'} ⥤ Sheaf J CommRingCat.{ww} where
  obj O := pullbackCommRingSheaf J Φ O
  map a := pullbackCommRingSheafMap J Φ a
  map_id O := by
    refine (fullyFaithfulForgetCommRingSheaf J).map_injective ?_
    rw [forgetCommRingSheaf_map_pullbackCommRingSheafMap, CategoryTheory.Functor.map_id,
      pullbackRingSheafMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp a b := by
    refine (fullyFaithfulForgetCommRingSheaf J).map_injective ?_
    rw [forgetCommRingSheaf_map_pullbackCommRingSheafMap, CategoryTheory.Functor.map_comp,
      pullbackRingSheafMap_comp, CategoryTheory.Functor.map_comp,
      forgetCommRingSheaf_map_pullbackCommRingSheafMap,
      forgetCommRingSheaf_map_pullbackCommRingSheafMap]
    rfl

/-- On objects, `pullbackCommRingSheafFunctor` is `pullbackCommRingSheaf`. -/
@[simp]
lemma pullbackCommRingSheafFunctor_obj (O : Sheaf K CommRingCat.{ww'}) :
    (pullbackCommRingSheafFunctor J Φ).obj O = pullbackCommRingSheaf J Φ O := rfl

/-- On morphisms, `pullbackCommRingSheafFunctor` is `pullbackCommRingSheafMap`. -/
@[simp]
lemma pullbackCommRingSheafFunctor_map {O O' : Sheaf K CommRingCat.{ww'}} (a : O ⟶ O') :
    (pullbackCommRingSheafFunctor J Φ).map a = pullbackCommRingSheafMap J Φ a := rfl

/-- Forgetting commutativity commutes with the inverse image, as a natural isomorphism. It is
the identity in each component. -/
noncomputable def forgetCommRingSheafCompPullbackIso :
    Stacks.forgetCommRingSheaf K ⋙ pullbackRingSheafFunctor J Φ ≅
      pullbackCommRingSheafFunctor J Φ ⋙ Stacks.forgetCommRingSheaf J :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun a ↦ by
    simp only [CategoryTheory.Functor.comp_map, Iso.refl_hom,
      pullbackRingSheafFunctor_map, pullbackCommRingSheafFunctor_map]
    exact (forgetCommRingSheaf_map_pullbackCommRingSheafMap J Φ a).symm)

end CommRingPullback

/-! ## Comparison with restriction along a continuous functor of sites -/

section CommRingRestriction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K CommRingCat.{ww})

/-- Over an object of the source site, the transported commutative ring structure on the
inverse image of `O` along restriction is the commutative ring structure of `O` over the image
object: the identity is a ring homomorphism from the former to the latter. -/
noncomputable def restrictionCommRingHom (X : Cᵒᵖ) :
    (pullbackCommRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X ⟶
      ((G.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O).obj.obj X :=
  letI := inverseImageSectionsCommRing J (G.sheafPushforwardContinuous (Type ww) J K)
    (SheafOfModules.Tensor.ringSheaf O) (commRingSheaf_mul_comm O) X
  CommRingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦
        Sheaf.sectionsFunctor_map_ringAddHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X) x y
      map_mul' := fun x y ↦
        Sheaf.sectionsFunctor_map_ringMulHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X) x y
      map_zero' :=
        Sheaf.sectionsFunctor_map_ringZeroHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X)
          default
      map_one' :=
        Sheaf.sectionsFunctor_map_ringOneHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X)
          default }

/-- The same identity, read as a ring homomorphism in the other direction. -/
noncomputable def restrictionCommRingHomInv (X : Cᵒᵖ) :
    ((G.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O).obj.obj X ⟶
      (pullbackCommRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X :=
  letI := inverseImageSectionsCommRing J (G.sheafPushforwardContinuous (Type ww) J K)
    (SheafOfModules.Tensor.ringSheaf O) (commRingSheaf_mul_comm O) X
  CommRingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦
        (Sheaf.sectionsFunctor_map_ringAddHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X) x
          y).symm
      map_mul' := fun x y ↦
        (Sheaf.sectionsFunctor_map_ringMulHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X) x
          y).symm
      map_zero' :=
        (Sheaf.sectionsFunctor_map_ringZeroHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X)
          default).symm
      map_one' :=
        (Sheaf.sectionsFunctor_map_ringOneHom (SheafOfModules.Tensor.ringSheaf O) (G.op.obj X)
          default).symm }

/-- For a continuous functor of sites `G`, the inverse image of a sheaf of commutative rings
along the induced restriction functor on sheaves of sets *is* the restriction of that sheaf of
commutative rings. The comparison is the identity on underlying sheaves of sets. -/
noncomputable def restrictionCommRingIso :
    pullbackCommRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O ≅
      (G.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O where
  hom :=
    { hom :=
        { app := fun X ↦ restrictionCommRingHom J K G O X
          naturality := fun _ _ _ ↦ rfl } }
  inv :=
    { hom :=
        { app := fun X ↦ restrictionCommRingHomInv J K G O X
          naturality := fun _ _ _ ↦ rfl } }
  hom_inv_id := rfl
  inv_hom_id := rfl

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- Forgetting commutativity carries the comparison to the ring-valued comparison. -/
lemma forgetCommRingSheaf_map_restrictionCommRingIso_hom :
    (Stacks.forgetCommRingSheaf J).map (restrictionCommRingIso J K G O).hom =
      (restrictionRingIso J K G (SheafOfModules.Tensor.ringSheaf O)).hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The comparison of the inverse image with restriction is the identity on underlying sheaves
of sets. -/
@[simp]
lemma restrictionCommRingIso_hom_forget [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget CommRingCat.{ww})] :
    (sheafCompose J (forget CommRingCat.{ww})).map (restrictionCommRingIso J K G O).hom =
      𝟙 ((G.sheafPushforwardContinuous (Type ww) J K).obj
        ((sheafCompose K (forget CommRingCat.{ww})).obj O)) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The inverse comparison is also the identity on underlying sheaves of sets. -/
@[simp]
lemma restrictionCommRingIso_inv_forget [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget CommRingCat.{ww})] :
    (sheafCompose J (forget CommRingCat.{ww})).map (restrictionCommRingIso J K G O).inv =
      𝟙 ((G.sheafPushforwardContinuous (Type ww) J K).obj
        ((sheafCompose K (forget CommRingCat.{ww})).obj O)) :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The comparison with restriction is natural in the sheaf of commutative rings. -/
lemma restrictionCommRingIso_naturality {O O' : Sheaf K CommRingCat.{ww}} (a : O ⟶ O') :
    pullbackCommRingSheafMap J (G.sheafPushforwardContinuous (Type ww) J K) a ≫
        (restrictionCommRingIso J K G O').hom =
      (restrictionCommRingIso J K G O).hom ≫
        (G.sheafPushforwardContinuous CommRingCat.{ww} J K).map a := by
  refine (fullyFaithfulForgetCommRingSheaf J).map_injective ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    forgetCommRingSheaf_map_pullbackCommRingSheafMap,
    forgetCommRingSheaf_map_restrictionCommRingIso_hom,
    forgetCommRingSheaf_map_restrictionCommRingIso_hom]
  exact restrictionRingIso_naturality J K G ((Stacks.forgetCommRingSheaf K).map a)

end CommRingRestriction

section CommRingMapForget

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

/-- On underlying sheaves of *sets*, the inverse image of a morphism of sheaves of commutative
rings is `Φ` of its underlying morphism of sheaves of sets. This is
`Stacks.Sheaves.ToposPullback.forgetCommRingSheaf_map_pullbackCommRingSheafMap` carried one
step further, past forgetting the ring operations. -/
@[simp]
lemma underlyingRingSheaf_map_pullbackCommRingSheafMap {O O' : Sheaf K CommRingCat.{ww'}}
    (a : O ⟶ O') :
    (sheafCompose J (forget CommRingCat.{ww})).map (pullbackCommRingSheafMap J Φ a) =
      Φ.map ((sheafCompose K (forget CommRingCat.{ww'})).map a) :=
  (congrArg (fun m ↦ (sheafCompose J (forget RingCat.{ww})).map m)
      (forgetCommRingSheaf_map_pullbackCommRingSheafMap J Φ a)).trans
    (ringSheafMap_pullbackRingSheafMap J Φ ((Stacks.forgetCommRingSheaf K).map a))

end CommRingMapForget

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section CommRingImageAdjunction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The inverse image of sheaves of commutative rings along a morphism of topoi. -/
noncomputable abbrev inverseImageCommRingFunctor :
    Sheaf K CommRingCat.{ww'} ⥤ Sheaf J CommRingCat.{ww} :=
  pullbackCommRingSheafFunctor J f.inverseImage

/-- The direct image of sheaves of commutative rings along a morphism of topoi. -/
noncomputable abbrev pushforwardCommRingFunctor :
    Sheaf J CommRingCat.{ww} ⥤ Sheaf K CommRingCat.{ww'} :=
  pullbackCommRingSheafFunctor K f.pushforward

/-- The inverse image of sheaves of commutative rings along a morphism of topoi is left adjoint
to the direct image. This is the ring-level adjunction of Stacks 00YV for commutative rings; it
is the adjunction `Stacks.Sheaves.ToposPushforward.ringImageAdjunction` of sheaves of rings,
restricted along the fully faithful inclusion of sheaves of commutative rings. -/
noncomputable def commRingImageAdjunction :
    inverseImageCommRingFunctor f ⊣ pushforwardCommRingFunctor f :=
  Adjunction.restrictFullyFaithful (ringImageAdjunction f)
    (fullyFaithfulForgetCommRingSheaf K) (fullyFaithfulForgetCommRingSheaf J)
    (forgetCommRingSheafCompPullbackIso J f.inverseImage)
    (forgetCommRingSheafCompPullbackIso K f.pushforward)

end CommRingImageAdjunction

end Stacks.Sheaves.ToposPushforward

end
