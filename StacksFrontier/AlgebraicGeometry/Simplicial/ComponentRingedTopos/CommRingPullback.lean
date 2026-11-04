module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Dependence of the inverse image of sheaves of commutative rings on the pullback functor

`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf J Φ O` transports the commutative ring
operations of a sheaf of commutative rings `O` along a finite-product-preserving functor `Φ` of
sheaves of sets. This file records how that construction depends on `Φ`: a natural
transformation `Φ ⟶ Φ'` induces a map of the transported sheaves of commutative rings, a natural
isomorphism `Φ ≅ Φ'` induces an isomorphism of the transported functors, and both are the given
natural transformation on underlying sheaves of sets.

As a consequence, the comparison with restriction along a continuous functor of sites is a
natural isomorphism of functors (`restrictionCommRingNatIso`), and inverse image along a
morphism of topoi whose set-level inverse image is isomorphic to restriction — as for a
cocontinuous and continuous functor of sites — can be compared with restriction on sheaves of
commutative rings.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafMapOfNatTrans`: the map of transported
  sheaves of commutative rings induced by a natural transformation of pullback functors.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso` and
  `.pullbackCommRingSheafFunctorIsoOfNatIso`: the isomorphism, and the isomorphism of functors,
  induced by a natural isomorphism of pullback functors.
* `Stacks.Sheaves.ToposPullback.forgetPullbackCommRingSheafIso`: the underlying sheaf of sets of
  the transported sheaf of commutative rings is the pullback of the underlying sheaf of sets.
* `Stacks.Sheaves.ToposPullback.restrictionCommRingNatIso`: the comparison of
  `pullbackCommRingSheafFunctor` along restriction with restriction of sheaves of commutative
  rings, as an isomorphism of functors.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorId`: its identity case, transporting
  the operations along the identity functor of sheaves of sets does nothing.
* `Stacks.Sheaves.ToposPushforward.inverseImageCommRingForgetIso`: the underlying sheaf of sets
  of the inverse image of a sheaf of commutative rings along a morphism of topoi is the
  geometric inverse image of its underlying sheaf of sets.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafMapOfNatTrans_forget`: on underlying
  sheaves of sets, the induced map is the given natural transformation.

## Implementation notes

The induced map is built sheaf by sheaf and section by section from
`CategoryTheory.Sheaf.ringObjHom`, which turns a natural transformation of
finite-product-preserving functors to types into a ring homomorphism between the two
transported ring structures. That is exactly the data `pullbackCommRingSheaf` is built from, so
the induced map is the identity in no sense weaker than the construction itself: its underlying
map of sheaves of sets is the given natural transformation on the nose, which is what
`pullbackCommRingSheafMapOfNatTrans_forget` records as an `rfl`.

Functoriality in the natural transformation (`pullbackCommRingSheafMapOfNatTrans_id` and
`_comp`) is definitional, which is what makes `pullbackCommRingSheafIsoOfNatIso` cheap: its two
identities are the two identities of the given isomorphism.

Equations between morphisms of sheaves of commutative rings are proved by applying
`sheafCompose J (forget CommRingCat)`, which is faithful because `forget CommRingCat` is, and
then appealing to the two `_forget` lemmas. This is cheaper than the route through
`fullyFaithfulForgetCommRingSheaf` used in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposCommRingImageAdjunction.lean`, because the
hypotheses needed to mention the underlying sheaf of sets are present here anyway.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

attribute [local implicit_reducible] pullbackCommRingSheafFunctor

section NatTransport

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']

/-- A natural transformation of finite-product-preserving functors of sheaves of sets induces a
map of the sheaves of commutative rings obtained by transporting the operations of `O` along
them. On sections it is the given natural transformation, read as a ring homomorphism by
`CategoryTheory.Sheaf.ringObjHom`. -/
noncomputable def pullbackCommRingSheafMapOfNatTrans (e : Φ ⟶ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheaf J Φ O ⟶ pullbackCommRingSheaf J Φ' O :=
  ⟨{ app := fun X ↦
       letI := inverseImageSectionsCommRing J Φ (SheafOfModules.Tensor.ringSheaf O)
         (commRingSheaf_mul_comm O) X
       letI := inverseImageSectionsCommRing J Φ' (SheafOfModules.Tensor.ringSheaf O)
         (commRingSheaf_mul_comm O) X
       CommRingCat.ofHom (Sheaf.ringObjHom (SheafOfModules.Tensor.ringSheaf O)
         (Functor.whiskerRight e (Sheaf.sectionsFunctor J X)))
     naturality := fun _ _ g ↦
       CommRingCat.hom_ext (RingHom.ext fun x ↦
         (Functor.natTrans_app_map_apply (Sheaf.sectionsRestrict g)
           (e.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))) x).symm) }⟩

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- Transporting along the identity natural transformation does nothing. -/
lemma pullbackCommRingSheafMapOfNatTrans_id (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheafMapOfNatTrans J (𝟙 Φ) O = 𝟙 (pullbackCommRingSheaf J Φ O) :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- Transporting along a composite is the composite of the transports. -/
lemma pullbackCommRingSheafMapOfNatTrans_comp
    {Φ'' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)} [PreservesFiniteProducts Φ'']
    (a : Φ ⟶ Φ') (b : Φ' ⟶ Φ'') (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheafMapOfNatTrans J (a ≫ b) O =
      pullbackCommRingSheafMapOfNatTrans J a O ≫ pullbackCommRingSheafMapOfNatTrans J b O :=
  rfl

/-- A natural isomorphism of finite-product-preserving functors of sheaves of sets induces an
isomorphism of the sheaves of commutative rings obtained by transporting the operations of `O`
along them. -/
noncomputable def pullbackCommRingSheafIsoOfNatIso (e : Φ ≅ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheaf J Φ O ≅ pullbackCommRingSheaf J Φ' O where
  hom := pullbackCommRingSheafMapOfNatTrans J e.hom O
  inv := pullbackCommRingSheafMapOfNatTrans J e.inv O
  hom_inv_id := by
    rw [← pullbackCommRingSheafMapOfNatTrans_comp, e.hom_inv_id,
      pullbackCommRingSheafMapOfNatTrans_id]
  inv_hom_id := by
    rw [← pullbackCommRingSheafMapOfNatTrans_comp, e.inv_hom_id,
      pullbackCommRingSheafMapOfNatTrans_id]

section Forget

variable [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- On underlying sheaves of sets, the map induced by a natural transformation of pullback
functors *is* that natural transformation. -/
lemma pullbackCommRingSheafMapOfNatTrans_forget (e : Φ ⟶ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafMapOfNatTrans J e O) =
      e.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- On underlying sheaves of sets, the isomorphism induced by a natural isomorphism of pullback
functors is that natural isomorphism. -/
@[simp]
lemma pullbackCommRingSheafIsoOfNatIso_hom_forget (e : Φ ≅ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafIsoOfNatIso J e O).hom =
      e.hom.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  rfl

/-- The underlying sheaf of sets of the transported sheaf of commutative rings is the pullback
of the underlying sheaf of sets, naturally and on the nose. -/
noncomputable def forgetPullbackCommRingSheafIso :
    pullbackCommRingSheafFunctor J Φ ⋙ sheafCompose J (forget CommRingCat.{ww}) ≅
      sheafCompose K (forget CommRingCat.{ww'}) ⋙ Φ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun a ↦
    (Category.comp_id _).trans
      ((underlyingRingSheaf_map_pullbackCommRingSheafMap J _ a).trans (Category.id_comp _).symm)

/-- The components of `forgetPullbackCommRingSheafIso` are identities. -/
@[simp]
lemma forgetPullbackCommRingSheafIso_hom_app (O : Sheaf K CommRingCat.{ww'}) :
    (forgetPullbackCommRingSheafIso J (Φ := Φ)).hom.app O =
      𝟙 ((sheafCompose J (forget CommRingCat.{ww})).obj (pullbackCommRingSheaf J Φ O)) :=
  rfl

/-- The isomorphism of functors induced by a natural isomorphism of pullback functors. -/
noncomputable def pullbackCommRingSheafFunctorIsoOfNatIso (e : Φ ≅ Φ') :
    pullbackCommRingSheafFunctor J Φ ≅ pullbackCommRingSheafFunctor J Φ' :=
  NatIso.ofComponents (pullbackCommRingSheafIsoOfNatIso J e) fun a ↦ by
    refine (sheafCompose J (forget CommRingCat.{ww})).map_injective ?_
    simp only [CategoryTheory.Functor.map_comp, pullbackCommRingSheafFunctor_map,
      underlyingRingSheaf_map_pullbackCommRingSheafMap, pullbackCommRingSheafIsoOfNatIso_hom_forget]
    exact e.hom.naturality _

/-- The component of `pullbackCommRingSheafFunctorIsoOfNatIso J e` at `O` is
`pullbackCommRingSheafIsoOfNatIso J e O`. -/
@[simp]
lemma pullbackCommRingSheafFunctorIsoOfNatIso_hom_app (e : Φ ≅ Φ')
    (O : Sheaf K CommRingCat.{ww'}) :
    (pullbackCommRingSheafFunctorIsoOfNatIso J e).hom.app O =
      (pullbackCommRingSheafIsoOfNatIso J e O).hom :=
  rfl

end Forget

end NatTransport

section Restriction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K]

/-- **The comparison with restriction, as an isomorphism of functors.** For a continuous functor
of sites, transporting the commutative ring operations along restriction of sheaves of sets is
restriction of sheaves of commutative rings. Its components are `restrictionCommRingIso`. -/
noncomputable def restrictionCommRingNatIso :
    pullbackCommRingSheafFunctor J (G.sheafPushforwardContinuous (Type ww) J K) ≅
      G.sheafPushforwardContinuous CommRingCat.{ww} J K :=
  NatIso.ofComponents (restrictionCommRingIso J K G) (restrictionCommRingIso_naturality J K G)

/-- The component of `restrictionCommRingNatIso J K G` at `O` is `restrictionCommRingIso J K G O`.
-/
@[simp]
lemma restrictionCommRingNatIso_hom_app (O : Sheaf K CommRingCat.{ww}) :
    (restrictionCommRingNatIso J K G).hom.app O = (restrictionCommRingIso J K G O).hom :=
  rfl

end Restriction

section Identity

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]

/-- **Transporting the operations along the identity does nothing.** Transporting the commutative
ring operations of sheaves along the identity functor of sheaves of sets is isomorphic to the
identity functor of sheaves of commutative rings. -/
noncomputable def pullbackCommRingSheafFunctorId :
    pullbackCommRingSheafFunctor J (𝟭 (Sheaf J (Type ww))) ≅ 𝟭 (Sheaf J CommRingCat.{ww}) :=
  restrictionCommRingNatIso J J (𝟭 C)

/-- On underlying sheaves of sets, the components of `pullbackCommRingSheafFunctorId` are
identities. -/
@[simp]
lemma forget_map_pullbackCommRingSheafFunctorId_hom_app
    [J.HasSheafCompose (forget CommRingCat.{ww})] (O : Sheaf J CommRingCat.{ww}) :
    (sheafCompose J (forget CommRingCat.{ww})).map
        ((pullbackCommRingSheafFunctorId J).hom.app O) =
      𝟙 ((sheafCompose J (forget CommRingCat.{ww})).obj O) :=
  restrictionCommRingIso_hom_forget J J (𝟭 C) O

end Identity

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The inverse image of a sheaf of commutative rings along a morphism of topoi has the
geometric inverse image of the underlying sheaf of sets as its underlying sheaf of sets. -/
noncomputable def inverseImageCommRingForgetIso :
    inverseImageCommRingFunctor f ⋙ sheafCompose J (forget CommRingCat.{ww}) ≅
      sheafCompose K (forget CommRingCat.{ww'}) ⋙ f.inverseImage :=
  forgetPullbackCommRingSheafIso J

/-- The components of `inverseImageCommRingForgetIso` are identities. -/
@[simp]
lemma inverseImageCommRingForgetIso_hom_app (O : Sheaf K CommRingCat.{ww'}) :
    (inverseImageCommRingForgetIso J f).hom.app O =
      𝟙 ((sheafCompose J (forget CommRingCat.{ww})).obj
        ((inverseImageCommRingFunctor f).obj O)) :=
  rfl

end Stacks.Sheaves.ToposPushforward

end
