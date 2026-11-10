module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The direct image of a sheaf of modules over a sheaf of commutative rings

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and let `O` be a sheaf of **commutative** rings
on `C`. `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean` builds Stacks 03D1
for a sheaf of rings: the direct image of a sheaf of `O`-modules is a sheaf of modules over the
direct-image sheaf of rings, packaged as
`Stacks.Sheaves.ToposPushforward.PushforwardModuleData`. This file carries that datum over to
the commutative setting, which is the form the ringed-topos vocabulary of this development uses:
`AlgebraicGeometry.RingedTopos` carries its structure sheaf in `Sheaf J CommRingCat`, and the
structure map of `AlgebraicGeometry.RingedToposHom` is therefore a morphism of sheaves of
commutative rings into `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor`.

The point of the commutative form is that the identification of the direct-image ring with the
canonical direct image is itself a morphism in `Sheaf K CommRingCat`, so it can be composed
with such a structure map *before* commutativity is forgotten. A statement about modules over
the direct image of a structure sheaf needs exactly that composite, and it cannot be formed
against the ring-valued datum, whose identification is between the underlying sheaves of sets.

Two definitional identities do all the work, and both are `rfl`:

* `ringSheaf_pushforwardCommRingFunctor_obj`: the underlying sheaf of rings of the
  direct-image sheaf of commutative rings **is** the ring-valued direct image of the underlying
  sheaf of rings. So modules over the one are modules over the other, with no transport, and
  `Stacks.Sheaves.ToposPushforward.pushforwardModuleFunctor` already lands in the right place.
* `ringSheaf_ringSheaf_eq_underlyingRingSheaf`: forgetting commutativity and then passing to
  sections agrees with passing to sections directly, so the product comparison and the scalar
  multiplication of the ring-valued datum are literally the ones the commutative datum needs.

Consequently every identifying isomorphism of `PushforwardCommRingModuleData` constructed by
`pushforwardCommRingModule` is `Iso.refl`, exactly as in the ring-valued file, and the content
of Stacks 03D1 is inherited rather than reproved.

## Main definitions

* `Stacks.Sheaves.ToposPushforward.PushforwardCommRingModuleData`: the data packaging the
  direct-image sheaf of commutative rings, the functor on modules over it, the identification
  of that ring with the canonical direct image *as a sheaf of commutative rings*, the
  identification of the underlying module sheaves with ordinary direct images, the binary
  product comparison, and both scalar multiplications.
* `Stacks.Sheaves.ToposPushforward.PushforwardCommRingModuleData.underlyingRingIso`: the
  identification induced on underlying sheaves of sets.
* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingForgetIso`: the underlying sheaf of sets
  of the direct image of a sheaf of commutative rings is the direct image of its underlying
  sheaf of sets, naturally.

## Main results

* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingModule` (Stacks 03D1 over a sheaf of
  commutative rings): the direct image of a sheaf of `O`-modules is a sheaf of modules over the
  direct image of `O` as a sheaf of commutative rings, with scalar multiplication the direct
  image of the original scalar multiplication read through the product comparison, functorially
  in the module.

## Implementation notes

The tag 03D1 is **not** restated here. It is carried by
`Stacks.Sheaves.ToposPushforward.pushforwardModule`, and the present construction is that
declaration applied to the underlying sheaf of rings and repackaged; stating the attribute again
would record a second, weaker formalization of the same tag.

The eight `GrothendieckTopology.HasSheafCompose` hypotheses are those of the pieces used:
`forget RingCat` and `forget AddCommGrpCat` on both sites for the ring-valued datum,
`forget₂ CommRingCat RingCat` on both for `Stacks.SheafOfModules.Tensor.ringSheaf`, and
`forget CommRingCat` on both for the underlying sheaf of sets of a sheaf of commutative rings.
None of them is derived, for the reason recorded in
`Stacks.Sheaves.ToposPushforward.forgetCommRingSheaf`: deriving the `forget₂` instance needs a
size hypothesis relating the site's hom universe to the universe of sections. For a ringed site
the `forget₂` instance is a theorem,
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`.

`PushforwardCommRingModuleData` records both scalar multiplications as fields, together with
the equations saying that each is the scalar multiplication of the module it belongs to. That
is what makes `action_eq` usable without unfolding `Sheaf.moduleSMulHom`: a consumer that has
its own name for the multiplication map of a sheaf of modules proves it equal to `sourceAction`
sectionwise from `sourceAction_apply` and then rewrites.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the direct image of a
  sheaf of modules along a morphism of topoi.
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV), that a morphism of
  topoi transports algebraic structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section CommRingPullbackSections

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- The underlying sheaf of sets of the inverse image of a sheaf of commutative rings is the
inverse image of its underlying sheaf of sets, on the nose. -/
lemma underlyingRingSheaf_pullbackCommRingSheaf (O : Sheaf K CommRingCat.{ww'}) :
    Stacks.underlyingRingSheaf J (pullbackCommRingSheaf J Φ O) =
      Φ.obj (Stacks.underlyingRingSheaf K O) :=
  rfl

end CommRingPullbackSections

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section Underlying

variable {C : Type uu} [Category.{vv} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- Taking the underlying sheaf of sets of a sheaf of commutative rings in one step agrees with
forgetting commutativity first. -/
lemma ringSheaf_ringSheaf_eq_underlyingRingSheaf (O : Sheaf J CommRingCat.{ww}) :
    Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O) = Stacks.underlyingRingSheaf J O :=
  rfl

end Underlying

section Forget

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

omit [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})] in
/-- The underlying sheaf of rings of the direct image of a sheaf of commutative rings **is** the
direct image of its underlying sheaf of rings. -/
lemma ringSheaf_pushforwardCommRingFunctor_obj (O : Sheaf J CommRingCat.{ww}) :
    SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor f).obj O) =
      pushforwardRingSheaf f (SheafOfModules.Tensor.ringSheaf O) :=
  rfl

/-- The underlying sheaf of sets of the direct image of a sheaf of commutative rings is the
direct image of its underlying sheaf of sets, naturally in the sheaf. Every component is the
identity. -/
noncomputable def pushforwardCommRingForgetIso :
    pushforwardCommRingFunctor f ⋙ sheafCompose K (forget CommRingCat.{ww'}) ≅
      sheafCompose J (forget CommRingCat.{ww}) ⋙ f.pushforward :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun a ↦
    (Category.comp_id _).trans
      ((underlyingRingSheaf_map_pullbackCommRingSheafMap K f.pushforward a).trans
        (Category.id_comp _).symm)

/-- Every component of the forward map of `pushforwardCommRingForgetIso` is the identity. -/
@[simp]
lemma pushforwardCommRingForgetIso_hom_app (O : Sheaf J CommRingCat.{ww}) :
    (pushforwardCommRingForgetIso f).hom.app O = 𝟙 _ :=
  rfl

/-- Every component of the inverse map of `pushforwardCommRingForgetIso` is the identity. -/
@[simp]
lemma pushforwardCommRingForgetIso_inv_app (O : Sheaf J CommRingCat.{ww}) :
    (pushforwardCommRingForgetIso f).inv.app O = 𝟙 _ :=
  rfl

end Forget

/-! ## The direct-image datum over a sheaf of commutative rings -/

/-- The data expressing that direct image along a morphism of topoi carries sheaves of modules
over a sheaf of commutative rings `O` to sheaves of modules over the direct image of `O`.

`ringIso` identifies the ring with the canonical direct image **as a sheaf of commutative
rings**. `moduleIso` identifies the underlying sheaves of sets of the
pushed-forward modules with ordinary direct images, and pins the action of `moduleFunctor` on
morphisms to ordinary direct image. `productIso` is the canonical binary product comparison, as
its two projection equations witness, and `action_eq` says that the resulting scalar
multiplication is the direct image of the original one read through that comparison. -/
structure PushforwardCommRingModuleData
    {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.HasSheafCompose (forget RingCat.{ww})]
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
    [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
    [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget RingCat.{ww'})]
    [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
    [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
    [K.HasSheafCompose (forget CommRingCat.{ww'})]
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf J CommRingCat.{ww}) where
  /-- The direct-image sheaf of commutative rings. -/
  ring : Sheaf K CommRingCat.{ww'}
  /-- Direct image of modules, functorial in the module. -/
  moduleFunctor : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O) ⥤
    SheafOfModules.{ww'} (SheafOfModules.Tensor.ringSheaf ring)
  /-- Identification with the canonical direct image, as a sheaf of commutative rings. -/
  ringIso : ring ≅ (pushforwardCommRingFunctor f).obj O
  /-- The underlying sheaf of a pushed-forward module is naturally its direct-image sheaf. -/
  moduleIso : moduleFunctor ⋙ Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf ring) ≅
    Sheaf.moduleSheafFunctor (SheafOfModules.Tensor.ringSheaf O) ⋙ f.pushforward
  /-- The canonical product comparison for the underlying ring and module sheaves. -/
  productIso (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    f.pushforward.obj (Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G) ≅
      f.pushforward.obj (Stacks.underlyingRingSheaf J O) ⨯
        f.pushforward.obj (Stacks.underlyingModuleSheaf J G)
  /-- The first projection of the product comparison is the direct image of the first
  projection. -/
  productIso_hom_fst (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    (productIso G).hom ≫ Limits.prod.fst =
      f.pushforward.map (Limits.prod.fst :
        Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G ⟶
          Stacks.underlyingRingSheaf J O)
  /-- The second projection of the product comparison is the direct image of the second
  projection. -/
  productIso_hom_snd (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    (productIso G).hom ≫ Limits.prod.snd =
      f.pushforward.map (Limits.prod.snd :
        Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G ⟶
          Stacks.underlyingModuleSheaf J G)
  /-- Scalar multiplication on the original module, as a map of sheaves of sets. -/
  sourceAction (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G ⟶
      Stacks.underlyingModuleSheaf J G
  /-- The preceding map is the scalar multiplication belonging to the original module. -/
  sourceAction_apply (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ)
      (p : (Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G).obj.obj X) :
      (sourceAction G).hom.app X p =
        let r : (SheafOfModules.Tensor.ringSheaf O).obj.obj X :=
          (Limits.prod.fst :
            Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G ⟶
              Stacks.underlyingRingSheaf J O).hom.app X p
        let m : G.val.obj X :=
          (Limits.prod.snd :
            Stacks.underlyingRingSheaf J O ⨯ Stacks.underlyingModuleSheaf J G ⟶
              Stacks.underlyingModuleSheaf J G).hom.app X p
        r • m
  /-- Scalar multiplication on the pushed-forward module, as a map of sheaves of sets. -/
  action (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    Stacks.underlyingRingSheaf K ring ⨯
      Stacks.underlyingModuleSheaf K (moduleFunctor.obj G) ⟶
        Stacks.underlyingModuleSheaf K (moduleFunctor.obj G)
  /-- The preceding map is the scalar multiplication belonging to the pushed-forward module. -/
  action_apply (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) (X : Dᵒᵖ)
      (p : (Stacks.underlyingRingSheaf K ring ⨯
        Stacks.underlyingModuleSheaf K (moduleFunctor.obj G)).obj.obj X) :
      (action G).hom.app X p =
        let r : (SheafOfModules.Tensor.ringSheaf ring).obj.obj X :=
          (Limits.prod.fst : Stacks.underlyingRingSheaf K ring ⨯
            Stacks.underlyingModuleSheaf K (moduleFunctor.obj G) ⟶
              Stacks.underlyingRingSheaf K ring).hom.app X p
        let m : (moduleFunctor.obj G).val.obj X :=
          (Limits.prod.snd : Stacks.underlyingRingSheaf K ring ⨯
            Stacks.underlyingModuleSheaf K (moduleFunctor.obj G) ⟶
              Stacks.underlyingModuleSheaf K (moduleFunctor.obj G)).hom.app X p
        r • m
  /-- Scalar multiplication after direct image is the product comparison followed by the direct
  image of the original scalar multiplication. -/
  action_eq (G : SheafOfModules.{ww} (SheafOfModules.Tensor.ringSheaf O)) :
    action G =
      Limits.prod.map
        ((sheafCompose K (forget CommRingCat.{ww'})).map ringIso.hom ≫
          (pushforwardCommRingForgetIso f).hom.app O) (moduleIso.hom.app G) ≫
        (productIso G).inv ≫ f.pushforward.map (sourceAction G) ≫
          moduleIso.inv.app G

namespace PushforwardCommRingModuleData

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]
  {f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww'))}
  {O : Sheaf J CommRingCat.{ww}}

/-- The identification of the underlying sheaves of sets induced by the identification of the
direct-image ring with the canonical direct image. -/
noncomputable def underlyingRingIso (P : PushforwardCommRingModuleData J K f O) :
    Stacks.underlyingRingSheaf K P.ring ≅ f.pushforward.obj (Stacks.underlyingRingSheaf J O) :=
  (sheafCompose K (forget CommRingCat.{ww'})).mapIso P.ringIso ≪≫
    (pushforwardCommRingForgetIso f).app O

end PushforwardCommRingModuleData

section Construction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]

/-- The direct image of a sheaf of `O`-modules under a morphism of topoi is naturally a sheaf
of modules over the direct image of `O` as a sheaf of commutative rings, with scalar
multiplication the direct image of the original scalar multiplication read through the product
comparison, functorially in the module. Every identifying isomorphism is the identity. -/
noncomputable def pushforwardCommRingModule
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (O : Sheaf J CommRingCat.{ww}) : PushforwardCommRingModuleData J K f O where
  ring := (pushforwardCommRingFunctor f).obj O
  moduleFunctor := pushforwardModuleFunctor f (SheafOfModules.Tensor.ringSheaf O)
  ringIso := Iso.refl _
  moduleIso := Iso.refl _
  productIso G := pushforwardProdIso f (Stacks.underlyingRingSheaf J O)
    (Stacks.underlyingModuleSheaf J G)
  productIso_hom_fst G := pushforwardProdIso_hom_fst f _ _
  productIso_hom_snd G := pushforwardProdIso_hom_snd f _ _
  sourceAction G := Sheaf.moduleSMulHom (SheafOfModules.Tensor.ringSheaf O) G
  sourceAction_apply _ _ _ := rfl
  action G :=
    Sheaf.moduleSMulHom (SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor f).obj O))
      ((pushforwardModuleFunctor f (SheafOfModules.Tensor.ringSheaf O)).obj G)
  action_apply _ _ _ := rfl
  action_eq G := by
    have h := PushforwardModuleData.action_eq f
      (pushforwardModule J K f (SheafOfModules.Tensor.ringSheaf O)) G
    simp only [pushforwardModule, Iso.refl_hom, Iso.refl_inv, CategoryTheory.Functor.map_id,
      pushforwardCommRingForgetIso_hom_app, NatTrans.id_app] at h ⊢
    exact h

end Construction

end Stacks.Sheaves.ToposPushforward

end
