module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Morphisms of ringed topoi whose inverse image is restriction along a functor of sites

A geometric morphism `f : Sh(C) → Sh(D)` is frequently *presented* by a continuous functor
`F : C ⥤ D` of the underlying sites, in the sense that `f⁻¹` is the restriction functor
`F^s = F.sheafPushforwardContinuous`. For such an `f` the inverse image of a sheaf of
commutative rings is again restriction, so an isomorphism `f⁻¹O_D ≅ O_C` of structure sheaves
can be produced from nothing, and a morphism of ringed topoi `(Sh(C), O_C) → (Sh(D), O_D)` can
be built from it by adjunction.

Both halves are carried out here. The comparison
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` identifies the inverse image along `F^s`
itself with restriction; what this file adds is the transport of that identification along a
natural isomorphism `f⁻¹ ≅ F^s`, which is how it is applied, and the passage from a
structure-sheaf isomorphism to a morphism of ringed topoi.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr`: the inverse image of a sheaf of
  commutative rings, transported along a natural isomorphism of the inverse-image functors of
  sheaves of sets.
* `Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso`: for a morphism of topoi
  whose inverse image is isomorphic to restriction along a continuous functor of sites, the
  inverse image of a sheaf of commutative rings is the restriction of that sheaf of
  commutative rings.
* `AlgebraicGeometry.RingedToposHom.ofInverseImageMap`: a morphism of topoi together with a
  map `f⁻¹O_D ⟶ O_C` of structure sheaves, read as a morphism of ringed topoi.
* `AlgebraicGeometry.RingedToposHom.ofInverseImageIso`: the same for an isomorphism
  `f⁻¹O_D ≅ O_C` of structure sheaves.

## Main results

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr_hom_forget` and
  `Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_hom_forget`: on underlying
  sheaves of sets both comparisons are the prescribed isomorphism of inverse-image functors,
  so no ring-theoretic choice is hidden in them.
* `AlgebraicGeometry.RingedToposHom.ofInverseImageMap_fSharpInverseImage` and
  `.ofInverseImageIso_fSharpInverseImage`: the inverse-image form of the structure map of the
  resulting morphism of ringed topoi is the map, respectively the isomorphism, it was built
  from.

## Implementation notes

The transport is built componentwise out of `CategoryTheory.Sheaf.ringObjHom`, which turns a
natural transformation of finite-product-preserving functors to types into a ring homomorphism
between the ring structures it transports. This keeps the underlying map of sheaves of sets
equal to the given isomorphism *by definition*, which is what
`pullbackCommRingSheafCongr_hom_forget` records and what consumers need: the ring operations
of the inverse image are read off from the functor, so a transport that went through
sheafification or through an internal-ring comparison would only be the prescribed map up to a
further isomorphism.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section Congr

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  {Φ Ψ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Ψ]

/-- A natural transformation `Φ ⟶ Ψ` of inverse-image functors of sheaves of sets induces, over
each object of the source site, a ring homomorphism between the two transported commutative
ring structures on the sections of the inverse image of a sheaf of commutative rings. -/
noncomputable def pullbackCommRingSheafCongrApp (θ : Φ ⟶ Ψ) (O : Sheaf K CommRingCat.{ww'})
    (X : Cᵒᵖ) :
    (pullbackCommRingSheaf J Φ O).obj.obj X ⟶ (pullbackCommRingSheaf J Ψ O).obj.obj X :=
  letI := inverseImageSectionsCommRing J Φ (SheafOfModules.Tensor.ringSheaf O)
      (commRingSheaf_mul_comm O) X
  letI := inverseImageSectionsCommRing J Ψ (SheafOfModules.Tensor.ringSheaf O)
      (commRingSheaf_mul_comm O) X
  CommRingCat.ofHom
    (Sheaf.ringObjHom (SheafOfModules.Tensor.ringSheaf O)
      (Functor.whiskerRight θ (Sheaf.sectionsFunctor J X)))

/-- The inverse image of a sheaf of commutative rings is functorial in the inverse-image
functor of sheaves of sets: a natural transformation `Φ ⟶ Ψ` induces a map of the inverse
images, which on underlying sheaves of sets is the given natural transformation. -/
noncomputable def pullbackCommRingSheafCongrMap (θ : Φ ⟶ Ψ) (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheaf J Φ O ⟶ pullbackCommRingSheaf J Ψ O where
  hom :=
    { app := fun X ↦ pullbackCommRingSheafCongrApp J θ O X
      naturality := fun X Y g ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        change (θ.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app Y
            ((Φ.obj (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).obj.map g x) =
          (Ψ.obj (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).obj.map g
            ((θ.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app X x)
        exact NatTrans.naturality_apply
          (θ.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom g x }

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- On underlying sheaves of sets the induced map is the given natural transformation. -/
@[simp]
lemma pullbackCommRingSheafCongrMap_forget [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget CommRingCat.{ww'})] (θ : Φ ⟶ Ψ)
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map (pullbackCommRingSheafCongrMap J θ O) =
      θ.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

/-- The inverse image of a sheaf of commutative rings, transported along a natural isomorphism
of the inverse-image functors of sheaves of sets. -/
noncomputable def pullbackCommRingSheafCongr (e : Φ ≅ Ψ) (O : Sheaf K CommRingCat.{ww'}) :
    pullbackCommRingSheaf J Φ O ≅ pullbackCommRingSheaf J Ψ O where
  hom := pullbackCommRingSheafCongrMap J e.hom O
  inv := pullbackCommRingSheafCongrMap J e.inv O
  hom_inv_id := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦
      CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)))
    change (e.inv.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app X
        ((e.hom.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app X x) = x
    exact congrFun (congrArg (fun m ↦ m.hom.app X)
      (e.hom_inv_id_app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)))) x
  inv_hom_id := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦
      CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)))
    change (e.hom.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app X
        ((e.inv.app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O))).hom.app X x) = x
    exact congrFun (congrArg (fun m ↦ m.hom.app X)
      (e.inv_hom_id_app (Sheaf.ringSheaf (SheafOfModules.Tensor.ringSheaf O)))) x

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})] in
/-- The transport is the identity on underlying sheaves of sets: it *is* the given
isomorphism. -/
@[simp]
lemma pullbackCommRingSheafCongr_hom_forget [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget CommRingCat.{ww'})] (e : Φ ≅ Ψ)
    (O : Sheaf K CommRingCat.{ww'}) :
    (sheafCompose J (forget CommRingCat.{ww})).map (pullbackCommRingSheafCongr J e O).hom =
      e.hom.app ((sheafCompose K (forget CommRingCat.{ww'})).obj O) :=
  pullbackCommRingSheafCongrMap_forget J e.hom O

end Congr

section Restriction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  (F : C ⥤ D) [F.IsContinuous J K]
  [PreservesFiniteProducts (F.sheafPushforwardContinuous (Type ww) J K)]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww)))
  (e : f.inverseImage ≅ F.sheafPushforwardContinuous (Type ww) J K)
  (O : Sheaf K CommRingCat.{ww})

/-- For a morphism of topoi whose inverse image is isomorphic to restriction along a continuous
functor `F` of the underlying sites, the inverse image of a sheaf of commutative rings is the
restriction of that sheaf of commutative rings along `F`. -/
noncomputable def inverseImageCommRingRestrictionIso :
    (inverseImageCommRingFunctor f).obj O ≅
      (F.sheafPushforwardContinuous CommRingCat.{ww} J K).obj O :=
  pullbackCommRingSheafCongr J e O ≪≫ restrictionCommRingIso J K F O

/-- The identification of the inverse image with restriction is, on underlying sheaves of sets,
the prescribed isomorphism `f⁻¹ ≅ F^s`. -/
lemma inverseImageCommRingRestrictionIso_hom_forget
    [J.HasSheafCompose (forget CommRingCat.{ww})]
    [K.HasSheafCompose (forget CommRingCat.{ww})] :
    (sheafCompose J (forget CommRingCat.{ww})).map
        (inverseImageCommRingRestrictionIso J K F f e O).hom =
      e.hom.app ((sheafCompose K (forget CommRingCat.{ww})).obj O) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

end Restriction

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : MorphismOfTopoi X.Topos Y.Topos)
  (e : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor f).obj Y.O ≅ X.O)

/-- A morphism of topoi together with a map `f⁻¹O_Y ⟶ O_X` of structure sheaves is a morphism
of ringed topoi, the direct-image form of the structure map being the adjunct of that map. -/
noncomputable def ofInverseImageMap
    (α : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor f).obj Y.O ⟶ X.O) :
    RingedToposHom X Y where
  toToposHom := f
  fSharp :=
    ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction f).homEquiv Y.O X.O) α

/-- The underlying morphism of topoi of `ofInverseImageMap f α` is `f`. -/
@[simp]
lemma ofInverseImageMap_toToposHom
    (α : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor f).obj Y.O ⟶ X.O) :
    (ofInverseImageMap f α).toToposHom = f :=
  rfl

/-- The inverse-image form of the structure map of `ofInverseImageMap f α` is `α`: taking the
adjunct and then its inverse recovers the map it was built from. -/
lemma ofInverseImageMap_fSharpInverseImage
    (α : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor f).obj Y.O ⟶ X.O) :
    (ofInverseImageMap f α).fSharpInverseImage = α :=
  ((Stacks.Sheaves.ToposPushforward.commRingImageAdjunction f).homEquiv Y.O X.O).symm_apply_apply α

/-- A morphism of topoi together with an isomorphism `f⁻¹O_Y ≅ O_X` of structure sheaves is a
morphism of ringed topoi, the direct-image form of the structure map being the adjunct of that
isomorphism. -/
noncomputable def ofInverseImageIso : RingedToposHom X Y :=
  ofInverseImageMap f e.hom

/-- The inverse-image form of the structure map of `ofInverseImageIso f e` is `e`: taking the
adjunct and then its inverse recovers the isomorphism it was built from. -/
lemma ofInverseImageIso_fSharpInverseImage : (ofInverseImageIso f e).fSharpInverseImage = e.hom :=
  ofInverseImageMap_fSharpInverseImage f e.hom

/-- The structure map of `ofInverseImageIso f e` is invertible in inverse-image form, being the
isomorphism `e`. -/
theorem isIso_fSharpInverseImage_ofInverseImageIso :
    IsIso (ofInverseImageIso f e).fSharpInverseImage := by
  rw [ofInverseImageIso_fSharpInverseImage]
  exact e.isIso_hom

end AlgebraicGeometry.RingedToposHom

end
