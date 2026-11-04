module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjointPullPush
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image and direct image of sheaves of rings as adjoint functors

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi. The library already has the inverse image
`f⁻¹O` of a sheaf of rings, the direct image `f_*O`, and the two canonical maps
`O ⟶ f_*f⁻¹O` and `f⁻¹f_*O ⟶ O` (`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf`,
`.pushforwardRingSheaf`, `.ringUnit`, `.ringCounit`), but only on *objects*: nothing said what
the inverse image does to a morphism of sheaves of rings. This file supplies that, and deduces
that the two constructions are adjoint functors

`f⁻¹ : Ring(Sh(D)) ⥤ Ring(Sh(C))`  ⊣  `f_* : Ring(Sh(C)) ⥤ Ring(Sh(D))`,

with `ringUnit` and `ringCounit` as unit and counit. This is the ring-level adjunction that
Stacks 00YV provides for a general algebraic structure, here for sheaves of rings and obtained
directly from the adjunction `f⁻¹ ⊣ f_*` on sheaves of sets.

The construction is elementary once it is said in the right place. Transport of the ring
structure along a finite-product-preserving functor `Φ` of sheaves of sets is natural in the
sheaf of rings: if `a : O ⟶ O'` is a morphism of sheaves of rings, then its underlying map of
sheaves of sets intertwines the addition, multiplication, zero and one *morphisms*
`ringAddHom`, `ringMulHom`, `ringZeroHom`, `ringOneHom` of `O` with those of `O'`, hence `Φ`
of it intertwines the transported operations. That gives `pullbackRingSheafMap`, hence the
functor `pullbackRingSheafFunctor`, and instantiating `Φ` at `f.inverseImage` and at
`f.pushforward` gives the two functors of the adjunction. Both triangle identities are then
read off from the triangle identities of `f⁻¹ ⊣ f_*`, because
`sheafCompose J (forget RingCat)` is faithful and carries `ringUnit` and `ringCounit` to the
unit and counit of that adjunction.

The last section compares the inverse image along a *continuous functor of sites* with
restriction. If `G : C ⥤ D` is continuous, the inverse image of the induced morphism of topoi
is restriction `G.sheafPushforwardContinuous`, and the sections of `f⁻¹O` over `X` are by
construction the sections of `O` over `G X` — with the ring structure transported rather than
the original one. `restrictionRingIso` identifies the two: the transported operations agree
with the original ones because the transport is along a sections functor, where
`CategoryTheory.Sheaf.sectionsFunctor_map_ringAddHom` and its siblings compute it. The
underlying map of sheaves of sets is the identity.

## Main definitions

* `CategoryTheory.Sheaf.ringObjMap`: the ring homomorphism induced by a morphism of sheaves of
  rings between the ring structures transported along a finite-product-preserving functor.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafMap` and `.pullbackRingSheafFunctor`: the
  inverse image of a morphism of sheaves of rings along a finite-product-preserving functor of
  sheaves of sets, and the resulting functor.
* `Stacks.Sheaves.ToposPullback.restrictionRingIso`: for a continuous functor of sites, the
  identification of the inverse image of a sheaf of rings with its restriction.
* `Stacks.Sheaves.ToposPushforward.inverseImageRingFunctor` and `.pushforwardRingFunctor`: the
  inverse image and the direct image of sheaves of rings along a morphism of topoi, as
  functors.
* `Stacks.Sheaves.ToposPushforward.ringImageAdjunction`: the adjunction between them.

## Main results

* `Stacks.Sheaves.ToposPushforward.ringImageAdjunction_homEquiv_apply` and
  `.ringImageAdjunction_homEquiv_symm_apply`: the bijection of the adjunction is the usual
  one, `φ ↦ ringUnit ≫ f_*φ` and `ψ ↦ f⁻¹ψ ≫ ringCounit`.
* `Stacks.Sheaves.ToposPullback.restrictionRingIso_hom_ringSheafMap`: the comparison with
  restriction is the identity on underlying sheaves of sets.

## Implementation notes

The adjunction is built with `CategoryTheory.Adjunction.mkOfUnitCounit` from the existing
`ringUnit` and `ringCounit` rather than from a hom-set bijection, so that the unit and counit
of the resulting adjunction are *those* maps and not some transport of them: every lemma about
them in the library applies to the adjunction unchanged.

Every equation between morphisms of sheaves of rings below is proved by applying
`Functor.map_injective` for `sheafCompose J (forget RingCat)` — which is faithful because
`forget RingCat` is — and then quoting the corresponding equation for the adjunction
`f⁻¹ ⊣ f_*` of sheaves of sets. No ring-theoretic content is involved beyond
`pullbackRingSheafMap` itself.

The sheaves of rings are sheaves of *not necessarily commutative* rings, as in Stacks 03AD,
03D1 and 03D2 and as in the rest of this development's topos-level ring theory. Commutativity
is nowhere used.

`HasSheafCompose (forget RingCat)` for each site is assumed, not derived, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean`: deriving it needs the
forgetful functor of rings to preserve limits of the site's size, which in the pinned Mathlib
holds only under a `UnivLE` hypothesis comparing the site's hom universe with the universe of
sections.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite

namespace CategoryTheory.Sheaf

universe t w v u

section RingSheafMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] {R R' : Sheaf J RingCat.{w}} (a : R ⟶ R')

/-- A morphism of sheaves of rings intertwines the two addition morphisms. -/
lemma ringAddHom_comp_ringSheafMap :
    ringAddHom R ≫ (sheafCompose J (forget RingCat.{w})).map a =
      Limits.prod.map ((sheafCompose J (forget RingCat.{w})).map a)
          ((sheafCompose J (forget RingCat.{w})).map a) ≫
        ringAddHom R' := by
  refine hom_ext_sections fun X s ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := sectionsFunctor J X) s,
    (sectionsFunctor J X).map_comp_apply, (sectionsFunctor J X).map_comp_apply,
    sectionsFunctor_map_ringAddHom, map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    sectionsFunctor_map_ringAddHom]
  exact (a.hom.app X).hom.map_add _ _

/-- A morphism of sheaves of rings intertwines the two multiplication morphisms. -/
lemma ringMulHom_comp_ringSheafMap :
    ringMulHom R ≫ (sheafCompose J (forget RingCat.{w})).map a =
      Limits.prod.map ((sheafCompose J (forget RingCat.{w})).map a)
          ((sheafCompose J (forget RingCat.{w})).map a) ≫
        ringMulHom R' := by
  refine hom_ext_sections fun X s ↦ ?_
  rw [← prodObjMk_map_fst_map_snd (P := sectionsFunctor J X) s,
    (sectionsFunctor J X).map_comp_apply, (sectionsFunctor J X).map_comp_apply,
    sectionsFunctor_map_ringMulHom, map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk,
    sectionsFunctor_map_ringMulHom]
  exact (a.hom.app X).hom.map_mul _ _

/-- A morphism of sheaves of rings carries the zero section to the zero section. -/
lemma ringZeroHom_comp_ringSheafMap :
    ringZeroHom R ≫ (sheafCompose J (forget RingCat.{w})).map a = ringZeroHom R' := by
  refine hom_ext_sections fun X s ↦ ?_
  rw [(sectionsFunctor J X).map_comp_apply, sectionsFunctor_map_ringZeroHom,
    sectionsFunctor_map_ringZeroHom]
  exact (a.hom.app X).hom.map_zero

/-- A morphism of sheaves of rings carries the unit section to the unit section. -/
lemma ringOneHom_comp_ringSheafMap :
    ringOneHom R ≫ (sheafCompose J (forget RingCat.{w})).map a = ringOneHom R' := by
  refine hom_ext_sections fun X s ↦ ?_
  rw [(sectionsFunctor J X).map_comp_apply, sectionsFunctor_map_ringOneHom,
    sectionsFunctor_map_ringOneHom]
  exact (a.hom.app X).hom.map_one

variable (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- A morphism of sheaves of rings induces a ring homomorphism between the ring structures
transported along a finite-product-preserving functor to types. This is the variance in the
sheaf of rings that `CategoryTheory.Sheaf.ringObjHom` provides in the functor. -/
noncomputable def ringObjMap :
    letI := ringObjRing R P
    letI := ringObjRing R' P
    P.obj (ringSheaf R) →+* P.obj (ringSheaf R') :=
  letI := ringObjRing R P
  letI := ringObjRing R' P
  { toFun := P.map ((sheafCompose J (forget RingCat.{w})).map a)
    map_add' := fun x y ↦ by
      change P.map ((sheafCompose J (forget RingCat.{w})).map a) (ringAddObj R P x y) =
        ringAddObj R' P _ _
      rw [ringAddObj, ← P.map_comp_apply, ringAddHom_comp_ringSheafMap, P.map_comp_apply,
        map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk, ringAddObj]
    map_mul' := fun x y ↦ by
      change P.map ((sheafCompose J (forget RingCat.{w})).map a) (ringMulObj R P x y) =
        ringMulObj R' P _ _
      rw [ringMulObj, ← P.map_comp_apply, ringMulHom_comp_ringSheafMap, P.map_comp_apply,
        map_prodMap_apply, map_fst_prodObjMk, map_snd_prodObjMk, ringMulObj]
    map_zero' := by
      change P.map ((sheafCompose J (forget RingCat.{w})).map a) (ringZeroObj R P) =
        ringZeroObj R' P
      rw [ringZeroObj, ← P.map_comp_apply, ringZeroHom_comp_ringSheafMap, ringZeroObj]
    map_one' := by
      change P.map ((sheafCompose J (forget RingCat.{w})).map a) (ringOneObj R P) =
        ringOneObj R' P
      rw [ringOneObj, ← P.map_comp_apply, ringOneHom_comp_ringSheafMap, ringOneObj] }

end RingSheafMap

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf

universe ww ww' vv uu vv' uu'

section PullbackRingSheafFunctor

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {O O' : Sheaf K RingCat.{ww'}}

/-- The inverse image of a morphism of sheaves of rings along a finite-product-preserving
functor of sheaves of sets. Its underlying morphism of sheaves of sets is `Φ` of the underlying
morphism of sheaves of sets. -/
noncomputable def pullbackRingSheafMap (a : O ⟶ O') :
    pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ O' where
  hom :=
    { app := fun X ↦
        letI := Sheaf.ringObjRing O (Φ ⋙ Sheaf.sectionsFunctor J X)
        letI := Sheaf.ringObjRing O' (Φ ⋙ Sheaf.sectionsFunctor J X)
        RingCat.ofHom (Sheaf.ringObjMap a (Φ ⋙ Sheaf.sectionsFunctor J X))
      naturality := fun X Y g ↦ by
        refine RingCat.hom_ext (RingHom.ext fun x ↦ ?_)
        change (Φ.map ((sheafCompose K (forget RingCat.{ww'})).map a)).hom.app Y
            ((Φ.obj (Sheaf.ringSheaf O)).obj.map g x) =
          (Φ.obj (Sheaf.ringSheaf O')).obj.map g
            ((Φ.map ((sheafCompose K (forget RingCat.{ww'})).map a)).hom.app X x)
        exact NatTrans.naturality_apply
          (Φ.map ((sheafCompose K (forget RingCat.{ww'})).map a)).hom g x }

/-- The underlying morphism of sheaves of sets of the inverse image of a morphism of sheaves of
rings is `Φ` of its underlying morphism of sheaves of sets. -/
@[simp]
lemma ringSheafMap_pullbackRingSheafMap (a : O ⟶ O') :
    (sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafMap J Φ a) =
      Φ.map ((sheafCompose K (forget RingCat.{ww'})).map a) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The inverse image of sheaves of rings along a finite-product-preserving functor of sheaves
of sets, as a functor. On objects it is
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf`. -/
noncomputable def pullbackRingSheafFunctor :
    Sheaf K RingCat.{ww'} ⥤ Sheaf J RingCat.{ww} where
  obj O := pullbackRingSheaf J Φ O
  map a := pullbackRingSheafMap J Φ a
  map_id O := by
    have h : Φ.map ((sheafCompose K (forget RingCat.{ww'})).map (𝟙 O)) =
        𝟙 (Φ.obj (Sheaf.ringSheaf O)) := by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    refine (sheafCompose J (forget RingCat.{ww})).map_injective
      (Sheaf.hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s
  map_comp a b := by
    have h : Φ.map ((sheafCompose K (forget RingCat.{ww'})).map (a ≫ b)) =
        Φ.map ((sheafCompose K (forget RingCat.{ww'})).map a) ≫
          Φ.map ((sheafCompose K (forget RingCat.{ww'})).map b) := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    refine (sheafCompose J (forget RingCat.{ww})).map_injective
      (Sheaf.hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s

/-- On objects, `pullbackRingSheafFunctor` is `pullbackRingSheaf`. -/
@[simp]
lemma pullbackRingSheafFunctor_obj (O : Sheaf K RingCat.{ww'}) :
    (pullbackRingSheafFunctor J Φ).obj O = pullbackRingSheaf J Φ O := rfl

/-- On morphisms, `pullbackRingSheafFunctor` is `pullbackRingSheafMap`. -/
@[simp]
lemma pullbackRingSheafFunctor_map (a : O ⟶ O') :
    (pullbackRingSheafFunctor J Φ).map a = pullbackRingSheafMap J Φ a := rfl

/-- The inverse image of the identity morphism of a sheaf of rings is the identity. -/
@[simp]
lemma pullbackRingSheafMap_id (O : Sheaf K RingCat.{ww'}) :
    pullbackRingSheafMap J Φ (𝟙 O) = 𝟙 (pullbackRingSheaf J Φ O) :=
  (pullbackRingSheafFunctor J Φ).map_id O

/-- The inverse image of a composite of morphisms of sheaves of rings is the composite of the
inverse images. -/
@[simp]
lemma pullbackRingSheafMap_comp {O₁ O₂ O₃ : Sheaf K RingCat.{ww'}} (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) :
    pullbackRingSheafMap J Φ (a ≫ b) =
      pullbackRingSheafMap J Φ a ≫ pullbackRingSheafMap J Φ b :=
  (pullbackRingSheafFunctor J Φ).map_comp a b

end PullbackRingSheafFunctor

/-! ## Comparison with restriction along a continuous functor of sites -/

section Restriction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{ww})

/-- Over an object of the source site, the transported ring structure on the inverse image of
`O` along restriction is the ring structure of `O` over the image object: the identity is a
ring homomorphism from the former to the latter. -/
noncomputable def restrictionRingHom (X : Cᵒᵖ) :
    (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X ⟶
      ((G.sheafPushforwardContinuous RingCat.{ww} J K).obj O).obj.obj X :=
  letI := Sheaf.ringObjRing O
    (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ Sheaf.sectionsFunctor_map_ringAddHom O (G.op.obj X) x y
      map_mul' := fun x y ↦ Sheaf.sectionsFunctor_map_ringMulHom O (G.op.obj X) x y
      map_zero' := Sheaf.sectionsFunctor_map_ringZeroHom O (G.op.obj X) default
      map_one' := Sheaf.sectionsFunctor_map_ringOneHom O (G.op.obj X) default }

/-- The same identity, read as a ring homomorphism in the other direction. -/
noncomputable def restrictionRingHomInv (X : Cᵒᵖ) :
    ((G.sheafPushforwardContinuous RingCat.{ww} J K).obj O).obj.obj X ⟶
      (pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O).obj.obj X :=
  letI := Sheaf.ringObjRing O
    (G.sheafPushforwardContinuous (Type ww) J K ⋙ Sheaf.sectionsFunctor J X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ (Sheaf.sectionsFunctor_map_ringAddHom O (G.op.obj X) x y).symm
      map_mul' := fun x y ↦ (Sheaf.sectionsFunctor_map_ringMulHom O (G.op.obj X) x y).symm
      map_zero' := (Sheaf.sectionsFunctor_map_ringZeroHom O (G.op.obj X) default).symm
      map_one' := (Sheaf.sectionsFunctor_map_ringOneHom O (G.op.obj X) default).symm }

/-- For a continuous functor of sites `G`, the inverse image of a sheaf of rings along the
induced restriction functor on sheaves of sets *is* the restriction of that sheaf of rings:
the sections agree on the nose, and the transported ring operations agree with the original
ones. The comparison is the identity on underlying sheaves of sets. -/
noncomputable def restrictionRingIso :
    pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O ≅
      (G.sheafPushforwardContinuous RingCat.{ww} J K).obj O where
  hom :=
    { hom :=
        { app := fun X ↦ restrictionRingHom J K G O X
          naturality := fun _ _ _ ↦ rfl } }
  inv :=
    { hom :=
        { app := fun X ↦ restrictionRingHomInv J K G O X
          naturality := fun _ _ _ ↦ rfl } }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison of the inverse image with restriction is the identity on underlying sheaves
of sets. -/
@[simp]
lemma restrictionRingIso_hom_ringSheafMap :
    (sheafCompose J (forget RingCat.{ww})).map (restrictionRingIso J K G O).hom =
      𝟙 ((G.sheafPushforwardContinuous (Type ww) J K).obj (Sheaf.ringSheaf O)) :=
  rfl

/-- The inverse comparison is also the identity on underlying sheaves of sets. -/
@[simp]
lemma restrictionRingIso_inv_ringSheafMap :
    (sheafCompose J (forget RingCat.{ww})).map (restrictionRingIso J K G O).inv =
      𝟙 ((G.sheafPushforwardContinuous (Type ww) J K).obj (Sheaf.ringSheaf O)) :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The comparison with restriction is natural in the sheaf of rings. -/
lemma restrictionRingIso_naturality {O O' : Sheaf K RingCat.{ww}} (a : O ⟶ O') :
    pullbackRingSheafMap J (G.sheafPushforwardContinuous (Type ww) J K) a ≫
        (restrictionRingIso J K G O').hom =
      (restrictionRingIso J K G O).hom ≫
        (G.sheafPushforwardContinuous RingCat.{ww} J K).map a :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ rfl))

end Restriction

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open CategoryTheory.Sheaf Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

section RingImageAdjunction

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))

/-- The inverse image of sheaves of rings along a morphism of topoi, as a functor. On objects
it is `Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf`. -/
noncomputable abbrev inverseImageRingFunctor :
    Sheaf K RingCat.{ww'} ⥤ Sheaf J RingCat.{ww} :=
  pullbackRingSheafFunctor J f.inverseImage

/-- The direct image of sheaves of rings along a morphism of topoi, as a functor. On objects it
is `Stacks.Sheaves.ToposPushforward.pushforwardRingSheaf`. -/
noncomputable abbrev pushforwardRingFunctor :
    Sheaf J RingCat.{ww} ⥤ Sheaf K RingCat.{ww'} :=
  pullbackRingSheafFunctor K f.pushforward

/-- The unit `O ⟶ f_*f⁻¹O` as a natural transformation. -/
noncomputable def ringUnitNatTrans :
    𝟭 (Sheaf K RingCat.{ww'}) ⟶ inverseImageRingFunctor f ⋙ pushforwardRingFunctor f where
  app O := ringUnit f O
  naturality O O' a := by
    have h := f.adj.unit.naturality ((sheafCompose K (forget RingCat.{ww'})).map a)
    refine (sheafCompose K (forget RingCat.{ww'})).map_injective
      (Sheaf.hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s

/-- The counit `f⁻¹f_*O ⟶ O` as a natural transformation. -/
noncomputable def ringCounitNatTrans :
    pushforwardRingFunctor f ⋙ inverseImageRingFunctor f ⟶ 𝟭 (Sheaf J RingCat.{ww}) where
  app O := ringCounit f O
  naturality O O' a := by
    have h := f.adj.counit.naturality ((sheafCompose J (forget RingCat.{ww})).map a)
    refine (sheafCompose J (forget RingCat.{ww})).map_injective
      (Sheaf.hom_ext_sections fun X s ↦ ?_)
    exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s

/-- The inverse image of sheaves of rings along a morphism of topoi is left adjoint to the
direct image, with `Stacks.Sheaves.ToposPushforward.ringUnit` and `.ringCounit` as unit and
counit. This is the ring-level adjunction of Stacks 00YV for the algebraic structure of a
ring, deduced from the adjunction `f⁻¹ ⊣ f_*` of sheaves of sets. -/
noncomputable def ringImageAdjunction :
    inverseImageRingFunctor f ⊣ pushforwardRingFunctor f :=
  Adjunction.mkOfUnitCounit
    { unit := ringUnitNatTrans f
      counit := ringCounitNatTrans f
      left_triangle := by
        refine NatTrans.ext (funext fun O ↦ ?_)
        have h := f.adj.left_triangle_components (Sheaf.ringSheaf O)
        refine (sheafCompose J (forget RingCat.{ww})).map_injective
          (Sheaf.hom_ext_sections fun X s ↦ ?_)
        exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s
      right_triangle := by
        refine NatTrans.ext (funext fun O ↦ ?_)
        have h := ringSheafMap_ringUnit_comp_pushforward_map_ringCounit f O
        refine (sheafCompose K (forget RingCat.{ww'})).map_injective
          (Sheaf.hom_ext_sections fun X s ↦ ?_)
        exact congrFun (congrArg (fun m ↦ m.hom.app X) h) s }

/-- The unit of `ringImageAdjunction` at `O` is `ringUnit f O`. -/
@[simp]
lemma ringImageAdjunction_unit_app (O : Sheaf K RingCat.{ww'}) :
    (ringImageAdjunction f).unit.app O = ringUnit f O := rfl

/-- The counit of `ringImageAdjunction` at `O` is `ringCounit f O`. -/
@[simp]
lemma ringImageAdjunction_counit_app (O : Sheaf J RingCat.{ww}) :
    (ringImageAdjunction f).counit.app O = ringCounit f O := rfl

/-- The adjunction bijection sends a map `f⁻¹O ⟶ O'` to `O ⟶ f_*f⁻¹O ⟶ f_*O'`. -/
lemma ringImageAdjunction_homEquiv_apply (O : Sheaf K RingCat.{ww'})
    (O' : Sheaf J RingCat.{ww}) (φ : inverseImageRingSheaf f O ⟶ O') :
    (ringImageAdjunction f).homEquiv O O' φ =
      ringUnit f O ≫ pullbackRingSheafMap K f.pushforward φ :=
  (ringImageAdjunction f).homEquiv_unit O O' φ

/-- The inverse adjunction bijection sends a map `O ⟶ f_*O'` to `f⁻¹O ⟶ f⁻¹f_*O' ⟶ O'`. -/
lemma ringImageAdjunction_homEquiv_symm_apply (O : Sheaf K RingCat.{ww'})
    (O' : Sheaf J RingCat.{ww}) (ψ : O ⟶ pushforwardRingSheaf f O') :
    ((ringImageAdjunction f).homEquiv O O').symm ψ =
      pullbackRingSheafMap J f.inverseImage ψ ≫ ringCounit f O' :=
  (ringImageAdjunction f).homEquiv_counit O O' ψ

end RingImageAdjunction

end Stacks.Sheaves.ToposPushforward

end
