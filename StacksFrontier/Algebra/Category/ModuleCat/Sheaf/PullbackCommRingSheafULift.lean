module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackULift

/-!
# Transporting sheaves of commutative rings along composites and universe lifts

`Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf J Φ O` transports the operations of a sheaf
of commutative rings `O` along a finite-product-preserving functor `Φ` of sheaves of sets. This
file records two facts about it that involve several universes of sets at once.

* Transporting along `Φ₁` and then along `Φ₂` is transporting along `Φ₁ ⋙ Φ₂`, for functors
  between sheaves of sets valued in three possibly different universes.
* Transporting along the universe lift `CategoryTheory.sheafCompose J uliftFunctor` is the
  universe lift `AlgebraicGeometry.SheafOfModules.sheafULift` of sheaves of commutative rings.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIterateIso`: the composition comparison,
  natural in the sheaf of commutative rings.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafULiftIso`: the comparison with
  `AlgebraicGeometry.SheafOfModules.sheafULift`, natural in the sheaf of commutative rings.

## Implementation notes

Both comparisons are the identity on sections. The first is the multi-universe form of
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafComp`, whose ring identities
(`Stacks.Sheaves.ToposPushforward.ringMulObj_comp` and its siblings) already hold for functors
between different universes. The second needs that the pair built from two lifted sections is
the lift of the pair built from the sections themselves,
`Stacks.Sheaves.ToposPullback.down_prodObjMk_sheafCompose_uliftFunctor`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

universe w w₁ w₂ v u v₁ u₁ v₂ u₂

namespace Stacks.Sheaves.ToposPullback

/-! ## Composites -/

section Iterate

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u} [Category.{v} D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) {K : GrothendieckTopology D}
  [J₁.HasSheafCompose (forget RingCat.{w₁})] [J₂.HasSheafCompose (forget RingCat.{w₂})]
  [K.HasSheafCompose (forget RingCat.{w})]
  [J₁.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [J₂.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ₁ : Sheaf K (Type w) ⥤ Sheaf J₁ (Type w₁)) [PreservesFiniteProducts Φ₁]
  (Φ₂ : Sheaf J₁ (Type w₁) ⥤ Sheaf J₂ (Type w₂)) [PreservesFiniteProducts Φ₂]

/-- The comparison from the commutative ring operations transported in two steps to those
transported along the composite. It is the identity on sections. -/
noncomputable def pullbackCommRingSheafIterateHom (O : Sheaf K CommRingCat.{w}) :
    pullbackCommRingSheaf J₂ Φ₂ (pullbackCommRingSheaf J₁ Φ₁ O) ⟶
      pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O :=
  ⟨{ app := fun X ↦
       letI := inverseImageSectionsCommRing J₂ Φ₂
         (SheafOfModules.Tensor.ringSheaf (pullbackCommRingSheaf J₁ Φ₁ O))
         (commRingSheaf_mul_comm (pullbackCommRingSheaf J₁ Φ₁ O)) X
       letI := inverseImageSectionsCommRing J₂ (Φ₁ ⋙ Φ₂) (SheafOfModules.Tensor.ringSheaf O)
         (commRingSheaf_mul_comm O) X
       CommRingCat.ofHom
         { toFun := id
           map_add' := fun x y ↦ Stacks.Sheaves.ToposPushforward.ringAddObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y
           map_mul' := fun x y ↦ Stacks.Sheaves.ToposPushforward.ringMulObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y
           map_zero' := Stacks.Sheaves.ToposPushforward.ringZeroObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)
           map_one' := Stacks.Sheaves.ToposPushforward.ringOneObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The comparison in the other direction, again the identity on sections. -/
noncomputable def pullbackCommRingSheafIterateInv (O : Sheaf K CommRingCat.{w}) :
    pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O ⟶
      pullbackCommRingSheaf J₂ Φ₂ (pullbackCommRingSheaf J₁ Φ₁ O) :=
  ⟨{ app := fun X ↦
       letI := inverseImageSectionsCommRing J₂ Φ₂
         (SheafOfModules.Tensor.ringSheaf (pullbackCommRingSheaf J₁ Φ₁ O))
         (commRingSheaf_mul_comm (pullbackCommRingSheaf J₁ Φ₁ O)) X
       letI := inverseImageSectionsCommRing J₂ (Φ₁ ⋙ Φ₂) (SheafOfModules.Tensor.ringSheaf O)
         (commRingSheaf_mul_comm O) X
       CommRingCat.ofHom
         { toFun := id
           map_add' := fun x y ↦ (Stacks.Sheaves.ToposPushforward.ringAddObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y).symm
           map_mul' := fun x y ↦ (Stacks.Sheaves.ToposPushforward.ringMulObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X) x y).symm
           map_zero' := (Stacks.Sheaves.ToposPushforward.ringZeroObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)).symm
           map_one' := (Stacks.Sheaves.ToposPushforward.ringOneObj_comp J₁ Φ₁
             (SheafOfModules.Tensor.ringSheaf O) (Φ₂ ⋙ Sheaf.sectionsFunctor J₂ X)).symm }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- **Transporting commutative ring operations along a composite is transporting them twice**,
for functors between sheaves of sets valued in arbitrary universes. The comparison is the
identity on sections. -/
noncomputable def pullbackCommRingSheafIterate (O : Sheaf K CommRingCat.{w}) :
    pullbackCommRingSheaf J₂ Φ₂ (pullbackCommRingSheaf J₁ Φ₁ O) ≅
      pullbackCommRingSheaf J₂ (Φ₁ ⋙ Φ₂) O where
  hom := pullbackCommRingSheafIterateHom J₁ J₂ Φ₁ Φ₂ O
  inv := pullbackCommRingSheafIterateInv J₁ J₂ Φ₁ Φ₂ O
  hom_inv_id := rfl
  inv_hom_id := rfl

variable [J₂.HasSheafCompose (forget CommRingCat.{w₂})]

omit [J₂.HasSheafCompose (forget RingCat)] [J₂.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The composition comparison is the identity on underlying sheaves of sets. -/
lemma forget_map_pullbackCommRingSheafIterate_hom (O : Sheaf K CommRingCat.{w}) :
    (sheafCompose J₂ (forget CommRingCat.{w₂})).map
        (pullbackCommRingSheafIterate J₁ J₂ Φ₁ Φ₂ O).hom = 𝟙 _ :=
  rfl

variable [J₁.HasSheafCompose (forget CommRingCat.{w₁})]
  [K.HasSheafCompose (forget CommRingCat.{w})]

/-- The composition comparison is natural in the sheaf of commutative rings. -/
lemma pullbackCommRingSheafIterate_naturality {O O' : Sheaf K CommRingCat.{w}} (a : O ⟶ O') :
    pullbackCommRingSheafMap J₂ Φ₂ (pullbackCommRingSheafMap J₁ Φ₁ a) ≫
        (pullbackCommRingSheafIterate J₁ J₂ Φ₁ Φ₂ O').hom =
      (pullbackCommRingSheafIterate J₁ J₂ Φ₁ Φ₂ O).hom ≫
        pullbackCommRingSheafMap J₂ (Φ₁ ⋙ Φ₂) a := by
  refine (sheafCompose J₂ (forget CommRingCat.{w₂})).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, forget_map_pullbackCommRingSheafIterate_hom,
    forget_map_pullbackCommRingSheafIterate_hom]
  refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
  exact (underlyingRingSheaf_map_pullbackCommRingSheafMap J₂ _ _).trans
    ((congrArg Φ₂.map (underlyingRingSheaf_map_pullbackCommRingSheafMap J₁ _ a)).trans
      (underlyingRingSheaf_map_pullbackCommRingSheafMap (Φ := Φ₁ ⋙ Φ₂) J₂ a).symm)

/-- **Transporting commutative ring operations along a composite is transporting them twice**,
as a natural isomorphism of functors. -/
noncomputable def pullbackCommRingSheafIterateIso :
    pullbackCommRingSheafFunctor J₁ Φ₁ ⋙ pullbackCommRingSheafFunctor J₂ Φ₂ ≅
      pullbackCommRingSheafFunctor J₂ (Φ₁ ⋙ Φ₂) :=
  NatIso.ofComponents (pullbackCommRingSheafIterate J₁ J₂ Φ₁ Φ₂)
    (pullbackCommRingSheafIterate_naturality J₁ J₂ Φ₁ Φ₂)

@[simp]
lemma pullbackCommRingSheafIterateIso_hom_app (O : Sheaf K CommRingCat.{w}) :
    (pullbackCommRingSheafIterateIso J₁ J₂ Φ₁ Φ₂).hom.app O =
      (pullbackCommRingSheafIterate J₁ J₂ Φ₁ Φ₂ O).hom :=
  rfl

end Iterate

/-! ## The universe lift -/

section ULift

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- The pair built from two lifted sections is the lift of the pair built from the sections. -/
lemma down_prodObjMk_sheafCompose_uliftFunctor
    [J.HasSheafCompose uliftFunctor.{max u₁ v₁, w}] (X : Cᵒᵖ) {A B : Sheaf J (Type w)}
    (x : (sheafCompose J uliftFunctor.{max u₁ v₁, w} ⋙ Sheaf.sectionsFunctor J X).obj A)
    (y : (sheafCompose J uliftFunctor.{max u₁ v₁, w} ⋙ Sheaf.sectionsFunctor J X).obj B) :
    ULift.down (CategoryTheory.Functor.prodObjMk
        (P := sheafCompose J uliftFunctor.{max u₁ v₁, w} ⋙ Sheaf.sectionsFunctor J X) x y) =
      CategoryTheory.Functor.prodObjMk (P := Sheaf.sectionsFunctor J X) x.down y.down :=
  CategoryTheory.Functor.prodObjMk_ext (P := Sheaf.sectionsFunctor J X) (A := A) (B := B)
    ((congrArg ULift.down (CategoryTheory.Functor.map_fst_prodObjMk
      (P := sheafCompose J uliftFunctor.{max u₁ v₁, w} ⋙ Sheaf.sectionsFunctor J X) x y)).trans
        (CategoryTheory.Functor.map_fst_prodObjMk (P := Sheaf.sectionsFunctor J X)
          (A := A) (B := B) x.down y.down).symm)
    ((congrArg ULift.down (CategoryTheory.Functor.map_snd_prodObjMk
      (P := sheafCompose J uliftFunctor.{max u₁ v₁, w} ⋙ Sheaf.sectionsFunctor J X) x y)).trans
        (CategoryTheory.Functor.map_snd_prodObjMk (P := Sheaf.sectionsFunctor J X)
          (A := A) (B := B) x.down y.down).symm)

variable [J.HasSheafCompose uliftFunctor.{max u₁ v₁, w}]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget RingCat.{max w u₁ v₁})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u₁ v₁} RingCat.{max w u₁ v₁})]

/-- Over each object, the identity of the lifted sections is a ring homomorphism from the
operations transported along the universe lift to the lifted operations. -/
noncomputable def pullbackCommRingSheafULiftHom (O : Sheaf J CommRingCat.{w}) :
    pullbackCommRingSheaf J (sheafCompose J uliftFunctor.{max u₁ v₁, w}) O ⟶
      (AlgebraicGeometry.SheafOfModules.sheafULift.{w, u₁, v₁} J).obj O :=
  ⟨{ app := fun X ↦
       letI := inverseImageSectionsCommRing J (sheafCompose J uliftFunctor.{max u₁ v₁, w})
         (SheafOfModules.Tensor.ringSheaf O) (commRingSheaf_mul_comm O) X
       CommRingCat.ofHom
         { toFun := id
           map_add' := fun x y ↦ congrArg ULift.up
             ((congrArg ((Sheaf.sectionsFunctor J X).map
                 (Sheaf.ringAddHom (SheafOfModules.Tensor.ringSheaf O)))
               (down_prodObjMk_sheafCompose_uliftFunctor J X x y)).trans
               (Sheaf.sectionsFunctor_map_ringAddHom (SheafOfModules.Tensor.ringSheaf O) X
                 x.down y.down))
           map_mul' := fun x y ↦ congrArg ULift.up
             ((congrArg ((Sheaf.sectionsFunctor J X).map
                 (Sheaf.ringMulHom (SheafOfModules.Tensor.ringSheaf O)))
               (down_prodObjMk_sheafCompose_uliftFunctor J X x y)).trans
               (Sheaf.sectionsFunctor_map_ringMulHom (SheafOfModules.Tensor.ringSheaf O) X
                 x.down y.down))
           map_zero' := rfl
           map_one' := rfl }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Over each object, the identity of the lifted sections is a ring homomorphism from the lifted
operations to those transported along the universe lift. -/
noncomputable def pullbackCommRingSheafULiftInv (O : Sheaf J CommRingCat.{w}) :
    (AlgebraicGeometry.SheafOfModules.sheafULift.{w, u₁, v₁} J).obj O ⟶
      pullbackCommRingSheaf J (sheafCompose J uliftFunctor.{max u₁ v₁, w}) O :=
  ⟨{ app := fun X ↦
       letI := inverseImageSectionsCommRing J (sheafCompose J uliftFunctor.{max u₁ v₁, w})
         (SheafOfModules.Tensor.ringSheaf O) (commRingSheaf_mul_comm O) X
       CommRingCat.ofHom
         { toFun := id
           map_add' := fun x y ↦
             (((pullbackCommRingSheafULiftHom J O).hom.app X).hom.map_add x y).symm
           map_mul' := fun x y ↦
             (((pullbackCommRingSheafULiftHom J O).hom.app X).hom.map_mul x y).symm
           map_zero' := rfl
           map_one' := rfl }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- **Transporting commutative ring operations along the universe lift of sheaves of sets is
the universe lift of sheaves of commutative rings.** The comparison is the identity on
sections. -/
noncomputable def pullbackCommRingSheafULift (O : Sheaf J CommRingCat.{w}) :
    pullbackCommRingSheaf J (sheafCompose J uliftFunctor.{max u₁ v₁, w}) O ≅
      (AlgebraicGeometry.SheafOfModules.sheafULift.{w, u₁, v₁} J).obj O where
  hom := pullbackCommRingSheafULiftHom J O
  inv := pullbackCommRingSheafULiftInv J O
  hom_inv_id := rfl
  inv_hom_id := rfl

variable [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{max w u₁ v₁})]

/-- The comparison with the universe lift is natural in the sheaf of commutative rings. -/
lemma pullbackCommRingSheafULift_naturality {O O' : Sheaf J CommRingCat.{w}} (a : O ⟶ O') :
    pullbackCommRingSheafMap J (sheafCompose J uliftFunctor.{max u₁ v₁, w}) a ≫
        (pullbackCommRingSheafULift J O').hom =
      (pullbackCommRingSheafULift J O).hom ≫
        (AlgebraicGeometry.SheafOfModules.sheafULift.{w, u₁, v₁} J).map a := by
  refine (sheafCompose J (forget CommRingCat.{max w u₁ v₁})).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, underlyingRingSheaf_map_pullbackCommRingSheafMap]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun X ↦ ?_))
  rfl

/-- The comparison with the universe lift, as a natural isomorphism of functors. -/
noncomputable def pullbackCommRingSheafULiftIso :
    pullbackCommRingSheafFunctor J (sheafCompose J uliftFunctor.{max u₁ v₁, w}) ≅
      AlgebraicGeometry.SheafOfModules.sheafULift.{w, u₁, v₁} J :=
  NatIso.ofComponents (pullbackCommRingSheafULift J) (pullbackCommRingSheafULift_naturality J)

@[simp]
lemma pullbackCommRingSheafULiftIso_hom_app (O : Sheaf J CommRingCat.{w}) :
    (pullbackCommRingSheafULiftIso J).hom.app O = (pullbackCommRingSheafULift J O).hom :=
  rfl

end ULift

end Stacks.Sheaves.ToposPullback

end
