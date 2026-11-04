module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.EtaleNeighbourhoodConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfUnitComm

/-!
# Restriction to an étale `T`-scheme, and its compatibility with composition

For an étale `T`-scheme `W`, restriction of abelian sheaves to `W` through the slice of `T_étale`
over `W` (`Stacks.EtaleCohomology.etaleOverRestriction`) and the inverse image along `W ⟶ T` are
both left adjoint to the direct image along `W ⟶ T`; this gives
`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleOverRestriction`.

For a morphism `m : W' ⟶ W` of étale `T`-schemes, restricting to `W` and then to `W'` is
restricting to `W'` (`Stacks.EtaleCohomology.etaleOverRestrictionCompIso`, the comparison of left
adjoints attached to the composition isomorphism of direct images). Two facts make it usable:

* it is, on sections, restriction along the identification of the two étale `T`-schemes
  (`Stacks.EtaleCohomology.etaleOverRestrictionCompIso_hom_app`), proved by transposing along
  the composite adjunction;
* it matches the composition isomorphism of inverse images under the comparisons with inverse
  images
  (`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_hom_app_comp_isoEtaleOverRestriction`),
  since both are comparisons of left adjoints of the same direct images.

Together they let a morphism between restrictions of sheaves, given on the slice site, be moved
to a morphism between inverse images compatibly with further restriction.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleOverRestriction`.
* `Stacks.EtaleCohomology.etaleOverRestrictionCompIso`.
* `Stacks.EtaleCohomology.pullbackSliceHom`.

## Main results

* `Stacks.EtaleCohomology.etaleOverRestrictionCompIso_hom_app`.
* `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_hom_app_comp_isoEtaleOverRestriction`.
* `Stacks.EtaleCohomology.etaleOverRestrictionCompIso_conj`.
* `Stacks.EtaleCohomology.sliceToRestriction_overMapPullback`.
* `Stacks.EtaleCohomology.pullbackSliceHom_overMapPullback`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

variable {T : Scheme.{u}}

/-- Restriction of abelian sheaves to an étale `T`-scheme `W`, through the slice over `W`, is left
adjoint to the direct image along `W ⟶ T`. -/
def etaleOverRestrictionAbAdj (W : T.Etale) :
    etaleOverRestriction W Ab.{u + 1} ⊣ smallEtalePushforwardAb W.hom :=
  etaleOverRestrictionAdj W Ab.{u + 1}

/-- The unit of restriction to `W` is restriction along the counit of composition with
`W ⟶ T`. -/
theorem etaleOverRestrictionAbAdj_unit_app_hom_app (W : T.Etale)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (Z : T.Etale) :
    ((etaleOverRestrictionAbAdj W).unit.app F).hom.app (op Z) =
      F.obj.map ((etaleOverCompositionAdj W).counit.app Z).op := rfl

/-- The counit of composition with `W ⟶ T` is the first projection of the fibre product. -/
theorem etaleOverCompositionAdj_counit_app_left (W : T.Etale) (Z : T.Etale) :
    ((etaleOverCompositionAdj W).counit.app Z).left = pullback.fst Z.hom W.hom := rfl

/-- **The inverse image along an étale `W ⟶ T` is restriction to `W`**: the two left adjoints of
the direct image along `W ⟶ T`. -/
def smallEtalePullbackAbIsoEtaleOverRestriction (W : T.Etale) :
    smallEtalePullbackAb W.hom ≅ etaleOverRestriction W Ab.{u + 1} :=
  (smallEtaleAdjunctionAb W.hom).leftAdjointUniq (etaleOverRestrictionAbAdj W)

/-- A morphism between the restrictions of two sheaves to the slice over `W`, read on
`W_étale`. -/
def sliceToRestriction (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    (etaleOverRestriction W Ab.{u + 1}).obj A ⟶ (etaleOverRestriction W Ab.{u + 1}).obj K :=
  (etaleOverSheafEquivalence W Ab.{u + 1}).functor.map α

/-- `sliceToRestriction` is functorial. -/
theorem sliceToRestriction_comp (W : T.Etale) {A K L : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K)
    (β : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj L) :
    sliceToRestriction W (α ≫ β) = sliceToRestriction W α ≫ sliceToRestriction W β :=
  (etaleOverSheafEquivalence W Ab.{u + 1}).functor.map_comp α β

/-- `sliceToRestriction` sends the identity to the identity. -/
@[simp]
theorem sliceToRestriction_id (W : T.Etale) (A : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    sliceToRestriction W (𝟙 (((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A)) = 𝟙 _ :=
  (etaleOverSheafEquivalence W Ab.{u + 1}).functor.map_id _

/-- On a morphism coming from `T`, `sliceToRestriction` is the restriction of it to `W`. -/
theorem sliceToRestriction_map (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (u' : A ⟶ K) :
    sliceToRestriction W (((smallEtaleTopology T).overPullback Ab.{u + 1} W).map u') =
      (etaleOverRestriction W Ab.{u + 1}).map u' := rfl

/-- `sliceToRestriction` is additive. -/
theorem sliceToRestriction_add (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α β : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    sliceToRestriction W (α + β) = sliceToRestriction W α + sliceToRestriction W β := by
  apply Sheaf.hom_ext
  ext P : 2
  rfl

/-- **A morphism between restrictions to the slice over `W`, as a morphism between inverse
images along `W ⟶ T`**: read it on `W_étale` and conjugate by the comparison of restriction with
inverse image. -/
def pullbackSliceHom (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    (smallEtalePullbackAb W.hom).obj A ⟶ (smallEtalePullbackAb W.hom).obj K :=
  (smallEtalePullbackAbIsoEtaleOverRestriction W).hom.app A ≫ sliceToRestriction W α ≫
    (smallEtalePullbackAbIsoEtaleOverRestriction W).inv.app K

/-- `pullbackSliceHom` is additive. -/
theorem pullbackSliceHom_add (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α β : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    pullbackSliceHom W (α + β) = pullbackSliceHom W α + pullbackSliceHom W β := by
  simp only [pullbackSliceHom, sliceToRestriction_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- `pullbackSliceHom` is functorial. -/
theorem pullbackSliceHom_comp (W : T.Etale) {A K L : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K)
    (β : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj L) :
    pullbackSliceHom W (α ≫ β) = pullbackSliceHom W α ≫ pullbackSliceHom W β := by
  simp only [pullbackSliceHom, sliceToRestriction_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- On a morphism coming from `T`, `pullbackSliceHom` is the inverse image of it. -/
theorem pullbackSliceHom_map (W : T.Etale) {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (u' : A ⟶ K) :
    pullbackSliceHom W (((smallEtaleTopology T).overPullback Ab.{u + 1} W).map u') =
      (smallEtalePullbackAb W.hom).map u' := by
  rw [pullbackSliceHom, sliceToRestriction_map, ← Category.assoc]
  exact (Iso.comp_inv_eq ((smallEtalePullbackAbIsoEtaleOverRestriction W).app K)).2
    ((smallEtalePullbackAbIsoEtaleOverRestriction W).hom.naturality u').symm

/-- `pullbackSliceHom` sends the identity to the identity. -/
@[simp]
theorem pullbackSliceHom_id (W : T.Etale) (A : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    pullbackSliceHom W (𝟙 (((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A)) = 𝟙 _ := by
  simp [pullbackSliceHom]

section Comp

variable {W W' : T.Etale} (m : W' ⟶ W)

/-- **Restricting to `W` and then to `W'` is restricting to `W'`**, for a morphism `m : W' ⟶ W`
of étale `T`-schemes: the comparison of left adjoints attached to the composition isomorphism of
the direct images along `W' ⟶ W ⟶ T`. -/
def etaleOverRestrictionCompIso :
    etaleOverRestriction W Ab.{u + 1} ⋙ etaleOverRestriction (Scheme.Etale.mk m.left) Ab.{u + 1} ≅
      etaleOverRestriction W' Ab.{u + 1} :=
  Adjunction.leftAdjointCompIso (etaleOverRestrictionAbAdj W)
    (etaleOverRestrictionAbAdj (Scheme.Etale.mk m.left)) (etaleOverRestrictionAbAdj W')
    (smallEtalePushforwardAbCompIso' m.left W.hom W'.hom (MorphismProperty.Over.w m).symm)

/-- **The inverse image and restriction comparisons are compatible with composition.** -/
theorem smallEtalePullbackAbCompIso'_hom_app_comp_isoEtaleOverRestriction
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtalePullbackAbCompIso' m.left W.hom W'.hom (MorphismProperty.Over.w m).symm).hom.app F ≫
        (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app F =
      (smallEtalePullbackAb m.left).map
          ((smallEtalePullbackAbIsoEtaleOverRestriction W).hom.app F) ≫
        (smallEtalePullbackAbIsoEtaleOverRestriction (Scheme.Etale.mk m.left)).hom.app
          ((etaleOverRestriction W Ab.{u + 1}).obj F) ≫
          (etaleOverRestrictionCompIso m).hom.app F :=
  CategoryTheory.leftAdjointCompIso_hom_app_comp_leftAdjointUniq_hom_app _ _ _ _ _ _ _ F

/-- The étale `T`-scheme `W'` over `P'`, and the same scheme seen through `W' ⟶ W`: they have the
same underlying scheme and equal structure morphisms. -/
def etaleOverCompositionCompObjIso (P' : W'.left.Etale) :
    (etaleOverComposition W').obj P' ≅
      (etaleOverComposition W).obj ((etaleOverComposition (Scheme.Etale.mk m.left)).obj P') :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ ((P'.hom ≫ m.left) ≫ W.hom) = P'.hom ≫ W'.hom
    rw [Category.id_comp, Category.assoc, MorphismProperty.Over.w m])

/-- The underlying morphism of schemes of `etaleOverCompositionCompObjIso` is the identity. -/
@[simp]
theorem etaleOverCompositionCompObjIso_hom_left (P' : W'.left.Etale) :
    (etaleOverCompositionCompObjIso m P').hom.left = 𝟙 _ := rfl

/-- The underlying morphism of schemes of the inverse of `etaleOverCompositionCompObjIso` is the
identity. -/
@[simp]
theorem etaleOverCompositionCompObjIso_inv_left (P' : W'.left.Etale) :
    (etaleOverCompositionCompObjIso m P').inv.left = 𝟙 _ := rfl

/-- The comparison of the two ways to see an étale `W'`-scheme as an étale `T`-scheme, as a
natural transformation of functors `W'_étale ⥤ T_étale`. -/
def etaleOverCompositionCompNatTrans :
    etaleOverComposition W' ⟶
      etaleOverComposition (Scheme.Etale.mk m.left) ⋙ etaleOverComposition W where
  app P' := (etaleOverCompositionCompObjIso m P').hom
  naturality _ _ g := by
    apply MorphismProperty.Over.Hom.ext
    change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
    rw [Category.comp_id, Category.id_comp]

/-- The morphism from the restriction to `W` and then to `W'` to the restriction to `W'`, given on
sections by restriction along `etaleOverCompositionCompObjIso`. -/
def etaleOverRestrictionCompHom (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (etaleOverRestriction (Scheme.Etale.mk m.left) Ab.{u + 1}).obj
        ((etaleOverRestriction W Ab.{u + 1}).obj F) ⟶
      (etaleOverRestriction W' Ab.{u + 1}).obj F :=
  ⟨{ app := fun P' => F.obj.map (etaleOverCompositionCompObjIso m P'.unop).hom.op
     naturality := fun P Q g => by
       change F.obj.map ((etaleOverComposition W).map
             ((etaleOverComposition (Scheme.Etale.mk m.left)).map g.unop)).op ≫
           F.obj.map (etaleOverCompositionCompObjIso m Q.unop).hom.op =
         F.obj.map (etaleOverCompositionCompObjIso m P.unop).hom.op ≫
           F.obj.map ((etaleOverComposition W').map g.unop).op
       rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
       exact congrArg (fun x => F.obj.map x.op)
         ((etaleOverCompositionCompNatTrans m).naturality g.unop).symm }⟩

/-- On sections over `P'`, `etaleOverRestrictionCompHom` is restriction along
`etaleOverCompositionCompObjIso`. -/
theorem etaleOverRestrictionCompHom_hom_app (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (P' : W'.left.Etale) :
    (etaleOverRestrictionCompHom m F).hom.app (op P') =
      F.obj.map (etaleOverCompositionCompObjIso m P').hom.op := rfl

/-- **The composition isomorphism of restrictions, on sections**: restriction along the
identification of the two étale `T`-schemes. -/
theorem etaleOverRestrictionCompIso_hom_app (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (etaleOverRestrictionCompIso m).hom.app F = etaleOverRestrictionCompHom m F := by
  have hP : (etaleOverRestrictionAbAdj W').unit.app F ≫
      (smallEtalePushforwardAbCompIso' m.left W.hom W'.hom
        (MorphismProperty.Over.w m).symm).inv.app ((etaleOverRestriction W' Ab.{u + 1}).obj F) =
      ((etaleOverRestrictionAbAdj W).comp
        (etaleOverRestrictionAbAdj (Scheme.Etale.mk m.left))).unit.app F ≫
        (smallEtalePushforwardAb m.left ⋙ smallEtalePushforwardAb W.hom).map
          ((etaleOverRestrictionCompIso m).hom.app F) :=
    unit_conjugateEquiv_symm (etaleOverRestrictionAbAdj W') ((etaleOverRestrictionAbAdj W).comp
      (etaleOverRestrictionAbAdj (Scheme.Etale.mk m.left))) _ F
  apply (((etaleOverRestrictionAbAdj W).comp
    (etaleOverRestrictionAbAdj (Scheme.Etale.mk m.left))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine hP.symm.trans ?_
  apply Sheaf.hom_ext
  ext Z : 2
  have hfst :=
    smallEtaleBaseChangeComp'_fst_fst m.left W.hom W'.hom (MorphismProperty.Over.w m).symm Z.unop
  have hinv : ((smallEtaleBaseChangeComp' m.left W.hom W'.hom
      (MorphismProperty.Over.w m).symm).inv.app Z.unop).left ≫
        ((smallEtaleBaseChangeComp' m.left W.hom W'.hom
          (MorphismProperty.Over.w m).symm).hom.app Z.unop).left = 𝟙 _ :=
    congrArg (fun x => x.left) (Iso.inv_hom_id_app (smallEtaleBaseChangeComp' m.left W.hom W'.hom
      (MorphismProperty.Over.w m).symm) Z.unop)
  have h : (etaleOverComposition W').map ((smallEtaleBaseChangeComp' m.left W.hom W'.hom
        (MorphismProperty.Over.w m).symm).inv.app Z.unop) ≫
        (etaleOverCompositionAdj W').counit.app Z.unop =
      (etaleOverCompositionCompObjIso m ((smallEtaleBaseChange m.left).obj
          ((smallEtaleBaseChange W.hom).obj Z.unop))).hom ≫
        (etaleOverComposition W).map ((etaleOverCompositionAdj
          (Scheme.Etale.mk m.left)).counit.app ((smallEtaleBaseChange W.hom).obj Z.unop)) ≫
        (etaleOverCompositionAdj W).counit.app Z.unop := by
    apply MorphismProperty.Over.Hom.ext
    show ((smallEtaleBaseChangeComp' m.left W.hom W'.hom
        (MorphismProperty.Over.w m).symm).inv.app Z.unop).left ≫ pullback.fst Z.unop.hom W'.hom =
      𝟙 _ ≫ pullback.fst ((smallEtaleBaseChange W.hom).obj Z.unop).hom m.left ≫
        pullback.fst Z.unop.hom W.hom
    rw [Category.id_comp, ← hfst, ← Category.assoc, hinv, Category.id_comp]
    rfl
  have h2 := congrArg (fun x => F.obj.map x.op) h
  simp only [op_comp, Functor.map_comp] at h2
  show F.obj.map ((etaleOverCompositionAdj W').counit.app Z.unop).op ≫
      F.obj.map ((etaleOverComposition W').map
        ((smallEtaleBaseChangeComp' m.left W.hom W'.hom
          (MorphismProperty.Over.w m).symm).inv.app Z.unop)).op =
    (F.obj.map ((etaleOverCompositionAdj W).counit.app Z.unop).op ≫
      F.obj.map ((etaleOverComposition W).map ((etaleOverCompositionAdj
        (Scheme.Etale.mk m.left)).counit.app ((smallEtaleBaseChange W.hom).obj Z.unop))).op) ≫
      F.obj.map (etaleOverCompositionCompObjIso m ((smallEtaleBaseChange m.left).obj
        ((smallEtaleBaseChange W.hom).obj Z.unop))).hom.op
  rw [Category.assoc]
  exact h2

/-- **Conjugation by the inverse image comparison is compatible with restriction.** A morphism
`φ` between inverse images along `W ⟶ T`, read as a morphism between restrictions to `W` and
restricted to `W'`, is the morphism between restrictions to `W'` read off from the inverse image
of `φ` along `W' ⟶ W`. -/
theorem etaleOverRestrictionCompIso_conj {X Y : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb W.hom).obj X ⟶ (smallEtalePullbackAb W.hom).obj Y) :
    (etaleOverRestrictionCompIso m).inv.app X ≫
        (etaleOverRestriction (Scheme.Etale.mk m.left) Ab.{u + 1}).map
          ((smallEtalePullbackAbIsoEtaleOverRestriction W).inv.app X ≫ φ ≫
            (smallEtalePullbackAbIsoEtaleOverRestriction W).hom.app Y) ≫
        (etaleOverRestrictionCompIso m).hom.app Y =
      (smallEtalePullbackAbIsoEtaleOverRestriction W').inv.app X ≫
        ((smallEtalePullbackAbCompIso' m.left W.hom W'.hom
            (MorphismProperty.Over.w m).symm).inv.app X ≫
          (smallEtalePullbackAb m.left).map φ ≫
          (smallEtalePullbackAbCompIso' m.left W.hom W'.hom
            (MorphismProperty.Over.w m).symm).hom.app Y) ≫
        (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app Y := by
  have h1 := smallEtalePullbackAbCompIso'_hom_app_comp_isoEtaleOverRestriction m X
  have h2 := smallEtalePullbackAbCompIso'_hom_app_comp_isoEtaleOverRestriction m Y
  apply (cancel_epi ((smallEtalePullbackAbCompIso' m.left W.hom W'.hom
      (MorphismProperty.Over.w m).symm).hom.app X ≫
    (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app X)).1
  have h3 := (smallEtalePullbackAbIsoEtaleOverRestriction (Scheme.Etale.mk m.left)).hom.naturality
    ((smallEtalePullbackAbIsoEtaleOverRestriction W).inv.app X ≫ φ ≫
      (smallEtalePullbackAbIsoEtaleOverRestriction W).hom.app Y)
  have hR : ((smallEtalePullbackAbCompIso' m.left W.hom W'.hom
        (MorphismProperty.Over.w m).symm).hom.app X ≫
      (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app X) ≫
      (smallEtalePullbackAbIsoEtaleOverRestriction W').inv.app X ≫
        ((smallEtalePullbackAbCompIso' m.left W.hom W'.hom
            (MorphismProperty.Over.w m).symm).inv.app X ≫
          (smallEtalePullbackAb m.left).map φ ≫
          (smallEtalePullbackAbCompIso' m.left W.hom W'.hom
            (MorphismProperty.Over.w m).symm).hom.app Y) ≫
        (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app Y =
      (smallEtalePullbackAb m.left).map φ ≫
        ((smallEtalePullbackAbCompIso' m.left W.hom W'.hom
            (MorphismProperty.Over.w m).symm).hom.app Y ≫
          (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app Y) := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  refine (congrArg (· ≫ _) h1).trans (Eq.trans ?_ hR.symm)
  rw [h2]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Iso.hom_inv_id_app_assoc _ _ _)))).trans ?_)
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h3.symm).trans (Category.assoc _ _ _)))).trans ?_
  refine ((smallEtalePullbackAb m.left).map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun x => (smallEtalePullbackAb m.left).map x ≫ _)
    (Iso.hom_inv_id_app_assoc _ _ _)).trans ?_
  exact (smallEtalePullbackAb m.left).map_comp_assoc _ _ _

/-- A morphism of étale `T`-schemes over `W`, from `W'` seen through `m` to `W'` seen through
`W' ⟶ W ⟶ T`. -/
def etaleOverCompositionCompOverHom (P' : W'.left.Etale) :
    (Over.map m).obj ((etaleOverEquivalence W').inverse.obj P') ⟶
      (etaleOverEquivalence W).inverse.obj
        ((etaleOverComposition (Scheme.Etale.mk m.left)).obj P') :=
  Over.homMk (etaleOverCompositionCompObjIso m P').hom (by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 _ ≫ (P'.hom ≫ m.left) = P'.hom ≫ m.left
    rw [Category.id_comp])

/-- **Restricting a morphism given on the slice over `W` to the slice over `W'`** is, read on
`W'_étale`, its restriction along `W' ⟶ W` through the composition isomorphism. -/
theorem etaleOverRestrictionCompIso_hom_app_comp_map_overMapPullback
    {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    (etaleOverRestrictionCompIso m).hom.app A ≫
        sliceToRestriction W'
          (((smallEtaleTopology T).overMapPullback Ab.{u + 1} m).map α :
            ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj A ⟶
              ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj K) =
      (etaleOverRestriction (Scheme.Etale.mk m.left) Ab.{u + 1}).map (sliceToRestriction W α) ≫
        (etaleOverRestrictionCompIso m).hom.app K := by
  rw [etaleOverRestrictionCompIso_hom_app, etaleOverRestrictionCompIso_hom_app]
  apply Sheaf.hom_ext
  ext P' : 2
  show A.obj.map (etaleOverCompositionCompObjIso m P'.unop).hom.op ≫
      α.hom.app (op ((Over.map m).obj ((etaleOverEquivalence W').inverse.obj P'.unop))) =
    α.hom.app (op ((etaleOverEquivalence W).inverse.obj
        ((etaleOverComposition (Scheme.Etale.mk m.left)).obj P'.unop))) ≫
      K.obj.map (etaleOverCompositionCompObjIso m P'.unop).hom.op
  exact α.hom.naturality (etaleOverCompositionCompOverHom m P'.unop).op

/-- **Restricting a slice morphism from the slice over `W` to the slice over `W'`**, read on
`W'_étale`, through the composition isomorphism of restrictions. -/
theorem sliceToRestriction_overMapPullback {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    sliceToRestriction W' (((smallEtaleTopology T).overMapPullback Ab.{u + 1} m).map α :
        ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj A ⟶
          ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj K) =
      (etaleOverRestrictionCompIso m).inv.app A ≫
        (etaleOverRestriction (Scheme.Etale.mk m.left) Ab.{u + 1}).map (sliceToRestriction W α) ≫
          (etaleOverRestrictionCompIso m).hom.app K :=
  (Iso.inv_hom_id_app_assoc (etaleOverRestrictionCompIso m) A _).symm.trans
    (congrArg ((etaleOverRestrictionCompIso m).inv.app A ≫ ·)
      (etaleOverRestrictionCompIso_hom_app_comp_map_overMapPullback m α))

/-- **Moving a slice morphism to inverse images is compatible with restriction**: for
`m : W' ⟶ W`, the inverse image comparison of the restriction of `α` to the slice over `W'` is
the inverse image along `W' ⟶ W` of the comparison of `α`, read through the composition
isomorphism of inverse images. -/
theorem pullbackSliceHom_overMapPullback {A K : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    (α : ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj A ⟶
      ((smallEtaleTopology T).overPullback Ab.{u + 1} W).obj K) :
    pullbackSliceHom W' (((smallEtaleTopology T).overMapPullback Ab.{u + 1} m).map α :
        ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj A ⟶
          ((smallEtaleTopology T).overPullback Ab.{u + 1} W').obj K) =
      (smallEtalePullbackAbCompIso' m.left W.hom W'.hom
          (MorphismProperty.Over.w m).symm).inv.app A ≫
        (smallEtalePullbackAb m.left).map (pullbackSliceHom W α) ≫
        (smallEtalePullbackAbCompIso' m.left W.hom W'.hom
          (MorphismProperty.Over.w m).symm).hom.app K := by
  have hE := sliceToRestriction_overMapPullback m α
  have hinner : (smallEtalePullbackAbIsoEtaleOverRestriction W).inv.app A ≫
      pullbackSliceHom W α ≫ (smallEtalePullbackAbIsoEtaleOverRestriction W).hom.app K =
      sliceToRestriction W α := by
    simp [pullbackSliceHom]
  have hc := etaleOverRestrictionCompIso_conj m (pullbackSliceHom W α)
  rw [hinner] at hc
  refine (congrArg (fun x => (smallEtalePullbackAbIsoEtaleOverRestriction W').hom.app A ≫ x ≫
    (smallEtalePullbackAbIsoEtaleOverRestriction W').inv.app K) (hE.trans hc)).trans ?_
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact congrArg (_ ≫ _ ≫ ·) (Category.comp_id _)

end Comp

end Stacks.EtaleCohomology

end
