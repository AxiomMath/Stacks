module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleCharacterTwistTorsor
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.PresheafTensorFunctor

/-!
# `Ext` out of a character twist, in every degree

Let `W` be a torsor under a group `G` over the final object of a site `(C, J)`, in the sense of
`CategoryTheory.IsTorsorObject`, and let `χ : G → ℤˣ` be a character. The units of `ℤ` are
`{+1, -1}`, so `χ² = 1`: the character squares to the trivial character. Consequently the twisting
functor `- ⊗_ℤ ℤ(χ)` on abelian sheaves is its own inverse, hence an equivalence — exact,
injective-preserving and adjoint to itself — and the twist of the constant sheaf `ℤ` is `ℤ(χ)`.
Stacks 015Z for `Ext` at that self-adjunction then gives

`Ext^q(ℤ(χ), ℱ) ≅ H^q(ℱ ⊗_ℤ ℤ(χ))` for every `q`, naturally in `ℱ`,

the derived form of Stacks 0727, whose degree-zero case is
`CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv`.

All names are in the namespace `CategoryTheory`.

## Main definitions

* `trivialTwistAugmentation`: the augmentation `ℤ(1) ⟶ ℤ` of the twist by the trivial character.
* `twistSquareCompare`: the comparison `ℱ ⊗_ℤ ℤ(1) ⟶ (ℱ ⊗_ℤ ℤ(χ)) ⊗_ℤ ℤ(χ)`, taking `t ⊗ [φ]` to
  `(t ⊗ [φ]) ⊗ [φ]`.
* `characterTwistFunctor`: the twisting functor `ℱ ↦ ℱ ⊗_ℤ ℤ(χ)` on abelian sheaves.
* `characterTwistFunctorObjConstant`: the twist of the constant sheaf `ℤ` is `ℤ(χ)`.

## Main results

* `IsTorsorObject.W_trivialTwistAugmentation` and `IsTorsorObject.W_twistSquareCompare`:
  sheafification inverts both comparisons.
* `IsTorsorObject.characterTwistFunctorCompSelfIso`: the twisting functor is its own inverse, and
  `IsTorsorObject.characterTwistEquivalence`, `IsTorsorObject.isEquivalence_characterTwistFunctor`
  and `IsTorsorObject.characterTwistSelfAdjunction` are the equivalence and the self-adjunction it
  yields.
* `IsTorsorObject.extFunctorObjCharacterTwistIso`: `Ext` out of `ℤ(χ)` is the cohomology of the
  twisted coefficients, as an isomorphism of functors of the coefficients, and
  `IsTorsorObject.characterTwistExtAddEquiv` is its component at a sheaf,
  `Ext^q(ℤ(χ), ℱ) ≃+ H^q(ℱ ⊗_ℤ ℤ(χ))`.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe w u₁ u

namespace CategoryTheory

/-! ### Morphisms out of a tensor product with a twist -/

section Construction

variable {C : Type u₁} [Category.{u + 1} C] {G : Type w} [Group G] (W : C) (act : G →* Aut W)
  (χ : G →* ℤˣ)

/-- **A morphism out of the objectwise tensor product of a presheaf with a twist presheaf is
determined by its values on the pure tensors with the classes of the morphisms into `W`.** -/
lemma twistTensor_hom_ext {F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {A : AddCommGrpCat.{u + 1}}
    {V : Cᵒᵖ} {a b : (AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ)).obj V ⟶ A}
    (hab : ∀ (t : F.obj V) (φ : V.unop ⟶ W),
      a (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ)) =
        b (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ))) :
    a = b := by
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add z z' hz hz' =>
      exact (map_add _ z z').trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)
  | tmul t x =>
      exact DFunLike.congr_fun (characterRelations_hom_ext W act χ
        (a.hom.comp (AddCommGrpCat.tmulLeftHom (L := characterTwistPresheaf W act χ) t))
        (b.hom.comp (AddCommGrpCat.tmulLeftHom (L := characterTwistPresheaf W act χ) t))
        fun φ => hab t φ) x

/-- **A morphism of presheaves out of the objectwise tensor product of a presheaf with a twist
presheaf is determined by its values on the pure tensors with the classes of the morphisms into
`W`.** -/
lemma twistTensor_natTrans_ext {F H : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {a b : AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ) ⟶ H}
    (hab : ∀ (V : Cᵒᵖ) (t : F.obj V) (φ : V.unop ⟶ W),
      a.app V (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ)) =
        b.app V (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ))) : a = b :=
  NatTrans.ext (funext fun V => twistTensor_hom_ext W act χ (hab V))

/-! ### The augmentation of the twist by the trivial character -/

/-- The augmentation of the twist by the trivial character: the morphism to the constant presheaf
`ℤ` taking the class of every morphism into `W` to `1`. -/
def trivialTwistAugmentation :
    characterTwistPresheaf W act (1 : G →* ℤˣ) ⟶ AddCommGrpCat.constInt.{u + 1, u₁, u} C where
  app V := AddCommGrpCat.ofHom
    (QuotientAddGroup.lift _
      (FreeAbelianGroup.lift (fun _ : V.unop ⟶ W => ULift.up.{u + 1} (1 : ℤ))) (by
        rw [characterRelations, AddSubgroup.closure_le]
        rintro x ⟨g, φ, rfl⟩
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift_apply_of,
          MonoidHom.one_apply, Units.val_one, one_smul, sub_self]))
  naturality := by
    intro V V' m
    apply AddCommGrpCat.hom_ext
    refine characterRelations_hom_ext W act (1 : G →* ℤˣ) _ _ fun φ => ?_
    rfl

/-- The augmentation of the trivial twist takes the class of every morphism into `W` to `1`. -/
@[simp]
lemma trivialTwistAugmentation_twistedGenerator {V : C} (φ : V ⟶ W) :
    (trivialTwistAugmentation.{w, u₁, u} W act).app (op V)
        (twistedGenerator W act (1 : G →* ℤˣ) φ) = ULift.up.{u + 1} (1 : ℤ) :=
  rfl

/-! ### The twist of the twist -/

/-- The doubly twisted objectwise tensor product `(F ⊗_ℤ ℤ(χ)) ⊗_ℤ ℤ(χ)`, before
sheafification. -/
abbrev twistSquarePresheaf (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.presheafTensor
    (AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ))
    (characterTwistPresheaf W act χ)

variable (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The restriction map of a twist presheaf on the class of a morphism into `W`, read on a
morphism of the opposite category. -/
lemma characterTwistPresheaf_map_twistedGenerator' {V V' : Cᵒᵖ} (m : V ⟶ V')
    (φ : V.unop ⟶ W) :
    ((characterTwistPresheaf W act χ).map m) (twistedGenerator W act χ φ) =
      twistedGenerator W act χ (m.unop ≫ φ) :=
  rfl

/-- The additive map to the doubly twisted tensor product attached to a morphism `φ : V ⟶ W`:
the section `t` goes to `(t ⊗ [φ]) ⊗ [φ]`. -/
def twistSquareGen {V : Cᵒᵖ} (φ : V.unop ⟶ W) :
    F.obj V →+ (twistSquarePresheaf W act χ F).obj V where
  toFun t := AddCommGrpCat.tensorGen
    (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ)) (twistedGenerator W act χ φ)
  map_zero' := by
    rw [AddCommGrpCat.tensorGen_zero_left, AddCommGrpCat.tensorGen_zero_left]
  map_add' t t' := by
    rw [AddCommGrpCat.tensorGen_add_left, AddCommGrpCat.tensorGen_add_left]

/-- The map attached to `φ` sends `t` to `(t ⊗ [φ]) ⊗ [φ]`. -/
@[simp]
lemma twistSquareGen_apply {V : Cᵒᵖ} (φ : V.unop ⟶ W) (t : F.obj V) :
    twistSquareGen W act χ F φ t = AddCommGrpCat.tensorGen
      (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ)) (twistedGenerator W act χ φ) :=
  rfl

/-- **Translating a morphism into `W` by a group element does not change the attached map to the
doubly twisted tensor product.** -/
lemma twistSquareGen_act {V : Cᵒᵖ} (φ : V.unop ⟶ W) (g : G) :
    twistSquareGen W act χ F (φ ≫ (act g).hom) = twistSquareGen W act χ F φ := by
  have hone : ((χ g : ℤ) * (χ g : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  refine AddMonoidHom.ext fun t => ?_
  rw [twistSquareGen_apply, twistSquareGen_apply, twistedGenerator_act,
    AddCommGrpCat.tensorGen_smul_right (χ g : ℤ) t (twistedGenerator W act χ φ),
    AddCommGrpCat.tensorGen_smul_smul, hone, one_smul]

/-- The map from the twist by the trivial character to the additive maps from `F` to the doubly
twisted tensor product: the class of `φ` goes to `t ↦ (t ⊗ [φ]) ⊗ [φ]`. -/
def twistSquareOuter (V : Cᵒᵖ) :
    (characterTwistPresheaf W act (1 : G →* ℤˣ)).obj V →+
      (F.obj V →+ (twistSquarePresheaf W act χ F).obj V) :=
  QuotientAddGroup.lift (characterRelations W act (1 : G →* ℤˣ) V.unop)
    (FreeAbelianGroup.lift fun φ : V.unop ⟶ W => twistSquareGen W act χ F φ) (by
      rw [characterRelations, AddSubgroup.closure_le]
      rintro x ⟨g, φ, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one,
        one_smul, sub_eq_zero]
      rw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, twistSquareGen_act])

/-- The class of `φ` in the trivial twist goes to the map attached to `φ`. -/
@[simp]
lemma twistSquareOuter_twistedGenerator (V : Cᵒᵖ) (φ : V.unop ⟶ W) :
    twistSquareOuter W act χ F V (twistedGenerator W act (1 : G →* ℤˣ) φ) =
      twistSquareGen W act χ F φ :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The bilinear map underlying the comparison is balanced over `ℤ`. -/
lemma twistSquareOuter_balanced (V : Cᵒᵖ) (r : ℤ) (t : F.obj V)
    (x : (characterTwistPresheaf W act (1 : G →* ℤˣ)).obj V) :
    (twistSquareOuter W act χ F V).flip (r • t) x =
      (twistSquareOuter W act χ F V).flip t (r • x) := by
  have h1 : twistSquareOuter W act χ F V x (r • t) = r • twistSquareOuter W act χ F V x t :=
    map_zsmul _ _ _
  have h2 : twistSquareOuter W act χ F V (r • x) = r • twistSquareOuter W act χ F V x :=
    map_zsmul _ _ _
  rw [AddMonoidHom.flip_apply, AddMonoidHom.flip_apply, h1, h2]
  rfl

/-- **The comparison of the tensor product with the trivial twist with the doubly twisted tensor
product**: `t ⊗ [φ]₁ ↦ (t ⊗ [φ]) ⊗ [φ]`. -/
def twistSquareCompare :
    AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act (1 : G →* ℤˣ)) ⟶
      twistSquarePresheaf W act χ F where
  app V := AddCommGrpCat.ofHom
    { toFun := fun z => TensorProduct.liftAddHom (twistSquareOuter W act χ F V).flip
        (twistSquareOuter_balanced W act χ F V) z
      map_zero' := map_zero _
      map_add' := fun z z' => map_add _ z z' }
  naturality := by
    intro V V' m
    refine twistTensor_hom_ext W act (1 : G →* ℤˣ) fun t φ => ?_
    change (twistSquareOuter W act χ F V').flip (F.map m t)
        ((characterTwistPresheaf W act (1 : G →* ℤˣ)).map m
          (twistedGenerator W act (1 : G →* ℤˣ) φ)) =
      (twistSquarePresheaf W act χ F).map m ((twistSquareOuter W act χ F V).flip t
        (twistedGenerator W act (1 : G →* ℤˣ) φ))
    rw [characterTwistPresheaf_map_twistedGenerator', AddMonoidHom.flip_apply,
      AddMonoidHom.flip_apply, twistSquareOuter_twistedGenerator,
      twistSquareOuter_twistedGenerator, twistSquareGen_apply, twistSquareGen_apply,
      AddCommGrpCat.presheafTensor_map_tensorGen, AddCommGrpCat.presheafTensor_map_tensorGen,
      characterTwistPresheaf_map_twistedGenerator']

/-- The comparison sends `t ⊗ [φ]₁` to `(t ⊗ [φ]) ⊗ [φ]`. -/
@[simp]
lemma twistSquareCompare_app_gen {V : Cᵒᵖ} (t : F.obj V) (φ : V.unop ⟶ W) :
    (twistSquareCompare W act χ F).app V
        (AddCommGrpCat.tensorGen t (twistedGenerator W act (1 : G →* ℤˣ) φ)) =
      AddCommGrpCat.tensorGen
        (AddCommGrpCat.tensorGen t (twistedGenerator W act χ φ)) (twistedGenerator W act χ φ) := by
  show (twistSquareOuter W act χ F V).flip t (twistedGenerator W act (1 : G →* ℤˣ) φ) = _
  rw [AddMonoidHom.flip_apply, twistSquareOuter_twistedGenerator, twistSquareGen_apply]

/-- **The comparison with the doubly twisted tensor product**, as a natural transformation
between the tensoring functors. -/
def twistSquareCompareNat :
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act (1 : G →* ℤˣ)) ⟶
      AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
        AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) where
  app F := twistSquareCompare W act χ F
  naturality F F' k := by
    change AddCommGrpCat.presheafTensorMap k (𝟙 (characterTwistPresheaf W act (1 : G →* ℤˣ))) ≫
        twistSquareCompare W act χ F' =
      twistSquareCompare W act χ F ≫
        AddCommGrpCat.presheafTensorMap
          (AddCommGrpCat.presheafTensorMap k (𝟙 (characterTwistPresheaf W act χ)))
          (𝟙 (characterTwistPresheaf W act χ))
    refine twistTensor_natTrans_ext W act (1 : G →* ℤˣ) fun V t φ => ?_
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply,
      AddCommGrpCat.presheafTensorMap_id_right_tensorGen, twistSquareCompare_app_gen]

/-- A morphism of presheaves of abelian groups kills the restriction of a difference of two
sections with the same image. -/
private theorem app_map_sub_eq_zero {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (a : P ⟶ Q) {V V' : Cᵒᵖ}
    (m : V ⟶ V') {x y : P.obj V} (hxy : a.app V x = a.app V y) :
    a.app V' (P.map m (x - y)) = 0 := by
  rw [NatTrans.naturality_apply, map_sub, hxy, sub_self, map_zero]

/-- The restrictions of two sections agree when the restriction of their difference vanishes. -/
private theorem map_eq_of_map_sub_eq_zero {P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {V V' : Cᵒᵖ}
    (m : V ⟶ V') {x y : P.obj V} (h : P.map m (x - y) = 0) : P.map m x = P.map m y :=
  sub_eq_zero.mp ((map_sub _ x y).symm.trans h)

end Construction

/-! ### The twisting functor -/

section TwistFunctor

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}] {G : Type w}
  [Group G] (W : C) (act : G →* Aut W) (χ : G →* ℤˣ) (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]

/-- **The twisting functor `F ↦ F ⊗_ℤ ℤ(χ)`** on abelian sheaves: the sheafification of the
objectwise tensor product with the twist presheaf. -/
abbrev characterTwistFunctor :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
      presheafToSheaf J AddCommGrpCat.{u + 1}

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- The twisting functor sends `F` to the twisted tensor product `F ⊗_ℤ ℤ(χ)`. -/
lemma characterTwistFunctor_obj (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (characterTwistFunctor W act χ J).obj F = characterTwistTensor F.obj act χ J := rfl

/-- The functor sending an abelian sheaf to the objectwise tensor product of its sections with
the twist by the trivial character. -/
abbrev trivialTwistTensorFunctor :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act (1 : G →* ℤˣ))

/-- The functor sending an abelian sheaf to the doubly twisted objectwise tensor product of its
sections. -/
abbrev twistSquareTensorFunctor :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) ⋙
      AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ)

/-- **The trivially twisted tensor product is the sections themselves**, naturally in the sheaf:
the augmentation of the trivial twist, tensored with the sections and followed by the unit
isomorphism. -/
def trivialTwistTensorUnit :
    trivialTwistTensorFunctor W act J ⟶ sheafToPresheaf J AddCommGrpCat.{u + 1} :=
  Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{u + 1})
    (AddCommGrpCat.presheafTensorRightMap (trivialTwistAugmentation.{w, u₁, u} W act) ≫
      (AddCommGrpCat.presheafTensorRightConstIso (C := C)).hom)

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}] in
/-- The component at `F` of the identification of the trivially twisted tensor product is the
augmentation tensored with the identity of `F`, followed by the unit isomorphism. -/
lemma trivialTwistTensorUnit_app (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (trivialTwistTensorUnit W act J).app F =
      AddCommGrpCat.presheafTensorMap (𝟙 F.obj)
          (trivialTwistAugmentation.{w, u₁, u} W act) ≫
        (AddCommGrpCat.presheafTensorConstRightIso F.obj).hom :=
  rfl

/-- **The comparison with the doubly twisted tensor product**, naturally in the sheaf. -/
def twistSquareTensorCompare :
    trivialTwistTensorFunctor W act J ⟶ twistSquareTensorFunctor W act χ J :=
  Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{u + 1}) (twistSquareCompareNat W act χ)

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}] in
/-- The component at `F` of the comparison with the doubly twisted tensor product is the
comparison for the sections of `F`. -/
lemma twistSquareTensorCompare_app (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (twistSquareTensorCompare W act χ J).app F = twistSquareCompare W act χ F.obj := rfl

/-- **Sheafifying the inner tensor factor**, naturally in the sheaf: the natural transformation
whose component at `F` is the objectwise tensor product of the sheafification map of
`F ⊗_ℤ ℤ(χ)` with the identity of `ℤ(χ)`. -/
def twistSquareTensorSheafify :
    twistSquareTensorFunctor W act χ J ⟶
      characterTwistFunctor W act χ J ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
        AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ) :=
  Functor.whiskerLeft
    (sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
      AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ))
    (Functor.whiskerRight (sheafificationAdjunction J AddCommGrpCat.{u + 1}).unit
      (AddCommGrpCat.presheafTensorRight (characterTwistPresheaf W act χ)))

omit [UnivLE.{max u₁ (u + 1), u + 1}] in
/-- The component at `F` of the sheafification of the inner tensor factor is the tensor product of
the sheafification map with the identity of the twist presheaf. -/
lemma twistSquareTensorSheafify_app (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (twistSquareTensorSheafify W act χ J).app F =
      AddCommGrpCat.presheafTensorMap
        (toSheafify J (AddCommGrpCat.presheafTensor F.obj (characterTwistPresheaf W act χ)))
        (𝟙 (characterTwistPresheaf W act χ)) :=
  rfl

/-- **The twist of the constant sheaf `ℤ` is `ℤ(χ)`.** -/
def characterTwistFunctorObjConstant :
    (characterTwistFunctor W act χ J).obj
        ((constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
      characterTwist W act χ J := by
  haveI : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.presheafTensorMap
        (toSheafify J (AddCommGrpCat.constInt.{u + 1, u₁, u} C))
        (𝟙 (characterTwistPresheaf W act χ)))) :=
    (J.W_iff _).mp (AddCommGrpCat.W_presheafTensorMap J (J.W_toSheafify _) (J.W.id_mem _))
  exact (asIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (AddCommGrpCat.presheafTensorMap
        (toSheafify J (AddCommGrpCat.constInt.{u + 1, u₁, u} C))
        (𝟙 (characterTwistPresheaf W act χ))))).symm ≪≫
    (presheafToSheaf J AddCommGrpCat.{u + 1}).mapIso
      (AddCommGrpCat.presheafTensorConstLeftIso (characterTwistPresheaf W act χ))

end TwistFunctor

/-! ### Both comparisons are local isomorphisms over a torsor -/

section Torsor

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
  {W : C} {G : Type w} [Group G] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

namespace IsTorsorObject

variable (h : IsTorsorObject act J)

include h

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- A sieve containing every arrow whose source admits a morphism to the torsor is covering. -/
theorem mem_of_hom_to_torsor {V : C} (P : Sieve V)
    (hP : ∀ ⦃V' : C⦄ (f : V' ⟶ V), (V' ⟶ W) → P f) : P ∈ J V :=
  J.superset_covering (fun _ f hf => hP f (Classical.choice hf)) (h.splittingSieve_mem V)

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- A sieve which, locally on every object admitting a morphism to the torsor, contains a
covering sieve, is covering. -/
theorem mem_of_splitting {V : C} (P : Sieve V)
    (hP : ∀ ⦃V' : C⦄ (f : V' ⟶ V), (V' ⟶ W) → ∃ S : Sieve V', S ∈ J V' ∧
      ∀ ⦃V'' : C⦄ (g : V'' ⟶ V'), S g → P (g ≫ f)) : P ∈ J V := by
  refine J.transitive (h.splittingSieve_mem V) P ?_
  intro V' f hf
  obtain ⟨S, hS, hSP⟩ := hP f (Classical.choice hf)
  exact J.superset_covering (fun _ g hg => hSP g hg) hS

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- A sieve which, locally on every object admitting a morphism to the torsor, contains a
covering sieve of arrows along which it becomes covering, is covering. -/
theorem mem_of_splitting' {V : C} (P : Sieve V)
    (hP : ∀ ⦃V' : C⦄ (f : V' ⟶ V), (V' ⟶ W) → ∃ S : Sieve V', S ∈ J V' ∧
      ∀ ⦃V'' : C⦄ (g : V'' ⟶ V'), S g → P.pullback (g ≫ f) ∈ J V'') : P ∈ J V := by
  refine J.transitive (h.splittingSieve_mem V) P ?_
  intro V' f hf
  obtain ⟨S, hS, hSP⟩ := hP f (Classical.choice hf)
  refine J.transitive hS _ ?_
  intro V'' g hg
  simpa only [Sieve.pullback_comp] using hSP g hg

/-! #### The augmentation of the trivial twist -/

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The augmentation of the trivial twist is locally surjective.** -/
theorem isLocallySurjective_trivialTwistAugmentation :
    Presheaf.IsLocallySurjective J (trivialTwistAugmentation.{w, u₁, u} W act) := by
  constructor
  intro V y
  refine h.mem_of_hom_to_torsor _ fun {V'} f q => ⟨y.down • twistedGenerator W act 1 q, ?_⟩
  rw [map_zsmul, trivialTwistAugmentation_twistedGenerator]
  exact ULift.ext _ _ (by simp)

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The augmentation of the trivial twist is locally injective.** -/
theorem isLocallyInjective_trivialTwistAugmentation :
    Presheaf.IsLocallyInjective J (trivialTwistAugmentation.{w, u₁, u} W act) := by
  constructor
  intro V x y hxy
  refine h.mem_of_splitting _ fun {V'} f q => ?_
  obtain ⟨S, hS, hfam⟩ := h.exists_sieve_twistedGenerator_zsmul (1 : G →* ℤˣ) q
    ((characterTwistPresheaf W act (1 : G →* ℤˣ)).map f.op (x - y))
  refine ⟨S, hS, fun {V''} g hg => ?_⟩
  obtain ⟨n, hn⟩ := hfam g hg
  have hcomp : (characterTwistPresheaf W act (1 : G →* ℤˣ)).map (g ≫ f).op (x - y) =
      n • twistedGenerator W act (1 : G →* ℤˣ) (g ≫ q) := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hn]
  have haug := app_map_sub_eq_zero (trivialTwistAugmentation.{w, u₁, u} W act) (g ≫ f).op hxy
  rw [hcomp, map_zsmul, trivialTwistAugmentation_twistedGenerator] at haug
  have hn0 : n = 0 := by simpa using congrArg ULift.down haug
  exact map_eq_of_map_sub_eq_zero (P := characterTwistPresheaf W act (1 : G →* ℤˣ)) (g ≫ f).op
    (by rw [hcomp, hn0, zero_zsmul])

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}] in
/-- **Sheafification inverts the augmentation of the trivial twist.** -/
theorem W_trivialTwistAugmentation :
    J.W (trivialTwistAugmentation.{w, u₁, u} W act) := by
  have := h.isLocallyInjective_trivialTwistAugmentation
  have := h.isLocallySurjective_trivialTwistAugmentation
  exact J.W_of_isLocallyBijective _

/-! #### The comparison with the doubly twisted tensor product -/

variable (χ : G →* ℤˣ)

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **Locally on an object lying over the torsor, every section of a tensor product with a twist
presheaf is a section of the left-hand factor tensored with the class of the structure
morphism.** -/
theorem exists_sieve_tensorGen (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {V : C} (p : V ⟶ W)
    (y : (AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ)).obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f →
      ∃ t : F.obj (op V'),
        (AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act χ)).map f.op y =
          AddCommGrpCat.tensorGen t (twistedGenerator W act χ (f ≫ p)) := by
  induction y using AddCommGrpCat.presheafTensor_induction_on with
  | zero =>
      refine ⟨⊤, J.top_mem V, fun V' f _ => ⟨0, ?_⟩⟩
      rw [map_zero, AddCommGrpCat.tensorGen_zero_left]
  | gen a x =>
      obtain ⟨S, hS, hfam⟩ := h.exists_sieve_twistedGenerator_zsmul χ p x
      refine ⟨S, hS, fun V' f hf => ?_⟩
      obtain ⟨n, hn⟩ := hfam f hf
      refine ⟨n • F.map f.op a, ?_⟩
      rw [AddCommGrpCat.presheafTensor_map_tensorGen, hn,
        AddCommGrpCat.tensorGen_smul_right, AddCommGrpCat.tensorGen_smul_left]
  | add y y' hy hy' =>
      obtain ⟨S, hS, hfam⟩ := hy
      obtain ⟨S', hS', hfam'⟩ := hy'
      refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V' f hf => ?_⟩
      obtain ⟨t, ht⟩ := hfam f hf.1
      obtain ⟨t', ht'⟩ := hfam' f hf.2
      refine ⟨t + t', ?_⟩
      rw [map_add, ht, ht', AddCommGrpCat.tensorGen_add_left]

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **Locally on an object lying over the torsor, every section of the doubly twisted tensor
product is in the image of the comparison.** -/
theorem exists_sieve_twistSquareCompare (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {V : C} (p : V ⟶ W)
    (z : (twistSquarePresheaf W act χ F).obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (g : V' ⟶ V), S g →
      ∃ y : (AddCommGrpCat.presheafTensor F
          (characterTwistPresheaf W act (1 : G →* ℤˣ))).obj (op V'),
        (twistSquareCompare W act χ F).app (op V') y =
          (twistSquarePresheaf W act χ F).map g.op z := by
  induction z using AddCommGrpCat.presheafTensor_induction_on with
  | zero =>
      refine ⟨⊤, J.top_mem V, fun V' g _ => ⟨0, ?_⟩⟩
      rw [map_zero, map_zero]
  | gen a x =>
      obtain ⟨S₁, hS₁, hfam₁⟩ := h.exists_sieve_tensorGen χ F p a
      obtain ⟨S₂, hS₂, hfam₂⟩ := h.exists_sieve_twistedGenerator_zsmul χ p x
      refine ⟨S₁ ⊓ S₂, J.intersection_covering hS₁ hS₂, fun V' g hg => ?_⟩
      obtain ⟨t, ht⟩ := hfam₁ g hg.1
      obtain ⟨n, hn⟩ := hfam₂ g hg.2
      refine ⟨AddCommGrpCat.tensorGen (n • t)
        (twistedGenerator W act (1 : G →* ℤˣ) (g ≫ p)), ?_⟩
      rw [twistSquareCompare_app_gen, AddCommGrpCat.presheafTensor_map_tensorGen, ht, hn,
        AddCommGrpCat.tensorGen_smul_left n t (twistedGenerator W act χ (g ≫ p)),
        AddCommGrpCat.tensorGen_smul_left, AddCommGrpCat.tensorGen_smul_right]
  | add z z' hz hz' =>
      obtain ⟨S, hS, hfam⟩ := hz
      obtain ⟨S', hS', hfam'⟩ := hz'
      refine ⟨S ⊓ S', J.intersection_covering hS hS', fun V' g hg => ?_⟩
      obtain ⟨y, hy⟩ := hfam g hg.1
      obtain ⟨y', hy'⟩ := hfam' g hg.2
      exact ⟨y + y', by rw [map_add, map_add, hy, hy']⟩

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The comparison with the doubly twisted tensor product is locally surjective.** -/
theorem isLocallySurjective_twistSquareCompare (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective J (twistSquareCompare W act χ F) := by
  constructor
  intro V z
  refine h.mem_of_splitting _ fun {V'} f q => ?_
  obtain ⟨S, hS, hfam⟩ := h.exists_sieve_twistSquareCompare χ F q
    ((twistSquarePresheaf W act χ F).map f.op z)
  refine ⟨S, hS, fun {V''} g hg => ?_⟩
  obtain ⟨y, hy⟩ := hfam g hg
  refine ⟨y, ?_⟩
  rw [hy, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
/-- **The comparison with the doubly twisted tensor product is locally injective.** -/
theorem isLocallyInjective_twistSquareCompare (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallyInjective J (twistSquareCompare W act χ F) := by
  constructor
  intro V y y' hyy
  refine h.mem_of_splitting' _ fun {V'} f q => ?_
  obtain ⟨S, hS, hfam⟩ := h.exists_sieve_tensorGen (1 : G →* ℤˣ) F q
    ((AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act (1 : G →* ℤˣ))).map f.op
      (y - y'))
  refine ⟨S, hS, fun {V''} g hg => ?_⟩
  by_cases hbot : (⊥ : Sieve V'') ∈ J V''
  · exact J.superset_covering bot_le hbot
  obtain ⟨t, ht⟩ := hfam g hg
  have hcomp : (AddCommGrpCat.presheafTensor F
        (characterTwistPresheaf W act (1 : G →* ℤˣ))).map (g ≫ f).op (y - y') =
      AddCommGrpCat.tensorGen t (twistedGenerator W act (1 : G →* ℤˣ) (g ≫ q)) := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ht]
  have himg := app_map_sub_eq_zero (twistSquareCompare W act χ F) (g ≫ f).op hyy
  rw [hcomp, twistSquareCompare_app_gen] at himg
  have hinner : AddCommGrpCat.tensorGen t (twistedGenerator W act χ (g ≫ q)) = 0 := by
    refine h.injective_tmul_twistedGenerator χ (g ≫ q) hbot ?_
    show AddCommGrpCat.tensorGen
        (AddCommGrpCat.tensorGen t (twistedGenerator W act χ (g ≫ q)))
        (twistedGenerator W act χ (g ≫ q)) =
      AddCommGrpCat.tensorGen (0 : (AddCommGrpCat.presheafTensor F
        (characterTwistPresheaf W act χ)).obj (op V''))
        (twistedGenerator W act χ (g ≫ q))
    rw [himg, AddCommGrpCat.tensorGen_zero_left]
  have ht0 : t = 0 := by
    refine h.injective_tmul_twistedGenerator χ (g ≫ q) hbot ?_
    show AddCommGrpCat.tensorGen t (twistedGenerator W act χ (g ≫ q)) =
      AddCommGrpCat.tensorGen (0 : F.obj (op V'')) (twistedGenerator W act χ (g ≫ q))
    rw [hinner, AddCommGrpCat.tensorGen_zero_left]
  have hzero : (AddCommGrpCat.presheafTensor F
      (characterTwistPresheaf W act (1 : G →* ℤˣ))).map (g ≫ f).op (y - y') = 0 := by
    rw [hcomp, ht0, AddCommGrpCat.tensorGen_zero_left]
  have heq := map_eq_of_map_sub_eq_zero
    (P := AddCommGrpCat.presheafTensor F (characterTwistPresheaf W act (1 : G →* ℤˣ)))
    (g ≫ f).op hzero
  refine J.superset_covering (fun V₃ k _ => ?_) (J.top_mem V'')
  have hk := congrArg (fun z => (AddCommGrpCat.presheafTensor F
    (characterTwistPresheaf W act (1 : G →* ℤˣ))).map k.op z) heq
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at hk
  exact hk

omit [UnivLE.{max u₁ (u + 1), u + 1}] [HasSheafify J AddCommGrpCat.{u + 1}] in
/-- **Sheafification inverts the comparison with the doubly twisted tensor product.** -/
theorem W_twistSquareCompare (F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    J.W (twistSquareCompare W act χ F) := by
  have := h.isLocallyInjective_twistSquareCompare χ F
  have := h.isLocallySurjective_twistSquareCompare χ F
  exact J.W_of_isLocallyBijective _

end IsTorsorObject

/-! ### The twisting functor is its own inverse over a torsor -/

namespace IsTorsorObject

variable (h : IsTorsorObject act J) (χ : G →* ℤˣ)

include h

/-- **The twisting functor by a character is its own inverse.** It is the sheafification of the
chain of comparisons `(F ⊗ ℤ(χ)) ⊗ ℤ(χ) ← F ⊗ ℤ(1) → F ⊗ ℤ → F`. -/
def characterTwistFunctorCompSelfIso :
    characterTwistFunctor W act χ J ⋙ characterTwistFunctor W act χ J ≅
      𝟭 (Sheaf J AddCommGrpCat.{u + 1}) :=
  (AddCommGrpCat.sheafifyNatIso J (twistSquareTensorSheafify W act χ J)
      (fun _ => AddCommGrpCat.W_presheafTensorMap J (J.W_toSheafify _)
        (J.W.id_mem _))).symm ≪≫
    (AddCommGrpCat.sheafifyNatIso J (twistSquareTensorCompare W act χ J)
      (fun F => h.W_twistSquareCompare χ F.obj)).symm ≪≫
      AddCommGrpCat.sheafifyNatIso J (trivialTwistTensorUnit W act J)
        (fun _ => J.W.comp_mem _ _
          (AddCommGrpCat.W_presheafTensorMap J (J.W.id_mem _) h.W_trivialTwistAugmentation)
          (J.W.of_isIso _)) ≪≫
        (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm

/-- **The twisting functor by a character is an equivalence**, being its own inverse. -/
def characterTwistEquivalence :
    Sheaf J AddCommGrpCat.{u + 1} ≌ Sheaf J AddCommGrpCat.{u + 1} :=
  Equivalence.mk (characterTwistFunctor W act χ J) (characterTwistFunctor W act χ J)
    (h.characterTwistFunctorCompSelfIso χ).symm (h.characterTwistFunctorCompSelfIso χ)

/-- The twisting functor by a character is an equivalence. -/
theorem isEquivalence_characterTwistFunctor :
    (characterTwistFunctor W act χ J).IsEquivalence :=
  (h.characterTwistEquivalence χ).isEquivalence_functor

/-- **The twisting functor is adjoint to itself.** -/
def characterTwistSelfAdjunction :
    characterTwistFunctor W act χ J ⊣ characterTwistFunctor W act χ J :=
  (h.characterTwistEquivalence χ).toAdjunction

end IsTorsorObject

end Torsor

/-! ### `Ext` out of the twist in every degree -/

section Ext

variable {C : Type u₁} [Category.{u + 1} C] [UnivLE.{max u₁ (u + 1), u + 1}]
  {W : C} {G : Type w} [Group G] {act : G →* Aut W} {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasExt.{max u₁ (u + 1)} (Sheaf J AddCommGrpCat.{u + 1})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u + 1})]

namespace IsTorsorObject

variable (h : IsTorsorObject act J) (χ : G →* ℤˣ)

include h

/-- **`Ext` out of the character twist is the cohomology of the twisted coefficients, in every
degree and naturally in the coefficients:**

`Ext^q(ℤ(χ), -) ≅ (- ⊗_ℤ ℤ(χ)) ⋙ Ext^q(ℤ, -)`.

It is `Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso`, Stacks 015Z for `Ext`, at the
self-adjunction of the twisting functor. -/
def extFunctorObjCharacterTwistIso (q : ℕ) :
    Abelian.extFunctorObj (characterTwist W act χ J) q ≅
      characterTwistFunctor W act χ J ⋙
        Abelian.extFunctorObj ((constantSheaf J AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) q :=
  haveI := h.isEquivalence_characterTwistFunctor χ
  Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso
    (h.characterTwistSelfAdjunction χ) (characterTwistFunctorObjConstant W act χ J) q

/-- **Stacks 0727 in every degree.**  For a torsor `W` under a group `G` over the final object of
a site and a character `χ : G → ℤˣ`, the `Ext`-groups out of the twisted free abelian sheaf
`ℤ(χ)` with coefficients in an abelian sheaf `F` are the cohomology groups of the twisted
coefficients `F ⊗_ℤ ℤ(χ)`:

`Ext^q(ℤ(χ), F) ≅ H^q(F ⊗_ℤ ℤ(χ))`  for every `q`.

It is the component at `F` of `CategoryTheory.IsTorsorObject.extFunctorObjCharacterTwistIso`. In
degree zero the same identification is `CategoryTheory.IsTorsorObject.twistTensorSectionsEquiv`. -/
def characterTwistExtAddEquiv (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ) :
    Abelian.Ext.{max u₁ (u + 1)} (characterTwist W act χ J) F q ≃+
      Sheaf.H.{max u₁ (u + 1), u + 1} (characterTwistTensor F.obj act χ J) q :=
  ((h.extFunctorObjCharacterTwistIso χ q).app F).addCommGroupIsoToAddEquiv

end IsTorsorObject

end Ext

end CategoryTheory

end
