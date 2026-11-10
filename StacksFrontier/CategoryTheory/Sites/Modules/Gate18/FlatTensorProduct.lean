module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of two flat sheaves of modules is flat

Let `(C, J)` be a site and `O` a sheaf of commutative rings on it. A sheaf of modules `F` over
`O` is flat when tensoring on the right with `F` is an exact endofunctor (Stacks 03ER). This
file proves Stacks 0G6Q: if `G` and `F` are flat, so is `G ⊗ F`.

## Main results

* `Stacks.SheafOfModules.FlatTensor.isFlat_tensor`: the tensor product of two flat sheaves of
  modules is flat.

## Implementation notes

Tensoring with `G ⊗ F` is not literally the composite of tensoring with `G` and tensoring with
`F`; the two agree up to the associativity isomorphism of the objectwise tensor product,
transported through sheafification. So the work is the construction of that natural
isomorphism, `sheafTensorAssocNatIsoZ`, after which the result follows because a functor
isomorphic to a composite of exact functors is exact.

Transporting associativity through sheafification needs to know that the sheafification of
`PresheafOfModules.tensorHom f (𝟙 X)` is an isomorphism whenever the sheafification of `f` is —
equivalently, that the class `J.W` of locally bijective maps of presheaves is stable under
tensoring with a fixed factor. Both halves of that are already proved at these universes, and are
used rather than redone:
`Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight` for the right factor, and
`Stacks.SheafOfModules.TensorColimits.sheafification_inverts_tensorLeft` — which carries the
symmetry of the objectwise tensor product internally — for the left one.

Fixing the right factor of the tensor bifunctor is `Functor.flip`, so the endofunctor
`G ↦ G ⊗_O F` is `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F` and its value on a
morphism `φ` is `((sheafTensor O).map φ).app F`, which
`Stacks.SheafOfModules.Tensor.sheafTensor_map_app` identifies with the sheafification of
`PresheafOfModules.tensorHom φ.val (𝟙 F.val)`. The presheaf layer here is therefore the
canonical `PresheafOfModules.tensorObj` and `PresheafOfModules.tensorHom`, so the associativity
maps and the fixed-factor functors compose with no comparison in between.

The module universe of the sheaves is independent of the ring universe and of the two site
universes, which is exactly what `PresheafOfModules.tensorObj` and
`PresheafOfModules.tensorHom` allow. Mathlib's monoidal structure on presheaves of modules, and
with it `α_`, is available only when the module universe is the ring universe, so the
associativity map of the objectwise tensor product, `tensorAssocMap`, is the one structural
morphism that has to be built here rather than taken from elsewhere.

Its proofs compute on honest pure tensors `x ⊗ₜ y` of local sections. The objectwise tensor
product is semireducible, so `(PresheafOfModules.tensorObj A X).map i` does not expose such an
element to the ordinary rewriting tactics without unfolding; making `tensorObj` locally
reducible in the implicit band is what lets them run, and is narrower than relaxing
transparency for the whole file.

## References

* [Stacks Project, Tag 0G6Q](https://stacks.math.columbia.edu/tag/0G6Q)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), the definition of
  flatness used here.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (ringPresheaf)


universe v u w z

namespace Stacks.SheafOfModules.FlatTensor

section AssociatorConstruction

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

attribute [local implicit_reducible] PresheafOfModules.tensorObj

@[implicit_reducible]
private noncomputable def sheafifyZ (O : Sheaf J CommRingCat.{w}) :
    PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)

@[implicit_reducible]
private noncomputable def toSheafifyZ (O : Sheaf J CommRingCat.{w})
    (P : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    P ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
      PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj
        ((sheafifyZ O).obj P) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app P

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem isIso_sheafify_map_toSheafifyZ (O : Sheaf J CommRingCat.{w})
    (P : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    IsIso ((sheafifyZ O).map (toSheafifyZ O P)) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).left_triangle_components P
  have ha : (sheafifyZ O).map (toSheafifyZ O P) =
      inv ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit.app ((sheafifyZ O).obj P)) := by
    refine (cancel_mono ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit.app
        ((sheafifyZ O).obj P))).mp ?_
    exact h.trans (IsIso.inv_hom_id _).symm
  exact ha ▸ inferInstance

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem isIso_sheafify_map_whiskerRightZ (O : Sheaf J CommRingCat.{w})
    {A B : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (f : A ⟶ B)
    (X : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (hf : IsIso ((sheafifyZ O).map f)) :
    IsIso ((sheafifyZ O).map (PresheafOfModules.tensorHom (O := O.obj) f (𝟙 X))) := by
  have key : ∀ {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
      (g : P ⟶ Q),
      IsIso ((sheafifyZ O).map g) ↔
        J.W ((PresheafOfModules.toPresheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map g) := by
    intro P Q g
    rw [sheafifyZ, show IsIso ((PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map g)
          ↔ MorphismProperty.isomorphisms _
              ((PresheafOfModules.sheafification
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map g)
          from (MorphismProperty.isomorphisms.iff _).symm,
        ← MorphismProperty.inverseImage_iff (MorphismProperty.isomorphisms _)
          (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)) g,
        ← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj),
        MorphismProperty.inverseImage_iff]
  -- `rw [key]` cannot be used on the goal: `PresheafOfModules.tensorHom (O := O.obj) f (𝟙 X)`
  -- is stated over `ringPresheaf O.obj`, which agrees with `(Tensor.ringSheaf O).obj` only at
  -- default transparency, so apply the equivalence by elaboration instead.
  exact (key (PresheafOfModules.tensorHom (O := O.obj) f (𝟙 X))).2
    (Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight
      O.obj f X ((key f).1 hf))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem isIso_sheafify_map_whiskerLeftZ (O : Sheaf J CommRingCat.{w})
    (X : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    {A B : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (f : A ⟶ B)
    (hf : IsIso ((sheafifyZ O).map f)) :
    IsIso ((sheafifyZ O).map (PresheafOfModules.tensorHom (O := O.obj) (𝟙 X) f)) :=
  Stacks.SheafOfModules.TensorColimits.sheafification_inverts_tensorLeft J O X f hf

private noncomputable abbrev sheafifiedUnderlyingZ (O : Sheaf J CommRingCat.{w})
    (P : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
  (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
    PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj
      ((sheafifyZ O).obj P)

private theorem tensorHom_interchange
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    {P P' : PresheafOfModules.{z} (ringPresheaf 𝒪)} (f : P ⟶ P')
    {Q Q' : PresheafOfModules.{z} (ringPresheaf 𝒪)} (g : Q ⟶ Q') :
    PresheafOfModules.tensorHom (O := 𝒪) f (𝟙 Q) ≫
        PresheafOfModules.tensorHom (O := 𝒪) (𝟙 P') g =
      PresheafOfModules.tensorHom (O := 𝒪) (𝟙 P) g ≫
        PresheafOfModules.tensorHom (O := 𝒪) f (𝟙 Q') := by
  rw [PresheafOfModules.tensorHom_comp, PresheafOfModules.tensorHom_comp]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat] in
private theorem restrictScalars_id_map
    (O : Sheaf J CommRingCat.{w})
    {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (f : P ⟶ Q) :
    (PresheafOfModules.restrictScalars
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map f = f := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem toSheafifyZ_naturality
    (O : Sheaf J CommRingCat.{w})
    {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (f : P ⟶ Q) :
    f ≫ toSheafifyZ O Q = toSheafifyZ O P ≫ ((sheafifyZ O).map f).val := by
  refine Eq.trans ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality f) ?_
  exact congrArg (fun g => toSheafifyZ O P ≫ g)
    (restrictScalars_id_map O ((sheafifyZ O).map f).val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem sheafify_unit_whiskerRight_natural
    (O : Sheaf J CommRingCat.{w})
    {P Q : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (f : P ⟶ Q)
    (R : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    (sheafifyZ O).map (PresheafOfModules.tensorHom (O := O.obj) (toSheafifyZ O P) (𝟙 R)) ≫
        (sheafifyZ O).map
          (PresheafOfModules.tensorHom (O := O.obj) (((sheafifyZ O).map f).val) (𝟙 R)) =
      (sheafifyZ O).map (PresheafOfModules.tensorHom (O := O.obj) f (𝟙 R)) ≫
    (sheafifyZ O).map (PresheafOfModules.tensorHom (O := O.obj) (toSheafifyZ O Q) (𝟙 R)) := by
  have right_comp : ∀ {P' Q' R' : PresheafOfModules.{z}
        (Stacks.SheafOfModules.Tensor.ringSheaf O).obj} (u : P' ⟶ Q') (v : Q' ⟶ R'),
      PresheafOfModules.tensorHom (O := O.obj) u (𝟙 R) ≫
          PresheafOfModules.tensorHom (O := O.obj) v (𝟙 R) =
        PresheafOfModules.tensorHom (O := O.obj) (u ≫ v) (𝟙 R) := by
    intro P' Q' R' u v
    refine Eq.trans (PresheafOfModules.tensorHom_comp (O := O.obj) u (𝟙 R) v (𝟙 R)) ?_
    exact congrArg (fun k => PresheafOfModules.tensorHom (O := O.obj) (u ≫ v) k)
      (Category.id_comp (𝟙 R))
  refine Eq.trans ((sheafifyZ O).map_comp _ _).symm
    (Eq.trans (congrArg (sheafifyZ O).map ?_) ((sheafifyZ O).map_comp _ _))
  exact (right_comp _ _).trans
    ((congrArg (fun k => PresheafOfModules.tensorHom (O := O.obj) k (𝟙 R))
      (toSheafifyZ_naturality O f).symm).trans
      (right_comp _ _).symm)

private noncomputable def tensorAssocMap
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (ringPresheaf 𝒪)) :
    PresheafOfModules.tensorObj (O := 𝒪) (PresheafOfModules.tensorObj (O := 𝒪) P Q) R ⟶
      PresheafOfModules.tensorObj (O := 𝒪) P (PresheafOfModules.tensorObj (O := 𝒪) Q R) := by
  refine ⟨fun U => ModuleCat.ofHom
    (TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
      (P.obj U) (Q.obj U) (R.obj U)).toLinearMap, ?_⟩
  intro U V i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x r
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
      change (TensorProduct.assoc ((ringPresheaf 𝒪).obj V)
          (P.obj V) (Q.obj V) (R.obj V))
          (((PresheafOfModules.tensorObj (O := 𝒪) P Q).map i).hom (p ⊗ₜ q) ⊗ₜ
            (R.map i).hom r) =
        ((PresheafOfModules.tensorObj (O := 𝒪) P
            (PresheafOfModules.tensorObj (O := 𝒪) Q R)).map i).hom
          ((TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
              (P.obj U) (Q.obj U) (R.obj U)) (p ⊗ₜ q ⊗ₜ r))
      refine Eq.trans (TensorProduct.assoc_tmul (R := (ringPresheaf 𝒪).obj V)
        (M := P.obj V) (N := Q.obj V) (P := R.obj V) _ _ _) ?_
      exact congrArg
        (fun t => (P.map i).hom p ⊗ₜ[(ringPresheaf 𝒪).obj V] t)
        (PresheafOfModules.tensorObj_restrictₛₗ_tmul (O := 𝒪) (F := Q) (G := R) i q r).symm
  | add x y hx hy =>
      simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply] at hx hy ⊢
      rw [TensorProduct.add_tmul]
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

private noncomputable def tensorAssocMapInv
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (ringPresheaf 𝒪)) :
    PresheafOfModules.tensorObj (O := 𝒪) P (PresheafOfModules.tensorObj (O := 𝒪) Q R) ⟶
      PresheafOfModules.tensorObj (O := 𝒪) (PresheafOfModules.tensorObj (O := 𝒪) P Q) R := by
  refine ⟨fun U => ModuleCat.ofHom
    (TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
      (P.obj U) (Q.obj U) (R.obj U)).symm.toLinearMap, ?_⟩
  intro U V i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext p x
  induction x using TensorProduct.inductionOn with
  | tmul q r =>
      change (TensorProduct.assoc ((ringPresheaf 𝒪).obj V)
          (P.obj V) (Q.obj V) (R.obj V)).symm
          ((P.map i).hom p ⊗ₜ
            (((PresheafOfModules.tensorObj (O := 𝒪) Q R).map i).hom (q ⊗ₜ r))) =
        ((PresheafOfModules.tensorObj (O := 𝒪)
            (PresheafOfModules.tensorObj (O := 𝒪) P Q) R).map i).hom
          ((TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
              (P.obj U) (Q.obj U) (R.obj U)).symm (p ⊗ₜ (q ⊗ₜ r)))
      refine Eq.trans (TensorProduct.assoc_symm_tmul ((P.map i).hom p) ((Q.map i).hom q)
        ((R.map i).hom r)) ?_
      exact congrArg (fun t => ((PresheafOfModules.tensorObj (O := 𝒪)
          (PresheafOfModules.tensorObj (O := 𝒪) P Q) R).map i).hom t)
        (TensorProduct.assoc_symm_tmul p q r).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

private theorem tensorAssocMap_comp_inv
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (ringPresheaf 𝒪)) :
    tensorAssocMap 𝒪 P Q R ≫ tensorAssocMapInv 𝒪 P Q R = 𝟙 _ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x r
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
      change (TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
          (P.obj U) (Q.obj U) (R.obj U)).symm
          ((TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
              (P.obj U) (Q.obj U) (R.obj U)) (p ⊗ₜ q ⊗ₜ r)) = p ⊗ₜ q ⊗ₜ r
      rw [TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul]
  | add x y hx hy =>
      simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply] at hx hy ⊢
      rw [TensorProduct.add_tmul]
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

private theorem tensorAssocMapInv_comp
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (ringPresheaf 𝒪)) :
    tensorAssocMapInv 𝒪 P Q R ≫ tensorAssocMap 𝒪 P Q R = 𝟙 _ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext p x
  induction x using TensorProduct.inductionOn with
  | tmul q r =>
      change (TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
          (P.obj U) (Q.obj U) (R.obj U))
          ((TensorProduct.assoc ((ringPresheaf 𝒪).obj U)
              (P.obj U) (Q.obj U) (R.obj U)).symm (p ⊗ₜ (q ⊗ₜ r))) = p ⊗ₜ (q ⊗ₜ r)
      rw [TensorProduct.assoc_symm_tmul, TensorProduct.assoc_tmul]
  | add x y hx hy =>
      simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply] at hx hy ⊢
      rw [TensorProduct.tmul_add]
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

private noncomputable def tensorAssocIso
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (ringPresheaf 𝒪)) :
    PresheafOfModules.tensorObj (O := 𝒪) (PresheafOfModules.tensorObj (O := 𝒪) P Q) R ≅
      PresheafOfModules.tensorObj (O := 𝒪) P
        (PresheafOfModules.tensorObj (O := 𝒪) Q R) where
  hom := tensorAssocMap 𝒪 P Q R
  inv := tensorAssocMapInv 𝒪 P Q R
  hom_inv_id := tensorAssocMap_comp_inv 𝒪 P Q R
  inv_hom_id := tensorAssocMapInv_comp 𝒪 P Q R

private theorem tensorAssocMap_naturality
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
    {P P' Q Q' R R' : PresheafOfModules.{z} (ringPresheaf 𝒪)}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    PresheafOfModules.tensorHom (O := 𝒪) (PresheafOfModules.tensorHom (O := 𝒪) f g) h ≫
        tensorAssocMap 𝒪 P' Q' R' =
      tensorAssocMap 𝒪 P Q R ≫
        PresheafOfModules.tensorHom (O := 𝒪) f (PresheafOfModules.tensorHom (O := 𝒪) g h) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x r
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
      change TensorProduct.assoc _ _ _ _
          (((TensorProduct.map (f.app U).hom (g.app U).hom) (p ⊗ₜ q)) ⊗ₜ
            (h.app U).hom r) =
        TensorProduct.map (f.app U).hom
          (TensorProduct.map (g.app U).hom (h.app U).hom)
            (TensorProduct.assoc _ _ _ _ (p ⊗ₜ q ⊗ₜ r))
      rw [TensorProduct.map_tmul, TensorProduct.assoc_tmul]
      rfl
  | add x y hx hy =>
      simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply] at hx hy ⊢
      rw [TensorProduct.add_tmul]
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy

private noncomputable def sheafTensorAssocIsoZ
    (O : Sheaf J CommRingCat.{w})
    (P Q R : PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    (sheafifyZ O).obj
        (PresheafOfModules.tensorObj (O := O.obj)
          (sheafifiedUnderlyingZ O (PresheafOfModules.tensorObj (O := O.obj) P Q)) R) ≅
      (sheafifyZ O).obj
        (PresheafOfModules.tensorObj (O := O.obj) P
          (sheafifiedUnderlyingZ O (PresheafOfModules.tensorObj (O := O.obj) Q R))) := by
  let uL := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj)
      (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) P Q)) (𝟙 R))
  let uR := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) (𝟙 P)
      (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) Q R)))
  have : IsIso uL := isIso_sheafify_map_whiskerRightZ O
    (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) P Q)) R
    (isIso_sheafify_map_toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) P Q))
  have : IsIso uR := isIso_sheafify_map_whiskerLeftZ O P
    (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) Q R))
    (isIso_sheafify_map_toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) Q R))
  exact (asIso uL).symm ≪≫
    (sheafifyZ O).mapIso (tensorAssocIso O.obj P Q R) ≪≫ asIso uR

private noncomputable def sheafTensorAssocNatIsoZ
    (O : Sheaf J CommRingCat.{w})
    (G F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F).obj G) := by
  refine NatIso.ofComponents
    (fun X => sheafTensorAssocIsoZ O X.val G.val F.val) ?_
  intro X Y f
  let aX := PresheafOfModules.tensorObj (O := O.obj) X.val G.val
  let aY := PresheafOfModules.tensorObj (O := O.obj) Y.val G.val
  let fA := PresheafOfModules.tensorHom (O := O.obj) f.val (𝟙 G.val)
  let fASh := (sheafifyZ O).map fA
  let rawMap := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) fA (𝟙 F.val))
  let sourceMap := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) fASh.val (𝟙 F.val))
  let midMap := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) f.val
      (𝟙 (PresheafOfModules.tensorObj (O := O.obj) G.val F.val)))
  let targetMap := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) f.val
      (𝟙 (sheafifiedUnderlyingZ O (PresheafOfModules.tensorObj (O := O.obj) G.val F.val))))
  let uLX := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) (toSheafifyZ O aX) (𝟙 F.val))
  let uLY := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) (toSheafifyZ O aY) (𝟙 F.val))
  let assocX := (sheafifyZ O).map (tensorAssocMap O.obj X.val G.val F.val)
  let assocY := (sheafifyZ O).map (tensorAssocMap O.obj Y.val G.val F.val)
  let uRX := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) (𝟙 X.val)
      (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) G.val F.val)))
  let uRY := (sheafifyZ O).map
    (PresheafOfModules.tensorHom (O := O.obj) (𝟙 Y.val)
      (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) G.val F.val)))
  change sourceMap ≫ (sheafTensorAssocIsoZ O Y.val G.val F.val).hom =
    (sheafTensorAssocIsoZ O X.val G.val F.val).hom ≫ targetMap
  have hL : uLX ≫ sourceMap = rawMap ≫ uLY :=
    sheafify_unit_whiskerRight_natural O fA F.val
  have hAssoc : rawMap ≫ assocY = assocX ≫ midMap := by
    refine Eq.trans ((sheafifyZ O).map_comp _ _).symm
      (Eq.trans (congrArg (sheafifyZ O).map ?_) ((sheafifyZ O).map_comp _ _))
    exact (tensorAssocMap_naturality O.obj f.val (𝟙 G.val) (𝟙 F.val)).trans
      (congrArg (fun k => tensorAssocMap O.obj X.val G.val F.val ≫
        PresheafOfModules.tensorHom (O := O.obj) f.val k)
        (PresheafOfModules.tensorHom_id (O := O.obj) G.val F.val))
  have hR : midMap ≫ uRY = uRX ≫ targetMap := by
    refine Eq.trans ((sheafifyZ O).map_comp _ _).symm
      (Eq.trans (congrArg (sheafifyZ O).map ?_) ((sheafifyZ O).map_comp _ _))
    exact tensorHom_interchange O.obj f.val
      (toSheafifyZ O (PresheafOfModules.tensorObj (O := O.obj) G.val F.val))
  have hIsoLX : IsIso uLX :=
    isIso_sheafify_map_whiskerRightZ O _ F.val (isIso_sheafify_map_toSheafifyZ O aX)
  have hIsoLY : IsIso uLY :=
    isIso_sheafify_map_whiskerRightZ O _ F.val (isIso_sheafify_map_toSheafifyZ O aY)
  change sourceMap ≫ @inv _ _ _ _ uLY hIsoLY ≫ assocY ≫ uRY =
    @inv _ _ _ _ uLX hIsoLX ≫ assocX ≫ uRX ≫ targetMap
  have hLinv : sourceMap ≫ @inv _ _ _ _ uLY hIsoLY = @inv _ _ _ _ uLX hIsoLX ≫ rawMap :=
    (IsIso.eq_inv_comp uLX).2 ((Category.assoc _ _ _).symm.trans ((IsIso.comp_inv_eq uLY).2 hL))
  exact ((reassoc_of% hLinv) _).trans
    (congrArg (_ ≫ ·) (((reassoc_of% hAssoc) _).trans (congrArg (assocX ≫ ·) hR)))

end AssociatorConstruction

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]


/-- **Stacks Project, Tag 0G6Q.** The tensor product of two flat sheaves of
modules is flat. -/
@[stacks 0G6Q]
public lemma isFlat_tensor {O : Sheaf J CommRingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (G F : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat G)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F).obj G) := by
  let SG := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj G
  let SF := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F
  change exactFunctor _ _ SG at hG
  change exactFunctor _ _ SF at hF
  rw [exactFunctor_iff] at hG hF
  obtain ⟨_, _⟩ := hG
  obtain ⟨_, _⟩ := hF
  have hComp : exactFunctor _ _ (SG ⋙ SF) := by
    rw [exactFunctor_iff]
    exact ⟨comp_preservesFiniteLimits SG SF,
      comp_preservesFiniteColimits SG SF⟩
  change exactFunctor _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj (SF.obj G))
  exact (exactFunctor _ _).prop_of_iso
    (sheafTensorAssocNatIsoZ O G F) hComp

end Stacks.SheafOfModules.FlatTensor
