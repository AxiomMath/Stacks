module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of algebras as sheaves of modules with a multiplication

The proof of Stacks 09ZT obtains the algebra structure on an algebraized coherent module from
full faithfulness of completion: "the multiplication maps `ℱₙ ⊗ ℱₙ ⟶ ℱₙ` fit together to give an
algebra structure on `ℱ`". This file carries that out in the generality in which it is a
statement about the tensor product of Tag 01CA alone.

* `MulData` is a commutative, associative, unital multiplication `F ⊗ F ⟶ F` on a sheaf of
  `𝒪_X`-modules, and `MulData.algebra` the sheaf of commutative `𝒪_X`-algebras it defines, with
  `MulData.underlyingIso` identifying its underlying module with `F` and `MulData.algHom` turning
  multiplicative module maps into morphisms of algebra sheaves.
* `mulMap` is the multiplication of an algebra sheaf as a morphism out of the tensor square of
  its underlying module.
* `LiftData` packages a coherent module `F` with maps `pₙ : F ⟶ Dₙ` to a compatible system of
  algebra sheaves, through which morphisms from coherent modules into `F` are exactly compatible
  families of morphisms into the `Dₙ`. `LiftData.mulData` is the multiplication on `F` obtained
  by lifting `(pₙ ⊗ pₙ) ≫ mulMap Dₙ` (applied to the coherent modules `F ⊗ F`, `(F ⊗ F) ⊗ F` and
  `𝒪_X ⊗ F`), and `LiftData.algebra`, `LiftData.c` the resulting finite quasi-coherent algebra
  sheaf and its morphisms to the `Dₙ`.

## Implementation notes

The monoidal structure is `Stacks.PullbackGradedAlgebra.monoidalCategory`, activated locally, at
the spelling `ModX X` of the category of `𝒪_X`-modules; the section formulas and extensionality
principles of `Stacks.PullbackTensorCoherence` are stated there. Morphisms out of a tensor
product are produced from bilinear maps on sections by `tensorDesc`.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TopologicalSpace
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.PullbackTensorCoherence (tmul)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.AdicFiniteAlgebra

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X : Scheme.{u}}

/-- The category of `𝒪_X`-modules, at the spelling carrying the monoidal structure of Tag 01CA. -/
public abbrev ModX (X : Scheme.{u}) :=
  SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)

/-! ### Local pure tensors -/

/-- A local pure tensor of two local sections. -/
public abbrev tm {M N : ModX X} (U : X.Opensᵒᵖ) (a : M.val.obj U) (b : N.val.obj U) :
    (M ⊗ N).val.obj U :=
  tmul X.toRingedSpace M N U a b

/-- Local pure tensors are additive in the first factor. -/
public theorem tm_add_left {M N : ModX X} (U : X.Opensᵒᵖ) (a a' : M.val.obj U)
    (b : N.val.obj U) : tm U (a + a') b = tm U a b + tm U a' b := by
  show ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) M N).app U).hom
    ((a + a') ⊗ₜ b) = _
  exact (congrArg _ (TensorProduct.add_tmul a a' b)).trans (map_add _ _ _)

/-- Local pure tensors are additive in the second factor. -/
public theorem tm_add_right {M N : ModX X} (U : X.Opensᵒᵖ) (a : M.val.obj U)
    (b b' : N.val.obj U) : tm U a (b + b') = tm U a b + tm U a b' := by
  show ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) M N).app U).hom
    (a ⊗ₜ (b + b')) = _
  exact (congrArg _ (TensorProduct.tmul_add a b b')).trans (map_add _ _ _)

/-- Local pure tensors are linear in the first factor. -/
public theorem tm_smul_left {M N : ModX X} (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) (a : M.val.obj U)
    (b : N.val.obj U) : tm U (r • a) b = r • tm U a b := by
  show ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) M N).app U).hom
    ((r • a) ⊗ₜ b) = _
  exact (congrArg _ (TensorProduct.smul_tmul' r a b).symm).trans (map_smul _ r _)

/-- Local pure tensors are linear in the second factor. -/
public theorem tm_smul_right {M N : ModX X} (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) (a : M.val.obj U)
    (b : N.val.obj U) : tm U a (r • b) = r • tm U a b := by
  show ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) M N).app U).hom
    (a ⊗ₜ (r • b)) = _
  exact (congrArg _ (TensorProduct.tmul_smul r a b)).trans (map_smul _ r _)

/-- Restriction of a local pure tensor restricts both factors. -/
public theorem tm_map {M N : ModX X} {U V : X.Opensᵒᵖ} (g : U ⟶ V) (a : M.val.obj U)
    (b : N.val.obj U) : (M ⊗ N).val.map g (tm U a b) = tm V (M.val.map g a) (N.val.map g b) :=
  (PresheafOfModules.naturality_apply
    (PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) M N) g (a ⊗ₜ b)).symm

/-! ### Morphisms out of a tensor product from bilinear maps -/

/-- The morphism out of `M ⊗ N` determined by a bilinear map on local sections. -/
public def tensorDesc {M N P : ModX X} (β : Stacks.BilinearMap M.val N.val P.val) :
    M ⊗ N ⟶ P :=
  PresheafOfModules.tensorSheafDesc (Osharp := X.toRingedSpace.sheaf) (F := M) (G := N) (Q := P)
    (PresheafOfModules.ofBilinear β)

/-- The morphism `tensorDesc β` on a local pure tensor is the value of `β`. -/
public theorem tensorDesc_tm {M N P : ModX X} (β : Stacks.BilinearMap M.val N.val P.val)
    (U : X.Opensᵒᵖ) (a : M.val.obj U) (b : N.val.obj U) :
    (tensorDesc β).val.app U (tm U a b) = β.app U a b :=
  (PresheafOfModules.tensorSheafDesc_unit _ U a b).trans
    (PresheafOfModules.ofBilinear_tmul β U a b)

/-- The bilinear map `(a, b) ↦ b ⊗ a`. -/
public def swapBilinear (M N : ModX X) : Stacks.BilinearMap M.val N.val (N ⊗ M).val where
  app U := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => tm U b a)
      (fun b b' => tm_add_left U b b' a))
    (fun a a' => by ext b; exact tm_add_right U b a a')
  map_smul_left U r a b := tm_smul_right U r b a
  map_smul_right U r a b := tm_smul_left U r b a
  naturality g a b := tm_map g b a

/-- The symmetry `M ⊗ N ⟶ N ⊗ M`. -/
public def swapTensor (M N : ModX X) : M ⊗ N ⟶ N ⊗ M := tensorDesc (swapBilinear M N)

/-- The symmetry exchanges the two factors of a local pure tensor. -/
public theorem swapTensor_tm {M N : ModX X} (U : X.Opensᵒᵖ) (a : M.val.obj U)
    (b : N.val.obj U) : (swapTensor M N).val.app U (tm U a b) = tm U b a :=
  tensorDesc_tm _ U a b


/-! ### The multiplication of a sheaf of algebras, as a morphism out of a tensor product -/

/-- The underlying `𝒪_X`-module of an algebra sheaf, at the monoidal spelling. -/
public abbrev uM (𝔄 : AlgebraSheaf X) : ModX X := AlgebraSheaf.underlyingModule 𝔄

/-- A local section of the underlying module, read as a section of the algebra. -/
public abbrev toR {𝔄 : AlgebraSheaf X} {U : X.Opensᵒᵖ} (a : (uM 𝔄).val.obj U) :
    𝔄.right.obj.obj U := a

/-- A local section of the algebra, read as a section of the underlying module. -/
public abbrev ofR {𝔄 : AlgebraSheaf X} {U : X.Opensᵒᵖ} (x : 𝔄.right.obj.obj U) :
    (uM 𝔄).val.obj U := x

/-- `ofR` is additive. -/
public theorem ofR_add {𝔄 : AlgebraSheaf X} {U : X.Opensᵒᵖ} (x y : 𝔄.right.obj.obj U) :
    ofR (x + y) = ofR x + ofR y := rfl

/-- `ofR` sends zero to zero. -/
public theorem ofR_zero {𝔄 : AlgebraSheaf X} {U : X.Opensᵒᵖ} :
    ofR (0 : 𝔄.right.obj.obj U) = 0 := rfl

/-- The scalar action on the underlying module is multiplication through the structure map. -/
public theorem smul_ofR {𝔄 : AlgebraSheaf X} {U : X.Opensᵒᵖ}
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U)
    (x : 𝔄.right.obj.obj U) : r • ofR x = ofR ((𝔄.hom.hom.app U).hom r * x) := rfl

/-- The multiplication of an algebra sheaf, as a bilinear map of its underlying module. -/
public def mulBilinear (𝔄 : AlgebraSheaf X) :
    Stacks.BilinearMap (uM 𝔄).val (uM 𝔄).val (uM 𝔄).val where
  app U := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => ofR (toR a * toR b))
      (fun b b' => (congrArg ofR (mul_add (toR a) (toR b) (toR b'))).trans (ofR_add _ _)))
    (fun a a' => by
      ext b
      exact (congrArg ofR (add_mul (toR a) (toR a') (toR b))).trans (ofR_add _ _))
  map_smul_left U r a b := by
    change ofR (toR (r • a) * toR b) = r • ofR (toR a * toR b)
    obtain ⟨x, rfl⟩ : ∃ x, ofR x = a := ⟨a, rfl⟩
    rw [smul_ofR, smul_ofR]
    exact congrArg ofR (mul_assoc _ _ _)
  map_smul_right U r a b := by
    change ofR (toR a * toR (r • b)) = r • ofR (toR a * toR b)
    obtain ⟨x, rfl⟩ : ∃ x, ofR x = b := ⟨b, rfl⟩
    rw [smul_ofR, smul_ofR]
    exact congrArg ofR (mul_left_comm _ _ _)
  naturality g a b := (map_mul (𝔄.right.obj.map g).hom (toR a) (toR b))

/-- The multiplication `𝔄 ⊗ 𝔄 ⟶ 𝔄` of an algebra sheaf. -/
public def mulMap (𝔄 : AlgebraSheaf X) : uM 𝔄 ⊗ uM 𝔄 ⟶ uM 𝔄 := tensorDesc (mulBilinear 𝔄)

/-- The multiplication map on a local pure tensor is the product of the two sections. -/
public theorem mulMap_tm (𝔄 : AlgebraSheaf X) (U : X.Opensᵒᵖ) (a b : (uM 𝔄).val.obj U) :
    (mulMap 𝔄).val.app U (tm U a b) = ofR (toR a * toR b) :=
  tensorDesc_tm _ U a b


/-! ### From a commutative multiplication on a module to a sheaf of algebras -/

/-- A commutative, associative and unital multiplication on a sheaf of modules, given by a
morphism out of its tensor square and a compatible family of local units. -/
public structure MulData (F : ModX X) where
  /-- The multiplication. -/
  m : F ⊗ F ⟶ F
  /-- The local units. -/
  one : ∀ U : X.Opensᵒᵖ, F.val.obj U
  one_map : ∀ {U V : X.Opensᵒᵖ} (g : U ⟶ V), F.val.map g (one U) = one V
  mul_assoc : ∀ (U : X.Opensᵒᵖ) (x y z : F.val.obj U),
    m.val.app U (tm U (m.val.app U (tm U x y)) z) = m.val.app U (tm U x (m.val.app U (tm U y z)))
  mul_comm : ∀ (U : X.Opensᵒᵖ) (x y : F.val.obj U), m.val.app U (tm U x y) = m.val.app U (tm U y x)
  one_mul : ∀ (U : X.Opensᵒᵖ) (x : F.val.obj U), m.val.app U (tm U (one U) x) = x

namespace MulData

variable {F : ModX X} (d : MulData F)

/-- The multiplication of local sections. -/
public abbrev mul (U : X.Opensᵒᵖ) (x y : F.val.obj U) : F.val.obj U := d.m.val.app U (tm U x y)

/-- Multiplication of local sections distributes over addition on the right. -/
public theorem mul_add (U : X.Opensᵒᵖ) (x y z : F.val.obj U) :
    d.mul U x (y + z) = d.mul U x y + d.mul U x z :=
  (congrArg (d.m.val.app U) (tm_add_right U x y z)).trans (map_add _ _ _)

/-- Multiplication of local sections distributes over addition on the left. -/
public theorem add_mul (U : X.Opensᵒᵖ) (x y z : F.val.obj U) :
    d.mul U (x + y) z = d.mul U x z + d.mul U y z :=
  (congrArg (d.m.val.app U) (tm_add_left U x y z)).trans (map_add _ _ _)

/-- Multiplication of local sections is linear in the first variable. -/
public theorem smul_mul (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) (x y : F.val.obj U) :
    d.mul U (r • x) y = r • d.mul U x y :=
  (congrArg (d.m.val.app U) (tm_smul_left U r x y)).trans (map_smul _ _ _)

/-- Multiplication of local sections is linear in the second variable. -/
public theorem mul_smul (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) (x y : F.val.obj U) :
    d.mul U x (r • y) = r • d.mul U x y :=
  (congrArg (d.m.val.app U) (tm_smul_right U r x y)).trans (map_smul _ _ _)

/-- Multiplication of local sections commutes with restriction. -/
public theorem mul_map {U V : X.Opensᵒᵖ} (g : U ⟶ V) (x y : F.val.obj U) :
    F.val.map g (d.mul U x y) = d.mul V (F.val.map g x) (F.val.map g y) :=
  (PresheafOfModules.naturality_apply d.m.val g (tm U x y)).symm.trans
    (congrArg (d.m.val.app V) (tm_map g x y))

/-- The local unit is a left identity, in the `mul` spelling. -/
public theorem one_mul' (U : X.Opensᵒᵖ) (x : F.val.obj U) : d.mul U (d.one U) x = x :=
  d.one_mul U x

/-- The commutative ring of local sections. -/
@[instance_reducible]
public def commRing (U : X.Opensᵒᵖ) : CommRing (F.val.obj U) :=
  { (inferInstance : AddCommGroup (F.val.obj U)) with
    mul := d.mul U
    one := d.one U
    left_distrib := d.mul_add U
    right_distrib := d.add_mul U
    zero_mul := fun x => by
      change d.m.val.app U (tm U (0 : F.val.obj U) x) = 0
      rw [show tm U (0 : F.val.obj U) x = 0 from by
        simpa using tm_add_left U (0 : F.val.obj U) 0 x, map_zero]
    mul_zero := fun x => by
      change d.m.val.app U (tm U x (0 : F.val.obj U)) = 0
      rw [show tm U x (0 : F.val.obj U) = 0 from by
        simpa using tm_add_right U x (0 : F.val.obj U) 0, map_zero]
    mul_assoc := d.mul_assoc U
    one_mul := d.one_mul U
    mul_one := fun x => (d.mul_comm U x (d.one U)).trans (d.one_mul U x)
    mul_comm := d.mul_comm U }

/-- The restriction maps, as ring homomorphisms. -/
public def ringMap {U V : X.Opensᵒᵖ} (g : U ⟶ V) :
    letI := d.commRing U
    letI := d.commRing V
    F.val.obj U →+* F.val.obj V :=
  let := d.commRing U
  let := d.commRing V
  { toFun := F.val.map g
    map_one' := d.one_map g
    map_mul' := d.mul_map g
    map_zero' := map_zero (F.val.map g).hom
    map_add' := map_add (F.val.map g).hom }

/-- The presheaf of commutative rings of local sections. -/
public def ringPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := @CommRingCat.of (F.val.obj U) (d.commRing U)
  map {U V} g := @CommRingCat.ofHom _ _ (d.commRing U) (d.commRing V) (d.ringMap g)
  map_id U := by
    ext x
    exact PresheafOfModules.map_id_apply _ _ x
  map_comp f g := by
    ext x
    exact PresheafOfModules.map_comp_apply _ _ _ x

/-- The underlying presheaf of types of `ringPresheaf` is that of `F`. -/
public def ringPresheafForgetIso :
    d.ringPresheaf ⋙ forget CommRingCat.{u} ≅ F.val.presheaf ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The presheaf of rings of local sections is a sheaf. -/
public theorem isSheaf_ringPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) d.ringPresheaf := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget _ d.ringPresheaf (forget CommRingCat.{u})).2 ?_
  refine (Presheaf.isSheaf_of_iso_iff d.ringPresheafForgetIso).2 ?_
  exact (Presheaf.isSheaf_iff_isSheaf_forget _ F.val.presheaf (forget AddCommGrpCat.{u})).1
    F.isSheaf

/-- The sheaf of commutative rings of local sections. -/
public def ringSheaf : TopCat.Sheaf CommRingCat.{u} X := ⟨d.ringPresheaf, d.isSheaf_ringPresheaf⟩

/-- A function on an open, read as a local section of the structure sheaf at the monoidal
spelling. -/
public abbrev rs {U : X.Opensᵒᵖ} (r : X.presheaf.obj U) :
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U := r

/-- The map `r ↦ r • 1` is multiplicative. -/
public theorem smul_one_mul_smul_one (U : X.Opensᵒᵖ) (r s : X.presheaf.obj U) :
    rs (r * s) • d.one U = d.mul U (rs r • d.one U) (rs s • d.one U) := by
  rw [d.smul_mul, d.mul_smul, d.one_mul']
  exact (smul_smul (rs r) (rs s) (d.one U)).symm

/-- The structure ring map `𝒪_X(U) ⟶ F(U)`, `r ↦ r • 1`. -/
public def structureRingMap (U : X.Opensᵒᵖ) :
    @RingHom (X.presheaf.obj U) (F.val.obj U) _ (d.commRing U).toNonAssocSemiring :=
  let := d.commRing U
  { toFun := fun r => rs r • d.one U
    map_one' := one_smul _ _
    map_mul' := d.smul_one_mul_smul_one U
    map_zero' := zero_smul _ _
    map_add' := fun r s => add_smul (rs r) (rs s) _ }

/-- The structure morphism `𝒪_X ⟶ F`, `r ↦ r • 1`. -/
public def structureHom : X.sheaf ⟶ d.ringSheaf :=
  ObjectProperty.homMk
    { app := fun U => @CommRingCat.ofHom _ _ _ (d.commRing U) (d.structureRingMap U)
      naturality := fun U V g => by
        ext r
        change rs ((X.presheaf.map g).hom r) • d.one V = F.val.map g (rs r • d.one U)
        rw [PresheafOfModules.map_smul, d.one_map g]
        rfl }

/-- **The sheaf of algebras defined by a commutative multiplication on a sheaf of modules.** -/
public def algebra : AlgebraSheaf X := Under.mk d.structureHom


/-- Multiplying by `r • 1` is the scalar action of `r`. -/
private theorem mul_smul_one (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) (x : F.val.obj U) :
    d.mul U (r • d.one U) x = r • x :=
  (d.smul_mul U r (d.one U) x).trans (congrArg (r • ·) (d.one_mul' U x))

/-- The local sections of the underlying module of `d.algebra` are those of `F`, linearly. -/
public def underlyingLinear (U : X.Opensᵒᵖ) :
    (uM d.algebra).val.obj U →ₗ[(Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U]
      F.val.obj U where
  toFun x := (show F.val.obj U from x)
  map_add' _ _ := rfl
  map_smul' r x :=
    (d.smul_mul U (rs r) (d.one U) x).trans (congrArg (rs r • ·) (d.one_mul' U x))

/-- The inverse of `underlyingLinear`. -/
public def underlyingLinearInv (U : X.Opensᵒᵖ) :
    F.val.obj U →ₗ[(Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U]
      (uM d.algebra).val.obj U where
  toFun x := (show (uM d.algebra).val.obj U from x)
  map_add' _ _ := rfl
  map_smul' r x :=
    ((d.smul_mul U (rs r) (d.one U) x).trans (congrArg (rs r • ·) (d.one_mul' U x))).symm

/-- **The underlying module of `d.algebra` is `F`.** -/
public def underlyingIso : uM d.algebra ≅ F where
  hom :=
    { val :=
        { app U := ConcreteCategory.ofHom (C := ModuleCat
              ((Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U))
            (underlyingLinear d U)
          naturality _ := rfl } }
  inv :=
    { val :=
        { app U := ConcreteCategory.ofHom (C := ModuleCat
              ((Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U))
            (underlyingLinearInv d U)
          naturality _ := rfl } }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- On sections, `underlyingIso` is the identity. -/
public theorem underlyingIso_hom_app (U : X.Opensᵒᵖ) (x : (uM d.algebra).val.obj U) :
    d.underlyingIso.hom.val.app U x = (show F.val.obj U from x) :=
  rfl

/-- **A multiplicative module map out of `F` is a morphism of algebra sheaves.** -/
public def algHom {P : AlgebraSheaf X} (φ : F ⟶ uM P)
    (hmul : ∀ (U : X.Opensᵒᵖ) (x y : F.val.obj U),
      φ.val.app U (d.mul U x y) = ofR (toR (φ.val.app U x) * toR (φ.val.app U y)))
    (hone : ∀ U : X.Opensᵒᵖ, φ.val.app U (d.one U) = ofR 1) : d.algebra ⟶ P :=
  Under.homMk (ObjectProperty.homMk
    { app := fun U =>
        let := d.commRing U
        CommRingCat.ofHom
          { toFun := fun x => toR (φ.val.app U x)
            map_one' := hone U
            map_mul' := hmul U
            map_zero' := map_zero (φ.val.app U).hom
            map_add' := map_add (φ.val.app U).hom }
      naturality := fun U V g => by
        ext x
        exact PresheafOfModules.naturality_apply φ.val g x })
    (by
      apply Sheaf.hom_ext
      refine NatTrans.ext (funext fun U => ?_)
      ext r
      change toR (φ.val.app U (rs r • d.one U)) = (P.hom.hom.app U).hom r
      rw [map_smul, hone, smul_ofR, mul_one])

/-- The underlying module morphism of `algHom` is the given module morphism. -/
public theorem underlyingModuleMap_algHom {P : AlgebraSheaf X} (φ : F ⟶ uM P)
    (hmul : ∀ (U : X.Opensᵒᵖ) (x y : F.val.obj U),
      φ.val.app U (d.mul U x y) = ofR (toR (φ.val.app U x) * toR (φ.val.app U y)))
    (hone : ∀ U : X.Opensᵒᵖ, φ.val.app U (d.one U) = ofR 1) :
    AlgebraSheaf.underlyingModuleMap (d.algHom φ hmul hone) = d.underlyingIso.hom ≫ φ :=
  rfl

end MulData


/-! ### Lifting a compatible system of algebra structures -/

/-- Coherence of an `𝒪_X`-module, at the monoidal spelling. -/
public abbrev Coh (G : ModX X) : Prop := _root_.SheafOfModules.IsCoherent.{u} G

/-- A tensor product of coherent modules is coherent (Stacks 01CE). -/
public theorem coh_tensor {G H : ModX X} (hG : Coh G) (hH : Coh H) : Coh (G ⊗ H) :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace G H hG hH

/-- The structure sheaf of a locally Noetherian scheme is coherent. -/
@[ega "I 10.11.1" "special case"]
public theorem coh_unit [IsLocallyNoetherian X] : Coh (𝟙_ (ModX X)) :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X

/-- The input of the lifting: a coherent module `F` with maps `pₙ` to the underlying modules of a
compatible system of algebra sheaves `Dₙ`, through which morphisms from coherent modules into `F`
are exactly compatible systems of morphisms into the `Dₙ`. -/
public structure LiftData (X : Scheme.{u}) where
  /-- The module. -/
  F : ModX X
  hF : Coh F
  /-- The system of algebra sheaves. -/
  D : ℕ → AlgebraSheaf X
  /-- The transition morphisms. -/
  τ : ∀ n, D (n + 1) ⟶ D n
  /-- The projections. -/
  p : ∀ n, F ⟶ uM (D n)
  hp : ∀ n, p (n + 1) ≫ AlgebraSheaf.underlyingModuleMap (τ n) = p n
  hex : ∀ (G : ModX X), Coh G → ∀ g : ∀ n, G ⟶ uM (D n),
    (∀ n, g (n + 1) ≫ AlgebraSheaf.underlyingModuleMap (τ n) = g n) →
      ∃ φ : G ⟶ F, ∀ n, φ ≫ p n = g n
  huniq : ∀ (G : ModX X), Coh G → ∀ φ ψ : G ⟶ F, (∀ n, φ ≫ p n = ψ ≫ p n) → φ = ψ

namespace LiftData

variable (L : LiftData X)

/-- The projections are compatible with the transition morphisms, on sections. -/
public theorem p_app (n : ℕ) (U : X.Opensᵒᵖ) (x : L.F.val.obj U) :
    (L.τ n).right.hom.app U (toR ((L.p (n + 1)).val.app U x)) = toR ((L.p n).val.app U x) :=
  congrArg (fun φ : L.F ⟶ uM (L.D n) => φ.val.app U x) (L.hp n)

/-- The target of the multiplication at level `n`: `F ⊗ F ⟶ Dₙ`, `x ⊗ y ↦ pₙ x · pₙ y`. -/
public def mulTarget (n : ℕ) : L.F ⊗ L.F ⟶ uM (L.D n) := (L.p n ⊗ₘ L.p n) ≫ mulMap (L.D n)

/-- The level-`n` multiplication target on a local pure tensor. -/
public theorem mulTarget_tm (n : ℕ) (U : X.Opensᵒᵖ) (x y : L.F.val.obj U) :
    (L.mulTarget n).val.app U (tm U x y) =
      ofR (toR ((L.p n).val.app U x) * toR ((L.p n).val.app U y)) :=
  (congrArg ((mulMap (L.D n)).val.app U)
    (Stacks.PullbackTensorCoherence.tensorHom_tmul (L.p n) (L.p n) U x y)).trans
    (mulMap_tm _ U _ _)

/-- The level-`n` multiplication targets form a compatible family. -/
public theorem mulTarget_compat (n : ℕ) :
    L.mulTarget (n + 1) ≫ AlgebraSheaf.underlyingModuleMap (L.τ n) = L.mulTarget n := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U x y => ?_
  refine ((congrArg ((AlgebraSheaf.underlyingModuleMap (L.τ n)).val.app U)
    (L.mulTarget_tm (n + 1) U x y)).trans ?_).trans (L.mulTarget_tm n U x y).symm
  exact (map_mul ((L.τ n).right.hom.app U).hom _ _).trans
    (congrArg₂ (fun a b => ofR (a * b)) (L.p_app n U x) (L.p_app n U y))

/-- The multiplication `m : F ⊗ F ⟶ F`. -/
public def m : L.F ⊗ L.F ⟶ L.F :=
  (L.hex _ (coh_tensor L.hF L.hF) L.mulTarget L.mulTarget_compat).choose

/-- The multiplication of `F` lifts the multiplications of the `Dₙ`. -/
public theorem m_p (n : ℕ) : L.m ≫ L.p n = L.mulTarget n :=
  (L.hex _ (coh_tensor L.hF L.hF) L.mulTarget L.mulTarget_compat).choose_spec n

/-- The projections are multiplicative, on sections. -/
public theorem p_m (n : ℕ) (U : X.Opensᵒᵖ) (x y : L.F.val.obj U) :
    (L.p n).val.app U (L.m.val.app U (tm U x y)) =
      ofR (toR ((L.p n).val.app U x) * toR ((L.p n).val.app U y)) :=
  (congrArg (fun φ : L.F ⊗ L.F ⟶ uM (L.D n) => φ.val.app U (tm U x y)) (L.m_p n)).trans
    (L.mulTarget_tm n U x y)

/-- The structure morphisms `𝒪_X ⟶ Dₙ`, as morphisms of modules. -/
public def unitTarget (n : ℕ) : 𝟙_ (ModX X) ⟶ uM (L.D n) :=
  Stacks.AlgebraPullbackQcoh.unitToRestrictScalarsObjUnit (AlgebraSheaf.structureMap (L.D n))

/-- The structure morphism of `Dₙ`, on sections. -/
public theorem unitTarget_app (n : ℕ) (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) :
    (L.unitTarget n).val.app U r = ofR (((L.D n).hom.hom.app U).hom r) :=
  rfl

/-- The structure morphisms of the `Dₙ` form a compatible family. -/
public theorem unitTarget_compat (n : ℕ) :
    L.unitTarget (n + 1) ≫ AlgebraSheaf.underlyingModuleMap (L.τ n) = L.unitTarget n := by
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  exact AlgebraSheaf.ringSheafMap_app_structureMap_app (L.τ n) U r

/-- The lifted multiplication is commutative. -/
public theorem m_comm : swapTensor L.F L.F ≫ L.m = L.m := by
  refine L.huniq _ (coh_tensor L.hF L.hF) _ _ fun n => ?_
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U x y => ?_
  show (L.p n).val.app U (L.m.val.app U ((swapTensor L.F L.F).val.app U (tm U x y))) =
    (L.p n).val.app U (L.m.val.app U (tm U x y))
  rw [swapTensor_tm, L.p_m, L.p_m]
  exact congrArg ofR (mul_comm _ _)

/-- The lifted multiplication is associative. -/
public theorem m_assoc :
    (L.m ▷ L.F) ≫ L.m = (α_ L.F L.F L.F).hom ≫ (L.F ◁ L.m) ≫ L.m := by
  refine L.huniq _ (coh_tensor (coh_tensor L.hF L.hF) L.hF) _ _ fun n => ?_
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext₂ fun U x y z => ?_
  show (L.p n).val.app U (L.m.val.app U ((L.m ▷ L.F).val.app U (tm U (tm U x y) z))) =
    (L.p n).val.app U (L.m.val.app U ((L.F ◁ L.m).val.app U
      ((α_ L.F L.F L.F).hom.val.app U (tm U (tm U x y) z))))
  rw [Stacks.PullbackTensorCoherence.whiskerRight_tmul,
    Stacks.PullbackTensorCoherence.associator_hom_tmul,
    Stacks.PullbackTensorCoherence.whiskerLeft_tmul, L.p_m, L.p_m, L.p_m, L.p_m]
  exact congrArg ofR (mul_assoc _ _ _)

variable [IsLocallyNoetherian X]

/-- The unit `𝒪_X ⟶ F`. -/
public def u : 𝟙_ (ModX X) ⟶ L.F :=
  (L.hex _ coh_unit L.unitTarget L.unitTarget_compat).choose

/-- The unit of `F` lifts the units of the `Dₙ`. -/
public theorem u_p (n : ℕ) : L.u ≫ L.p n = L.unitTarget n :=
  (L.hex _ coh_unit L.unitTarget L.unitTarget_compat).choose_spec n

/-- The projections are unital, on sections. -/
public theorem p_u (n : ℕ) (U : X.Opensᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) :
    (L.p n).val.app U (L.u.val.app U r) = ofR (((L.D n).hom.hom.app U).hom r) :=
  congrArg (fun φ : 𝟙_ (ModX X) ⟶ uM (L.D n) => φ.val.app U r) (L.u_p n)

/-- The lifted unit is a left identity for the lifted multiplication. -/
public theorem u_m : (L.u ▷ L.F) ≫ L.m = (λ_ L.F).hom := by
  refine L.huniq _ (coh_tensor coh_unit L.hF) _ _ fun n => ?_
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U r x => ?_
  let r' : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U := r
  have hl : (λ_ L.F).hom.val.app U (tm U r x) = r' • x :=
    Stacks.PullbackTensorCoherence.leftUnitor_hom_tmul U r' x
  show (L.p n).val.app U (L.m.val.app U ((L.u ▷ L.F).val.app U (tm U r x))) =
    (L.p n).val.app U ((λ_ L.F).hom.val.app U (tm U r x))
  rw [Stacks.PullbackTensorCoherence.whiskerRight_tmul, L.p_m, hl, map_smul]
  exact (congrArg (fun a => ofR (toR a * toR ((L.p n).val.app U x))) (L.p_u n U r')).trans
    (smul_ofR r' _).symm

/-- The multiplication data on `F`. -/
public def mulData : MulData L.F where
  m := L.m
  one U := L.u.val.app U (Stacks.PullbackTensorCoherence.oneSec X.toRingedSpace U)
  one_map {U V} g := (PresheafOfModules.naturality_apply L.u.val g _).symm.trans
    (congrArg (L.u.val.app V)
      (map_one ((Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.map g).hom))
  mul_assoc U x y z := by
    have h := congrArg (fun φ : (L.F ⊗ L.F) ⊗ L.F ⟶ L.F => φ.val.app U (tm U (tm U x y) z))
      L.m_assoc
    simp only at h
    rw [SheafOfModules.comp_val_app_apply, Stacks.PullbackTensorCoherence.whiskerRight_tmul,
      SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
      Stacks.PullbackTensorCoherence.associator_hom_tmul,
      Stacks.PullbackTensorCoherence.whiskerLeft_tmul] at h
    exact h
  mul_comm U x y := by
    have h := congrArg (fun φ : L.F ⊗ L.F ⟶ L.F => φ.val.app U (tm U y x)) L.m_comm
    simp only at h
    rw [SheafOfModules.comp_val_app_apply, swapTensor_tm] at h
    exact h
  one_mul U x := by
    have h := congrArg (fun φ : 𝟙_ (ModX X) ⊗ L.F ⟶ L.F => φ.val.app U
      (tm U (Stacks.PullbackTensorCoherence.oneSec X.toRingedSpace U) x)) L.u_m
    have h1 := Stacks.PullbackTensorCoherence.whiskerRight_tmul (Z := X.toRingedSpace) L.u U
      (Stacks.PullbackTensorCoherence.oneSec X.toRingedSpace U) x
    have h2 := Stacks.PullbackTensorCoherence.leftUnitor_hom_tmul (Z := X.toRingedSpace)
      (B := L.F) U (1 : (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).obj.obj U) x
    exact (congrArg (L.m.val.app U) h1).symm.trans (h.trans (h2.trans (one_smul _ x)))


/-- `F`, at the `X.Modules` spelling. -/
public abbrev FX : X.Modules := L.F

/-- **The lifted sheaf of algebras.** -/
public def algebra : AlgebraSheaf X := L.mulData.algebra

/-- The underlying module of the lifted algebra is `F`. -/
public def underlyingIso : uM L.algebra ≅ L.F := L.mulData.underlyingIso

/-- The lifted algebra is quasi-coherent. -/
public theorem isQuasicoherent_algebra : AlgebraSheaf.IsQuasicoherent L.algebra :=
  have hF : L.FX.IsQuasicoherent :=
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X
      L.FX L.hF).1
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    L.underlyingIso.symm hF

/-- The lifted algebra is finite. -/
public theorem isFinite_algebra : AlgebraSheaf.IsFinite L.algebra := by
  intro U hU
  obtain ⟨hq, hf⟩ :=
    @Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X
      L.FX L.hF
  have hfin : Module.Finite Γ(X, U) Γ(L.FX, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections L.FX hU
  let _ : Module Γ(X, U) (L.algebra.right.obj.obj (op U)) :=
    (RingHom.toAlgebra (L.algebra.hom.hom.app (op U)).hom).toModule
  let e : Γ(L.FX, U) ≃ₗ[Γ(X, U)] L.algebra.right.obj.obj (op U) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (L.mulData.mul_smul_one _ r x).symm }
  exact Module.Finite.equiv (R := Γ(X, U)) e

/-- The morphisms of algebras `C ⟶ Dₙ`. -/
public def c (n : ℕ) : L.algebra ⟶ L.D n :=
  L.mulData.algHom (L.p n) (fun U x y => L.p_m n U x y) (fun U =>
    (L.p_u n U 1).trans (congrArg ofR (map_one ((L.D n).hom.hom.app U).hom)))

/-- The morphisms `c n` are the projections, on sections. -/
public theorem c_app (n : ℕ) (U : X.Opensᵒᵖ) (x : L.algebra.right.obj.obj U) :
    (L.c n).right.hom.app U x = toR ((L.p n).val.app U x) :=
  rfl

/-- The morphisms `c n` are compatible with the transition morphisms. -/
public theorem c_comp_τ (n : ℕ) : L.c (n + 1) ≫ L.τ n = L.c n := by
  ext1
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  ext x
  exact L.p_app n U x


/-- The scalar action on `F` is multiplication by the image of the structure map of the
lifted algebra. -/
public theorem smul_eq_mul (U : X.Opensᵒᵖ) (r : X.presheaf.obj U) (x : L.F.val.obj U) :
    MulData.rs r • x =
      (show L.F.val.obj U from
        (L.algebra.hom.hom.app U).hom r * (show L.algebra.right.obj.obj U from x)) :=
  (L.mulData.mul_smul_one U r x).symm

/-- An element of `𝔞 • F(U)` lies in the ideal of `C(U)` generated by `𝔞`. -/
public theorem mem_map_of_mem_smul_top (U : X.Opens) (𝔞 : Ideal Γ(X, U)) {x : Γ(L.FX, U)}
    (hx : x ∈ 𝔞 • (⊤ : Submodule Γ(X, U) Γ(L.FX, U))) :
    (show L.algebra.right.obj.obj (op U) from x) ∈
      Ideal.map (L.algebra.hom.hom.app (op U)).hom 𝔞 := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun y z hy hz => ?_)
  · have h := L.smul_eq_mul (op U) a m
    have h' : (show L.algebra.right.obj.obj (op U) from a • m) =
        (L.algebra.hom.hom.app (op U)).hom a * (show L.algebra.right.obj.obj (op U) from m) := h
    rw [h']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · exact Ideal.add_mem _ hy hz

/-- `c n` is surjective on sections wherever the projection is. -/
public theorem c_surjective (n : ℕ) (U : X.Opensᵒᵖ)
    (h : Function.Surjective ((L.p n).val.app U)) :
    Function.Surjective ((L.c n).right.hom.app U) := fun y => by
  obtain ⟨x, hx⟩ := h y
  exact ⟨x, hx⟩

/-- The kernel of `c n` on sections over `U` is generated by an ideal annihilating the kernel of the
projection. -/
public theorem ker_c_le (n : ℕ) (U : X.Opens) (𝔞 : Ideal Γ(X, U))
    (h : ∀ x : Γ(L.FX, U), (L.p n).val.app (op U) x = 0 →
      x ∈ 𝔞 • (⊤ : Submodule Γ(X, U) Γ(L.FX, U))) :
    RingHom.ker ((L.c n).right.hom.app (op U)).hom ≤
      Ideal.map (L.algebra.hom.hom.app (op U)).hom 𝔞 :=
  fun x hx => L.mem_map_of_mem_smul_top U 𝔞 (h x hx)

end LiftData

end AlgebraicGeometry.AdicFiniteAlgebra

end
