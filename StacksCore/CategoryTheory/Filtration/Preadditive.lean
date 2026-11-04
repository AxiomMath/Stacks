module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Limits.Shapes.BinaryBiproducts
import StacksCore.Tactic.StacksAttribute

/-! # Filtered objects of an additive category

Stacks 0122 (1) and (2): the category `Fil(𝒜)` of filtered objects of an abelian category is
additive and has a zero object. Everything here holds for an arbitrary index category `I` and
needs only the corresponding structure on `C`.

* `FilteredObject.hasZeroMorphisms`: zero morphisms of `Fil(𝒜)` from those of `𝒜`, so that
  `Fil(𝒜)` has zero morphisms whenever `𝒜` does, not only when `𝒜` is preadditive.
* `FilteredObject.eval i` (evaluation at a step) preserves zero morphisms and is additive.
* `FilteredObject.preadditive`: morphisms of filtered objects are added, negated, subtracted
  and scaled on the underlying morphism and on every step, `(f + g).hom = f.hom + g.hom`,
  `(n • f).hom = n • f.hom`; the forgetful functor is additive.
* `FilteredObject.hasZeroObject`: the zero object of `C` with the constant filtration `0 ⊆ 0`,
  for any `C` with a zero object. `isZero_iff` says that a filtered object is zero if and only
  if its underlying object is.
* `FilteredObject.hasBinaryBiproducts`: `biprodObj A B` is `A ⊕ B` with
  `F^i(A ⊕ B) = F^iA ⊕ F^iB`, a biproduct by `biprodBiconeIsBilimit`; Mathlib's chosen `A ⊞ B`
  is isomorphic to it by `biprodIsoBiprodObj`, the analogue of `kernelIsoKernelObj` in
  `StacksCore.CategoryTheory.Filtration.Limits`. Hence `hasFiniteBiproducts`: `Fil(𝒜)` is an
  additive category, and `forget` preserves binary biproducts. `biprodObjLift f g` is the
  pairing `(f, g) : A ⟶ biprodObj B D`, level by level `(F^if, F^ig)`, and
  `biprod_lift_biprodIsoBiprodObj_hom` identifies it with Mathlib's `biprod.lift f g`; dually
  `biprodObjDesc f g : biprodObj B D ⟶ A` is the copairing `f ⊕ g`, identified with
  `biprod.desc f g` by `biprodIsoBiprodObj_hom_biprodObjDesc`.

Kernels and cokernels, 0122 (3), are in `StacksCore.CategoryTheory.Filtration.Limits`, which also
discusses 0122 (4).
-/

@[expose] public section

namespace CategoryTheory.FilteredObject

open Limits ZeroObject

variable {C : Type*} [Category* C] {I : Type*} [Category* I] {A B : FilteredObject C I}

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- The zero morphism of filtered objects: zero on the underlying morphism and on every step. -/
instance instZero : Zero (A ⟶ B) :=
  ⟨homMk 0 (fun _ => 0) (fun _ => by simp)⟩

@[simp] lemma zero_hom : (0 : A ⟶ B).hom = 0 := rfl

@[simp] lemma zero_natTrans_app (i : I) : (0 : A ⟶ B).natTrans.app i = 0 := rfl

/-- Zero morphisms of filtered objects: zero on the underlying morphism and on every step. -/
instance hasZeroMorphisms : HasZeroMorphisms (FilteredObject C I) where
  comp_zero f Z := hom_ext (by simp)
  zero_comp X {Y Z} g := hom_ext (by simp)

/-- Evaluation at a step `i` preserves zero morphisms. -/
instance (i : I) : (eval (C := C) i).PreservesZeroMorphisms where

end ZeroMorphisms

section Preadditive

variable [Preadditive C]

/-- Morphisms of filtered objects are added on the underlying morphism and on every step. -/
noncomputable instance instAdd : Add (A ⟶ B) :=
  ⟨fun f g => homMk (f.hom + g.hom) (fun i => f.natTrans.app i + g.natTrans.app i)
    (fun i => by simp [Preadditive.add_comp, Preadditive.comp_add])⟩

/-- Morphisms of filtered objects are negated on the underlying morphism and on every step. -/
noncomputable instance instNeg : Neg (A ⟶ B) :=
  ⟨fun f => homMk (-f.hom) (fun i => -f.natTrans.app i) (fun i => by simp)⟩

/-- The additive group of morphisms of filtered objects; subtraction and the `ℕ`- and
`ℤ`-actions are pointwise as well, so that `(n • f).hom = n • f.hom` holds by `rfl`. -/
noncomputable instance instAddCommGroup : AddCommGroup (A ⟶ B) where
  sub f g := homMk (f.hom - g.hom) (fun i => f.natTrans.app i - g.natTrans.app i)
    (fun i => by simp)
  nsmul n f := homMk (n • f.hom) (fun i => n • f.natTrans.app i)
    (fun i => by simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul])
  zsmul n f := homMk (n • f.hom) (fun i => n • f.natTrans.app i)
    (fun i => by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul])
  add_assoc f g h := hom_ext (add_assoc f.hom g.hom h.hom)
  zero_add f := hom_ext (zero_add f.hom)
  add_zero f := hom_ext (add_zero f.hom)
  neg_add_cancel f := hom_ext (neg_add_cancel f.hom)
  add_comm f g := hom_ext (add_comm f.hom g.hom)
  nsmul_zero f := hom_ext (zero_nsmul f.hom)
  nsmul_succ n f := hom_ext (succ_nsmul f.hom n)
  sub_eq_add_neg f g := hom_ext (sub_eq_add_neg f.hom g.hom)
  zsmul_zero' f := hom_ext (zero_zsmul f.hom)
  zsmul_succ' n f := hom_ext (SubNegMonoid.zsmul_succ' n f.hom)
  zsmul_neg' n f := hom_ext (SubNegMonoid.zsmul_neg' n f.hom)

/-- Stacks 0122 (1): `Fil(𝒜)` is preadditive. Morphisms are added on the underlying morphism
and on every step of the filtration. -/
@[stacks 0122 "(1) `Fil(𝒜)` is preadditive, for any preadditive `𝒜` and any index category"]
noncomputable instance preadditive : Preadditive (FilteredObject C I) where
  add_comp _ _ _ _ _ _ := hom_ext (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := hom_ext (Preadditive.comp_add _ _ _ _ _ _)

@[simp] lemma add_hom (f g : A ⟶ B) : (f + g).hom = f.hom + g.hom := rfl

@[simp] lemma add_natTrans_app (f g : A ⟶ B) (i : I) :
    (f + g).natTrans.app i = f.natTrans.app i + g.natTrans.app i := rfl

@[simp] lemma neg_hom (f : A ⟶ B) : (-f).hom = -f.hom := rfl

@[simp] lemma neg_natTrans_app (f : A ⟶ B) (i : I) : (-f).natTrans.app i = -f.natTrans.app i :=
  rfl

@[simp] lemma sub_hom (f g : A ⟶ B) : (f - g).hom = f.hom - g.hom := rfl

@[simp] lemma sub_natTrans_app (f g : A ⟶ B) (i : I) :
    (f - g).natTrans.app i = f.natTrans.app i - g.natTrans.app i := rfl

@[simp] lemma nsmul_hom (n : ℕ) (f : A ⟶ B) : (n • f).hom = n • f.hom := rfl

@[simp] lemma nsmul_natTrans_app (n : ℕ) (f : A ⟶ B) (i : I) :
    (n • f).natTrans.app i = n • f.natTrans.app i := rfl

@[simp] lemma zsmul_hom (n : ℤ) (f : A ⟶ B) : (n • f).hom = n • f.hom := rfl

@[simp] lemma zsmul_natTrans_app (n : ℤ) (f : A ⟶ B) (i : I) :
    (n • f).natTrans.app i = n • f.natTrans.app i := rfl

/-- The forgetful functor `Fil(𝒜) ⥤ 𝒜` is additive. -/
instance : (forget (C := C) (I := I)).Additive where
  map_add := rfl

/-- Evaluation at a step `i` is an additive functor. -/
instance (i : I) : (eval (C := C) i).Additive where

end Preadditive

section Zero

variable [HasZeroObject C]

/-- The zero filtered object: the zero object of `C` with the constant filtration `0 ⊆ 0`. -/
noncomputable def zero : FilteredObject C I := ⟨0, ⟨(Functor.const I).obj ⊤⟩⟩

/-- The filtered object `zero` is a zero object of `Fil(𝒜)`. -/
lemma isZero_zero : IsZero (zero : FilteredObject C I) :=
  have h := Limits.isZero_zero C
  { unique_to Y := ⟨⟨⟨homMk (h.to_ Y.X) (fun _ => h.to_ _) (fun _ => h.eq_of_src _ _)⟩,
      fun _ => hom_ext (h.eq_of_src _ _)⟩⟩
    unique_from Y := ⟨⟨⟨homMk (h.from_ Y.X) (fun _ => h.from_ _) (fun _ => h.eq_of_tgt _ _)⟩,
      fun _ => hom_ext (h.eq_of_tgt _ _)⟩⟩ }

/-- Stacks 0122 (2): `Fil(𝒜)` has a zero object. -/
@[stacks 0122 "(2) the zero object, for any `𝒜` with a zero object and any index category"]
noncomputable instance hasZeroObject : HasZeroObject (FilteredObject C I) := ⟨⟨zero, isZero_zero⟩⟩

/-- A filtered object is zero if and only if its underlying object is zero. -/
lemma isZero_iff (A : FilteredObject C I) : IsZero A ↔ IsZero A.X := by
  let _ : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
  have h := Limits.isZero_zero C
  exact ⟨fun hA => h.of_iso ((forget (C := C) (I := I)).mapIso (hA.iso isZero_zero)),
    fun hX => isZero_zero.of_iso (isoMk (hX.iso h)
      (fun i => (hX.of_mono (A.filtration.ι.app i)).iso h) (fun i => h.eq_of_tgt _ _))⟩

end Zero

section Biproducts

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The direct sum of filtered objects, `A ⊕ B` with `F^i(A ⊕ B) = F^iA ⊕ F^iB`. -/
@[implicit_reducible]
noncomputable def biprodObj (A B : FilteredObject C I) : FilteredObject C I where
  X := A.X ⊞ B.X
  filtration :=
    ⟨{ obj i := ⟨Over.mk (biprod.map (A.filtration.ι.app i) (B.filtration.ι.app i)),
         inferInstanceAs (Mono (biprod.map _ _))⟩
       map {i j} f := MonoOver.homMk
         (biprod.map (A.filtration.diagram.map f) (B.filtration.diagram.map f))
         (by simp only [MonoOver.arrow, Over.mk_hom]; ext <;> simp)
       map_id _ := Subsingleton.elim _ _
       map_comp _ _ := Subsingleton.elim _ _ }⟩

@[simp] lemma biprodObj_X (A B : FilteredObject C I) : (biprodObj A B).X = (A.X ⊞ B.X) := rfl

@[simp] lemma biprodObj_ι_app (A B : FilteredObject C I) (i : I) :
    (biprodObj A B).filtration.ι.app i =
      biprod.map (A.filtration.ι.app i) (B.filtration.ι.app i) := rfl

/-- The bicone exhibiting `biprodObj A B` as a biproduct of `A` and `B` in `Fil(𝒜)`. -/
@[implicit_reducible]
noncomputable def biprodBicone (A B : FilteredObject C I) : BinaryBicone A B where
  pt := biprodObj A B
  fst := homMk biprod.fst (fun _ => biprod.fst) (fun _ => (biprod.map_fst _ _).symm)
  snd := homMk biprod.snd (fun _ => biprod.snd) (fun _ => (biprod.map_snd _ _).symm)
  inl := homMk biprod.inl (fun _ => biprod.inl) (fun _ => biprod.inl_map _ _)
  inr := homMk biprod.inr (fun _ => biprod.inr) (fun _ => biprod.inr_map _ _)
  inl_fst := hom_ext biprod.inl_fst
  inl_snd := hom_ext biprod.inl_snd
  inr_fst := hom_ext biprod.inr_fst
  inr_snd := hom_ext biprod.inr_snd

@[simp] lemma biprodBicone_pt (A B : FilteredObject C I) : (biprodBicone A B).pt = biprodObj A B :=
  rfl

@[simp] lemma biprodBicone_fst_hom (A B : FilteredObject C I) :
    (biprodBicone A B).fst.hom = biprod.fst := rfl

@[simp] lemma biprodBicone_snd_hom (A B : FilteredObject C I) :
    (biprodBicone A B).snd.hom = biprod.snd := rfl

@[simp] lemma biprodBicone_inl_hom (A B : FilteredObject C I) :
    (biprodBicone A B).inl.hom = biprod.inl := rfl

@[simp] lemma biprodBicone_inr_hom (A B : FilteredObject C I) :
    (biprodBicone A B).inr.hom = biprod.inr := rfl

/-- `biprodBicone A B` is a bilimit: `biprodObj A B`, with `F^i(A ⊕ B) = F^iA ⊕ F^iB`, is a
biproduct of `A` and `B` in `Fil(𝒜)`. -/
noncomputable def biprodBiconeIsBilimit (A B : FilteredObject C I) :
    (biprodBicone A B).IsBilimit :=
  isBinaryBilimitOfTotal _ (hom_ext biprod.total)

/-- Stacks 0122 (1): `Fil(𝒜)` has direct sums, `F^i(A ⊕ B) = F^iA ⊕ F^iB`. -/
@[stacks 0122 "(1) direct sums `A ⊕ B` with `F^i(A ⊕ B) = F^iA ⊕ F^iB`, for any index category"]
noncomputable instance hasBinaryBiproducts : HasBinaryBiproducts (FilteredObject C I) :=
  ⟨fun A B => HasBinaryBiproduct.mk ⟨_, biprodBiconeIsBilimit A B⟩⟩

/-- Mathlib's chosen biproduct in `Fil(𝒜)` is isomorphic to the explicit model `biprodObj A B`. -/
noncomputable def biprodIsoBiprodObj (A B : FilteredObject C I) : A ⊞ B ≅ biprodObj A B :=
  (biprod.uniqueUpToIso A B (biprodBiconeIsBilimit A B)).symm

/-- The first inclusion into `A ⊞ B` followed by `biprodIsoBiprodObj` is the first inclusion
of `biprodBicone A B`. -/
@[reassoc (attr := simp)]
lemma inl_biprodIsoBiprodObj_hom (A B : FilteredObject C I) :
    biprod.inl ≫ (biprodIsoBiprodObj A B).hom = (biprodBicone A B).inl :=
  biprod.inl_desc _ _

/-- The second inclusion into `A ⊞ B` followed by `biprodIsoBiprodObj` is the second inclusion
of `biprodBicone A B`. -/
@[reassoc (attr := simp)]
lemma inr_biprodIsoBiprodObj_hom (A B : FilteredObject C I) :
    biprod.inr ≫ (biprodIsoBiprodObj A B).hom = (biprodBicone A B).inr :=
  biprod.inr_desc _ _

/-- The inverse of `biprodIsoBiprodObj` followed by the first projection of `A ⊞ B` is the
first projection of `biprodBicone A B`. -/
@[reassoc (attr := simp)]
lemma biprodIsoBiprodObj_inv_fst (A B : FilteredObject C I) :
    (biprodIsoBiprodObj A B).inv ≫ biprod.fst = (biprodBicone A B).fst :=
  biprod.lift_fst _ _

/-- The inverse of `biprodIsoBiprodObj` followed by the second projection of `A ⊞ B` is the
second projection of `biprodBicone A B`. -/
@[reassoc (attr := simp)]
lemma biprodIsoBiprodObj_inv_snd (A B : FilteredObject C I) :
    (biprodIsoBiprodObj A B).inv ≫ biprod.snd = (biprodBicone A B).snd :=
  biprod.lift_snd _ _

/-- `biprodIsoBiprodObj` followed by the first projection of `biprodBicone A B` is the first
projection of `A ⊞ B`. -/
@[reassoc (attr := simp)]
lemma biprodIsoBiprodObj_hom_fst (A B : FilteredObject C I) :
    (biprodIsoBiprodObj A B).hom ≫ (biprodBicone A B).fst = biprod.fst := by
  rw [← biprodIsoBiprodObj_inv_fst, Iso.hom_inv_id_assoc]

/-- `biprodIsoBiprodObj` followed by the second projection of `biprodBicone A B` is the second
projection of `A ⊞ B`. -/
@[reassoc (attr := simp)]
lemma biprodIsoBiprodObj_hom_snd (A B : FilteredObject C I) :
    (biprodIsoBiprodObj A B).hom ≫ (biprodBicone A B).snd = biprod.snd := by
  rw [← biprodIsoBiprodObj_inv_snd, Iso.hom_inv_id_assoc]

/-- The pairing `(f, g) : A ⟶ B ⊕ D` into the explicit direct sum `biprodObj B D`, level by
level `(F^if, F^ig) : F^iA ⟶ F^iB ⊕ F^iD`. -/
noncomputable def biprodObjLift {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    A ⟶ biprodObj B D :=
  homMk (biprod.lift f.hom g.hom) (fun i => biprod.lift (f.natTrans.app i) (g.natTrans.app i))
    (fun i => (biprod.lift_map _ _ _ _).trans
      ((congr_arg₂ biprod.lift (f.comm i) (g.comm i)).trans (biprod.comp_lift _ _ _).symm))

@[simp] lemma biprodObjLift_hom {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    (biprodObjLift f g).hom = biprod.lift f.hom g.hom := rfl

@[simp] lemma biprodObjLift_natTrans_app {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) (i : I) :
    (biprodObjLift f g).natTrans.app i = biprod.lift (f.natTrans.app i) (g.natTrans.app i) := rfl

/-- The pairing `biprodObjLift f g` followed by the first projection is `f`. -/
@[reassoc (attr := simp)]
lemma biprodObjLift_fst {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    biprodObjLift f g ≫ (biprodBicone B D).fst = f :=
  hom_ext (biprod.lift_fst _ _)

/-- The pairing `biprodObjLift f g` followed by the second projection is `g`. -/
@[reassoc (attr := simp)]
lemma biprodObjLift_snd {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    biprodObjLift f g ≫ (biprodBicone B D).snd = g :=
  hom_ext (biprod.lift_snd _ _)

/-- Mathlib's `biprod.lift f g` corresponds to `biprodObjLift f g` under `biprodIsoBiprodObj`. -/
@[reassoc (attr := simp)]
lemma biprod_lift_biprodIsoBiprodObj_hom {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    biprod.lift f g ≫ (biprodIsoBiprodObj B D).hom = biprodObjLift f g :=
  (Iso.eq_comp_inv _).1 (biprod.hom_ext _ _ (by simp) (by simp))

/-- Mathlib's `biprod.lift f g` is `biprodObjLift f g` followed by the inverse of
`biprodIsoBiprodObj`. -/
lemma biprod_lift_eq {D : FilteredObject C I} (f : A ⟶ B) (g : A ⟶ D) :
    biprod.lift f g = biprodObjLift f g ≫ (biprodIsoBiprodObj B D).inv :=
  (Iso.eq_comp_inv _).2 (biprod_lift_biprodIsoBiprodObj_hom f g)

/-- The copairing `f ⊕ g : B ⊕ D ⟶ A` out of the explicit direct sum `biprodObj B D`, level by
level `F^if ⊕ F^ig : F^iB ⊕ F^iD ⟶ F^iA`. -/
noncomputable def biprodObjDesc {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    biprodObj B D ⟶ A :=
  homMk (biprod.desc f.hom g.hom) (fun i => biprod.desc (f.natTrans.app i) (g.natTrans.app i))
    (fun i => (biprod.desc_comp _ _ _).trans
      ((congr_arg₂ biprod.desc (f.comm i) (g.comm i)).trans (biprod.map_desc _ _ _ _).symm))

@[simp] lemma biprodObjDesc_hom {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    (biprodObjDesc f g).hom = biprod.desc f.hom g.hom := rfl

@[simp] lemma biprodObjDesc_natTrans_app {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) (i : I) :
    (biprodObjDesc f g).natTrans.app i = biprod.desc (f.natTrans.app i) (g.natTrans.app i) := rfl

/-- The first inclusion followed by the copairing `biprodObjDesc f g` is `f`. -/
@[reassoc (attr := simp)]
lemma biprodObjDesc_inl {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    (biprodBicone B D).inl ≫ biprodObjDesc f g = f :=
  hom_ext (biprod.inl_desc _ _)

/-- The second inclusion followed by the copairing `biprodObjDesc f g` is `g`. -/
@[reassoc (attr := simp)]
lemma biprodObjDesc_inr {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    (biprodBicone B D).inr ≫ biprodObjDesc f g = g :=
  hom_ext (biprod.inr_desc _ _)

/-- Mathlib's `biprod.desc f g` corresponds to `biprodObjDesc f g` under `biprodIsoBiprodObj`. -/
@[reassoc (attr := simp)]
lemma biprodIsoBiprodObj_hom_biprodObjDesc {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    (biprodIsoBiprodObj B D).hom ≫ biprodObjDesc f g = biprod.desc f g :=
  biprod.hom_ext' _ _
    ((inl_biprodIsoBiprodObj_hom_assoc B D _).trans ((biprodObjDesc_inl f g).trans
      (biprod.inl_desc f g).symm))
    ((inr_biprodIsoBiprodObj_hom_assoc B D _).trans ((biprodObjDesc_inr f g).trans
      (biprod.inr_desc f g).symm))

/-- Mathlib's `biprod.desc f g` is `biprodIsoBiprodObj` followed by `biprodObjDesc f g`. -/
lemma biprod_desc_eq {D : FilteredObject C I} (f : B ⟶ A) (g : D ⟶ A) :
    biprod.desc f g = (biprodIsoBiprodObj B D).hom ≫ biprodObjDesc f g :=
  (biprodIsoBiprodObj_hom_biprodObjDesc f g).symm

/-- The forgetful functor `Fil(𝒜) ⥤ 𝒜` preserves binary biproducts, being additive. -/
instance : PreservesBinaryBiproducts (forget (C := C) (I := I)) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Stacks 0122 (1): `Fil(𝒜)` is an additive category (preadditive with finite biproducts). -/
@[stacks 0122 "(1) `Fil(𝒜)` is additive: preadditive with finite biproducts"]
noncomputable instance hasFiniteBiproducts [HasZeroObject C] :
    HasFiniteBiproducts (FilteredObject C I) :=
  have : HasFiniteProducts (FilteredObject C I) := hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

end Biproducts

end CategoryTheory.FilteredObject
