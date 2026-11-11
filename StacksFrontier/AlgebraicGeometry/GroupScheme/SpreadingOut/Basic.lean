module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Models of a group object along a monoidal functor

Let `F : C ⥤ E` be a monoidal functor between cartesian monoidal categories, let `A` be a group
object of `E` and let `e : F.obj X ≅ A`. Three morphisms `m : X ⊗ X ⟶ X`, `u : 𝟙_ C ⟶ X` and
`i : X ⟶ X` of `C` are *models* of the multiplication, unit and inverse of `A` along `F` and `e`
when their images under `F`, read through `e` and the monoidal structure of `F`, are those of `A`.
Such morphisms need not make `X` a group object; but the group axioms for them hold after
applying `F`, and they are transported to every other monoidal functor through which `F`
factors up to isomorphism.

This is the categorical half of spreading out a group scheme over a limit of schemes: there `F`
is base change from a stage to the limit, the models are obtained by descending morphisms, and
the axioms, which hold after `F`, hold after base change to a later stage.

## Main definitions

* `CategoryTheory.IsMulModel`, `CategoryTheory.IsOneModel`, `CategoryTheory.IsInvModel`: the
  three model conditions.
* `CategoryTheory.grpObjOfMap`: the group object structure on `G.obj X` induced by morphisms `m`,
  `u`, `i` whose group axioms hold after applying the monoidal functor `G`.

## Main results

* `CategoryTheory.IsMulModel.map_mul_assoc` and its companions: the group axioms of models hold
  after applying `F`.
* `CategoryTheory.IsMulModel.comp`, `CategoryTheory.IsOneModel.comp`,
  `CategoryTheory.IsInvModel.comp`: models along `F` are models along `F'` for every
  factorisation `G ⋙ F' ≅ F`.
* `CategoryTheory.isMonHom_of_isMulModel`: if the multiplication and unit of a group object `Y`
  are models along `F` and `e`, then `e` is a homomorphism from the group object
  `F.mapGrp.obj Y`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open Functor.LaxMonoidal

/-- The tensor structure morphism of a lax monoidal functor. -/
local notation "μ'" => Functor.LaxMonoidal.μ
/-- The unit structure morphism of a lax monoidal functor. -/
local notation "ε'" => Functor.LaxMonoidal.ε
/-- The inverse tensor structure morphism of an oplax monoidal functor. -/
local notation "δ'" => Functor.OplaxMonoidal.δ
/-- The inverse unit structure morphism of an oplax monoidal functor. -/
local notation "η'" => Functor.OplaxMonoidal.η

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]

section Cartesian

/-- Two morphisms into `F.obj (X ⊗ Y)` agree if they agree after the images of the two
projections, for a monoidal functor `F` between cartesian monoidal categories. -/
lemma hom_ext_map_tensorObj (F : C ⥤ E) [F.Monoidal] {Z : E} {X Y : C} {f g : Z ⟶ F.obj (X ⊗ Y)}
    (h₁ : f ≫ F.map (fst X Y) = g ≫ F.map (fst X Y))
    (h₂ : f ≫ F.map (snd X Y) = g ≫ F.map (snd X Y)) : f = g := by
  have : IsIso (δ' F X Y) := (Functor.Monoidal.μIso F X Y).isIso_inv
  rw [← cancel_mono (δ' F X Y)]
  ext
  · rw [Category.assoc, Category.assoc, ← Functor.Monoidal.μ_fst F, Functor.Monoidal.δ_μ_assoc,
      h₁]
  · rw [Category.assoc, Category.assoc, ← Functor.Monoidal.μ_snd F, Functor.Monoidal.δ_μ_assoc,
      h₂]

/-- A monoidal functor between braided cartesian monoidal categories is compatible with the
braidings. -/
lemma μ_map_braiding_hom (F : C ⥤ E) [F.Monoidal] [BraidedCategory C] [BraidedCategory E]
    (X Y : C) : μ' F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ' F Y X := by
  apply hom_ext_map_tensorObj F
  · rw [Category.assoc, Category.assoc, ← F.map_comp, braiding_hom_fst, Functor.Monoidal.μ_snd,
      Functor.Monoidal.μ_fst, braiding_hom_fst]
  · rw [Category.assoc, Category.assoc, ← F.map_comp, braiding_hom_snd, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd, braiding_hom_snd]

end Cartesian

section Model

variable (F : C ⥤ E) [F.Monoidal] {X : C} {A : E} (e : F.obj X ≅ A)

/-- The morphism `m : X ⊗ X ⟶ X` is a model of the multiplication of the monoid object `A` along
the monoidal functor `F` and the isomorphism `e : F.obj X ≅ A`. -/
def IsMulModel [MonObj A] (m : X ⊗ X ⟶ X) : Prop :=
  μ' F X X ≫ F.map m ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[A]

/-- The morphism `u : 𝟙_ C ⟶ X` is a model of the unit of the monoid object `A` along the
monoidal functor `F` and the isomorphism `e : F.obj X ≅ A`. -/
def IsOneModel [MonObj A] (u : 𝟙_ C ⟶ X) : Prop :=
  ε' F ≫ F.map u ≫ e.hom = η[A]

/-- The morphism `i : X ⟶ X` is a model of the inverse of the group object `A` along the functor
`F` and the isomorphism `e : F.obj X ≅ A`. -/
def IsInvModel [GrpObj A] (i : X ⟶ X) : Prop :=
  F.map i ≫ e.hom = e.hom ≫ ι[A]

variable {F e}

/-- A model of the multiplication, solved for its image under `F`. -/
lemma IsMulModel.μ_map [MonObj A] {m : X ⊗ X ⟶ X} (h : IsMulModel F e m) :
    μ' F X X ≫ F.map m = (e.hom ⊗ₘ e.hom) ≫ μ[A] ≫ e.inv := by
  have h' : μ' F X X ≫ F.map m ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[A] := h
  rw [← reassoc_of% h']
  simp

/-- A model of the unit, solved for its image under `F`. -/
lemma IsOneModel.ε_map [MonObj A] {u : 𝟙_ C ⟶ X} (h : IsOneModel F e u) :
    ε' F ≫ F.map u = η[A] ≫ e.inv := by
  have h' : ε' F ≫ F.map u ≫ e.hom = η[A] := h
  rw [← reassoc_of% h']
  simp

/-- The image under `F` of a model of the multiplication followed by its unit. -/
lemma IsMulModel.map_one_mul [MonObj A] {m : X ⊗ X ⟶ X} {u : 𝟙_ C ⟶ X}
    (hm : IsMulModel F e m) (hu : IsOneModel F e u) :
    F.map (u ▷ X ≫ m) = F.map (λ_ X).hom := by
  let := MonObj.ofIso e.symm
  have hm' : μ' F X X ≫ F.map m = μ[F.obj X] := hm.μ_map
  have hu' : ε' F ≫ F.map u = η[F.obj X] := hu.ε_map
  have : IsIso (ε' F) := (Functor.Monoidal.εIso F).isIso_hom
  have : IsIso (μ' F (𝟙_ C) X) := (Functor.Monoidal.μIso F _ _).isIso_hom
  rw [← cancel_epi (ε' F ▷ F.obj X ≫ μ' F (𝟙_ C) X)]
  calc (ε' F ▷ F.obj X ≫ μ' F (𝟙_ C) X) ≫ F.map (u ▷ X ≫ m)
      = η[F.obj X] ▷ F.obj X ≫ μ[F.obj X] := by
        rw [F.map_comp, Category.assoc, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc, hu',
          hm']
    _ = (λ_ (F.obj X)).hom := MonObj.one_mul _
    _ = (ε' F ▷ F.obj X ≫ μ' F (𝟙_ C) X) ≫ F.map (λ_ X).hom := by
        rw [Category.assoc, ← left_unitality]

/-- The image under `F` of a model of the multiplication preceded by its unit on the right. -/
lemma IsMulModel.map_mul_one [MonObj A] {m : X ⊗ X ⟶ X} {u : 𝟙_ C ⟶ X}
    (hm : IsMulModel F e m) (hu : IsOneModel F e u) :
    F.map (X ◁ u ≫ m) = F.map (ρ_ X).hom := by
  let := MonObj.ofIso e.symm
  have hm' : μ' F X X ≫ F.map m = μ[F.obj X] := hm.μ_map
  have hu' : ε' F ≫ F.map u = η[F.obj X] := hu.ε_map
  have : IsIso (ε' F) := (Functor.Monoidal.εIso F).isIso_hom
  have : IsIso (μ' F X (𝟙_ C)) := (Functor.Monoidal.μIso F _ _).isIso_hom
  rw [← cancel_epi (F.obj X ◁ ε' F ≫ μ' F X (𝟙_ C))]
  calc (F.obj X ◁ ε' F ≫ μ' F X (𝟙_ C)) ≫ F.map (X ◁ u ≫ m)
      = F.obj X ◁ η[F.obj X] ≫ μ[F.obj X] := by
        rw [F.map_comp, Category.assoc, ← μ_natural_right_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, hu', hm']
    _ = (ρ_ (F.obj X)).hom := MonObj.mul_one _
    _ = (F.obj X ◁ ε' F ≫ μ' F X (𝟙_ C)) ≫ F.map (ρ_ X).hom := by
        rw [Category.assoc, ← right_unitality]

/-- The image under `F` of the associativity of a model of the multiplication. -/
lemma IsMulModel.map_mul_assoc [MonObj A] {m : X ⊗ X ⟶ X} (hm : IsMulModel F e m) :
    F.map (m ▷ X ≫ m) = F.map ((α_ X X X).hom ≫ X ◁ m ≫ m) := by
  let := MonObj.ofIso e.symm
  have hm' : μ' F X X ≫ F.map m = μ[F.obj X] := hm.μ_map
  have : IsIso (μ' F X X) := (Functor.Monoidal.μIso F _ _).isIso_hom
  have : IsIso (μ' F (X ⊗ X) X) := (Functor.Monoidal.μIso F _ _).isIso_hom
  rw [← cancel_epi (μ' F X X ▷ F.obj X ≫ μ' F (X ⊗ X) X)]
  calc (μ' F X X ▷ F.obj X ≫ μ' F (X ⊗ X) X) ≫ F.map (m ▷ X ≫ m)
      = μ[F.obj X] ▷ F.obj X ≫ μ[F.obj X] := by
        rw [F.map_comp, Category.assoc, ← μ_natural_left_assoc, ← comp_whiskerRight_assoc]
        simp only [hm']
    _ = (α_ _ _ _).hom ≫ F.obj X ◁ μ[F.obj X] ≫ μ[F.obj X] := MonObj.mul_assoc _
    _ = (μ' F X X ▷ F.obj X ≫ μ' F (X ⊗ X) X) ≫ F.map ((α_ X X X).hom ≫ X ◁ m ≫ m) := by
        rw [F.map_comp, F.map_comp, Category.assoc, associativity_assoc, ← μ_natural_right_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc]
        simp only [hm']

/-- The image under `F` of the commutativity of a model of the multiplication of a commutative
monoid object. -/
lemma IsMulModel.map_mul_comm [BraidedCategory C] [BraidedCategory E] [MonObj A]
    [IsCommMonObj A] {m : X ⊗ X ⟶ X} (hm : IsMulModel F e m) :
    F.map ((β_ X X).hom ≫ m) = F.map m := by
  have : IsIso (μ' F X X) := (Functor.Monoidal.μIso F X X).isIso_hom
  rw [← cancel_epi (μ' F X X), F.map_comp, reassoc_of% (μ_map_braiding_hom F X X), hm.μ_map,
    ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

/-- The image under `F` of the left inverse law of models of the multiplication, unit and
inverse. -/
lemma IsMulModel.map_left_inv [GrpObj A] {m : X ⊗ X ⟶ X} {u : 𝟙_ C ⟶ X} {i : X ⟶ X}
    (hm : IsMulModel F e m) (hu : IsOneModel F e u) (hi : IsInvModel F e i) :
    F.map (lift i (𝟙 X) ≫ m) = F.map (toUnit X ≫ u) := by
  calc F.map (lift i (𝟙 X) ≫ m) = lift (F.map i) (𝟙 _) ≫ μ' F X X ≫ F.map m := by
        rw [F.map_comp, ← Functor.Monoidal.lift_μ, F.map_id, Category.assoc]
    _ = e.hom ≫ (lift ι[A] (𝟙 A) ≫ μ[A]) ≫ e.inv := by
        rw [hm.μ_map, lift_map_assoc, hi]
        simp
    _ = toUnit _ ≫ η[A] ≫ e.inv := by
        rw [GrpObj.left_inv]
        simp
    _ = F.map (toUnit X ≫ u) := by
        rw [F.map_comp, ← Functor.Monoidal.toUnit_ε_assoc, hu.ε_map]

/-- The image under `F` of the right inverse law of models of the multiplication, unit and
inverse. -/
lemma IsMulModel.map_right_inv [GrpObj A] {m : X ⊗ X ⟶ X} {u : 𝟙_ C ⟶ X} {i : X ⟶ X}
    (hm : IsMulModel F e m) (hu : IsOneModel F e u) (hi : IsInvModel F e i) :
    F.map (lift (𝟙 X) i ≫ m) = F.map (toUnit X ≫ u) := by
  calc F.map (lift (𝟙 X) i ≫ m) = lift (𝟙 _) (F.map i) ≫ μ' F X X ≫ F.map m := by
        rw [F.map_comp, ← Functor.Monoidal.lift_μ, F.map_id, Category.assoc]
    _ = e.hom ≫ (lift (𝟙 A) ι[A] ≫ μ[A]) ≫ e.inv := by
        rw [hm.μ_map, lift_map_assoc, hi]
        simp
    _ = toUnit _ ≫ η[A] ≫ e.inv := by
        rw [GrpObj.right_inv]
        simp
    _ = F.map (toUnit X ≫ u) := by
        rw [F.map_comp, ← Functor.Monoidal.toUnit_ε_assoc, hu.ε_map]

end Model

/-! ### The group object induced by morphisms satisfying the axioms after a functor -/

section OfMap

variable (G : C ⥤ D) [G.Monoidal] {X : C} (m : X ⊗ X ⟶ X) (u : 𝟙_ C ⟶ X) (i : X ⟶ X)

/-- Morphisms `m`, `u`, `i` of `C` whose group axioms hold after applying the monoidal functor
`G` induce a group object structure on `G.obj X`, with multiplication `μ ≫ G.map m`, unit
`ε ≫ G.map u` and inverse `G.map i`. -/
abbrev grpObjOfMap (one_mul : G.map (u ▷ X ≫ m) = G.map (λ_ X).hom)
    (mul_one : G.map (X ◁ u ≫ m) = G.map (ρ_ X).hom)
    (mul_assoc : G.map (m ▷ X ≫ m) = G.map ((α_ X X X).hom ≫ X ◁ m ≫ m))
    (left_inv : G.map (lift i (𝟙 X) ≫ m) = G.map (toUnit X ≫ u))
    (right_inv : G.map (lift (𝟙 X) i ≫ m) = G.map (toUnit X ≫ u)) : GrpObj (G.obj X) where
  one := ε' G ≫ G.map u
  mul := μ' G X X ≫ G.map m
  inv := G.map i
  one_mul := by
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← G.map_comp, one_mul,
      left_unitality]
  mul_one := by
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc, ← G.map_comp,
      mul_one, right_unitality]
  mul_assoc := by
    rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← G.map_comp, mul_assoc,
      G.map_comp, G.map_comp, associativity_assoc, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, μ_natural_right_assoc]
  left_inv := by
    rw [← G.map_id, ← Category.assoc, Functor.Monoidal.lift_μ, ← G.map_comp, left_inv,
      G.map_comp, ← Category.assoc, Functor.Monoidal.toUnit_ε]
  right_inv := by
    rw [← G.map_id, ← Category.assoc, Functor.Monoidal.lift_μ, ← G.map_comp, right_inv,
      G.map_comp, ← Category.assoc, Functor.Monoidal.toUnit_ε]

/-- If moreover the commutativity of `m` holds after applying the braided functor `G`, the group
object `CategoryTheory.grpObjOfMap` is commutative. -/
lemma isCommMonObj_grpObjOfMap [BraidedCategory C] [BraidedCategory D]
    (one_mul : G.map (u ▷ X ≫ m) = G.map (λ_ X).hom)
    (mul_one : G.map (X ◁ u ≫ m) = G.map (ρ_ X).hom)
    (mul_assoc : G.map (m ▷ X ≫ m) = G.map ((α_ X X X).hom ≫ X ◁ m ≫ m))
    (left_inv : G.map (lift i (𝟙 X) ≫ m) = G.map (toUnit X ≫ u))
    (right_inv : G.map (lift (𝟙 X) i ≫ m) = G.map (toUnit X ≫ u))
    (mul_comm : G.map ((β_ X X).hom ≫ m) = G.map m) :
    letI := grpObjOfMap G m u i one_mul mul_one mul_assoc left_inv right_inv
    IsCommMonObj (G.obj X) := by
  let := grpObjOfMap G m u i one_mul mul_one mul_assoc left_inv right_inv
  exact ⟨by
    change (β_ _ _).hom ≫ μ' G X X ≫ G.map m = μ' G X X ≫ G.map m
    rw [← reassoc_of% (μ_map_braiding_hom G X X), ← G.map_comp, mul_comm]⟩

end OfMap

/-! ### Transport of models along a factorisation of the functor -/

section Comp

variable {G : C ⥤ D} [G.Monoidal] {F' : D ⥤ E} [F'.Monoidal] {F : C ⥤ E} [F.Monoidal]
  (τ : G ⋙ F' ≅ F)

/-- A natural isomorphism `G ⋙ F' ≅ F` of monoidal functors into a cartesian monoidal category is
compatible with the tensor structure morphisms. -/
lemma μ_map_μ_app_hom (X Y : C) :
    μ' F' (G.obj X) (G.obj Y) ≫ F'.map (μ' G X Y) ≫ τ.hom.app (X ⊗ Y) =
      (τ.hom.app X ⊗ₘ τ.hom.app Y) ≫ μ' F X Y := by
  apply hom_ext_map_tensorObj F
  · have hn : F'.map (G.map (fst X Y)) ≫ τ.hom.app X = τ.hom.app (X ⊗ Y) ≫ F.map (fst X Y) :=
      τ.hom.naturality (fst X Y)
    rw [Category.assoc, Category.assoc, ← hn, ← F'.map_comp_assoc, Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_fst_assoc, Category.assoc, Functor.Monoidal.μ_fst, tensorHom_fst]
    rfl
  · have hn : F'.map (G.map (snd X Y)) ≫ τ.hom.app Y = τ.hom.app (X ⊗ Y) ≫ F.map (snd X Y) :=
      τ.hom.naturality (snd X Y)
    rw [Category.assoc, Category.assoc, ← hn, ← F'.map_comp_assoc, Functor.Monoidal.μ_snd,
      Functor.Monoidal.μ_snd_assoc, Category.assoc, Functor.Monoidal.μ_snd, tensorHom_snd]
    rfl

/-- A natural isomorphism `G ⋙ F' ≅ F` of monoidal functors into a cartesian monoidal category is
compatible with the unit structure morphisms. -/
lemma ε_map_ε_app_hom : ε' F' ≫ F'.map (ε' G) ≫ τ.hom.app (𝟙_ C) = ε' F := by
  have : IsIso (η' F) := (Functor.Monoidal.εIso F).isIso_inv
  rw [← cancel_mono (η' F)]
  exact toUnit_unique _ _

variable {X : C} {A : E} {e : F.obj X ≅ A}

/-- A model of the multiplication along `F` gives one along `F'`, for `G ⋙ F' ≅ F`. -/
lemma IsMulModel.comp [MonObj A] {m : X ⊗ X ⟶ X} (h : IsMulModel F e m) :
    IsMulModel F' (τ.app X ≪≫ e) (μ' G X X ≫ G.map m) := by
  have hn : F'.map (G.map m) ≫ τ.hom.app X = τ.hom.app (X ⊗ X) ≫ F.map m := τ.hom.naturality m
  unfold IsMulModel at h ⊢
  rw [Iso.trans_hom, Iso.app_hom, F'.map_comp, Category.assoc, reassoc_of% hn,
    reassoc_of% (μ_map_μ_app_hom τ X X), h, tensorHom_comp_tensorHom_assoc]

/-- A model of the unit along `F` gives one along `F'`, for `G ⋙ F' ≅ F`. -/
lemma IsOneModel.comp [MonObj A] {u : 𝟙_ C ⟶ X} (h : IsOneModel F e u) :
    IsOneModel F' (τ.app X ≪≫ e) (ε' G ≫ G.map u) := by
  have hn : F'.map (G.map u) ≫ τ.hom.app X = τ.hom.app (𝟙_ C) ≫ F.map u := τ.hom.naturality u
  unfold IsOneModel at h ⊢
  rw [Iso.trans_hom, Iso.app_hom, F'.map_comp, Category.assoc, reassoc_of% hn,
    reassoc_of% (ε_map_ε_app_hom τ), h]

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [G.Monoidal] [F'.Monoidal]
  [F.Monoidal] in
/-- A model of the inverse along `F` gives one along `F'`, for `G ⋙ F' ≅ F`. -/
lemma IsInvModel.comp [GrpObj A] {i : X ⟶ X} (h : IsInvModel F e i) :
    IsInvModel F' (τ.app X ≪≫ e) (G.map i) := by
  have hn : F'.map (G.map i) ≫ τ.hom.app X = τ.hom.app X ≫ F.map i := τ.hom.naturality i
  unfold IsInvModel at h ⊢
  rw [Iso.trans_hom, Iso.app_hom, reassoc_of% hn, h, Category.assoc]

/-- A morphism `g : G.obj (X ⊗ X) ⟶ G.obj X` whose image under `F'` is the multiplication of `A`
up to `τ` and `e` gives a model `μ ≫ g` of the multiplication along `F'`. -/
lemma isMulModel_of_map [MonObj A] {g : G.obj (X ⊗ X) ⟶ G.obj X}
    (h : F'.map g ≫ τ.hom.app X ≫ e.hom =
      τ.hom.app (X ⊗ X) ≫ δ' F X X ≫ (e.hom ⊗ₘ e.hom) ≫ μ[A]) :
    IsMulModel F' (τ.app X ≪≫ e) (μ' G X X ≫ g) := by
  unfold IsMulModel
  rw [Iso.trans_hom, Iso.app_hom, F'.map_comp, Category.assoc, h,
    reassoc_of% (μ_map_μ_app_hom τ X X), Functor.Monoidal.μ_δ_assoc,
    tensorHom_comp_tensorHom_assoc]

/-- A morphism `g : G.obj (𝟙_ C) ⟶ G.obj X` whose image under `F'` is the unit of `A` up to `τ`
and `e` gives a model `ε ≫ g` of the unit along `F'`. -/
lemma isOneModel_of_map [MonObj A] {g : G.obj (𝟙_ C) ⟶ G.obj X}
    (h : F'.map g ≫ τ.hom.app X ≫ e.hom = τ.hom.app (𝟙_ C) ≫ η' F ≫ η[A]) :
    IsOneModel F' (τ.app X ≪≫ e) (ε' G ≫ g) := by
  unfold IsOneModel
  rw [Iso.trans_hom, Iso.app_hom, F'.map_comp, Category.assoc, h,
    reassoc_of% (ε_map_ε_app_hom τ), Functor.Monoidal.ε_η_assoc]

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [G.Monoidal] [F'.Monoidal]
  [F.Monoidal] in
/-- A morphism `g : G.obj X ⟶ G.obj X` whose image under `F'` is the inverse of `A` up to `τ`
and `e` is a model of the inverse along `F'`. -/
lemma isInvModel_of_map [GrpObj A] {g : G.obj X ⟶ G.obj X}
    (h : F'.map g ≫ τ.hom.app X ≫ e.hom = (τ.hom.app X ≫ e.hom) ≫ ι[A]) :
    IsInvModel F' (τ.app X ≪≫ e) g := by
  unfold IsInvModel
  rw [Iso.trans_hom, Iso.app_hom, h, Category.assoc]

end Comp

/-- If the multiplication and the unit of a group object `Y` are models of those of `A` along `F`
and `e`, then `e` is a homomorphism from the group object `F.mapGrp.obj Y` to `A`. -/
lemma isMonHom_of_isMulModel {F : C ⥤ E} [F.Monoidal] (Y : Grp C) {A : E} [GrpObj A]
    {e : (F.mapGrp.obj Y).X ≅ A} (hm : IsMulModel F e μ[Y.X]) (hu : IsOneModel F e η[Y.X]) :
    IsMonHom e.hom where
  one_hom := (Category.assoc _ _ _).trans hu
  mul_hom := (Category.assoc _ _ _).trans hm

end CategoryTheory
