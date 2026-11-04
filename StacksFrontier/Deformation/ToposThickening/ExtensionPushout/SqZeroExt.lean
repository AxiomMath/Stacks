module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.CategoryTheory.Abelian.CommSq
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SqZeroExt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Deformation.ToposThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ActionMapUnique
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.TensorSheafSections

/-!
# Pushout along a morphism of thickenings: the square-zero extension `T = O'₂ ⋉ I₁`

For a morphism of first order thickenings `h^♯ : O'₂ ⟶ O'₁` of a ringed topos, this file builds
the sheaf of rings `T = O'₂ ⋉ I₁`, the trivial square-zero extension of the second thickened
structure sheaf by the defining ideal of the first, and the map `q : T ⟶ O'₁`,
`(a, m) ↦ h^♯(a) - m`. It shows that `q` is locally surjective, so that restriction of scalars
along `q` is fully faithful, and identifies the sections killed by `q`.

See `StacksFrontier.Deformation.ToposThickening.ExtensionPushout` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v₂ u₂ t

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

namespace Deformation.ToposThickening

/-- Restriction along an identity acts as the identity on sections of a presheaf of modules. -/
private theorem presheafMap_id_apply {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w} R) {U : Cᵒᵖ} (x : M.obj U) : M.map (𝟙 U) x = x := by
  rw [← PresheafOfModules.presheaf_map_apply_coe, M.presheaf.map_id]
  rfl

/-- A module structure built from the four axioms that do not mention zero; over an additive
group the two remaining axioms follow by cancellation. -/
@[instance_reducible]
noncomputable def moduleOfAxioms {R M : Type t} [Ring R] [AddCommGroup M]
    (sm : R → M → M)
    (h₁ : ∀ (r : R) (x y : M), sm r (x + y) = sm r x + sm r y)
    (h₂ : ∀ (r s : R) (x : M), sm (r + s) x = sm r x + sm s x)
    (h₃ : ∀ (r s : R) (x : M), sm (r * s) x = sm r (sm s x))
    (h₄ : ∀ x : M, sm 1 x = x) : Module R M where
  smul := sm
  smul_add := h₁
  add_smul := h₂
  mul_smul := h₃
  one_smul := h₄
  smul_zero r := by
    change sm r 0 = 0
    exact (add_left_cancel (a := sm r 0) ((add_zero _).trans (by rw [← h₁ r 0 0, add_zero]))).symm
  zero_smul x := by
    change sm 0 x = 0
    exact (add_left_cancel (a := sm 0 x) ((add_zero _).trans (by rw [← h₂ 0 0 x, add_zero]))).symm

/-- Sections of a sheaf of commutative rings commute, read in the underlying sheaf of rings. -/
lemma mul_comm_sections {C : Type u₂} [Category.{v₂} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]
    (O : Sheaf J CommRingCat.{max v₂ u₂}) (U : Cᵒᵖ)
    (a b : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U) : a * b = b * a :=
  mul_comm (show O.obj.obj U from a) (show O.obj.obj U from b)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]

namespace MorphismOfFirstOrderThickenings

variable {i : RingedToposHom X Y} (D : MorphismOfFirstOrderThickenings i)

/-- A module over the base is a module over the structure sheaf of the second thickening,
through the structure map of that thickening. -/
@[instance_reducible]
noncomputable def sectionsModuleOverTwo
    (M : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (U : Y.Cᵒᵖ) :
    Module (D.O₂.obj.obj U) (M.val.obj U) :=
  (((SheafOfModules.restrictScalars D.ringMap₂).obj M).val.obj U).isModule

attribute [local instance] sectionsModuleOverTwo

/-- The action of the structure sheaf of the second thickening on a module over the base is the
action of the base through the structure map of the second thickening. -/
lemma sectionsModuleOverTwo_smul
    (M : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (U : Y.Cᵒᵖ)
    (a : D.O₂.obj.obj U) (m : M.val.obj U) : a • m = D.ringMap₂.hom.app U a • m := rfl

/-- Restriction of a section of the defining ideal of the first thickening, read in the module
of sections over the smaller object. -/
noncomputable def idealRestrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m : D.first.I.val.obj U) :
    D.first.I.val.obj V := D.first.I.val.map g m

/-- Restriction of ideal sections is the restriction map of the ideal. -/
lemma idealRestrict_eq {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m : D.first.I.val.obj U) :
    D.idealRestrict g m = D.first.I.val.map g m := rfl

/-- Restriction of ideal sections is additive. -/
lemma idealRestrict_add {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m m' : D.first.I.val.obj U) :
    D.idealRestrict g (m + m') = D.idealRestrict g m + D.idealRestrict g m' :=
  map_add (D.first.I.val.map g).hom m m'

/-- Restriction of ideal sections kills zero. -/
lemma idealRestrict_zero {U V : Y.Cᵒᵖ} (g : U ⟶ V) :
    D.idealRestrict g (0 : D.first.I.val.obj U) = 0 :=
  map_zero (D.first.I.val.map g).hom

/-- Restriction of ideal sections along an identity changes nothing. -/
lemma idealRestrict_id {U : Y.Cᵒᵖ} (m : D.first.I.val.obj U) :
    D.idealRestrict (𝟙 U) m = m :=
  presheafMap_id_apply D.first.I.val m

/-- Restriction of ideal sections is compatible with composition. -/
lemma idealRestrict_comp {U V W : Y.Cᵒᵖ} (g : U ⟶ V) (g' : V ⟶ W)
    (m : D.first.I.val.obj U) :
    D.idealRestrict (g ≫ g') m = D.idealRestrict g' (D.idealRestrict g m) :=
  PresheafOfModules.map_comp_apply D.first.I.val g g' m

/-- The action of the structure sheaf of the second thickening on the defining ideal of the
first restricts semilinearly. -/
lemma idealRestrict_smul {U V : Y.Cᵒᵖ} (g : U ⟶ V) (a : D.O₂.obj.obj U)
    (m : D.first.I.val.obj U) :
    D.idealRestrict g (a • m) = (D.O₂.obj.map g).hom a • D.idealRestrict g m :=
  (D.first.I.val.map_smul g (D.ringMap₂.hom.app U a) m).trans
    (congrArg (fun r => r • D.idealRestrict g m)
      (ConcreteCategory.congr_hom (D.ringMap₂.hom.naturality g) a).symm)

/-- The inclusion of the defining ideal of the first thickening commutes with restriction. -/
lemma inclOne_idealRestrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m : D.first.I.val.obj U) :
    D.inclOne V (D.idealRestrict g m) =
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g (D.inclOne U m) :=
  D.inclOne_naturality g m

/-- The ring of local sections of the trivial square-zero extension `T = O'₂ ⋉ I₁` of the
structure sheaf of the second thickening by the defining ideal of the first. -/
noncomputable def sqZeroSections (U : Y.Cᵒᵖ) : RingCat.{max v₂ u₂} :=
  RingCat.of (TrivSqZeroExt (D.O₂.obj.obj U) (D.first.I.val.obj U))

/-- The section of `T` with the given ring and ideal components. -/
noncomputable def sqZeroMk {U : Y.Cᵒᵖ} (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U) :
    D.sqZeroSections U := (a, m)

/-- The ring component of a section of `T`. -/
noncomputable def sqZeroFst {U : Y.Cᵒᵖ} (s : D.sqZeroSections U) : D.O₂.obj.obj U := s.1

/-- The ideal component of a section of `T`. -/
noncomputable def sqZeroSnd {U : Y.Cᵒᵖ} (s : D.sqZeroSections U) : D.first.I.val.obj U := s.2

/-- Two sections of `T` with the same components agree. -/
lemma sqZero_ext {U : Y.Cᵒᵖ} {s s' : D.sqZeroSections U} (h₁ : D.sqZeroFst s = D.sqZeroFst s')
    (h₂ : D.sqZeroSnd s = D.sqZeroSnd s') : s = s' :=
  TrivSqZeroExt.ext h₁ h₂

/-- The ring component of a section of `T` with prescribed components. -/
@[simp] lemma sqZeroFst_mk {U : Y.Cᵒᵖ} (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U) :
    D.sqZeroFst (D.sqZeroMk a m) = a := rfl

/-- The ideal component of a section of `T` with prescribed components. -/
@[simp] lemma sqZeroSnd_mk {U : Y.Cᵒᵖ} (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U) :
    D.sqZeroSnd (D.sqZeroMk a m) = m := rfl

/-- The ring component of zero. -/
@[simp] lemma sqZeroFst_zero {U : Y.Cᵒᵖ} : D.sqZeroFst (0 : D.sqZeroSections U) = 0 := rfl

/-- The ideal component of zero. -/
@[simp] lemma sqZeroSnd_zero {U : Y.Cᵒᵖ} : D.sqZeroSnd (0 : D.sqZeroSections U) = 0 := rfl

/-- The ring component of one. -/
@[simp] lemma sqZeroFst_one {U : Y.Cᵒᵖ} : D.sqZeroFst (1 : D.sqZeroSections U) = 1 := rfl

/-- The ideal component of one. -/
@[simp] lemma sqZeroSnd_one {U : Y.Cᵒᵖ} : D.sqZeroSnd (1 : D.sqZeroSections U) = 0 := rfl

/-- The ring component is additive. -/
@[simp] lemma sqZeroFst_add {U : Y.Cᵒᵖ} (s s' : D.sqZeroSections U) :
    D.sqZeroFst (s + s') = D.sqZeroFst s + D.sqZeroFst s' := rfl

/-- The ideal component is additive. -/
@[simp] lemma sqZeroSnd_add {U : Y.Cᵒᵖ} (s s' : D.sqZeroSections U) :
    D.sqZeroSnd (s + s') = D.sqZeroSnd s + D.sqZeroSnd s' := rfl

/-- The ring component is multiplicative. -/
@[simp] lemma sqZeroFst_mul {U : Y.Cᵒᵖ} (s s' : D.sqZeroSections U) :
    D.sqZeroFst (s * s') = D.sqZeroFst s * D.sqZeroFst s' := rfl

/-- The ideal component of a product in `T`, by the Leibniz rule of the square-zero
multiplication. -/
@[simp] lemma sqZeroSnd_mul {U : Y.Cᵒᵖ} (s s' : D.sqZeroSections U) :
    D.sqZeroSnd (s * s') =
      D.sqZeroFst s • D.sqZeroSnd s' + D.sqZeroFst s' • D.sqZeroSnd s := rfl

/-- The restriction homomorphism of `T`, acting on the two components separately. -/
noncomputable def sqZeroRestrictHom {U V : Y.Cᵒᵖ} (g : U ⟶ V) :
    TrivSqZeroExt (D.O₂.obj.obj U) (D.first.I.val.obj U) →+*
      TrivSqZeroExt (D.O₂.obj.obj V) (D.first.I.val.obj V) where
  toFun s := (((D.O₂.obj.map g).hom s.fst, D.idealRestrict g s.snd) : TrivSqZeroExt _ _)
  map_one' := TrivSqZeroExt.ext (map_one _) (D.idealRestrict_zero g)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (D.idealRestrict_zero g)
  map_add' s s' := TrivSqZeroExt.ext (map_add _ _ _) (D.idealRestrict_add g _ _)
  map_mul' s s' := TrivSqZeroExt.ext (map_mul _ _ _) (by
    rw [show (s * s').snd = s.fst • s'.snd + s'.fst • s.snd from rfl,
      D.idealRestrict_add, D.idealRestrict_smul, D.idealRestrict_smul]
    rfl)

/-- The restriction map of `T`. -/
noncomputable def sqZeroRestrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) :
    D.sqZeroSections U ⟶ D.sqZeroSections V :=
  RingCat.ofHom (D.sqZeroRestrictHom g)

/-- Restriction acts on the ring component through the restriction of `O'₂`. -/
@[simp] lemma sqZeroFst_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (s : D.sqZeroSections U) :
    D.sqZeroFst ((D.sqZeroRestrict g).hom s) = (D.O₂.obj.map g).hom (D.sqZeroFst s) := rfl

/-- Restriction acts on the ideal component through the restriction of `I₁`. -/
@[simp] lemma sqZeroSnd_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (s : D.sqZeroSections U) :
    D.sqZeroSnd ((D.sqZeroRestrict g).hom s) = D.idealRestrict g (D.sqZeroSnd s) := rfl

/-- The trivial square-zero extension `T = O'₂ ⋉ I₁`, as a presheaf of rings. -/
noncomputable def sqZeroPresheaf : Y.Cᵒᵖ ⥤ RingCat.{max v₂ u₂} where
  obj U := D.sqZeroSections U
  map g := D.sqZeroRestrict g
  map_id U := by
    refine RingCat.hom_ext (RingHom.ext fun s => D.sqZero_ext ?_ ?_)
    · rw [D.sqZeroFst_restrict]
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (D.sqZeroFst s)) (D.O₂.obj.map_id U)
    · rw [D.sqZeroSnd_restrict]
      exact D.idealRestrict_id (D.sqZeroSnd s)
  map_comp {U V W} g g' := by
    refine RingCat.hom_ext (RingHom.ext fun s => D.sqZero_ext ?_ ?_)
    · rw [D.sqZeroFst_restrict]
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (D.sqZeroFst s)) (D.O₂.obj.map_comp g g')
    · rw [D.sqZeroSnd_restrict]
      exact D.idealRestrict_comp g g' (D.sqZeroSnd s)

/-- The trivial square-zero extension of a sheaf of commutative rings by a sheaf of modules
satisfies the sheaf condition, since both of its components do. -/
lemma isSheaf_sqZeroPresheaf : Presheaf.IsSheaf Y.J D.sqZeroPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget Y.J _ (forget RingCat.{max v₂ u₂}),
    isSheaf_iff_isSheaf_of_type]
  have hO : Presieve.IsSheaf Y.J (D.O₂.obj ⋙ forget CommRingCat.{max v₂ u₂}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget Y.J _ (forget CommRingCat.{max v₂ u₂})]
    exact D.O₂.property
  have hI : Presieve.IsSheaf Y.J
      (D.first.I.val.presheaf ⋙ forget AddCommGrpCat.{max v₂ u₂}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget Y.J _ (forget AddCommGrpCat.{max v₂ u₂})]
    exact D.first.I.isSheaf
  intro Z S hS x hx
  obtain ⟨t₁, ht₁, ht₁'⟩ := hO S hS (fun _ f h => D.sqZeroFst (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg => congrArg D.sqZeroFst (hx g₁ g₂ h₁ h₂ hg))
  obtain ⟨t₂, ht₂, ht₂'⟩ := hI S hS (fun _ f h => D.sqZeroSnd (x f h))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hg => congrArg D.sqZeroSnd (hx g₁ g₂ h₁ h₂ hg))
  refine ⟨D.sqZeroMk t₁ t₂, fun V f h => ?_, fun y hy => ?_⟩
  · exact D.sqZero_ext (ht₁ f h) (ht₂ f h)
  · exact D.sqZero_ext (ht₁' _ fun _ f h => congrArg D.sqZeroFst (hy f h))
      (ht₂' _ fun _ f h => congrArg D.sqZeroSnd (hy f h))

/-- The trivial square-zero extension `T = O'₂ ⋉ I₁`, as a sheaf of rings. -/
noncomputable def sqZeroExt : Sheaf Y.J RingCat.{max v₂ u₂} where
  obj := D.sqZeroPresheaf
  property := D.isSheaf_sqZeroPresheaf

/-- The structure map `T ⟶ O'₁` on local sections: the image under `h^♯` of the ring component
minus the image in `O'₁` of the ideal component. It is a ring homomorphism because the defining
ideal of the first thickening is square zero. -/
noncomputable def sqZeroProjHom (U : Y.Cᵒᵖ) :
    TrivSqZeroExt (D.O₂.obj.obj U) (D.first.I.val.obj U) →+*
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U where
  toFun s := D.ringMapH.hom.app U s.fst - D.inclOne U s.snd
  map_one' := by
    rw [show ((1 : TrivSqZeroExt (D.O₂.obj.obj U) (D.first.I.val.obj U))).snd = 0 from rfl,
      show D.inclOne U 0 = 0 from map_zero (D.first.incl.val.app U).hom, sub_zero]
    exact map_one _
  map_zero' := by
    rw [show ((0 : TrivSqZeroExt (D.O₂.obj.obj U) (D.first.I.val.obj U))).snd = 0 from rfl,
      show D.inclOne U 0 = 0 from map_zero (D.first.incl.val.app U).hom, sub_zero]
    exact map_zero _
  map_add' s s' := by
    have hfst : D.ringMapH.hom.app U (s + s').fst =
        D.ringMapH.hom.app U s.fst + D.ringMapH.hom.app U s'.fst := map_add _ _ _
    have hsnd : D.inclOne U (s + s').snd =
        D.inclOne U s.snd + D.inclOne U s'.snd := D.inclOne_add U _ _
    have alg : ∀ x y a b a' b' : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U,
        x = a + a' → y = b + b' → x - y = a - b + (a' - b') := by
      intro x y a b a' b' hx hy
      rw [hx, hy]
      abel
    exact alg _ _ _ _ _ _ hfst hsnd
  map_mul' s s' := by
    have key (a : D.O₂.obj.obj U) (m : D.first.I.val.obj U) :
        D.inclOne U (a • m) = D.ringMapH.hom.app U a * D.inclOne U m := by
      rw [D.sectionsModuleOverTwo_smul D.first.I, ← D.structureRingMap_ringMapH_apply U a,
        D.inclOne_smul]
    have hfst : D.ringMapH.hom.app U (s * s').fst =
        D.ringMapH.hom.app U s.fst * D.ringMapH.hom.app U s'.fst := map_mul _ _ _
    have hsnd : D.inclOne U (s * s').snd =
        D.ringMapH.hom.app U s.fst * D.inclOne U s'.snd +
          D.ringMapH.hom.app U s'.fst * D.inclOne U s.snd :=
      (D.inclOne_add U (s.fst • s'.snd) (s'.fst • s.snd)).trans
        ((congrArg (fun t => t + D.inclOne U (s'.fst • s.snd)) (key s.fst s'.snd)).trans
          (congrArg (fun t => D.ringMapH.hom.app U s.fst * D.inclOne U s'.snd + t)
            (key s'.fst s.snd)))
    have hsq : D.inclOne U s.snd * D.inclOne U s'.snd = 0 := D.first.square_zero U _ _
    have hcomm : D.inclOne U s.snd * D.ringMapH.hom.app U s'.fst =
        D.ringMapH.hom.app U s'.fst * D.inclOne U s.snd := mul_comm_sections Y.O U _ _
    have alg : ∀ x y a b a' b' : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U,
        x = a * a' → y = a * b' + a' * b → b * b' = 0 → b * a' = a' * b →
        x - y = (a - b) * (a' - b') := by
      intro x y a b a' b' hx hy h₀ hc
      rw [hx, hy, sub_mul, mul_sub, mul_sub, h₀, hc]
      abel
    exact alg _ _ _ _ _ _ hfst hsnd hsq hcomm

/-- The structure map `q : T ⟶ O'₁` of the square-zero extension. -/
noncomputable def sqZeroProj : D.sqZeroExt ⟶ Stacks.SheafOfModules.Tensor.ringSheaf Y.O :=
  ObjectProperty.homMk
    { app U := RingCat.ofHom (D.sqZeroProjHom U)
      naturality := fun {U V} g => by
        refine RingCat.hom_ext (RingHom.ext fun s => ?_)
        have hnat : D.ringMapH.hom.app V ((D.O₂.obj.map g).hom (D.sqZeroFst s)) =
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g
              (D.ringMapH.hom.app U (D.sqZeroFst s)) :=
          ConcreteCategory.congr_hom (D.ringMapH.hom.naturality g) (D.sqZeroFst s)
        change D.ringMapH.hom.app V ((D.O₂.obj.map g).hom (D.sqZeroFst s)) -
            D.inclOne V (D.idealRestrict g (D.sqZeroSnd s)) =
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g
            (D.ringMapH.hom.app U (D.sqZeroFst s) - D.inclOne U (D.sqZeroSnd s))
        rw [map_sub, D.inclOne_idealRestrict, hnat] }

/-- The structure map of the square-zero extension, on local sections. -/
@[simp] lemma sqZeroProj_hom_app (U : Y.Cᵒᵖ) (s : D.sqZeroSections U) :
    D.sqZeroProj.hom.app U s =
      D.ringMapH.hom.app U (D.sqZeroFst s) - D.inclOne U (D.sqZeroSnd s) := rfl

/-- A section of the defining ideal of the first thickening is killed by the structure map of
that thickening. -/
lemma structureRingMap_inclOne (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) :
    (structureRingMap i).hom.app U (D.inclOne U m) = 0 :=
  (D.first.kernel U _).2 ⟨m, rfl⟩

/-- The structure map of the square-zero extension is locally surjective: a section of `O'₁`
maps into `O`, lifts locally to `O'₂`, and the difference lies in the defining ideal of the
first thickening. -/
lemma sqZeroProj_locallySurjective : Presheaf.IsLocallySurjective Y.J D.sqZeroProj.hom := by
  constructor
  intro U s
  refine Y.J.superset_covering ?_ (D.ringMap₂_locallySurjective.imageSieve_mem
    ((structureRingMap i).hom.app (Opposite.op U) s))
  rintro V f ⟨a, ha⟩
  change D.ringMap₂.hom.app (Opposite.op V) a =
    (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj.map f.op
      ((structureRingMap i).hom.app (Opposite.op U) s) at ha
  set s' : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f.op s with hs'
  have hnat : (structureRingMap i).hom.app (Opposite.op V) s' =
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj.map f.op
        ((structureRingMap i).hom.app (Opposite.op U) s) :=
    ConcreteCategory.congr_hom ((structureRingMap i).hom.naturality f.op) s
  have hzero : (structureRingMap i).hom.app (Opposite.op V)
      (s' - D.ringMapH.hom.app (Opposite.op V) a) = 0 := by
    rw [map_sub, hnat, D.structureRingMap_ringMapH_apply, ha, sub_self]
  obtain ⟨m, hm⟩ := (D.first.kernel (Opposite.op V) _).1 hzero
  have hm' : D.inclOne (Opposite.op V) m =
    s' - D.ringMapH.hom.app (Opposite.op V) a := hm
  refine ⟨D.sqZeroMk a (-m), ?_⟩
  have hneg : D.inclOne (Opposite.op V) (-m) = -D.inclOne (Opposite.op V) m :=
    map_neg (D.first.incl.val.app (Opposite.op V)).hom m
  change D.ringMapH.hom.app (Opposite.op V) a - D.inclOne (Opposite.op V) (-m) = s'
  rw [hneg, hm']
  abel

/-- The composite of `q` with the structure map of the first thickening reads off the ring
component of a section of `T`: the ideal component is killed by that structure map. -/
lemma structureRingMap_sqZeroProj (U : Y.Cᵒᵖ) (s : D.sqZeroSections U) :
    (structureRingMap i).hom.app U (D.sqZeroProj.hom.app U s) =
      D.fSharp₂.hom.app U (D.sqZeroFst s) :=
  have hsub : (structureRingMap i).hom.app U (D.sqZeroProj.hom.app U s) =
      (structureRingMap i).hom.app U (D.ringMapH.hom.app U (D.sqZeroFst s)) -
        (structureRingMap i).hom.app U (D.inclOne U (D.sqZeroSnd s)) := map_sub _ _ _
  have hmap : (structureRingMap i).hom.app U (D.ringMapH.hom.app U (D.sqZeroFst s)) =
      D.ringMap₂.hom.app U (D.sqZeroFst s) :=
    D.structureRingMap_ringMapH_apply U (D.sqZeroFst s)
  have hzero : (structureRingMap i).hom.app U (D.inclOne U (D.sqZeroSnd s)) = 0 :=
    D.structureRingMap_inclOne U (D.sqZeroSnd s)
  hsub.trans
    ((congrArg (fun t => t - (structureRingMap i).hom.app U (D.inclOne U (D.sqZeroSnd s)))
        hmap).trans
      ((congrArg (fun t => D.ringMap₂.hom.app U (D.sqZeroFst s) - t) hzero).trans (sub_zero _)))

/-- The section of `T` with zero ring component and ideal component `-m` is carried by `q` to
the image of `m` in `O'₁`. -/
lemma sqZeroProj_mk_zero_neg (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) :
    D.sqZeroProj.hom.app U (D.sqZeroMk 0 (-m)) = D.inclOne U m :=
  have hzero : D.ringMapH.hom.app U (0 : D.O₂.obj.obj U) = 0 := map_zero _
  have hneg : D.inclOne U (-m) = -D.inclOne U m := map_neg (D.first.incl.val.app U).hom m
  (congrArg (fun t => t - D.inclOne U (-m)) hzero).trans
    ((congrArg (fun t => (0 : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) - t)
        hneg).trans ((zero_sub _).trans (neg_neg _)))

/-- Restriction of scalars along `q` is fully faithful, since `q` is locally surjective. -/
noncomputable def sqZeroRestrictFullyFaithful :
    (SheafOfModules.restrictScalars.{max v₂ u₂} D.sqZeroProj).FullyFaithful :=
  letI := D.sqZeroProj_locallySurjective
  Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective.{max v₂ u₂} _

/-- A section of `T` killed by `q` has ring component in the defining ideal of the second
thickening, with ideal component its image under the induced map of defining ideals. -/
lemma exists_ideal_of_sqZeroProj_eq_zero (U : Y.Cᵒᵖ) (s : D.sqZeroSections U)
    (hs : D.sqZeroProj.hom.app U s = 0) :
    ∃ b : D.second.I.val.obj U,
      D.inclTwo U b = D.sqZeroFst s ∧ D.idealMap.val.app U b = D.sqZeroSnd s := by
  have heq : D.ringMapH.hom.app U (D.sqZeroFst s) = D.inclOne U (D.sqZeroSnd s) :=
    sub_eq_zero.1 ((D.sqZeroProj_hom_app U s).symm.trans hs)
  have hring : D.ringMap₂.hom.app U (D.sqZeroFst s) = 0 := by
    rw [← D.structureRingMap_ringMapH_apply U (D.sqZeroFst s), heq]
    exact D.structureRingMap_inclOne U (D.sqZeroSnd s)
  obtain ⟨b, hb⟩ := (D.second.kernel U _).1 hring
  have hb' : D.inclTwo U b = D.sqZeroFst s := hb
  refine ⟨b, hb', D.inclOne_injective U ?_⟩
  rw [D.inclOne_idealMap, hb', heq]

/-- Conversely, the section of `T` whose ring component is a section of the defining ideal of
the second thickening and whose ideal component is its image is killed by `q`. -/
lemma sqZeroProj_eq_zero_of_ideal (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) :
    D.sqZeroProj.hom.app U (D.sqZeroMk (D.inclTwo U b) (D.idealMap.val.app U b)) = 0 := by
  change D.ringMapH.hom.app U (D.inclTwo U b) - D.inclOne U (D.idealMap.val.app U b) = 0
  exact sub_eq_zero.2 (D.inclOne_idealMap U b).symm

end MorphismOfFirstOrderThickenings

end Deformation.ToposThickening

end
