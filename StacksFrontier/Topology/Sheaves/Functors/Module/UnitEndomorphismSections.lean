module

public import StacksFrontier.CategoryTheory.Monoidal.UnitEndomorphism
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackUnitEndomorphism

/-!
# Endomorphisms of the free sheaf of modules of rank one

An endomorphism `a` of `SheafOfModules.unit S`, the free sheaf of `S`-modules of rank one, is
multiplication by its value at `1`: `a.val.app X x = x • a.val.app X 1`. Hence composition of
endomorphisms multiplies their values at `1`, and for a continuous map of ringed sites with
morphism of sheaves of rings `φ`, the square expressing that an endomorphism `b` of `unit R` is
the pullback of an endomorphism `a` of `unit S` commutes exactly when `φ(a(1)) = b(1)`.

## Main definitions

* `Stacks.SheafOfModules.unitAutValue`: the value at `1` of an automorphism of `unit S`, as a
  unit of the ring of sections.
* `Stacks.SheafOfModules.negUnitAut`: the automorphism `-𝟙` of `SheafOfModules.unit S`.

## Main results

* `Stacks.SheafOfModules.unitHom_val_app_apply`: a morphism out of `unit S` is multiplication
  by its value at `1`.
* `Stacks.SheafOfModules.unitAut_autPow_val_app_one`: the value at `1` of the `n`-fold composite
  of an automorphism of `unit S` is the `n`-th power of its value at `1`.
* `Stacks.SheafOfModules.unitAut_val_app_one_congr`: equal automorphisms have equal values.
* `Stacks.SheafOfModules.unitAutValue_autPow`: the unit attached to the `n`-fold composite is the
  `n`-th power of the unit.
* `Stacks.SheafOfModules.comm_unitToPushforwardObjUnit_iff`: the pullback square for
  endomorphisms of the free sheaf of rank one commutes if and only if `φ(a(1)) = b(1)`.
* `RingedSpaceModuleAdjunction.pullbackUnitAut_eq_iff_val_app_one`: for a morphism of ringed
  spaces `f`, the pullback of `a` is `b` if and only if `f^♯` carries the value of `a` at `1` to
  the value of `b` at `1` on every open.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u₁ u₂ u

namespace Stacks.SheafOfModules

section Linearity

variable {C : Type u₁} [Category C] {J : GrothendieckTopology C} {S : Sheaf J RingCat.{u}}

/-- A morphism out of the free sheaf of modules of rank one is multiplication by its value
at `1`. -/
theorem unitHom_val_app_apply {M : _root_.SheafOfModules.{u} S}
    (a : _root_.SheafOfModules.unit S ⟶ M) (X : Cᵒᵖ) (x : S.obj.obj X) :
    a.val.app X x = x • a.val.app X (1 : S.obj.obj X) :=
  (congrArg (a.val.app X) (mul_one x).symm).trans
    (map_smul (a.val.app X).hom x (1 : S.obj.obj X))

/-- If an automorphism of the free sheaf of rank one has value `r` at `1`, then its `n`-fold
composite has value `r ^ n` at `1`. -/
theorem unitAut_autPow_val_app_one
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) (X : Cᵒᵖ)
    (r : S.obj.obj X) (ha : a.hom.val.app X (1 : S.obj.obj X) = r) (n : ℕ) :
    (a.autPow n).hom.val.app X (1 : S.obj.obj X) = r ^ n := by
  induction n with
  | zero => rw [Iso.autPow_zero, pow_zero]; rfl
  | succ n ih =>
      rw [Iso.autPow_succ, pow_succ]
      exact (unitHom_val_app_apply a.hom X _).trans (congrArg₂ (· • ·) ih ha)

/-- Equal automorphisms of the free sheaf of rank one have equal values at `1`. -/
theorem unitAut_val_app_one_congr
    {a b : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S} (h : a = b) (X : Cᵒᵖ) :
    a.hom.val.app X (1 : S.obj.obj X) = b.hom.val.app X (1 : S.obj.obj X) := by
  rw [h]

/-- The value at `1` of an automorphism of the free sheaf of rank one, as a unit of the ring
of sections whose inverse is the value at `1` of the inverse automorphism. -/
def unitAutValue (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) (X : Cᵒᵖ) :
    (S.obj.obj X)ˣ where
  val := a.hom.val.app X (1 : S.obj.obj X)
  inv := a.inv.val.app X (1 : S.obj.obj X)
  val_inv := (unitHom_val_app_apply a.inv X (a.hom.val.app X (1 : S.obj.obj X))).symm.trans <|
    congrArg (fun e : _root_.SheafOfModules.unit S ⟶ _root_.SheafOfModules.unit S =>
      e.val.app X (1 : S.obj.obj X)) a.hom_inv_id
  inv_val := (unitHom_val_app_apply a.hom X (a.inv.val.app X (1 : S.obj.obj X))).symm.trans <|
    congrArg (fun e : _root_.SheafOfModules.unit S ⟶ _root_.SheafOfModules.unit S =>
      e.val.app X (1 : S.obj.obj X)) a.inv_hom_id

/-- The underlying element of `Stacks.SheafOfModules.unitAutValue a X` is the value of `a`
at `1`. -/
@[simp]
theorem unitAutValue_val (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S)
    (X : Cᵒᵖ) :
    (unitAutValue a X : S.obj.obj X) = a.hom.val.app X (1 : S.obj.obj X) :=
  rfl

/-- `Stacks.SheafOfModules.unitAutValue` carries the `n`-fold composite of an automorphism to the
`n`-th power of its unit. -/
theorem unitAutValue_autPow
    (a : _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S) (X : Cᵒᵖ) (n : ℕ) :
    unitAutValue (a.autPow n) X = unitAutValue a X ^ n :=
  Units.ext ((unitAut_autPow_val_app_one a X _ rfl n).trans
    (Units.val_pow_eq_pow_val (unitAutValue a X) n).symm)

/-- The automorphism `-𝟙` of the free sheaf of modules of rank one. -/
def negUnitAut (S : Sheaf J RingCat.{u}) :
    _root_.SheafOfModules.unit S ≅ _root_.SheafOfModules.unit S where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The value of `Stacks.SheafOfModules.negUnitAut` at `1` is `-1`. -/
theorem negUnitAut_hom_val_app_one (X : Cᵒᵖ) :
    (negUnitAut S).hom.val.app X (1 : S.obj.obj X) = (-1 : S.obj.obj X) :=
  rfl

end Linearity

section Criterion

variable {C : Type u₁} [Category C] {D : Type u₂} [Category D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [F.IsContinuous J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The square `a ≫ unitToPushforwardObjUnit φ = unitToPushforwardObjUnit φ ≫ pushforward φ b`
commutes if and only if `φ` carries the value of `a` at `1` to the value of `b` at `1` on every
object. -/
theorem comm_unitToPushforwardObjUnit_iff
    (a : _root_.SheafOfModules.unit S ⟶ _root_.SheafOfModules.unit S)
    (b : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R) :
    a ≫ _root_.SheafOfModules.unitToPushforwardObjUnit φ =
        _root_.SheafOfModules.unitToPushforwardObjUnit φ ≫
          (_root_.SheafOfModules.pushforward.{u} φ).map b ↔
      ∀ X : Cᵒᵖ, φ.hom.app X (a.val.app X (1 : S.obj.obj X)) =
        b.val.app (F.op.obj X) (1 : R.obj.obj (F.op.obj X)) := by
  have hone : ∀ X : Cᵒᵖ, φ.hom.app X (1 : S.obj.obj X) = (1 : R.obj.obj (F.op.obj X)) :=
    fun _ ↦ map_one _
  refine ⟨fun h X ↦ (congrArg (fun m => m.val.app X (1 : S.obj.obj X)) h).trans
    (congrArg (b.val.app (F.op.obj X)) (hone X)), fun h ↦ ?_⟩
  refine (_root_.SheafOfModules.unitHomEquiv _).injective ?_
  ext X
  exact (h X).trans (congrArg (b.val.app (F.op.obj X)) (hone X).symm)

end Criterion

end Stacks.SheafOfModules

namespace RingedSpaceModuleAdjunction

open AlgebraicGeometry TopologicalSpace

/-- The pullback along `f` of an automorphism `a` of the structure sheaf of `Y` is `b` if and
only if, on every open, `f^♯` carries the value of `a` at `1` to the value of `b` at `1`. -/
theorem pullbackUnitAut_eq_iff_val_app_one {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (a : SheafOfModules.unit (structureSheafRing Y) ≅ SheafOfModules.unit (structureSheafRing Y))
    (b : SheafOfModules.unit (structureSheafRing X) ≅ SheafOfModules.unit (structureSheafRing X)) :
    pullbackUnitAut f a = b ↔
      ∀ U : (Opens Y.carrier)ᵒᵖ,
        (structureSheafHom f).hom.app U
            (a.hom.val.app U (1 : (structureSheafRing Y).obj.obj U)) =
          b.hom.val.app ((opensMap f).op.obj U)
            (1 : (structureSheafRing X).obj.obj ((opensMap f).op.obj U)) :=
  (pullbackUnitAut_eq_iff f a b).trans
    (Stacks.SheafOfModules.comm_unitToPushforwardObjUnit_iff _ a.hom b.hom)

end RingedSpaceModuleAdjunction

end
