module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Bijectivity of an extended map, read through a model over isomorphic rings

Let `φ : A →+* A'` be a ring map, `M` an `A`-module, `P` an `A'`-module and `u : M ⟶ P` an
`A`-linear map (with `P` viewed over `A` through `φ`).  Its extension of scalars is the
`A'`-linear map `A' ⊗_A M ⟶ P`, `b ⊗ m ↦ b • u m`.

Suppose that this situation has a *model* over another pair of rings: an `R`-algebra `R'`, ring
isomorphisms `R ≃+* A` and `R' ≃+* A'` compatible with the two ring maps, an `R`-module `Mc`
additively isomorphic to `M` semilinearly, an `R'`-module `Pc` additively isomorphic to `P`
semilinearly, and an `R'`-linear `c : R' ⊗_R Mc ⟶ Pc` agreeing with `b ⊗ m ↦ b • u m` through
these identifications.  If `c` is bijective then so is the extension of scalars of `u`.

The point is that the two tensor products are over *different* rings, so the two maps cannot be
compared as morphisms of modules.  The additive map `R' ⊗_R Mc ⟶ A' ⊗_A M` that applies the two
identifications factorwise is surjective, and that is all that is needed.

## Main results

* `Stacks.ModuleCat.bijective_extendScalars_homEquiv_symm_of_model`: if the model map `c` is
  bijective, then so is the extension of scalars of `u`.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

namespace Stacks.ModuleCat

universe v

variable {A A' : Type v} [CommRing A] [CommRing A'] (φ : A →+* A')
    {M : _root_.ModuleCat.{v} A} {P : _root_.ModuleCat.{v} A'}
    (u : M ⟶ (_root_.ModuleCat.restrictScalars φ).obj P)
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {Mc Pc : Type*} [AddCommGroup Mc] [Module R Mc] [AddCommGroup Pc] [Module R' Pc]
    (eR : R ≃+* A) (eR' : R' ≃+* A')
    (hcomp : ∀ r : R, φ (eR r) = eR' (algebraMap R R' r))
    (eM : Mc ≃+ M) (heM : ∀ (r : R) (x : Mc), eM (r • x) = eR r • eM x)

/-- The unit `m ↦ 1 ⊗ m` of extension of scalars, as an additive map. -/
abbrev extendScalarsUnit : M →+ (_root_.ModuleCat.extendScalars φ).obj M :=
  (((_root_.ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom : _ →ₗ[A] _).toAddMonoidHom

/-- The unit of extension of scalars is `φ`-semilinear: `1 ⊗ (t • m) = φ t • (1 ⊗ m)`. -/
theorem extendScalarsUnit_smul (t : A) (m : M) :
    extendScalarsUnit φ (t • m) = φ t • extendScalarsUnit φ m :=
  ((_root_.ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom.map_smul t m

/-- A scalar acting on the unit is a pure tensor: `b • (1 ⊗ m) = b ⊗ m`. -/
theorem smul_extendScalarsUnit (b : A') (m : M) :
    b • extendScalarsUnit φ m = (b ⊗ₜ[A, φ] m : (_root_.ModuleCat.extendScalars φ).obj M) :=
  (_root_.ModuleCat.ExtendScalars.smul_tmul φ b 1 m).trans
    (congrArg (fun t ↦ (t ⊗ₜ[A, φ] m : (_root_.ModuleCat.extendScalars φ).obj M)) (mul_one b))

/-- The additive map `R' ⊗_R Mc ⟶ A' ⊗_A M` applying the two identifications factorwise. -/
def modelTensorToExtendScalars :
    R' ⊗[R] Mc →+ (_root_.ModuleCat.extendScalars φ).obj M :=
  TensorProduct.liftAddHom
    { toFun := fun a ↦
        { toFun := fun x ↦ eR' a • extendScalarsUnit φ (eM x)
          map_zero' := by rw [map_zero, map_zero, smul_zero]
          map_add' := fun x y ↦ by rw [map_add, map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun x ↦ by
        change eR' 0 • extendScalarsUnit φ (eM x) = 0
        rw [map_zero, zero_smul]
      map_add' := fun a b ↦ AddMonoidHom.ext fun x ↦ by
        change eR' (a + b) • extendScalarsUnit φ (eM x) =
          eR' a • extendScalarsUnit φ (eM x) + eR' b • extendScalarsUnit φ (eM x)
        rw [map_add, add_smul] }
    fun r a x ↦ by
      change eR' (r • a) • extendScalarsUnit φ (eM x) = eR' a • extendScalarsUnit φ (eM (r • x))
      rw [heM, extendScalarsUnit_smul, smul_smul, Algebra.smul_def, map_mul, ← hcomp, mul_comm]

/-- On a pure tensor, `modelTensorToExtendScalars` sends `a ⊗ x` to `eR' a • (1 ⊗ eM x)`. -/
theorem modelTensorToExtendScalars_tmul (a : R') (x : Mc) :
    modelTensorToExtendScalars φ eR eR' hcomp eM heM (a ⊗ₜ[R] x) =
      eR' a • extendScalarsUnit φ (eM x) :=
  rfl

/-- The additive map `modelTensorToExtendScalars : R' ⊗_R Mc ⟶ A' ⊗_A M` is surjective. -/
theorem surjective_modelTensorToExtendScalars :
    Function.Surjective (modelTensorToExtendScalars φ eR eR' hcomp eM heM) := by
  intro w
  refine TensorProduct.inductionOn
    (motive := fun w ↦ ∃ z, modelTensorToExtendScalars φ eR eR' hcomp eM heM z = w) w
    (fun b m ↦ ⟨eR'.symm (show A' from b) ⊗ₜ[R] eM.symm m, ?_⟩) ?_
  · exact (congrArg₂ (fun (t : A') (y : M) ↦ t • extendScalarsUnit φ y)
      (eR'.apply_symm_apply _) (eM.apply_symm_apply m)).trans (smul_extendScalarsUnit φ b m)
  · rintro w₁ w₂ ⟨z₁, e₁⟩ ⟨z₂, e₂⟩
    exact ⟨z₁ + z₂, (map_add _ _ _).trans (congrArg₂ (· + ·) e₁ e₂)⟩

/-- The extension of scalars of `u` on the unit is `u`. -/
theorem extendScalars_homEquiv_symm_extendScalarsUnit (m : M) :
    (((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm u).hom
        (extendScalarsUnit φ m) = u m :=
  congrArg (fun f : M ⟶ (_root_.ModuleCat.restrictScalars φ).obj P ↦ f m)
    (((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply u)

include hcomp heM in
/-- **Bijectivity of an extended map, read through a model over isomorphic rings.** -/
theorem bijective_extendScalars_homEquiv_symm_of_model
    (eP : P ≃+ Pc) (heP : ∀ (a : R') (p : P), eP (eR' a • p) = a • eP p)
    (c : R' ⊗[R] Mc → Pc) (hcadd : ∀ z w, c (z + w) = c z + c w)
    (hc : ∀ (a : R') (x : Mc), c (a ⊗ₜ[R] x) = a • eP (u (eM x)))
    (hcb : Function.Bijective c) :
    Function.Bijective
      (((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm u).hom := by
  set U := (((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm u).hom
  set T := modelTensorToExtendScalars φ eR eR' hcomp eM heM
  have hstep : ∀ z, eP (U (T z)) = c z := by
    intro z
    refine TensorProduct.inductionOn (motive := fun z ↦ eP (U (T z)) = c z) z ?_ ?_
    · intro a x
      refine Eq.trans ?_ ((heP a _).trans (hc a x).symm)
      refine congrArg eP ((map_smul U (eR' a) (extendScalarsUnit φ (eM x))).trans ?_)
      exact congrArg (eR' a • ·) (extendScalars_homEquiv_symm_extendScalarsUnit φ u (eM x))
    · intro z w hz hw
      rw [map_add, map_add, map_add, hz, hw, hcadd]
  have hsurj := surjective_modelTensorToExtendScalars φ eR eR' hcomp eM heM
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨zx, rfl⟩ := hsurj x
    obtain ⟨zy, rfl⟩ := hsurj y
    exact congrArg T (hcb.injective ((hstep zx).symm.trans ((congrArg eP hxy).trans (hstep zy))))
  · obtain ⟨z, hz⟩ := hcb.surjective (eP y)
    exact ⟨T z, eP.injective ((hstep z).trans hz)⟩

end Stacks.ModuleCat

end
