module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Group
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Algebra
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Tangent vectors commute with flat base change

Let `R` be a framed algebra and `B'` a flat `A'`-algebra.  This file proves that the map
`G(R) ⊗_{A'} B' → G(R ⊗_{A'} B')`, `g ⊗ b ↦ b · g|_{R ⊗ B'}`, from the tangent vectors over `R`
to those over `R ⊗_{A'} B'`, is bijective (`Framing.baseChange_bijective`).

In coordinates the tangent vectors are `Hom_{Γ(W)}(Ω_{Γ(W)/Γ(V)}, CR)`, the chart morphism
`W ⟶ V` is smooth, so `Ω_{Γ(W)/Γ(V)}` is finite projective and the claim is
`Stacks.SmoothLift.homTensorMap_bijective` together with `CR ⊗_{A'} B' ≅ C(R ⊗_{A'} B')`, which
is flatness of `B'`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct Cardinal

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : Base B S hS}

/-! ### The tensor product algebra -/

/-- The tensor product over `A'` of two algebras of size below the cutoff has size below the
cutoff. -/
theorem mk_tensor_lt (R R' : Alg D) : #(R.R ⊗[D.A] R'.R) < B.cutoff := by
  have hsurj : Function.Surjective
      (fun l : List (R.R × R'.R) => (l.map (fun p => p.1 ⊗ₜ[D.A] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], rfl⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨l', rfl⟩ := hy
      exact ⟨l ++ l', by simp⟩
  refine lt_of_le_of_lt (Cardinal.mk_le_of_surjective hsurj) ?_
  refine lt_of_le_of_lt (Cardinal.mk_list_le_max _) (max_lt B.aleph0_lt_cutoff ?_)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le R.size R'.size

/-- The tensor product of two algebras of size below the cutoff. -/
noncomputable def Alg.tensor (R R' : Alg D) : Alg D := ⟨R.R ⊗[D.A] R'.R, mk_tensor_lt R R'⟩

/-- The carrier of the tensor product algebra is the tensor product, as algebras. -/
noncomputable def Alg.tensorEquiv (R R' : Alg D) : (R.R ⊗[D.A] R'.R) ≃ₐ[D.A] (Alg.tensor R R').R :=
  AlgEquiv.refl

/-- A pure tensor in the tensor product algebra. -/
noncomputable def Alg.tmul {R R' : Alg D} (r : R.R) (b : R'.R) : (Alg.tensor R R').R :=
  Alg.tensorEquiv R R' (r ⊗ₜ[D.A] b)

/-- Pure tensors multiply factorwise: `(r ⊗ b) (r' ⊗ b') = (r r') ⊗ (b b')`. -/
theorem Alg.tmul_mul_tmul {R R' : Alg D} (r r' : R.R) (b b' : R'.R) :
    Alg.tmul r b * Alg.tmul r' b' = Alg.tmul (r * r') (b * b') := by
  rw [Alg.tmul, Alg.tmul, Alg.tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- A pure tensor is additive in its first factor. -/
theorem Alg.add_tmul {R R' : Alg D} (r r' : R.R) (b : R'.R) :
    Alg.tmul (r + r') b = Alg.tmul r b + Alg.tmul r' b := by
  rw [Alg.tmul, Alg.tmul, Alg.tmul, ← map_add, TensorProduct.add_tmul]

/-- A pure tensor is additive in its second factor. -/
theorem Alg.tmul_add {R R' : Alg D} (r : R.R) (b b' : R'.R) :
    Alg.tmul r (b + b') = Alg.tmul r b + Alg.tmul r b' := by
  rw [Alg.tmul, Alg.tmul, Alg.tmul, ← map_add, TensorProduct.tmul_add]

/-- A scalar of `A'` on the first factor of a pure tensor acts on the whole tensor. -/
theorem Alg.smul_tmul' {R R' : Alg D} (c : D.A) (r : R.R) (b : R'.R) :
    Alg.tmul (c • r) b = c • Alg.tmul r b := by
  rw [Alg.tmul, Alg.tmul, ← map_smul, TensorProduct.smul_tmul']

/-- A scalar of `A'` on the second factor of a pure tensor acts on the whole tensor. -/
theorem Alg.tmul_smul {R R' : Alg D} (c : D.A) (r : R.R) (b : R'.R) :
    Alg.tmul r (c • b) = c • Alg.tmul r b := by
  rw [Alg.tmul, Alg.tmul, ← map_smul, TensorProduct.tmul_smul]

/-- Induction principle for the tensor product algebra: a predicate holding at `0`, on pure
tensors and closed under addition holds everywhere. -/
theorem Alg.induction_on {R R' : Alg D} {P : (Alg.tensor R R').R → Prop}
    (x : (Alg.tensor R R').R) (zero : P 0) (tmul : ∀ r b, P (Alg.tmul r b))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  obtain ⟨x, rfl⟩ := (Alg.tensorEquiv R R').surjective x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero
  | tmul r b => exact tmul r b
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

/-- The tensor product of an algebra map with the identity of a second factor. -/
noncomputable def Alg.tensorMap {R₁ R₂ : Alg D} (h : R₁.R →ₐ[D.A] R₂.R) (R' : Alg D) :
    (Alg.tensor R₁ R').R →ₐ[D.A] (Alg.tensor R₂ R').R :=
  (Alg.tensorEquiv R₂ R').toAlgHom.comp ((Algebra.TensorProduct.map h (AlgHom.id D.A R'.R)).comp
    (Alg.tensorEquiv R₁ R').symm.toAlgHom)

/-- `Alg.tensorMap h R'` sends `r ⊗ b` to `h r ⊗ b`. -/
theorem Alg.tensorMap_tmul {R₁ R₂ : Alg D} (h : R₁.R →ₐ[D.A] R₂.R) (R' : Alg D) (r : R₁.R)
    (b : R'.R) : Alg.tensorMap h R' (Alg.tmul r b) = Alg.tmul (h r) b := rfl

/-- Two `A'`-algebra maps out of the tensor product algebra agreeing on pure tensors are
equal. -/
theorem Alg.algHom_ext {R R' : Alg D} {T : Type*} [CommRing T] [Algebra D.A T]
    {f g : (Alg.tensor R R').R →ₐ[D.A] T} (h : ∀ r b, f (Alg.tmul r b) = g (Alg.tmul r b)) :
    f = g := by
  apply AlgHom.ext
  intro x
  induction x using Alg.induction_on with
  | zero => simp
  | tmul r b => exact h r b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-! ### Coordinate derivations as maps out of the module of differentials -/

variable {𝔓 : Problem D} {F : Frame 𝔓} {R : Alg D} (Fr : Framing F R)

/-- `Γ(W)` as a `Γ(V)`-algebra along the chart morphism. -/
noncomputable instance Frame.algebraPVPW : Algebra F.PV F.PW := F.kS.hom.toAlgebra

/-- The structure map `Γ(V) → Γ(W)` is the ring map of the chart morphism. -/
theorem Frame.algebraMap_PVPW (v : F.PV) : algebraMap F.PV F.PW v = F.kS v := rfl

/-- The square-zero ideal, as a module over `Γ(W)` through the chart of `x`. -/
def Framing.MW (_ : Framing F R) : Type u := M D.C R.R

/-- Read an element of the synonym as an element of the square-zero ideal. -/
def Framing.ofMW (m : Fr.MW) : M D.C R.R := m

/-- Read an element of the square-zero ideal as an element of the synonym. -/
def Framing.toMW (m : M D.C R.R) : Fr.MW := m

/-- The additive group structure of the square-zero ideal. -/
noncomputable instance Framing.instAddCommGroupMW : AddCommGroup Fr.MW :=
  inferInstanceAs (AddCommGroup (M D.C R.R))

/-- The module structure of the square-zero ideal over the quotient by it. -/
noncomputable instance Framing.instModuleQMW : Module (Q D.C R.R) Fr.MW :=
  inferInstanceAs (Module (Q D.C R.R) (M D.C R.R))

/-- The `Γ(W)`-module structure on the square-zero ideal through the chart of `x`. -/
noncomputable instance Framing.instModulePWMW : Module F.PW Fr.MW :=
  Module.compHom (M D.C R.R) Fr.lS.hom

/-- The `Γ(V)`-module structure on the square-zero ideal through the chart morphism and the
chart of `x`. -/
noncomputable instance Framing.instModulePVMW : Module F.PV Fr.MW :=
  Module.compHom (M D.C R.R) (F.kS ≫ Fr.lS).hom

/-- The actions of `Γ(V)` and `Γ(W)` on the square-zero ideal form a scalar tower. -/
instance Framing.instIsScalarTowerMW : IsScalarTower F.PV F.PW Fr.MW where
  smul_assoc v a m := by
    change Fr.lS (F.kS v * a) • m = Fr.lS (F.kS v) • Fr.lS a • m
    rw [map_mul, mul_smul]

/-- An element of `Γ(W)` acts on the square-zero ideal through its image under the chart of
`x`. -/
theorem Framing.smul_MW (a : F.PW) (m : Fr.MW) :
    a • m = (Fr.lS a • (m : M D.C R.R) : M D.C R.R) := rfl

/-- A coordinate derivation, as a derivation in the sense of Mathlib. -/
noncomputable def Framing.toDerivation (δ : Fr.Der) : Derivation F.PV F.PW Fr.MW :=
  Derivation.mk'
    { toFun := fun a => (δ : F.PW →+ M D.C R.R) a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun v a => by
        change (δ : F.PW →+ M D.C R.R) (F.kS v * a) = Fr.lS (F.kS v) • _
        rw [Framing.Der.map_mul, Framing.Der.map_base, smul_zero, add_zero] }
    (fun a b => Framing.Der.map_mul Fr δ a b)

/-- A Mathlib derivation, as a coordinate derivation. -/
noncomputable def Framing.ofDerivation (d : Derivation F.PV F.PW Fr.MW) : Fr.Der :=
  ⟨{ toFun := fun a => d a
     map_zero' := d.map_zero
     map_add' := fun a b => d.map_add a b }, fun a b => d.leibniz a b, fun v => by
    change d (algebraMap F.PV F.PW v) = 0
    exact d.map_algebraMap v⟩

/-- **Coordinate derivations are linear maps out of the module of differentials.** -/
noncomputable def Framing.homEquiv : Fr.Der ≃ (Ω[F.PW⁄F.PV] →ₗ[F.PW] Fr.MW) where
  toFun δ := (KaehlerDifferential.linearMapEquivDerivation F.PV F.PW).symm (Fr.toDerivation δ)
  invFun L := Fr.ofDerivation (KaehlerDifferential.linearMapEquivDerivation F.PV F.PW L)
  left_inv δ := by
    apply Subtype.ext
    ext a
    simp [Framing.ofDerivation, Framing.toDerivation]
    rfl
  right_inv L := by
    apply (KaehlerDifferential.linearMapEquivDerivation F.PV F.PW).injective
    rw [LinearEquiv.apply_symm_apply]
    ext a
    rfl

/-- The linear map attached to a coordinate derivation `δ` sends `d a` to `δ a`. -/
theorem Framing.homEquiv_D (δ : Fr.Der) (a : F.PW) :
    Fr.homEquiv δ (KaehlerDifferential.D F.PV F.PW a) = (δ : F.PW →+ M D.C R.R) a := by
  simp [Framing.homEquiv, Framing.toDerivation]
  rfl

/-- The coordinate derivation attached to a linear map `L` sends `a` to `L (d a)`. -/
theorem Framing.homEquiv_symm_apply (L : Ω[F.PW⁄F.PV] →ₗ[F.PW] Fr.MW) (a : F.PW) :
    ((Fr.homEquiv.symm L : Fr.Der) : F.PW →+ M D.C R.R) a = L (KaehlerDifferential.D F.PV F.PW a) :=
  rfl

/-- The ring map `Γ(V) → Γ(W)` of the chart morphism is smooth. -/
theorem Frame.smooth_PW : Algebra.Smooth F.PV F.PW := by
  have h := (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Smooth)).mp F.sm
  exact h

/-- The `A'`-module structure of the square-zero ideal. -/
noncomputable instance Framing.instModuleAMW : Module D.A Fr.MW :=
  inferInstanceAs (Module D.A (M D.C R.R))

/-- The actions of the quotient ring and of `A'` on the square-zero ideal commute. -/
theorem smul_comm_Q_A {R : Alg D} (q : Q D.C R.R) (a : D.A) (m : M D.C R.R) :
    q • (a • m) = a • (q • m) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [mk_smul, mk_smul]
  apply Subtype.ext
  show r * (a • (m : R.R)) = a • (r * (m : R.R))
  rw [mul_smul_comm]

/-- The actions of `Γ(W)` and of `A'` on the square-zero ideal commute. -/
instance Framing.instSMulCommClassMW : SMulCommClass F.PW D.A Fr.MW where
  smul_comm p a m := smul_comm_Q_A (Fr.lS p) a (m : M D.C R.R)

/-- The actions of `A'` and of `Γ(W)` on the square-zero ideal commute. -/
instance Framing.instSMulCommClassMW' : SMulCommClass D.A F.PW Fr.MW :=
  SMulCommClass.symm _ _ _

/-- The identification of `Framing.homEquiv`, as an isomorphism of `A'`-modules. -/
noncomputable def Framing.homLinearEquiv : Fr.Der ≃ₗ[D.A] (Ω[F.PW⁄F.PV] →ₗ[F.PW] Fr.MW) :=
  { Fr.homEquiv with
    map_add' := fun δ δ' => by
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      change Fr.homEquiv (δ + δ') (KaehlerDifferential.D _ _ a) =
        Fr.homEquiv δ (KaehlerDifferential.D _ _ a) + Fr.homEquiv δ' (KaehlerDifferential.D _ _ a)
      rw [Fr.homEquiv_D, Fr.homEquiv_D, Fr.homEquiv_D]
      rfl
    map_smul' := fun c δ => by
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      change Fr.homEquiv (c • δ) (KaehlerDifferential.D _ _ a) =
        c • Fr.homEquiv δ (KaehlerDifferential.D _ _ a)
      rw [Fr.homEquiv_D, Fr.homEquiv_D]
      rfl }

/-! ### The base change map -/

variable (R' : Alg D)

/-- The inclusion of the first factor of a tensor product algebra. -/
noncomputable def incl₁ : R.R →ₐ[D.A] (Alg.tensor R R').R :=
  (Alg.tensorEquiv R R').toAlgHom.comp Algebra.TensorProduct.includeLeft

/-- The inclusion of the second factor of a tensor product algebra. -/
noncomputable def incl₂ : R'.R →ₐ[D.A] (Alg.tensor R R').R :=
  (Alg.tensorEquiv R R').toAlgHom.comp Algebra.TensorProduct.includeRight

/-- The first inclusion sends `r` to `r ⊗ 1`. -/
theorem incl₁_apply (r : R.R) : incl₁ R' r = Alg.tmul r 1 := rfl

/-- The second inclusion sends `b` to `1 ⊗ b`. -/
theorem incl₂_apply (b : R'.R) : incl₂ R' b = Alg.tmul (1 : R.R) b := rfl

/-- The product of the images of `r` and `b` in a tensor product algebra is the pure tensor. -/
private theorem incl₂_mul_incl₁ (r : R.R) (b : R'.R) :
    incl₂ R' b * incl₁ R' r = Alg.tmul r b := by
  rw [incl₁_apply, incl₂_apply, Alg.tmul_mul_tmul, one_mul, mul_one]

/-- The framing of a tensor product algebra by its first factor. -/
noncomputable abbrev Framing.tens : Framing F (Alg.tensor R R') := Fr.pull (incl₁ R')

/-- Pushing a coordinate derivation forward along `h` is semilinear over `qMap D.C h`. -/
theorem Framing.pushDer_smul (q : Q D.C R.R) (δ : Fr.Der) {R'' : Alg D}
    (h : R.R →ₐ[D.A] R''.R) : Fr.pushDer h (q • δ) = qMap D.C h q • Fr.pushDer h δ := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  have : mMap D.C h ((q • (δ : F.PW →+ M D.C R.R)) a) =
      qMap D.C h q • mMap D.C h ((δ : F.PW →+ M D.C R.R) a) := by
    rw [AddMonoidHom.smul_apply, mMap_smul]
  exact this

/-- Pushing coordinate derivations forward along `h` is additive. -/
theorem Framing.pushDer_add (δ δ' : Fr.Der) {R'' : Alg D} (h : R.R →ₐ[D.A] R''.R) :
    Fr.pushDer h (δ + δ') = Fr.pushDer h δ + Fr.pushDer h δ' := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro a
  have : mMap D.C h (((δ + δ' : Fr.Der) : F.PW →+ M D.C R.R) a) =
      mMap D.C h ((δ : F.PW →+ M D.C R.R) a) + mMap D.C h ((δ' : F.PW →+ M D.C R.R) a) := by
    rw [← map_add]; rfl
  exact this

/-- The map of quotients induced by an `A'`-algebra map commutes with the structure maps
from `A'`. -/
theorem qMap_algebraMap {R'' : Alg D} (h : R.R →ₐ[D.A] R''.R) (c : D.A) :
    qMap D.C h (algebraMap D.A (Q D.C R.R) c) = algebraMap D.A (Q D.C R''.R) c := by
  show Ideal.Quotient.mk _ (h (algebraMap D.A R.R c)) = Ideal.Quotient.mk _ _
  rw [h.commutes]

/-- **The base change map** `Der(R) ⊗_{A'} R' → Der(R ⊗_{A'} R')`,
`δ ⊗ b ↦ (1 ⊗ b) · δ|_{R ⊗ R'}`. -/
noncomputable def Framing.baseChange : Fr.Der ⊗[D.A] R'.R →ₗ[D.A] (Fr.tens R').Der :=
  TensorProduct.lift (LinearMap.mk₂ D.A
    (fun δ b => Ideal.Quotient.mk (sqIdeal D.C (Alg.tensor R R').R) (incl₂ R' b) •
      Fr.pushDer (incl₁ R') δ)
    (fun δ δ' b => by rw [Fr.pushDer_add, smul_add])
    (fun c δ b => by
      rw [← algebraMap_smul (Q D.C R.R) c δ, Fr.pushDer_smul, qMap_algebraMap, smul_comm,
        algebraMap_smul])
    (fun δ b b' => by rw [map_add, map_add, add_smul])
    (fun c δ b => by
      rw [map_smul, ← smul_assoc]
      rfl))

/-- The base change map sends `δ ⊗ b` to `(1 ⊗ b) · δ|_{R ⊗ R'}`. -/
theorem Framing.baseChange_tmul (δ : Fr.Der) (b : R'.R) :
    Fr.baseChange R' (δ ⊗ₜ b) =
      Ideal.Quotient.mk (sqIdeal D.C (Alg.tensor R R').R) (incl₂ R' b) • Fr.pushDer (incl₁ R') δ :=
  rfl

/-! ### The square-zero ideal of a flat base change -/

/-- For `m` in the square-zero ideal of `R`, the tensor `m ⊗ b` lies in the square-zero ideal
of `R ⊗_{A'} R'`. -/
theorem tmul_mem_sqIdeal (m : M D.C R.R) (b : R'.R) :
    Alg.tmul (m : R.R) b ∈ sqIdeal D.C (Alg.tensor R R').R := by
  rw [← incl₂_mul_incl₁]
  exact Ideal.mul_mem_left _ _ (mem_sqIdeal_of_mem D.C (incl₁ R') m.2)

/-- The comparison `CR ⊗_{A'} R' → C(R ⊗_{A'} R')`. -/
noncomputable def kappaA : M D.C R.R ⊗[D.A] R'.R →ₗ[D.A] M D.C (Alg.tensor R R').R :=
  TensorProduct.lift (LinearMap.mk₂ D.A (fun m b => ⟨Alg.tmul (m : R.R) b, tmul_mem_sqIdeal R' m b⟩)
    (fun _ _ _ => Subtype.ext (Alg.add_tmul _ _ _))
    (fun _ _ _ => Subtype.ext (Alg.smul_tmul' _ _ _))
    (fun _ _ _ => Subtype.ext (Alg.tmul_add _ _ _))
    (fun _ _ _ => Subtype.ext (Alg.tmul_smul _ _ _)))

/-- The comparison `kappaA` sends `m ⊗ b` to the pure tensor `m ⊗ b` of `R ⊗_{A'} R'`. -/
theorem kappaA_tmul (m : M D.C R.R) (b : R'.R) :
    ((kappaA R' (m ⊗ₜ b) : M D.C (Alg.tensor R R').R) : (Alg.tensor R R').R) =
      Alg.tmul (m : R.R) b := rfl

/-- Followed by the inclusion of the ideal, `kappaA` is the base change along `R'` of the
inclusion `CR → R`. -/
theorem val_comp_kappaA :
    (Submodule.subtype _).restrictScalars D.A ∘ₗ kappaA (R := R) R' =
      (Alg.tensorEquiv R R').toLinearMap ∘ₗ
        ((Submodule.subtype (sqIdeal D.C R.R)).restrictScalars D.A).rTensor R'.R := by
  ext m b
  rfl

/-- For `R'` flat over `A'`, the comparison `CR ⊗_{A'} R' → C(R ⊗_{A'} R')` is injective. -/
theorem kappaA_injective [Module.Flat D.A R'.R] : Function.Injective (kappaA (R := R) R') := by
  have h : Function.Injective ((Alg.tensorEquiv R R').toLinearMap ∘ₗ
      ((Submodule.subtype (sqIdeal D.C R.R)).restrictScalars D.A).rTensor R'.R) :=
    (Alg.tensorEquiv R R').injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  rw [← val_comp_kappaA] at h
  intro x y hxy
  exact h (by simp only [LinearMap.coe_comp, Function.comp_apply, hxy])

/-- The comparison `CR ⊗_{A'} R' → C(R ⊗_{A'} R')` is surjective. -/
theorem kappaA_surjective : Function.Surjective (kappaA (R := R) R') := by
  intro y
  obtain ⟨y, hy⟩ := y
  let S : Submodule D.A (Alg.tensor R R').R :=
    LinearMap.range ((Submodule.subtype _).restrictScalars D.A ∘ₗ kappaA (R := R) R')
  suffices H : y ∈ S by
    obtain ⟨z, hz⟩ := H
    exact ⟨z, Subtype.ext hz⟩
  have hmulmem : ∀ (x : (Alg.tensor R R').R) (z : M D.C R.R ⊗[D.A] R'.R),
      x * ((kappaA (R := R) R' z : M D.C (Alg.tensor R R').R) : (Alg.tensor R R').R) ∈ S := by
    intro x z
    induction x using Alg.induction_on with
    | zero => simp
    | tmul r b =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m b' =>
        refine ⟨(r • m) ⊗ₜ (b * b'), ?_⟩
        show Alg.tmul ((r • m : M D.C R.R) : R.R) (b * b') = Alg.tmul r b * Alg.tmul (m : R.R) b'
        rw [Alg.tmul_mul_tmul]
        rfl
      | add z z' hz hz' =>
        simpa only [map_add, Submodule.coe_add, mul_add] using S.add_mem hz hz'
    | add x x' hx hx' => simpa only [add_mul] using S.add_mem hx hx'
  change y ∈ Ideal.map (algebraMap D.A (Alg.tensor R R').R) D.C at hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨⟨algebraMap D.A R.R c, Ideal.mem_map_of_mem _ hc⟩ ⊗ₜ 1, ?_⟩
    show Alg.tmul (algebraMap D.A R.R c) (1 : R'.R) = _
    rw [← incl₁_apply, AlgHom.commutes]
  · exact S.zero_mem
  · rintro x x' - - hx hx'
    exact S.add_mem hx hx'
  · rintro a x - ⟨w, rfl⟩
    exact hmulmem a w

/-! ### Bijectivity of the base change map -/

/-- The actions of `A'` and of the quotient ring on the square-zero ideal commute. -/
instance smulCommClass_A_Q_M : SMulCommClass D.A (Q D.C R.R) (M D.C R.R) where
  smul_comm a q m := (smul_comm_Q_A q a m).symm

/-- The comparison `kappaA` is semilinear over the map of quotients induced by the first
inclusion. -/
theorem kappaA_smul (q : Q D.C R.R) (x : M D.C R.R ⊗[D.A] R'.R) :
    kappaA (R := R) R' (q • x) = qMap D.C (incl₁ R') q • kappaA (R := R) R' x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m b =>
    rw [TensorProduct.smul_tmul']
    apply Subtype.ext
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [qMap_mk, mk_smul, mk_smul]
    show Alg.tmul (r * (m : R.R)) b = Alg.tmul r (1 : R'.R) * Alg.tmul (m : R.R) b
    rw [Alg.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The comparison `CR ⊗_{A'} R' ≅ C(R ⊗_{A'} R')`, on the module carrying the action of
`Γ(W)`. -/
noncomputable def Framing.kappaA' : Fr.MW ⊗[D.A] R'.R →ₗ[D.A] (Fr.tens R').MW :=
  kappaA (R := R) R'

/-- `Framing.kappaA'` is `kappaA` on the underlying square-zero ideals. -/
theorem Framing.kappaA'_eq (x : Fr.MW ⊗[D.A] R'.R) :
    (Fr.tens R').ofMW (Fr.kappaA' R' x) = kappaA (R := R) R' x := by
  rfl

/-- The comparison `Framing.kappaA'` is `Γ(W)`-linear. -/
theorem kappaA_smul_aux (p : F.PW) (x : Fr.MW ⊗[D.A] R'.R) :
    Fr.kappaA' R' (p • x) = p • Fr.kappaA' R' x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m b =>
    rw [TensorProduct.smul_tmul']
    have h := kappaA_smul (R := R) R' (Fr.lS p) (Fr.ofMW m ⊗ₜ b)
    rw [TensorProduct.smul_tmul'] at h
    show kappaA (R := R) R' ((Fr.lS p • Fr.ofMW m) ⊗ₜ b) =
      ((Fr.tens R').lS p : Q D.C (Alg.tensor R R').R) • kappaA (R := R) R' (Fr.ofMW m ⊗ₜ b)
    rw [Fr.pull_lS]
    exact h
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The comparison `CR ⊗_{A'} R' ≅ C(R ⊗_{A'} R')`, as a `Γ(W)`-linear map. -/
noncomputable def Framing.kappa : Fr.MW ⊗[D.A] R'.R →ₗ[F.PW] (Fr.tens R').MW where
  toFun x := Fr.kappaA' R' x
  map_add' x y := map_add (Fr.kappaA' R') x y
  map_smul' p x := kappaA_smul_aux Fr R' p x

/-- For `R'` flat over `A'`, the comparison `CR ⊗_{A'} R' → C(R ⊗_{A'} R')` is bijective. -/
theorem Framing.kappa_bijective [Module.Flat D.A R'.R] : Function.Bijective (Fr.kappa R') := by
  refine ⟨fun x y h => kappaA_injective (R := R) R' ?_, fun y => ?_⟩
  · have hx := Fr.kappaA'_eq R' x
    have hy := Fr.kappaA'_eq R' y
    exact hx.symm.trans ((congrArg (Fr.tens R').ofMW h).trans hy)
  · obtain ⟨x, hx⟩ := kappaA_surjective (R := R) R' y
    exact ⟨x, (Fr.kappaA'_eq R' x).trans hx⟩

/-- The module of differentials `Ω_{Γ(W)/Γ(V)}` is finite over `Γ(W)`. -/
instance Frame.finite_differentials : Module.Finite F.PW Ω[F.PW⁄F.PV] := by
  have := F.smooth_PW
  infer_instance

/-- The module of differentials `Ω_{Γ(W)/Γ(V)}` is projective over `Γ(W)`. -/
instance Frame.projective_differentials : Module.Projective F.PW Ω[F.PW⁄F.PV] := by
  have := F.smooth_PW
  infer_instance

/-- **Tangent vectors commute with flat base change.** -/
theorem Framing.baseChange_bijective [Module.Flat D.A R'.R] :
    Function.Bijective (Fr.baseChange R') := by
  set θ := Fr.homLinearEquiv
  set θ' := (Fr.tens R').homLinearEquiv
  set H := homTensorMap (A := D.A) (P := F.PW) (N := Fr.MW) R'.R Ω[F.PW⁄F.PV]
  set κ := LinearEquiv.ofBijective (Fr.kappa R') (Fr.kappa_bijective R')
  set Post : (Ω[F.PW⁄F.PV] →ₗ[F.PW] Fr.MW ⊗[D.A] R'.R) ≃
      (Ω[F.PW⁄F.PV] →ₗ[F.PW] (Fr.tens R').MW) :=
    (LinearEquiv.congrRight κ).toEquiv
  have key : ∀ x, θ' (Fr.baseChange R' x) = Post (H ((θ.toLinearMap.rTensor R'.R) x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [(Fr.baseChange R').map_zero, θ'.map_zero, (θ.toLinearMap.rTensor R'.R).map_zero,
        H.map_zero]
      exact (LinearEquiv.congrRight κ).map_zero.symm
    | tmul δ b =>
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      show θ' (Fr.baseChange R' (δ ⊗ₜ b)) (KaehlerDifferential.D _ _ a) =
        κ (H (θ δ ⊗ₜ b) (KaehlerDifferential.D _ _ a))
      have e1 : θ' (Fr.baseChange R' (δ ⊗ₜ b)) (KaehlerDifferential.D _ _ a) =
          ((Fr.baseChange R' (δ ⊗ₜ b) : (Fr.tens R').Der) : F.PW →+ M D.C _) a :=
        (Fr.tens R').homEquiv_D _ a
      have e2 : θ δ (KaehlerDifferential.D _ _ a) = (δ : F.PW →+ M D.C R.R) a := Fr.homEquiv_D δ a
      rw [e1, homTensorMap_tmul, e2]
      apply Subtype.ext
      rw [Fr.baseChange_tmul]
      show ((Ideal.Quotient.mk (sqIdeal D.C (Alg.tensor R R').R) (incl₂ R' b) •
        mMap D.C (incl₁ R') ((δ : F.PW →+ M D.C R.R) a) : M D.C (Alg.tensor R R').R) :
          (Alg.tensor R R').R) = Alg.tmul ((δ : F.PW →+ M D.C R.R) a : R.R) b
      rw [mk_smul]
      exact incl₂_mul_incl₁ R' _ b
    | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, hx, hy]
      exact (map_add (LinearEquiv.congrRight κ) _ _).symm
  have hcomp : (Fr.baseChange R' : _ → _) =
      θ'.symm ∘ Post ∘ H ∘ (θ.toLinearMap.rTensor R'.R) := by
    funext x
    simp only [Function.comp_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  rw [hcomp]
  exact θ'.symm.bijective.comp (Post.bijective.comp ((homTensorMap_bijective (A := D.A)
    (P := F.PW) (N := Fr.MW) R'.R Ω[F.PW⁄F.PV]).comp (LinearEquiv.rTensor R'.R θ).bijective))

end AlgebraicGeometry.Space.SmoothLift
