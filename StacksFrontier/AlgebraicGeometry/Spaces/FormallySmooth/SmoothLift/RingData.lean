module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# The rings of a square-zero thickening of an algebra

Let `C` be an ideal of a commutative ring `A'` with `C * C = 0`, and let `R` be an `A'`-algebra.
This file builds the rings out of which the étale-local lifting argument of
[Stacks Project, Tag 04AM] is made:

* the reduction `Q = R ⧸ CR` and the square-zero ideal `M = CR` as a `Q`-module;
* the trivial square-zero extension `E = Q ⊕ M`, whose spectrum is the "tangent thickening";
* the fibre product `P = E ×_Q R`, whose spectrum is the pushout `Spec R ⊔_{Spec Q} Spec E`, and
  the ring map `σ : P → R`, `((q, m), r) ↦ r + m`, which is the action of tangent vectors on lifts;
* the functoriality of all of these in the algebra `R`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

namespace Stacks.SmoothLift

universe u

variable {A' : Type u} [CommRing A'] (C : Ideal A') [hC : Fact (C * C = ⊥)]
variable (R : Type u) [CommRing R] [Algebra A' R]

/-- The extension `CR` of the square-zero ideal `C` to the algebra `R`. -/
def sqIdeal : Ideal R := C.map (algebraMap A' R)

/-- The ideal `CR` squares to zero. -/
theorem sqIdeal_mul_self : sqIdeal C R * sqIdeal C R = ⊥ := by
  rw [sqIdeal, ← Ideal.map_mul, hC.out, Ideal.map_bot]

/-- The product of two elements of `CR` is zero. -/
theorem mul_eq_zero_of_mem {a b : R} (ha : a ∈ sqIdeal C R) (hb : b ∈ sqIdeal C R) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [sqIdeal_mul_self, Ideal.mem_bot] at this

/-- The reduction `R ⧸ CR`. -/
abbrev Q := R ⧸ sqIdeal C R

/-- The square-zero ideal `CR`, as a module over the reduction. -/
abbrev M := ↥(sqIdeal C R)

/-- The module `M = CR` is annihilated by the ideal `CR`. -/
theorem isTorsionBySet_M : Module.IsTorsionBySet R (M C R) (sqIdeal C R) :=
  fun m a ↦ Subtype.ext (mul_eq_zero_of_mem C R a.2 m.2)

/-- The square-zero ideal `CR` as a module over the reduction `R ⧸ CR`. -/
noncomputable instance moduleQ : Module (Q C R) (M C R) :=
  (isTorsionBySet_M C R).module

/-- The class of `r` acts on `M` as `r` does. -/
theorem mk_smul (r : R) (m : M C R) : (Ideal.Quotient.mk (sqIdeal C R) r) • m = r • m := rfl

/-- The actions of `A'` and of the reduction on `M` form a scalar tower. -/
instance isScalarTower_A_Q_M : IsScalarTower A' (Q C R) (M C R) where
  smul_assoc a q m := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : a • Ideal.Quotient.mk (sqIdeal C R) r = Ideal.Quotient.mk (sqIdeal C R) (a • r) := rfl
    rw [h1, mk_smul, mk_smul]
    apply Subtype.ext
    change (a • r) * (m : R) = a • (r * (m : R))
    rw [smul_mul_assoc]

/-- The right action of the reduction on `M`, equal to the left action. -/
noncomputable instance moduleQop : Module (Q C R)ᵐᵒᵖ (M C R) :=
  Module.compHom (M C R) ((RingEquiv.toOpposite (Q C R)).symm : (Q C R)ᵐᵒᵖ →+* Q C R)

/-- The left and right actions of the reduction on `M` agree. -/
instance isCentralScalarQ : IsCentralScalar (Q C R) (M C R) := ⟨fun _ _ => rfl⟩

/-- The trivial square-zero extension `E = Q ⊕ M`. -/
abbrev E := TrivSqZeroExt (Q C R) (M C R)

/-- The augmentation `E → Q`. -/
noncomputable abbrev fstE : E C R →+* Q C R :=
  (TrivSqZeroExt.fstHom (Q C R) (Q C R) (M C R)).toRingHom

/-- The inclusion `Q → E`. -/
noncomputable abbrev inlE : Q C R →+* E C R := TrivSqZeroExt.inlHom (Q C R) (M C R)

/-- The augmentation `E → Q` is a retraction of the inclusion `Q → E`. -/
theorem fstE_comp_inlE : (fstE C R).comp (inlE C R) = RingHom.id _ := rfl

/-- The fibre product `P = E ×_Q R`. -/
noncomputable abbrev P := (fstE C R).pullback (Ideal.Quotient.mk (sqIdeal C R))

/-- The action ring map `σ : P → R`, `((q, m), r) ↦ r + m`. -/
noncomputable def sigma : P C R →+* R where
  toFun x := x.1.2 + ((x.1.1.snd : M C R) : R)
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨⟨e, r⟩, hx⟩ := x
    obtain ⟨⟨e', r'⟩, hy⟩ := y
    simp only [RingHom.mem_eqLocus, RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst,
      RingHom.coe_snd] at hx hy
    change r * r' + (((e * e').snd : M C R) : R) =
      (r + ((e.snd : M C R) : R)) * (r' + ((e'.snd : M C R) : R))
    rw [TrivSqZeroExt.snd_mul]
    have hx' : e.fst = Ideal.Quotient.mk (sqIdeal C R) r := hx
    have hy' : e'.fst = Ideal.Quotient.mk (sqIdeal C R) r' := hy
    have h1 : (MulOpposite.op e'.fst • e.snd : M C R) = e'.fst • e.snd := rfl
    rw [h1, hx', hy', mk_smul, mk_smul]
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    have h0 := mul_eq_zero_of_mem C R (e.snd).2 (e'.snd).2
    rw [mul_comm ((e.snd : M C R) : R)] at h0
    ring_nf
    rw [h0, add_zero]
  map_zero' := by simp
  map_add' x y := by
    change (x.1.2 + y.1.2) + (((x.1.1 + y.1.1).snd : M C R) : R) = _
    simp only [TrivSqZeroExt.snd_add, Submodule.coe_add]
    ring

/-- Reducing `σ` modulo `CR` gives the augmentation of the first projection `P → E`. -/
theorem mk_comp_sigma : (Ideal.Quotient.mk (sqIdeal C R)).comp (sigma C R) =
    (fstE C R).comp ((fstE C R).pullbackFst (Ideal.Quotient.mk (sqIdeal C R))) := by
  ext ⟨⟨e, r⟩, hx⟩
  have hx' : e.fst = Ideal.Quotient.mk (sqIdeal C R) r := hx
  show Ideal.Quotient.mk _ (r + ((e.snd : M C R) : R)) = e.fst
  rw [hx', map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (e.snd).2, add_zero]

/-! ### Scalar multiplication on the tangent thickening -/

/-- The right action of `q` on `M` is its left action. -/
theorem op_smul_M (q : Q C R) (m : M C R) : MulOpposite.op q • m = q • m := rfl

/-- Multiplication of the square-zero part of `E` by a scalar `a` of `Q`, as a ring
endomorphism of `E`. -/
noncomputable def smulE (a : Q C R) : E C R →+* E C R where
  toFun x := TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (a • x.snd)
  map_one' := TrivSqZeroExt.ext (by simp) (by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (by
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      add_zero, op_smul_M, smul_add]
    rw [smul_comm a x.fst, smul_comm a y.fst])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (by simp [smul_add])

/-- `smulE a` fixes the first component. -/
@[simp] theorem fst_smulE (a : Q C R) (x : E C R) : (smulE C R a x).fst = x.fst := by
  simp [smulE]

/-- `smulE a` multiplies the second component by `a`. -/
@[simp] theorem snd_smulE (a : Q C R) (x : E C R) : (smulE C R a x).snd = a • x.snd := by
  simp [smulE]

/-- `smulE a` is compatible with the augmentation `E → Q`. -/
theorem fstE_comp_smulE (a : Q C R) : (fstE C R).comp (smulE C R a) = fstE C R := by
  ext x; simp

/-- `smulE a` fixes the inclusion `Q → E`. -/
theorem smulE_comp_inlE (a : Q C R) : (smulE C R a).comp (inlE C R) = inlE C R := by
  ext x <;> simp

/-! ### Functoriality in the algebra -/

variable {R} {R' : Type u} [CommRing R'] [Algebra A' R'] (h : R →ₐ[A'] R')

omit hC in
/-- An algebra map `R → R'` sends `CR` into `CR'`. -/
theorem sqIdeal_map_le : (sqIdeal C R).map h ≤ sqIdeal C R' := by
  show Ideal.map h.toRingHom (Ideal.map (algebraMap A' R) C) ≤ _
  rw [sqIdeal, Ideal.map_map]
  exact le_of_eq (congrArg (fun g => Ideal.map g C) h.comp_algebraMap)

omit hC in
/-- An algebra map `R → R'` sends elements of `CR` to elements of `CR'`. -/
theorem mem_sqIdeal_of_mem {x : R} (hx : x ∈ sqIdeal C R) : h x ∈ sqIdeal C R' :=
  sqIdeal_map_le C h (Ideal.mem_map_of_mem _ hx)

/-- The map of reductions induced by an algebra map. -/
noncomputable def qMap : Q C R →+* Q C R' :=
  Ideal.quotientMap _ h.toRingHom (Ideal.map_le_iff_le_comap.mp (sqIdeal_map_le C h))

omit hC in
/-- `qMap h` sends the class of `x` to the class of `h x`. -/
theorem qMap_mk (x : R) : qMap C h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (h x) := rfl

omit hC in
/-- `qMap h` is compatible with the quotient maps and `h`. -/
theorem qMap_comp_mk : (qMap C h).comp (Ideal.Quotient.mk (sqIdeal C R)) =
    (Ideal.Quotient.mk (sqIdeal C R')).comp h.toRingHom := rfl

/-- The map of square-zero ideals induced by an algebra map. -/
def mMap : M C R →+ M C R' where
  toFun x := ⟨h (x : R), mem_sqIdeal_of_mem C h x.2⟩
  map_zero' := Subtype.ext (map_zero h)
  map_add' x y := Subtype.ext (map_add h (x : R) y)

omit hC in
/-- `mMap h` is `h` on underlying elements. -/
theorem mMap_coe (x : M C R) : ((mMap C h x : M C R') : R') = h (x : R) := rfl

/-- `mMap h` is semilinear along `qMap h`. -/
theorem mMap_smul (q : Q C R) (x : M C R) : mMap C h (q • x) = qMap C h q • mMap C h x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact Subtype.ext (map_mul h r x)

/-- The map of tangent thickenings induced by an algebra map. -/
noncomputable def eMap : E C R →+* E C R' where
  toFun x := TrivSqZeroExt.inl (qMap C h x.fst) + TrivSqZeroExt.inr (mMap C h x.snd)
  map_one' := TrivSqZeroExt.ext (by simp) (by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (by
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      add_zero, map_add, op_smul_M, mMap_smul])
  map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (by simp)

/-- The first component of `eMap h x` is `qMap h` of that of `x`. -/
@[simp] theorem fst_eMap (x : E C R) : (eMap C h x).fst = qMap C h x.fst := by simp [eMap]

/-- The second component of `eMap h x` is `mMap h` of that of `x`. -/
@[simp] theorem snd_eMap (x : E C R) : (eMap C h x).snd = mMap C h x.snd := by simp [eMap]

/-- `eMap h` lies over `qMap h` along the augmentations `E → Q`. -/
theorem fstE_comp_eMap : (fstE C R').comp (eMap C h) = (qMap C h).comp (fstE C R) := by
  ext x; simp

/-- `eMap h` lies over `qMap h` along the inclusions `Q → E`. -/
theorem eMap_comp_inlE : (eMap C h).comp (inlE C R) = (inlE C R').comp (qMap C h) := by
  ext x <;> simp

/-- `eMap h` intertwines `smulE a` and `smulE (qMap h a)`. -/
theorem eMap_comp_smulE (a : Q C R) :
    (eMap C h).comp (smulE C R a) = (smulE C R' (qMap C h a)).comp (eMap C h) := by
  ext x <;> simp [mMap_smul]

/-- The map of the fibre products `E ×_Q R` induced by an algebra map. -/
noncomputable def pMap : P C R →+* P C R' where
  toFun x := ⟨(eMap C h x.1.1, h x.1.2), by
    have hx : x.1.1.fst = Ideal.Quotient.mk _ x.1.2 := x.2
    change (eMap C h x.1.1).fst = Ideal.Quotient.mk _ (h x.1.2)
    rw [fst_eMap, hx, qMap_mk]⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-- The first projection of `pMap h` is `eMap h` of the first projection. -/
theorem pullbackFst_comp_pMap :
    ((fstE C R').pullbackFst (Ideal.Quotient.mk (sqIdeal C R'))).comp (pMap C h) =
      (eMap C h).comp ((fstE C R).pullbackFst (Ideal.Quotient.mk (sqIdeal C R))) := rfl

/-- The second projection of `pMap h` is `h` of the second projection. -/
theorem pullbackSnd_comp_pMap :
    ((fstE C R').pullbackSnd (Ideal.Quotient.mk (sqIdeal C R'))).comp (pMap C h) =
      h.toRingHom.comp ((fstE C R).pullbackSnd (Ideal.Quotient.mk (sqIdeal C R))) := rfl

/-- `pMap h` intertwines the action maps `σ`. -/
theorem sigma_comp_pMap : (sigma C R').comp (pMap C h) = h.toRingHom.comp (sigma C R) := by
  ext x
  show h x.1.2 + (((eMap C h x.1.1).snd : M C R') : R') =
    h (x.1.2 + ((x.1.1.snd : M C R) : R))
  rw [snd_eMap, mMap_coe, map_add]

/-! ### Composition -/

variable {R'' : Type u} [CommRing R''] [Algebra A' R''] (h' : R' →ₐ[A'] R'')

omit hC in
/-- `qMap` takes a composite of algebra maps to the composite. -/
theorem qMap_comp : qMap C (h'.comp h) = (qMap C h').comp (qMap C h) := by
  ext x
  rfl

/-- `eMap` takes a composite of algebra maps to the composite. -/
theorem eMap_comp : eMap C (h'.comp h) = (eMap C h').comp (eMap C h) := by
  ext x
  · simp [qMap_comp]
  · simp only [snd_eMap, RingHom.coe_comp, Function.comp_apply]
    rfl

/-- `pMap` takes a composite of algebra maps to the composite. -/
theorem pMap_comp : pMap C (h'.comp h) = (pMap C h').comp (pMap C h) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · show eMap C (h'.comp h) x.1.1 = eMap C h' (eMap C h x.1.1)
    rw [eMap_comp]
    rfl
  · rfl

end Stacks.SmoothLift
