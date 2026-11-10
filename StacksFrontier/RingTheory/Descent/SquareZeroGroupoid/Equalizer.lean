module

public import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid.DescentDatum

/-!
# The equalizer of a groupoid deformed along a square-zero ideal

Let `s, t : B ⇉ C` be a groupoid of rings and `J ⊆ B` an ideal of square zero whose two
extensions to `C` agree, with the reduced groupoid effective over `A₀ → B₀`. Descent
(`Module.Descent.Datum.isBaseChange`) identifies `J` with `B₀ ⊗[A₀] J₀` for `J₀ = J ∩ A`, where
`A` is the equalizer of `s` and `t`. The obstruction to lifting an element of `A₀` to `A` is an
Amitsur `1`-cocycle of `J₀`, hence a coboundary (`Module.Descent.exists_amitsurDiff₀_eq`), so
`A → A₀` is surjective with kernel `J₀`. Flatness of `A → B` is the local criterion of
Stacks 051C for the square-zero ideal `J₀`, and `B ⊗[A] B → C` is a bijection because its
reduction modulo `J` is one and its kernel is detected on `B₀ ⊗[A₀] J`, where it is the bijection
`B₀ ⊗[A₀] J ≅ J C` again.

## Main definitions

* `Module.Descent.SquareZero.toA₀`: the reduction `A → A₀` of the equalizer.

## Main results

* `Module.Descent.SquareZero.toA₀_surjective`: `A → A₀` is surjective.
* `Module.Descent.SquareZero.faithfullyFlat_eqLocus`: `B` is faithfully flat over `A`.
* `Module.Descent.SquareZero.bijective_cmp_eqLocus`: the comparison `B ⊗[A] B → C` is bijective.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open TensorProduct

universe u

namespace Module.Descent.SquareZero

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]

variable (s : B →+* C) (J : Ideal B)

/-! ### The equalizer and its reduction -/

/-- Two elements of an ideal of square zero multiply to zero. -/
private theorem mul_eq_zero_of_sq_eq_bot {R : Type*} [CommRing R] {I : Ideal R} (h : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have : x * y ∈ I ^ 2 := pow_two I ▸ Ideal.mul_mem_mul hx hy
  rwa [h, Ideal.mem_bot] at this

section Main

variable {A₀ : Type u} [CommRing A₀] [Algebra A₀ (B ⧸ J)] [Algebra A₀ (C ⧸ extJ C J)]
  [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)]
  [Module.FaithfullyFlat A₀ (B ⧸ J)]
  (hJ : J ^ 2 = ⊥) (hinv : J.map s = extJ C J)
  (hcomp : ∀ a : A₀, s₀ s J hinv (algebraMap A₀ (B ⧸ J) a) =
    algebraMap (B ⧸ J) (C ⧸ extJ C J) (algebraMap A₀ (B ⧸ J) a))
  [Module.Flat B C] (hbij : Function.Bijective (cmp (s₀ s J hinv) A₀ hcomp))
  {D : Type u} [CommRing D] [Algebra B D] (σ : C ≃+* D)
  (hσ : ∀ b, σ (s b) = algebraMap B D b)
  (m : C →+* C ⊗[B] D) (hms : ∀ b, m (s b) = s b ⊗ₜ 1)
  (hmt : ∀ b, m (algebraMap B C b) = 1 ⊗ₜ σ (algebraMap B C b))
  (e : C →+* B) (hes : ∀ b, e (s b) = b) (het : ∀ b, e (algebraMap B C b) = b)

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
include hbij in
/-- The class in `B₀` of an element of the equalizer lies in the image of `A₀`. -/
lemma mk_mem_range (a : eqLocus s) :
    Ideal.Quotient.mk J (a : B) ∈ (algebraMap A₀ (B ⧸ J)).range :=
  mem_range_of_eq (s₀ s J hinv) hcomp hbij (by rw [s₀_mk, t₀_mk, a.2])

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
include hbij in
/-- The reduction `A → A₀` of the equalizer. -/
noncomputable def toA₀ : eqLocus s →+* A₀ :=
  (RingEquiv.ofBijective (algebraMap A₀ (B ⧸ J)).rangeRestrict
      ⟨fun _x _y h => FaithfulSMul.algebraMap_injective A₀ (B ⧸ J) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩).symm.toRingHom.comp
    (((Ideal.Quotient.mk J).comp (eqLocus s).subtype).codRestrict _
      (mk_mem_range s J hinv hcomp hbij))

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
/-- The image in `B₀` of `toA₀ a` is the class of `a`. -/
lemma algebraMap_toA₀ (a : eqLocus s) :
    algebraMap A₀ (B ⧸ J) (toA₀ s J hinv hcomp hbij a) = Ideal.Quotient.mk J (a : B) := by
  set ψ := RingEquiv.ofBijective (algebraMap A₀ (B ⧸ J)).rangeRestrict
      ⟨fun x y h => FaithfulSMul.algebraMap_injective A₀ (B ⧸ J) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  have h := ψ.apply_symm_apply ⟨Ideal.Quotient.mk J (a : B), mk_mem_range s J hinv hcomp hbij a⟩
  exact congrArg Subtype.val h

include hJ hσ hms hmt hes het in
/-- The reduction `A → A₀` of the equalizer is surjective. -/
lemma toA₀_surjective : Function.Surjective (toA₀ s J hinv hcomp hbij) := by
  intro a₀
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (algebraMap A₀ (B ⧸ J) a₀)
  have hsub : s b - algebraMap B C b ∈ extJ C J := s_sub_t_mem s J hinv (hb ▸ hcomp a₀)
  obtain ⟨j, hj, hbj⟩ :=
    exists_sub_mem_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het hsub
  refine ⟨⟨b - j, hbj⟩, FaithfulSMul.algebraMap_injective A₀ (B ⧸ J) ?_⟩
  rw [algebraMap_toA₀, ← hb]
  exact Ideal.Quotient.eq.mpr (by simpa using hj)

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
/-- An element of the equalizer lies in the kernel of `toA₀` if and only if it lies in `J`. -/
lemma mem_ker_toA₀ (a : eqLocus s) :
    a ∈ RingHom.ker (toA₀ s J hinv hcomp hbij) ↔ (a : B) ∈ J := by
  rw [RingHom.mem_ker, ← (FaithfulSMul.algebraMap_injective A₀ (B ⧸ J)).eq_iff, map_zero,
    algebraMap_toA₀, Ideal.Quotient.eq_zero_iff_mem]

include hJ hσ hms hmt hes het in
/-- Every element of `J` lies in `ker (toA₀) • B`. -/
lemma mem_ker_smul_top {j : B} (hj : j ∈ J) :
    j ∈ (RingHom.ker (toA₀ s J hinv hcomp hbij)) • (⊤ : Submodule (eqLocus s) B) := by
  set d := datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
  have hJ₀ : ∀ i : d.descended, s (i : J) = algebraMap B C (i : J) := fun i =>
    (mem_descended_iff s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i).mp i.2
  obtain ⟨z, hz⟩ := (d.isBaseChange).equiv.surjective ⟨j, hj⟩
  have key : ∀ z : (B ⧸ J) ⊗[A₀] d.descended, (((d.isBaseChange).equiv z : J) : B) ∈
      (RingHom.ker (toA₀ s J hinv hcomp hbij)) • (⊤ : Submodule (eqLocus s) B) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add, Submodule.coe_add] using Submodule.add_mem _ hx hy
    | tmul y i =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [IsBaseChange.equiv_tmul]
      change ((Ideal.Quotient.mk J b • (i : J) : J) : B) ∈ _
      rw [mk_smul_of_tower, Submodule.coe_smul_of_tower, smul_eq_mul, mul_comm]
      have hi : (⟨((i : J) : B), hJ₀ i⟩ : eqLocus s) ∈ RingHom.ker (toA₀ s J hinv hcomp hbij) :=
        (mem_ker_toA₀ s J hinv hcomp hbij _).mpr (i : J).2
      exact Submodule.smul_mem_smul hi Submodule.mem_top
  simpa [hz] using key z

/-- The kernel `I₀ = J ∩ A` of the reduction `A → A₀`. -/
noncomputable abbrev I₀ : Ideal (eqLocus s) := RingHom.ker (toA₀ s J hinv hcomp hbij)

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
include hJ in
/-- If `J ^ 2 = ⊥` then `I₀ ^ 2 = ⊥`. -/
lemma I₀_sq : I₀ s J hinv hcomp hbij ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  apply Subtype.ext
  simpa using mul_eq_zero_of_sq_eq_bot hJ ((mem_ker_toA₀ s J hinv hcomp hbij x).mp hx)
    ((mem_ker_toA₀ s J hinv hcomp hbij y).mp hy)

include hJ hσ hms hmt hes het in
/-- The extension `I₀ B` of `I₀` to `B` is `J`. -/
lemma I₀_smul_top :
    I₀ s J hinv hcomp hbij • (⊤ : Submodule (eqLocus s) B) = J.restrictScalars (eqLocus s) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro a ha b _
    have h := (mem_ker_toA₀ s J hinv hcomp hbij a).mp ha
    change (a : B) * b ∈ J
    exact J.mul_mem_right b h
  · intro j hj
    exact mem_ker_smul_top s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het hj

include hJ hσ hms hmt hes het in
/-- In `I₀ ⊗[A] B`, `i ⊗ b = 0` for every `b ∈ J`. -/
lemma tmul_eq_zero_of_mem_J (i : I₀ s J hinv hcomp hbij) {b : B} (hb : b ∈ J) :
    i ⊗ₜ[eqLocus s] b = 0 := by
  refine Submodule.smul_induction_on
    ((I₀_smul_top s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).ge hb)
    (fun a ha b _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul]
    have : (a • i : I₀ s J hinv hcomp hbij) = 0 :=
      Subtype.ext (mul_eq_zero_of_sq_eq_bot (I₀_sq s J hJ hinv hcomp hbij) ha i.2)
    rw [this, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

include hJ hσ hms hmt hes het in
/-- In `I₀ ⊗[A] B`, `i ⊗ x = i ⊗ y` whenever `x` and `y` are congruent modulo `J`. -/
lemma tmul_eq_tmul_of_mk_eq (i : I₀ s J hinv hcomp hbij) {x y : B}
    (h : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y) :
    i ⊗ₜ[eqLocus s] x = i ⊗ₜ y := by
  rw [← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact tmul_eq_zero_of_mem_J s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i
    (Ideal.Quotient.eq.mp h)

/-- The inclusion `J₀ → I₀` of the descended module into the kernel of `A → A₀`. -/
def toI : (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended →+
    I₀ s J hinv hcomp hbij where
  toFun i := ⟨⟨((i : J) : B),
      (mem_descended_iff s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _).mp i.2⟩,
    (mem_ker_toA₀ s J hinv hcomp hbij _).mpr (i : J).2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Module.Flat B C] [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] in
/-- `toA₀ a` acts on `J` as `a`. -/
lemma toA₀_smul (a : eqLocus s) (x : J) : toA₀ s J hinv hcomp hbij a • x = a • x := by
  rw [← algebraMap_smul (B ⧸ J), algebraMap_toA₀, mk_smul_of_tower]
  rfl

/-- A chosen lift `B ⧸ J → B`. -/
noncomputable def lift0 : B ⧸ J → B := Function.surjInv (Ideal.Quotient.mk_surjective (I := J))

omit [CommRing C] [Algebra B C] [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] in
/-- `lift0 J β` is a lift of `β`. -/
lemma mk_lift0 (β : B ⧸ J) : Ideal.Quotient.mk J (lift0 J β) = β :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := J)) β

/-- The map `J₀ → I₀ ⊗[A] B`, `i ↦ i ⊗ lift(β)`, for a fixed `β ∈ B₀`. -/
noncomputable def κinvAt (β : B ⧸ J) :
    (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended →+
      I₀ s J hinv hcomp hbij ⊗[eqLocus s] B where
  toFun i := toI s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i ⊗ₜ lift0 J β
  map_zero' := by rw [map_zero, TensorProduct.zero_tmul]
  map_add' x y := by rw [map_add, TensorProduct.add_tmul]

/-- The left inverse `B₀ ⊗[A₀] J₀ → I₀ ⊗[A] B` of the reduction. -/
noncomputable def κinv :
    (B ⧸ J) ⊗[A₀] (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended →+
      I₀ s J hinv hcomp hbij ⊗[eqLocus s] B :=
  TensorProduct.liftAddHom
    { toFun := κinvAt s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      map_zero' := by
        ext i
        exact tmul_eq_tmul_of_mk_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _
          ((mk_lift0 J 0).trans (map_zero _).symm) |>.trans (TensorProduct.tmul_zero _ _)
      map_add' := fun x y => by
        ext i
        refine (tmul_eq_tmul_of_mk_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _
          (y := lift0 J x + lift0 J y) (by rw [mk_lift0, map_add, mk_lift0, mk_lift0])).trans ?_
        exact TensorProduct.tmul_add _ _ _ }
    (fun a₀ β i => by
      obtain ⟨a, rfl⟩ := toA₀_surjective s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het a₀
      have h1 : toI s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
          (toA₀ s J hinv hcomp hbij a • i) =
            a • toI s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i := by
        apply Subtype.ext
        apply Subtype.ext
        change (((toA₀ s J hinv hcomp hbij a • (i : J)) : J) : B) = (a : B) * ((i : J) : B)
        rw [toA₀_smul]
        rfl
      change _ ⊗ₜ lift0 J (toA₀ s J hinv hcomp hbij a • β) =
        toI s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (toA₀ s J hinv hcomp hbij a • i) ⊗ₜ
          lift0 J β
      rw [h1, TensorProduct.smul_tmul]
      refine tmul_eq_tmul_of_mk_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _ ?_
      rw [mk_lift0, Algebra.smul_def a (lift0 J β), map_mul, mk_lift0, Algebra.smul_def,
        algebraMap_toA₀]
      rfl)

/-- The inclusion `I₀ → J₀`. -/
def toJ₀ : I₀ s J hinv hcomp hbij →
    (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended := fun i =>
  ⟨⟨(i : B), (mem_ker_toA₀ s J hinv hcomp hbij _).mp i.2⟩,
    (mem_descended_iff s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _).mpr (i : eqLocus s).2⟩

/-- The reduction `I₀ ⊗[A] B → B₀ ⊗[A₀] J₀`, `i ⊗ b ↦ b̄ ⊗ i`, at a fixed `i`. -/
noncomputable def ρAt (i : I₀ s J hinv hcomp hbij) :
    B →+ (B ⧸ J) ⊗[A₀] (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended where
  toFun b := Ideal.Quotient.mk J b ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i
  map_zero' := by simp
  map_add' x y := by simp [TensorProduct.add_tmul]

/-- The reduction `I₀ ⊗[A] B → B₀ ⊗[A₀] J₀`, `i ⊗ b ↦ b̄ ⊗ i`. -/
noncomputable def ρ :
    I₀ s J hinv hcomp hbij ⊗[eqLocus s] B →+
      (B ⧸ J) ⊗[A₀] (datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).descended :=
  TensorProduct.liftAddHom
    { toFun := ρAt s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      map_zero' := by
        ext b
        change Ideal.Quotient.mk J b ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het 0 = 0
        rw [show toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het 0 = 0 from rfl,
          TensorProduct.tmul_zero]
      map_add' := fun x y => by
        ext b
        change Ideal.Quotient.mk J b ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
          (x + y) = _ ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het x +
            _ ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het y
        rw [← TensorProduct.tmul_add]
        rfl }
    (fun a i b => by
      change Ideal.Quotient.mk J b ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (a • i) =
        Ideal.Quotient.mk J (a • b) ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i
      have h1 : Ideal.Quotient.mk J (a • b) =
          toA₀ s J hinv hcomp hbij a • Ideal.Quotient.mk J b := by
        rw [Algebra.smul_def (toA₀ s J hinv hcomp hbij a), algebraMap_toA₀, ← map_mul]
        rfl
      have h2 : toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (a • i) =
          toA₀ s J hinv hcomp hbij a • toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i := by
        apply Subtype.ext
        apply Subtype.ext
        change ((a • i : I₀ s J hinv hcomp hbij) : B) =
          (((toA₀ s J hinv hcomp hbij a • ((toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i :
            _) : J)) : J) : B)
        rw [toA₀_smul]
        rfl
      rw [h1, h2, TensorProduct.smul_tmul])

/-- `κinv` is a left inverse of `ρ`. -/
lemma κinv_ρ (z : I₀ s J hinv hcomp hbij ⊗[eqLocus s] B) :
    κinv s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      (ρ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het z) = z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul i b =>
    change toI s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      (toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i) ⊗ₜ
        lift0 J (Ideal.Quotient.mk J b) = i ⊗ₜ b
    exact tmul_eq_tmul_of_mk_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het _ (mk_lift0 J _)

/-- The descent identification `B₀ ⊗[A₀] J₀ ≅ J` composed with `ρ` is the multiplication map
`I₀ ⊗[A] B → B`. -/
lemma equiv_ρ (z : I₀ s J hinv hcomp hbij ⊗[eqLocus s] B) :
    ((((datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).isBaseChange).equiv
      (ρ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het z) : J) : B) =
      TensorProduct.lid (eqLocus s) B ((I₀ s J hinv hcomp hbij).subtype.rTensor B z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | tmul i b =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    change (((datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).isBaseChange.equiv
      (Ideal.Quotient.mk J b ⊗ₜ toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i) :
        J) : B) = _
    rw [IsBaseChange.equiv_tmul]
    change ((Ideal.Quotient.mk J b • ((toJ₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het i :
      _) : J) : J) : B) = (i : eqLocus s) • b
    rw [mk_smul_of_tower, Submodule.coe_smul_of_tower, smul_eq_mul, mul_comm]
    rfl

include hJ hσ hms hmt hes het in
/-- The map `I₀ ⊗[A] B → B` is injective. -/
lemma injective_rTensor_I₀ :
    Function.Injective ((I₀ s J hinv hcomp hbij).subtype.rTensor B) := by
  intro x y hxy
  rw [← κinv_ρ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het x,
    ← κinv_ρ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het y]
  congr 1
  apply ((datum s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).isBaseChange).equiv.injective
  apply Subtype.ext
  rw [equiv_ρ, equiv_ρ, hxy]

include hJ hσ hms hmt hes het in
/-- `B ⧸ I₀ B` is flat over `A ⧸ I₀`. -/
lemma flat_quotient_I₀ :
    Module.Flat (eqLocus s ⧸ I₀ s J hinv hcomp hbij)
      (B ⧸ (I₀ s J hinv hcomp hbij • (⊤ : Submodule (eqLocus s) B))) := by
  set I := I₀ s J hinv hcomp hbij
  let eA : eqLocus s ⧸ I ≃+* A₀ := RingHom.quotientKerEquivOfSurjective
    (toA₀_surjective s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het)
  have heA : ∀ a : eqLocus s, eA (Ideal.Quotient.mk I a) = toA₀ s J hinv hcomp hbij a :=
    fun _ => rfl
  let : Algebra (eqLocus s ⧸ I) A₀ := eA.toRingHom.toAlgebra
  let lA : A₀ ≃ₗ[eqLocus s ⧸ I] (eqLocus s ⧸ I) :=
    { toFun := eA.symm
      invFun := eA
      map_add' := map_add _
      map_smul' := fun x y => by
        change eA.symm (eA x * y) = x * eA.symm y
        rw [map_mul, RingEquiv.symm_apply_apply]
      left_inv := eA.apply_symm_apply
      right_inv := eA.symm_apply_apply }
  have : Module.Flat (eqLocus s ⧸ I) A₀ := Module.Flat.of_linearEquiv lA
  let : Module (eqLocus s ⧸ I) (B ⧸ J) := Module.compHom _ eA.toRingHom
  have : IsScalarTower (eqLocus s ⧸ I) A₀ (B ⧸ J) :=
    ⟨fun x y z => by
      change (eA x * y) • z = eA x • (y • z)
      rw [mul_smul]⟩
  have : Module.Flat (eqLocus s ⧸ I) (B ⧸ J) := Module.Flat.trans (eqLocus s ⧸ I) A₀ (B ⧸ J)
  have hsm : I • (⊤ : Submodule (eqLocus s) B) = J.restrictScalars (eqLocus s) :=
    I₀_smul_top s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
  let e₀ : (B ⧸ (I • (⊤ : Submodule (eqLocus s) B))) ≃ₗ[eqLocus s] B ⧸ J :=
    (Submodule.quotEquivOfEq _ _ hsm).trans
      (Submodule.Quotient.restrictScalarsEquiv (eqLocus s) J)
  have he₀ : ∀ b : B, e₀ (Submodule.Quotient.mk b) = Ideal.Quotient.mk J b := fun _ => rfl
  have hsmul : ∀ (x : eqLocus s ⧸ I) (y : B ⧸ (I • (⊤ : Submodule (eqLocus s) B))),
      e₀ (x • y) = x • e₀ y := by
    intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change e₀ (Ideal.Quotient.mk I a • Submodule.Quotient.mk b) =
      eA (Ideal.Quotient.mk I a) • e₀ (Submodule.Quotient.mk b)
    rw [Module.Quotient.mk_smul_mk, he₀, he₀, heA,
      Algebra.smul_def (toA₀ s J hinv hcomp hbij a), algebraMap_toA₀, ← map_mul]
    rfl
  exact Module.Flat.of_linearEquiv
    { toFun := e₀
      invFun := e₀.symm
      map_add' := map_add _
      map_smul' := hsmul
      left_inv := e₀.symm_apply_apply
      right_inv := e₀.apply_symm_apply }

include hJ hinv hcomp hbij hσ hms hmt hes het in
/-- `B` is flat over the equalizer `A` of `s` and `t`. -/
lemma flat_eqLocus : Module.Flat (eqLocus s) B :=
  flat_of_sq_eq_bot (I₀ s J hinv hcomp hbij) (I₀_sq s J hJ hinv hcomp hbij)
    (flat_quotient_I₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het)
    (injective_rTensor_I₀ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het)

include hJ hinv hcomp hbij hσ hms hmt hes het in
/-- `B` is faithfully flat over the equalizer `A` of `s` and `t`. -/
lemma faithfullyFlat_eqLocus : Module.FaithfullyFlat (eqLocus s) B := by
  have := flat_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun 𝔞 h𝔞 htop => ?_⟩
  set ψ := toA₀ s J hinv hcomp hbij
  have hψ := toA₀_surjective s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
  have h𝔞' : 𝔞.map ψ ≠ ⊤ := by
    intro h
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective ψ hψ).mp
      (by rw [h]; exact Submodule.mem_top : (1 : A₀) ∈ 𝔞.map ψ)
    have hk : 1 - x ∈ RingHom.ker ψ := by rw [RingHom.mem_ker, map_sub, map_one, hx1, sub_self]
    have hsq := mul_eq_zero_of_sq_eq_bot (I₀_sq s J hJ hinv hcomp hbij) hk hk
    apply h𝔞
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : eqLocus s) = x * (2 - x) := by linear_combination hsq
    rw [h1]
    exact 𝔞.mul_mem_right _ hx
  have hFF := ((Module.FaithfullyFlat.iff_flat_and_proper_ideal A₀ (B ⧸ J)).mp
    inferInstance).2 (𝔞.map ψ) h𝔞'
  apply hFF
  have hmk : ∀ (a : eqLocus s) (b : B),
      Ideal.Quotient.mk J (a • b) = ψ a • Ideal.Quotient.mk J b := fun a b => by
    rw [Algebra.smul_def (ψ a), algebraMap_toA₀, ← map_mul]
    rfl
  let S : Submodule (eqLocus s) B :=
    { carrier := {b | Ideal.Quotient.mk J b ∈ (𝔞.map ψ) • (⊤ : Submodule A₀ (B ⧸ J))}
      add_mem' := fun ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact Submodule.add_mem _ ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [hmk]
        exact Submodule.smul_mem _ _ hb }
  have hle : 𝔞 • (⊤ : Submodule (eqLocus s) B) ≤ S := by
    rw [Submodule.smul_le]
    intro r hr n _
    change Ideal.Quotient.mk J (r • n) ∈ (𝔞.map ψ) • (⊤ : Submodule A₀ (B ⧸ J))
    rw [hmk]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem ψ hr) Submodule.mem_top
  rw [eq_top_iff]
  intro y _
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact hle (by rw [htop]; exact Submodule.mem_top)

omit [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C]
  [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)] in
/-- The class of `a • b` in `B₀` is `toA₀ a` acting on the class of `b`. -/
lemma mk_smul_eqLocus (a : eqLocus s) (b : B) :
    Ideal.Quotient.mk J (a • b) = toA₀ s J hinv hcomp hbij a • Ideal.Quotient.mk J b := by
  rw [Algebra.smul_def (toA₀ s J hinv hcomp hbij a), algebraMap_toA₀, ← map_mul]
  rfl

omit [Module.Flat B C] in
/-- The compatibility of `s` and `t` on the equalizer. -/
lemma eqLocus_comp (a : eqLocus s) :
    s (algebraMap (eqLocus s) B a) = algebraMap B C (algebraMap (eqLocus s) B a) := a.2

/-- The reduction `B ⊗[A] B → B₀ ⊗[A₀] B₀`. -/
noncomputable def red : B ⊗[eqLocus s] B →+ (B ⧸ J) ⊗[A₀] (B ⧸ J) :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun y => Ideal.Quotient.mk J x ⊗ₜ Ideal.Quotient.mk J y
          map_zero' := by simp
          map_add' := fun _ _ => by simp [TensorProduct.tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [TensorProduct.add_tmul] }
    (fun a x y => by
      change Ideal.Quotient.mk J (a • x) ⊗ₜ Ideal.Quotient.mk J y =
        Ideal.Quotient.mk J x ⊗ₜ Ideal.Quotient.mk J (a • y)
      rw [mk_smul_eqLocus s J hinv hcomp hbij, mk_smul_eqLocus s J hinv hcomp hbij,
        TensorProduct.smul_tmul])

omit [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C] in
/-- `red (x ⊗ y) = x̄ ⊗ ȳ`. -/
lemma red_tmul (x y : B) :
    red s J hinv hcomp hbij (x ⊗ₜ y) = Ideal.Quotient.mk J x ⊗ₜ Ideal.Quotient.mk J y := rfl

omit [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C] in
/-- The reduced comparison `B₀ ⊗[A₀] B₀ → C₀` composed with `red` is the comparison
`B ⊗[A] B → C` followed by reduction modulo `J C`. -/
lemma cmp₀_red (z : B ⊗[eqLocus s] B) :
    cmp (s₀ s J hinv) A₀ hcomp (red s J hinv hcomp hbij z) =
      Ideal.Quotient.mk (extJ C J) (cmp s (eqLocus s) (eqLocus_comp s) z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul x y =>
    rw [red_tmul, cmp_tmul, cmp_tmul, s₀_mk, t₀_mk, map_mul]

include hJ hinv hcomp hbij hσ hms hmt hes het in
/-- In `B ⊗[A] B`, `j ⊗ x = 0` for all `j, x ∈ J`. -/
lemma tmul_eq_zero_of_mem_J_eqLocus {j : B} (hj : j ∈ J) {x : B} (hx : x ∈ J) :
    j ⊗ₜ[eqLocus s] x = 0 := by
  refine Submodule.smul_induction_on
    ((I₀_smul_top s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).ge hx)
    (fun a ha b _ => ?_) (fun y z hy hz => ?_)
  · rw [← TensorProduct.smul_tmul]
    have h0 : (a • j : B) = 0 :=
      mul_eq_zero_of_sq_eq_bot hJ ((mem_ker_toA₀ s J hinv hcomp hbij a).mp ha) hj
    rw [h0, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hy, hz, add_zero]

/-- The map `B₀ ⊗[A₀] J → B ⊗[A] B`, `b̄ ⊗ j ↦ j ⊗ b`. -/
noncomputable def κJ : (B ⧸ J) ⊗[A₀] J →+ B ⊗[eqLocus s] B :=
  TensorProduct.liftAddHom
    { toFun := fun β =>
        { toFun := fun j => (j : B) ⊗ₜ lift0 J β
          map_zero' := by simp
          map_add' := fun _ _ => by simp [TensorProduct.add_tmul] }
      map_zero' := by
        ext j
        change (j : B) ⊗ₜ lift0 J 0 = 0
        exact tmul_eq_zero_of_mem_J_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het j.2
          (Ideal.Quotient.eq_zero_iff_mem.mp (mk_lift0 J 0))
      map_add' := fun x y => by
        ext j
        change (j : B) ⊗ₜ lift0 J (x + y) = (j : B) ⊗ₜ lift0 J x + (j : B) ⊗ₜ lift0 J y
        rw [← TensorProduct.tmul_add, ← sub_eq_zero, ← TensorProduct.tmul_sub]
        refine tmul_eq_zero_of_mem_J_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het j.2 ?_
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, mk_lift0, mk_lift0, mk_lift0,
          sub_self] }
    (fun a₀ β j => by
      obtain ⟨a, rfl⟩ := toA₀_surjective s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het a₀
      change (j : B) ⊗ₜ lift0 J (toA₀ s J hinv hcomp hbij a • β) =
        ((toA₀ s J hinv hcomp hbij a • j : J) : B) ⊗ₜ lift0 J β
      rw [toA₀_smul, Submodule.coe_smul_of_tower, TensorProduct.smul_tmul, ← sub_eq_zero,
        ← TensorProduct.tmul_sub]
      refine tmul_eq_zero_of_mem_J_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het j.2 ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, mk_lift0, mk_smul_eqLocus s J hinv hcomp hbij,
        mk_lift0, sub_self])

/-- `κJ (b̄ ⊗ j) = j ⊗ b`. -/
lemma κJ_tmul (b : B) (j : J) :
    κJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (Ideal.Quotient.mk J b ⊗ₜ j) =
      (j : B) ⊗ₜ b := by
  change (j : B) ⊗ₜ lift0 J (Ideal.Quotient.mk J b) = _
  rw [← sub_eq_zero, ← TensorProduct.tmul_sub]
  refine tmul_eq_zero_of_mem_J_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het j.2 ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, mk_lift0, sub_self]

/-- The comparison `B ⊗[A] B → C` composed with `κJ` is `α`. -/
lemma cmp_κJ (w : (B ⧸ J) ⊗[A₀] J) :
    cmp s (eqLocus s) (eqLocus_comp s) (κJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het w) =
      (α s J hinv hcomp w : C) := by
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Submodule.coe_add]
  | tmul β j =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
    rw [κJ_tmul, cmp_tmul, α_tmul, s₀_mk, mk_smul_extJ, Submodule.coe_smul_of_tower, tJ_apply,
      smul_eq_mul, mul_comm]

/-- The image of `κJ`, as an additive subgroup. -/
noncomputable abbrev rangeκJ : AddSubgroup (B ⊗[eqLocus s] B) :=
  (κJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).range

/-- `j ⊗ b` lies in the image of `κJ` for every `j ∈ J`. -/
lemma tmul_mem_rangeκJ_left {j : B} (hj : j ∈ J) (b : B) :
    j ⊗ₜ[eqLocus s] b ∈ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het :=
  ⟨Ideal.Quotient.mk J b ⊗ₜ ⟨j, hj⟩, κJ_tmul s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het b _⟩

/-- `b ⊗ j` lies in the image of `κJ` for every `j ∈ J`. -/
lemma tmul_mem_rangeκJ_right (b : B) {j : B} (hj : j ∈ J) :
    b ⊗ₜ[eqLocus s] j ∈ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het := by
  refine Submodule.smul_induction_on
    ((I₀_smul_top s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het).ge hj)
    (fun a ha c _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul]
    refine tmul_mem_rangeκJ_left s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het ?_ c
    change (a : B) * b ∈ J
    exact J.mul_mem_right b ((mem_ker_toA₀ s J hinv hcomp hbij a).mp ha)
  · rw [TensorProduct.tmul_add]
    exact AddSubgroup.add_mem _ hx hy

/-- Modulo the image of `κJ`, the class of `x ⊗ y` depends only on the classes of `x` and `y`
modulo `J`. -/
lemma mk_tmul_eq {x x' y y' : B} (hx : Ideal.Quotient.mk J x = Ideal.Quotient.mk J x')
    (hy : Ideal.Quotient.mk J y = Ideal.Quotient.mk J y') :
    (QuotientAddGroup.mk (x ⊗ₜ[eqLocus s] y) :
        (B ⊗[eqLocus s] B) ⧸ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het) =
      QuotientAddGroup.mk (x' ⊗ₜ y') := by
  rw [QuotientAddGroup.eq]
  have h : -(x ⊗ₜ[eqLocus s] y) + x' ⊗ₜ y' = (x' - x) ⊗ₜ y + x' ⊗ₜ (y' - y) := by
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [h]
  refine AddSubgroup.add_mem _
    (tmul_mem_rangeκJ_left s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      (Ideal.Quotient.eq.mp hx.symm) y)
    (tmul_mem_rangeκJ_right s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het x'
      (Ideal.Quotient.eq.mp hy.symm))

/-- The map `B₀ ⊗[A₀] B₀ → (B ⊗[A] B) ⧸ im κJ` lifting both factors. -/
noncomputable def μbar : (B ⧸ J) ⊗[A₀] (B ⧸ J) →+
    (B ⊗[eqLocus s] B) ⧸ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het :=
  TensorProduct.liftAddHom
    { toFun := fun β =>
        { toFun := fun β' => QuotientAddGroup.mk (lift0 J β ⊗ₜ lift0 J β')
          map_zero' := by
            rw [mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het rfl
              (y' := 0) (by rw [mk_lift0, map_zero]), TensorProduct.tmul_zero,
              QuotientAddGroup.mk_zero]
          map_add' := fun x y => by
            rw [mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het rfl
              (y' := lift0 J x + lift0 J y) (by rw [mk_lift0, map_add, mk_lift0, mk_lift0]),
              TensorProduct.tmul_add, QuotientAddGroup.mk_add] }
      map_zero' := by
        ext β'
        change QuotientAddGroup.mk (lift0 J 0 ⊗ₜ lift0 J β') = 0
        rw [mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
          (x' := 0) (by rw [mk_lift0, map_zero]) rfl, TensorProduct.zero_tmul,
          QuotientAddGroup.mk_zero]
      map_add' := fun x y => by
        ext β'
        change (QuotientAddGroup.mk (lift0 J (x + y) ⊗ₜ[eqLocus s] lift0 J β') :
            (B ⊗[eqLocus s] B) ⧸ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het) =
          QuotientAddGroup.mk (lift0 J x ⊗ₜ[eqLocus s] lift0 J β') +
            QuotientAddGroup.mk (lift0 J y ⊗ₜ[eqLocus s] lift0 J β')
        rw [mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
          (x' := lift0 J x + lift0 J y) (by rw [mk_lift0, map_add, mk_lift0, mk_lift0]) rfl,
          TensorProduct.add_tmul, QuotientAddGroup.mk_add] }
    (fun a₀ β β' => by
      obtain ⟨a, rfl⟩ := toA₀_surjective s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het a₀
      change (QuotientAddGroup.mk (lift0 J (toA₀ s J hinv hcomp hbij a • β) ⊗ₜ[eqLocus s]
          lift0 J β') :
            (B ⊗[eqLocus s] B) ⧸ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het) =
        QuotientAddGroup.mk (lift0 J β ⊗ₜ[eqLocus s] lift0 J (toA₀ s J hinv hcomp hbij a • β'))
      rw [mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
          (x' := a • lift0 J β) (by rw [mk_lift0, mk_smul_eqLocus s J hinv hcomp hbij, mk_lift0])
          rfl,
        mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (x' := lift0 J β) rfl
          (y' := a • lift0 J β') (by rw [mk_lift0, mk_smul_eqLocus s J hinv hcomp hbij, mk_lift0]),
        TensorProduct.smul_tmul])

/-- `μbar ∘ red` is the quotient map `B ⊗[A] B → (B ⊗[A] B) ⧸ im κJ`. -/
lemma μbar_red (z : B ⊗[eqLocus s] B) :
    μbar s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (red s J hinv hcomp hbij z) =
      QuotientAddGroup.mk z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, QuotientAddGroup.mk_add]
  | tmul x y =>
    change (QuotientAddGroup.mk (lift0 J (Ideal.Quotient.mk J x) ⊗ₜ[eqLocus s]
      lift0 J (Ideal.Quotient.mk J y)) :
        (B ⊗[eqLocus s] B) ⧸ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het) = _
    exact mk_tmul_eq s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het (mk_lift0 J _) (mk_lift0 J _)

/-- The kernel of `red` is contained in the image of `κJ`. -/
lemma mem_rangeκJ_of_red_eq_zero {z : B ⊗[eqLocus s] B} (hz : red s J hinv hcomp hbij z = 0) :
    z ∈ rangeκJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het := by
  have h := μbar_red s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het z
  rw [hz, map_zero] at h
  exact (QuotientAddGroup.eq_zero_iff z).mp h.symm

omit [Algebra A₀ (C ⧸ extJ C J)] [IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J)]
  [Module (B ⧸ J) J] [IsScalarTower B (B ⧸ J) J] [Module A₀ J] [IsScalarTower A₀ (B ⧸ J) J]
  [Module (C ⧸ extJ C J) (extJ C J)] [IsScalarTower C (C ⧸ extJ C J) (extJ C J)]
  [Module A₀ (extJ C J)] [IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J)] [Module.Flat B C] in
/-- The reduction `B ⊗[A] B → B₀ ⊗[A₀] B₀` is surjective. -/
lemma red_surjective : Function.Surjective (red s J hinv hcomp hbij) := by
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul β β' =>
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective β
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective β'
    exact ⟨x ⊗ₜ y, rfl⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

include hJ hinv hcomp hbij hσ hms hmt hes het in
/-- The comparison `B ⊗[A] B → C` over the equalizer `A` of `s` and `t` is bijective. -/
theorem bijective_cmp_eqLocus :
    Function.Bijective (cmp s (eqLocus s) (eqLocus_comp s)) := by
  have hα := α_bijective (s := s) (J := J) (hinv := hinv) (hcomp := hcomp) hbij
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hred : red s J hinv hcomp hbij z = 0 := by
      apply hbij.1
      rw [cmp₀_red, hz, map_zero, map_zero]
    obtain ⟨w, rfl⟩ := mem_rangeκJ_of_red_eq_zero s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het
      hred
    rw [cmp_κJ] at hz
    have hw : α s J hinv hcomp w = 0 := Subtype.ext hz
    rw [(injective_iff_map_eq_zero _).mp hα.1 w hw, map_zero]
  · intro c
    obtain ⟨w₀, hw₀⟩ := hbij.2 (Ideal.Quotient.mk (extJ C J) c)
    obtain ⟨z, rfl⟩ := red_surjective s J hinv hcomp hbij w₀
    rw [cmp₀_red] at hw₀
    have hmem : c - cmp s (eqLocus s) (eqLocus_comp s) z ∈ extJ C J := by
      rw [← Ideal.Quotient.eq]
      exact hw₀.symm
    obtain ⟨w, hw⟩ := hα.2 ⟨_, hmem⟩
    refine ⟨z + κJ s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het w, ?_⟩
    rw [map_add, cmp_κJ, hw]
    simp

end Main

end Module.Descent.SquareZero

end
