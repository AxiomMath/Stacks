module

public import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid.Equalizer

/-!
# Deforming an effective flat groupoid along a nilpotent invariant ideal

A *groupoid of rings* here is a pair of ring maps `s, t : B → C`, with `t = algebraMap B C`
flat, together with a unit `e : C → B` (`e ∘ s = e ∘ t = id`) and a composition
`m : C → C ⊗[B] D` (`m ∘ s = s ⊗ 1`, `m ∘ t = 1 ⊗ σ ∘ t`), where `σ : C ≃+* D` is a copy of
`C` whose `B`-algebra structure is that of `s`. It is *effective* when it is the Čech groupoid of
a faithfully flat ring map: some `A → B` is faithfully flat, `s` and `t` agree on `A`, and
`B ⊗[A] B → C`, `x ⊗ y ↦ t x * s y`, is bijective.

Let `K ⊆ B` be a nilpotent ideal whose two extensions to `C` agree. The main result says: **if the
reduced groupoid `B ⧸ K ⇉ C ⧸ K C` is effective, then so is the groupoid itself**, over the
equalizer of `s` and `t`.

This is the ring-level content of the source's proof that a first-order, and hence a
finite-order, thickening of an affine algebraic space is affine (the proof for finite order
thickenings of Stacks 05ZR, with the vanishing of `H¹` of Stacks 05ZQ). On a surjective étale
affine chart `V = Spec B` of the thickening with `V ×_X V = Spec C`, `K` is the ideal of the
closed subspace, and the conclusion says that the thickening is `Spec A`.

## Main results

* `Module.Descent.SquareZero.isEffective_of_sq_eq_bot`: the deformation statement along an ideal
  of square zero.
* `Module.Descent.SquareZero.isEffective_of_pow_eq_bot`: **the deformation statement along a
  nilpotent ideal**, by induction on the nilpotency exponent through the groupoids modulo the
  powers of the ideal.
* `Module.Descent.SquareZero.isEffective_s₀_of_bijective_tensorLift`: effectiveness of a reduced
  groupoid from a bijective `Stacks.AffineStageCore.tensorLift`.

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

/-! ### The deformation statement -/

/-- **An effective flat groupoid deforms along a square-zero invariant ideal.** Let `s, t : B ⇉ C`
be a groupoid of rings (`t = algebraMap B C` flat, unit `e`, composition `m` into `C ⊗[B] D` for
a copy `σ : C ≃+* D` of `C` carrying the `B`-algebra structure of `s`), and let `J ⊆ B` be an
ideal of square zero with `s(J) C = t(J) C`. If the reduced groupoid `B ⧸ J ⇉ C ⧸ J C` is
effective, then so is the groupoid itself. -/
theorem isEffective_of_sq_eq_bot [Module.Flat B C] {D : Type u} [CommRing D] [Algebra B D]
    (σ : C ≃+* D) (hσ : ∀ b, σ (s b) = algebraMap B D b)
    (m : C →+* C ⊗[B] D) (hms : ∀ b, m (s b) = s b ⊗ₜ 1)
    (hmt : ∀ b, m (algebraMap B C b) = 1 ⊗ₜ σ (algebraMap B C b))
    (e : C →+* B) (hes : ∀ b, e (s b) = b) (het : ∀ b, e (algebraMap B C b) = b)
    (hJ : J ^ 2 = ⊥) (hinv : J.map s = extJ C J) (h₀ : IsEffective (s₀ s J hinv)) :
    IsEffective s := by
  obtain ⟨A₀, _, _, hcomp, _, hbij⟩ := h₀
  let : Algebra A₀ (C ⧸ extJ C J) :=
    ((algebraMap (B ⧸ J) (C ⧸ extJ C J)).comp (algebraMap A₀ (B ⧸ J))).toAlgebra
  have : IsScalarTower A₀ (B ⧸ J) (C ⧸ extJ C J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module (B ⧸ J) J := quotModule J hJ
  have : IsScalarTower B (B ⧸ J) J := (isTorsionBySet_of_sq J hJ).isScalarTower
  let : Module A₀ J := Module.compHom J (algebraMap A₀ (B ⧸ J))
  have : IsScalarTower A₀ (B ⧸ J) J := ⟨fun a b j => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let : Module (C ⧸ extJ C J) (extJ C J) := quotModule _ (extJ_sq C J hJ)
  have : IsScalarTower C (C ⧸ extJ C J) (extJ C J) :=
    (isTorsionBySet_of_sq _ (extJ_sq C J hJ)).isScalarTower
  let : Module A₀ (extJ C J) := Module.compHom _ (algebraMap A₀ (C ⧸ extJ C J))
  have : IsScalarTower A₀ (C ⧸ extJ C J) (extJ C J) :=
    ⟨fun a b j => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact ⟨eqLocus s, inferInstance, inferInstance, eqLocus_comp s,
    faithfullyFlat_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het,
    bijective_cmp_eqLocus s J hJ hinv hcomp hbij σ hσ m hms hmt e hes het⟩

/-! ### The groupoid modulo an invariant ideal -/

section Quotient

variable {D : Type u} [CommRing D] [Algebra B D] (σ : C ≃+* D)
  (hσ : ∀ b, σ (s b) = algebraMap B D b)
  (m : C →+* C ⊗[B] D) (hms : ∀ b, m (s b) = s b ⊗ₜ 1)
  (hmt : ∀ b, m (algebraMap B C b) = 1 ⊗ₜ σ (algebraMap B C b))
  (e : C →+* B) (hes : ∀ b, e (s b) = b) (het : ∀ b, e (algebraMap B C b) = b)
  (L : Ideal B) (hL : L.map s = extJ C L)

omit [Algebra B D] in
include hσ in
/-- `σ` modulo `L`. -/
noncomputable def σq : C ⧸ extJ C L ≃+* D ⧸ extJ D L :=
  Ideal.quotientEquiv (extJ C L) (extJ D L) σ (map_σ_extJ s L σ hσ hL).symm

/-- `σq` sends the class of `c` to the class of `σ c`. -/
lemma σq_mk (c : C) :
    σq s σ hσ L hL (Ideal.Quotient.mk (extJ C L) c) = Ideal.Quotient.mk (extJ D L) (σ c) := rfl

/-- `σq ∘ s₀` is the structure map `B ⧸ L → D ⧸ L D`. -/
lemma σq_s₀ (β : B ⧸ L) :
    σq s σ hσ L hL (s₀ s L hL β) = algebraMap (B ⧸ L) (D ⧸ extJ D L) β := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  rw [s₀_mk, σq_mk, hσ, t₀_mk]

omit [Algebra B D] in
/-- The unit `e` modulo `L`. -/
def eq' : C ⧸ extJ C L →+* B ⧸ L :=
  Ideal.quotientMap L e (Ideal.map_le_iff_le_comap.mp (by
    rw [extJ, Ideal.map_map, show e.comp (algebraMap B C) = RingHom.id B from RingHom.ext het,
      Ideal.map_id]))

omit [Algebra B D] in
/-- `eq'` sends the class of `c` to the class of `e c`. -/
lemma eq'_mk (c : C) : eq' e het L (Ideal.Quotient.mk (extJ C L) c) = Ideal.Quotient.mk L (e c) :=
  Ideal.quotientMap_mk

/-- The left factor of the induced map on tensor products. -/
noncomputable def quotLeft : C →ₐ[B] (C ⧸ extJ C L) ⊗[B ⧸ L] (D ⧸ extJ D L) :=
  ((Algebra.TensorProduct.includeLeft : C ⧸ extJ C L →ₐ[B ⧸ L] _).restrictScalars B).comp
    (Ideal.Quotient.mkₐ B (extJ C L))

/-- The right factor of the induced map on tensor products. -/
noncomputable def quotRight : D →ₐ[B] (C ⧸ extJ C L) ⊗[B ⧸ L] (D ⧸ extJ D L) :=
  ((Algebra.TensorProduct.includeRight : D ⧸ extJ D L →ₐ[B ⧸ L] _).restrictScalars B).comp
    (Ideal.Quotient.mkₐ B (extJ D L))

/-- The induced map `C ⊗[B] D → (C ⧸ L C) ⊗[B ⧸ L] (D ⧸ L D)`. -/
noncomputable def quotTensorMap : C ⊗[B] D →+* (C ⧸ extJ C L) ⊗[B ⧸ L] (D ⧸ extJ D L) :=
  (Algebra.TensorProduct.lift (quotLeft L) (quotRight L) (fun _ _ => Commute.all _ _)).toRingHom

/-- `quotTensorMap` sends `c ⊗ d` to `c̄ ⊗ d̄`. -/
lemma quotTensorMap_tmul (c : C) (d : D) :
    quotTensorMap L (c ⊗ₜ d) =
      Ideal.Quotient.mk (extJ C L) c ⊗ₜ[B ⧸ L] Ideal.Quotient.mk (extJ D L) d := by
  show quotLeft L c * quotRight L d = _
  simp [quotLeft, quotRight, Algebra.TensorProduct.tmul_mul_tmul]

include hσ hmt hL in
/-- `L C` lies in the kernel of `m` followed by `quotTensorMap`. -/
lemma le_ker_quotTensorMap_comp : extJ C L ≤ RingHom.ker ((quotTensorMap L).comp m) := by
  refine Ideal.map_le_iff_le_comap.mpr fun l hl => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hmt, quotTensorMap_tmul,
    Ideal.Quotient.eq_zero_iff_mem.mpr (σ_mem_extJ s L σ hσ hL (Ideal.mem_map_of_mem _ hl)),
    TensorProduct.tmul_zero]

/-- The composition `m` modulo `L`. -/
noncomputable def mq : C ⧸ extJ C L →+* (C ⧸ extJ C L) ⊗[B ⧸ L] (D ⧸ extJ D L) :=
  Ideal.Quotient.lift (extJ C L) ((quotTensorMap L).comp m)
    (fun _x hx => le_ker_quotTensorMap_comp s σ hσ m hmt L hL hx)

/-- `mq` sends the class of `c` to the image of `m c`. -/
lemma mq_mk (c : C) :
    mq s σ hσ m hmt L hL (Ideal.Quotient.mk (extJ C L) c) = quotTensorMap L (m c) := rfl

include hms in
/-- `mq ∘ s₀ = s₀ ⊗ 1`. -/
lemma mq_s₀ (β : B ⧸ L) : mq s σ hσ m hmt L hL (s₀ s L hL β) = s₀ s L hL β ⊗ₜ 1 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  rw [s₀_mk, mq_mk, hms, quotTensorMap_tmul, map_one]

/-- `mq ∘ t₀ = 1 ⊗ σq ∘ t₀`. -/
lemma mq_t₀ (β : B ⧸ L) :
    mq s σ hσ m hmt L hL (algebraMap (B ⧸ L) (C ⧸ extJ C L) β) =
      1 ⊗ₜ σq s σ hσ L hL (algebraMap (B ⧸ L) (C ⧸ extJ C L) β) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  rw [t₀_mk, mq_mk, hmt, quotTensorMap_tmul, map_one, σq_mk]

include hes in
/-- `eq' ∘ s₀ = id`. -/
lemma eq'_s₀ (β : B ⧸ L) : eq' e het L (s₀ s L hL β) = β := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  rw [s₀_mk, eq'_mk, hes]

/-- `eq' ∘ t₀ = id`. -/
lemma eq'_t₀ (β : B ⧸ L) : eq' e het L (algebraMap (B ⧸ L) (C ⧸ extJ C L) β) = β := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective β
  rw [t₀_mk, eq'_mk, het]

end Quotient

/-! ### Effectiveness from a bijective tensor comparison -/

section TensorLift

/-- **Effectiveness of a reduced groupoid from a bijective tensor comparison.** The reduced
groupoid `B ⧸ K ⇉ C ⧸ K C` is effective as soon as some faithfully flat `A → B ⧸ K` equalizes its
two maps and makes the comparison `Stacks.AffineStageCore.tensorLift` bijective. This converts
the output of `AlgebraicGeometry.Space.exists_effective_of_isAffineSpace` into the hypothesis of
`Module.Descent.SquareZero.isEffective_of_pow_eq_bot`. -/
theorem isEffective_s₀_of_bijective_tensorLift {B C : Type u} [CommRing B] [CommRing C]
    [Algebra B C] (s : B →+* C) (K : Ideal B) (hK : K.map s = extJ C K)
    {A : Type u} [CommRing A] [Algebra A (B ⧸ K)] [Module.FaithfullyFlat A (B ⧸ K)]
    (hst : (Stacks.AffineStageCore.sBar (algebraMap B C) K).comp (algebraMap A (B ⧸ K)) =
      (Stacks.AffineStageCore.tBar (algebraMap B C) s K hK).comp (algebraMap A (B ⧸ K)))
    (hbij : Function.Bijective (Stacks.AffineStageCore.tensorLift
      (Stacks.AffineStageCore.sBar (algebraMap B C) K)
      (Stacks.AffineStageCore.tBar (algebraMap B C) s K hK) hst)) :
    IsEffective (s₀ s K hK) := by
  have hσ : ∀ x : B ⧸ K, Stacks.AffineStageCore.sBar (algebraMap B C) K x =
      algebraMap (B ⧸ K) (C ⧸ extJ C K) x := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Stacks.AffineStageCore.sBar_mk, t₀_mk]
  have hτ : ∀ x : B ⧸ K, Stacks.AffineStageCore.tBar (algebraMap B C) s K hK x = s₀ s K hK x := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Stacks.AffineStageCore.tBar_mk, s₀_mk]
  have h : ∀ a : A, s₀ s K hK (algebraMap A (B ⧸ K) a) =
      algebraMap (B ⧸ K) (C ⧸ extJ C K) (algebraMap A (B ⧸ K) a) := by
    intro a
    have := congrArg (fun f : A →+* C ⧸ extJ C K => f a) hst
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    rw [← hσ, ← hτ, this]
  refine ⟨A, inferInstance, inferInstance, h, inferInstance, ?_⟩
  have hfun : (cmp (s₀ s K hK) A h : (B ⧸ K) ⊗[A] (B ⧸ K) → C ⧸ extJ C K) =
      Stacks.AffineStageCore.tensorLift (Stacks.AffineStageCore.sBar (algebraMap B C) K)
        (Stacks.AffineStageCore.tBar (algebraMap B C) s K hK) hst := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul x y => rw [cmp_tmul, Stacks.AffineStageCore.tensorLift_tmul, hσ, hτ]
  rw [hfun]
  exact hbij

end TensorLift

/-! ### Nilpotent invariant ideals -/

section Nilpotent

omit [CommRing C] [Algebra B C] in
/-- The image of `K` in `B ⧸ K ^ n` has `n`-th power zero. -/
lemma map_mk_pow_eq_bot {K : Ideal B} {n : ℕ} :
    (K.map (Ideal.Quotient.mk (K ^ n))) ^ n = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

/-- If `K` and `J` are invariant ideals of `B`, the two extensions of the image of `K` in
`B ⧸ J` to `C ⧸ J C` are both the image of `K C`. -/
lemma extJ_quot_eq (K J : Ideal B) (hK : K.map s = extJ C K) (hJ : J.map s = extJ C J) :
    (K.map (Ideal.Quotient.mk J)).map (s₀ s J hJ) = (extJ C K).map (Ideal.Quotient.mk (extJ C J)) ∧
      extJ (C ⧸ extJ C J) (K.map (Ideal.Quotient.mk J)) =
        (extJ C K).map (Ideal.Quotient.mk (extJ C J)) := by
  constructor
  · rw [Ideal.map_map, ← hK, Ideal.map_map]
    congr 1
  · show (K.map (Ideal.Quotient.mk J)).map (algebraMap (B ⧸ J) (C ⧸ extJ C J)) =
      (K.map (algebraMap B C)).map (Ideal.Quotient.mk (extJ C J))
    rw [Ideal.map_map, Ideal.map_map]
    congr 1

/-- If `K ^ a = ⊥` and `a ≤ b` then `K ^ b = ⊥`. -/
private lemma pow_eq_bot_of_le {K : Ideal B} {a b : ℕ} (h : K ^ a = ⊥) (hab : a ≤ b) :
    K ^ b = ⊥ :=
  le_bot_iff.mp (h ▸ Ideal.pow_le_pow_right hab)

/-- **An effective flat groupoid deforms along a nilpotent invariant ideal.** Let `s, t : B ⇉ C`
be a groupoid of rings as in `Module.Descent.SquareZero.isEffective_of_sq_eq_bot`, and let
`K ⊆ B` be a nilpotent ideal with `s(K) C = t(K) C`. If the reduced groupoid
`B ⧸ K ⇉ C ⧸ K C` is effective, then so is the groupoid itself. -/
theorem isEffective_of_pow_eq_bot {B C D : Type u} [CommRing B] [CommRing C] [Algebra B C]
    [Module.Flat B C] [CommRing D] [Algebra B D]
    (s : B →+* C) (σ : C ≃+* D) (hσ : ∀ b, σ (s b) = algebraMap B D b)
    (e : C →+* B) (hes : ∀ b, e (s b) = b) (het : ∀ b, e (algebraMap B C b) = b)
    (m : C →+* C ⊗[B] D) (hms : ∀ b, m (s b) = s b ⊗ₜ 1)
    (hmt : ∀ b, m (algebraMap B C b) = 1 ⊗ₜ σ (algebraMap B C b))
    (K : Ideal B) (hK : K.map s = extJ C K) {n : ℕ} (hn : K ^ n = ⊥)
    (h₀ : IsEffective (s₀ s K hK)) : IsEffective s := by
  induction n generalizing B C D with
  | zero =>
    exact isEffective_of_sq_eq_bot s K σ hσ m hms hmt e hes het
      (pow_eq_bot_of_le hn (Nat.zero_le 2)) hK h₀
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact isEffective_of_sq_eq_bot s K σ hσ m hms hmt e hes het
        (pow_eq_bot_of_le hn (by norm_num)) hK h₀
    set J := K ^ n with hJdef
    have hJ2 : J ^ 2 = ⊥ := by
      rw [hJdef, ← pow_mul]
      exact pow_eq_bot_of_le hn (by omega)
    have hinvJ : J.map s = extJ C J := by
      rw [hJdef, Ideal.map_pow, hK, extJ, extJ, Ideal.map_pow]
    have hJK : J ≤ K := Ideal.pow_le_self (by omega)
    have : Module.Flat (B ⧸ J) (C ⧸ extJ C J) := flat_quotient_map (R := B) (S := C) J
    obtain ⟨hKs, hKt⟩ := extJ_quot_eq s K J hK hinvJ
    have hK' : (K.map (Ideal.Quotient.mk J)).map (s₀ s J hinvJ) =
        extJ (C ⧸ extJ C J) (K.map (Ideal.Quotient.mk J)) := hKs.trans hKt.symm
    have hn' : (K.map (Ideal.Quotient.mk J)) ^ n = ⊥ := map_mk_pow_eq_bot
    have h₀' : IsEffective (s₀ (s₀ s J hinvJ) (K.map (Ideal.Quotient.mk J)) hK') := by
      refine IsEffective.of_ringEquiv (s₀ s K hK) (DoubleQuot.quotQuotEquivQuotOfLE hJK).symm
        ((DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hJK : extJ C J ≤ extJ C K)).symm.trans
          (Ideal.quotEquivOfEq hKt.symm)) (fun b => ?_) (fun b => ?_) h₀ <;>
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b <;> rfl
    have hJeff : IsEffective (s₀ s J hinvJ) :=
      ih (s₀ s J hinvJ) (σq s σ hσ J hinvJ) (σq_s₀ s σ hσ J hinvJ) (eq' e het J)
        (eq'_s₀ s e hes het J hinvJ) (eq'_t₀ e het J) (mq s σ hσ m hmt J hinvJ)
        (mq_s₀ s σ hσ m hms hmt J hinvJ) (mq_t₀ s σ hσ m hmt J hinvJ)
        (K.map (Ideal.Quotient.mk J)) hK' hn' h₀'
    exact isEffective_of_sq_eq_bot s J σ hσ m hms hmt e hes het hJ2 hinvJ hJeff

end Nilpotent

end Module.Descent.SquareZero

end
