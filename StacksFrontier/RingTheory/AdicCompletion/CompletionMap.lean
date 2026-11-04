module

public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The completion of an algebra map

For an `A`-algebra `B` and an ideal `I` of `A`, `AdicCompletion.completionMap I` is the induced
algebra map from the `I`-adic completion of `A` to the `IB`-adic completion of `B`. For a ring
homomorphism `f : A →+* B` carrying an ideal `J` of `A` into an ideal `I` of `B`,
`adicCompletionMap f J I` is the induced ring homomorphism from the `J`-adic completion of `A` to
the `I`-adic completion of `B`.

## Main definitions

* `AdicCompletion.completionMap`: the algebra map `A^∧_I → B^∧_{IB}` induced by `A → B`.
* `adicCompletionMap`: the ring homomorphism `A^∧_J → B^∧_I` induced by `f : A →+* B` with
  `J.map f ≤ I`.
-/

@[expose] public section

universe u v

namespace AdicCompletion

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The level-`n` map `AdicCompletion I A → B ⧸ (IB) ^ n`, the level-`n` evaluation followed by
the reduction of `A → B`. -/
noncomputable def completionLevel (I : Ideal A) (n : ℕ) :
    AdicCompletion I A →ₐ[A] B ⧸ (I.map (algebraMap A B)) ^ n :=
  (Ideal.quotientMapₐ ((I.map (algebraMap A B)) ^ n) (Algebra.ofId A B)
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)).comp (evalₐ I n)

/-- The level maps `completionLevel` are compatible with the transition maps. -/
theorem factor_completionLevel (I : Ideal A) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
        (completionLevel (B := B) I n) = completionLevel I m := by
  ext x
  simp only [completionLevel, AlgHom.coe_comp, Function.comp_apply]
  rw [← factorPow_evalₐ I hmn x]
  exact congr($(Ideal.Quotient.factorPow_comp_quotientMap (algebraMap A B) I
    (I.map (algebraMap A B)) hmn (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
    (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)) (evalₐ I n x))

/-- The completion of an algebra map, as an algebra map from the `I`-adic completion of the base
to the completion of the algebra along the extended ideal. -/
noncomputable def completionMap (I : Ideal A) :
    AdicCompletion I A →ₐ[A] AdicCompletion (I.map (algebraMap A B)) B :=
  liftAlgHom _ (completionLevel I) (fun hmn => factor_completionLevel I hmn)

/-- Level-`n` evaluation of `completionMap` sends a representative `a` of `x` to the class of
`algebraMap A B a`. -/
theorem evalₐ_completionMap (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) (a : A)
    (ha : evalₐ I n x = Ideal.Quotient.mk (I ^ n) a) :
    evalₐ (I.map (algebraMap A B)) n (completionMap (B := B) I x) =
      Ideal.Quotient.mk _ (algebraMap A B a) := by
  rw [completionMap, evalₐ_liftAlgHom _ (completionLevel I)
    (fun hmn => factor_completionLevel I hmn)]
  simp [completionLevel, ha]

/-- Level-`n` value of `completionMap`: it sends a representative `a` of `x` at level `n` to the
class of `algebraMap A B a`. -/
theorem val_completionMap (I : Ideal A) (n : ℕ) (x : AdicCompletion I A) (a : A)
    (ha : x.val n = Submodule.Quotient.mk a) :
    (completionMap (B := B) I x).val n = Submodule.Quotient.mk (algebraMap A B a) :=
  val_eq_mk _ n _ _ (evalₐ_completionMap I n x a (evalₐ_eq_mk I n x a ha))

/-- `completionMap` agrees with `algebraMap A B` on the image of `A`. -/
theorem completionMap_algebraMap (I : Ideal A) (a : A) :
    completionMap (B := B) I (algebraMap A (AdicCompletion I A) a) =
      algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) (algebraMap A B a) :=
  (completionMap (B := B) I).commutes a


end AdicCompletion

/-! ### The induced map for an arbitrary ring homomorphism -/

/-- The map on adic completions induced by a ring homomorphism `f : A →+* B` that carries
`J ⊆ A` into `I ⊆ B`. -/
public noncomputable def adicCompletionMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (J : Ideal A) (I : Ideal B)
    (hf : J.map f ≤ I) : AdicCompletion J A →+* AdicCompletion I B :=
  let hle : ∀ n : ℕ, J ^ n ≤ (I ^ n).comap f := fun n ↦
    Ideal.map_le_iff_le_comap.mp (by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hf n)
  AdicCompletion.liftRingHom I
    (fun n ↦ (Ideal.quotientMap _ f (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom)
    (fun {m n} hmn ↦ by
      ext x
      induction x using AdicCompletion.induction_on with
      | h a =>
        simp only [RingHom.comp_apply]
        change Ideal.Quotient.factorPow I hmn
            (Ideal.quotientMap (I ^ n) f (hle n) (AdicCompletion.evalₐ J n
              (AdicCompletion.mk J A a))) =
          Ideal.quotientMap (I ^ m) f (hle m) (AdicCompletion.evalₐ J m
            (AdicCompletion.mk J A a))
        rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
        simp only [Ideal.quotientMap_mk, Ideal.Quotient.factorPow,
          Ideal.Quotient.factor_mk]
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
        apply hle m
        simpa only [neg_sub, smul_eq_mul, Ideal.mul_top] using
          (Submodule.neg_mem (J ^ m • (⊤ : Submodule A A))
            (SModEq.sub_mem.mp (a.property hmn))))

/-- The `n`-th evaluation of `adicCompletionMap` is the reduction of `f` modulo the `n`-th
powers. -/
public theorem adicCompletionMap_evalₐ {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map f ≤ J)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicCompletionMap f I J h x) =
      Ideal.quotientMap (J ^ n) f
        (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]; exact pow_le_pow_left' h n))
        (AdicCompletion.evalₐ I n x) := by
  rw [adicCompletionMap, AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- `adicCompletionMap f J I hf` commutes with the maps from the uncompleted rings. -/
public lemma adicCompletionMap_comp_algebraMap {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (J : Ideal A) (I : Ideal B)
    (hf : J.map f ≤ I) :
    (adicCompletionMap f J I hf).comp (algebraMap A (AdicCompletion J A)) =
      (algebraMap B (AdicCompletion I B)).comp f :=
  RingHom.ext fun _ => AdicCompletion.ext_evalₐ fun _ => by
    simp [adicCompletionMap_evalₐ]
