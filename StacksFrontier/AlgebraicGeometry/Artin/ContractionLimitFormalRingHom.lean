module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# The ring map between adic completions induced by a ring map

For a ring map `f : A → A'` and ideals `I ⊆ A`, `I' ⊆ A'` with `f(I) ⊆ I'`, this file constructs
the induced ring map `A^∧ → A'^∧` from the `I`-adic completion of `A` to the `I'`-adic completion
of `A'`.

## Main definitions

* `AlgebraicGeometry.Artin.FormalDictionary.completionRingHom`: the induced ring map.

## Main results

* `AlgebraicGeometry.Artin.FormalDictionary.completionRingHom_of`: it extends `f`.
* `AlgebraicGeometry.Artin.FormalDictionary.evalₐ_completionRingHom`: it is `f` modulo powers of
  the ideals.
* `AlgebraicGeometry.Artin.FormalDictionary.completionRingHom_comp`: functoriality.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Artin.FormalDictionary

open AdicCompletion

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A''] (f : A →+* A')
  {I : Ideal A} {I' : Ideal A'} (h : I.map f ≤ I')

include h in
/-- If `f(I) ⊆ I'`, then `f(Iⁿ) ⊆ I'ⁿ` for every `n`. -/
theorem pow_le_comap_pow (n : ℕ) : I ^ n ≤ (I' ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

include h in
/-- The maps `A^∧ → A ⧸ Iⁿ → A' ⧸ I'ⁿ` induced by `f` are compatible with the transition maps
`A' ⧸ I'ⁿ → A' ⧸ I'ᵐ` for `m ≤ n`. -/
theorem completionRingHom_compat {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I' hmn).comp
        ((Ideal.quotientMap (I' ^ n) f (pow_le_comap_pow f h n)).comp
          (evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) =
      (Ideal.quotientMap (I' ^ m) f (pow_le_comap_pow f h m)).comp
        (evalₐ I m : AdicCompletion I A →+* A ⧸ I ^ m) := by
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [← AdicCompletion.factorPow_evalₐ I hmn x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hy, Ideal.quotientMap_mk]
  rfl

/-- The ring map `A^∧ → A'^∧` induced by `f : A → A'` with `f(I) ⊆ I'`. -/
noncomputable def completionRingHom : AdicCompletion I A →+* AdicCompletion I' A' :=
  liftRingHom I' (fun n => (Ideal.quotientMap (I' ^ n) f (pow_le_comap_pow f h n)).comp
      (evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) (completionRingHom_compat f h)

/-- Modulo `I'ⁿ`, `completionRingHom f h` is the map `A ⧸ Iⁿ → A' ⧸ I'ⁿ` induced by `f`. -/
@[simp]
theorem evalₐ_completionRingHom (n : ℕ) (x : AdicCompletion I A) :
    evalₐ I' n (completionRingHom f h x) =
      Ideal.quotientMap (I' ^ n) f (pow_le_comap_pow f h n) (evalₐ I n x) := by
  rw [completionRingHom, evalₐ_liftRingHom I' _ (completionRingHom_compat f h)]
  rfl

/-- `completionRingHom f h` sends the image of `a ∈ A` to the image of `f a`. -/
theorem completionRingHom_of (a : A) :
    completionRingHom f h (of I A a) = of I' A' (f a) :=
  ext_evalₐ fun n => by
    rw [evalₐ_completionRingHom, evalₐ_of, evalₐ_of, Ideal.quotientMap_mk]

/-- The map induced by `g ∘ f` is the composite of the maps induced by `f` and `g`. -/
theorem completionRingHom_comp (g : A' →+* A'') {I'' : Ideal A''} (h' : I'.map g ≤ I'')
    (h'' : I.map (g.comp f) ≤ I'') :
    (completionRingHom g h').comp (completionRingHom f h) = completionRingHom (g.comp f) h'' := by
  refine RingHom.ext fun x => ext_evalₐ (I := I'') fun n => ?_
  simp only [RingHom.comp_apply, evalₐ_completionRingHom]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

end AlgebraicGeometry.Artin.FormalDictionary

end
