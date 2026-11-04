module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerSucc

/-!
# The successor equation for the integer addition law, uniformly in the second exponent

`Stacks.TensorPowers.TensorInverse.addIso` is the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of the integer tensor powers of an object `L` carrying a
two-sided tensor inverse. It recurses on its second exponent, and the two halves of that
recursion come with their own successor equations:
`Stacks.TensorPowers.TensorInverse.addNatIso_succ` upwards and
`Stacks.TensorPowers.TensorInverse.subNatIso_succ` downwards. This file glues them, along
`Stacks.TensorPowers.TensorInverse.addIso_neg_natCast`, into one successor equation for an
arbitrary integer second exponent.

## Main results

* `Stacks.TensorPowers.TensorInverse.addIso_succ`: the successor equation for the addition law,
  uniformly in the integer second exponent.
* `Stacks.TensorPowers.TensorInverse.addIso_succ_natCast` and
  `Stacks.TensorPowers.TensorInverse.addIso_succ_neg_natCast`: the two halves. The second
  carries the snake-compatibility hypothesis of `subNatIso_succ` on the two inverse laws of `L`,
  which holds for an invertible sheaf of modules by
  `AlgebraicGeometry.SheafOfModules.tensorInverse_snake`.
* `Stacks.TensorPowers.TensorInverse.addIso_congr_right` and
  `Stacks.TensorPowers.TensorInverse.addIso_congr_left`: the addition law commutes with the
  transport along an equality of either exponent.

## Implementation notes

`addIso_succ` takes `m` and `m'` with `hm : m + 1 = m'` rather than speaking of `m + 1`: at a
negative second exponent `Int.negSucc k + 1` and `-(k : ℤ)` are the same integer but not the same
term, and the transport `reindex L h.inv hm.symm` in the statement compares the two spellings.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- Two transports along mutually inverse equalities of degrees cancel. -/
theorem reindex_comp_reindex {L : C} (h : TensorInverse L) {n m k : ℤ} (hnm : n = m)
    (hmk : m = k) :
    (reindex L h.inv hnm).hom ≫ (reindex L h.inv hmk).hom =
      (reindex L h.inv (hnm.trans hmk)).hom := by
  simp only [reindex, eqToIso.hom, eqToHom_trans]

/-- A transport along a reflexive equality of degrees is the identity. -/
theorem reindex_self {L : C} (h : TensorInverse L) {n : ℤ} (hn : n = n) :
    (reindex L h.inv hn).hom = 𝟙 (intTensorPow L h.inv n) := rfl

/-- The addition law commutes with the transport along an equality of the second exponent. -/
theorem addIso_congr_right {L : C} (h : TensorInverse L) (n : ℤ) {m m' : ℤ} (hm : m = m') :
    (h.addIso n m').hom =
      (intTensorPow L h.inv n ◁ (reindex L h.inv hm.symm).hom) ≫ (h.addIso n m).hom ≫
        (reindex L h.inv (show n + m = n + m' from by omega)).hom := by
  cases hm
  simp [reindex_self]

/-- The addition law commutes with the transport along an equality of the first exponent. -/
theorem addIso_congr_left {L : C} (h : TensorInverse L) {n n' : ℤ} (hn : n = n') (m : ℤ) :
    (h.addIso n' m).hom =
      ((reindex L h.inv hn.symm).hom ▷ intTensorPow L h.inv m) ≫ (h.addIso n m).hom ≫
        (reindex L h.inv (show n + m = n' + m from by omega)).hom := by
  cases hn
  simp [reindex_self]

/-- The successor equation for the addition law at a nonnegative second exponent: this is
`Stacks.TensorPowers.TensorInverse.addNatIso_succ`, read through the integer spelling of the
exponent. -/
theorem addIso_succ_natCast {L : C} (h : TensorInverse L) (n : ℤ) (k : ℕ) :
    (h.addIso n ((k : ℤ) + 1)).hom =
      (intTensorPow L h.inv n ◁ (h.succIso (k : ℤ)).hom) ≫
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (k : ℤ)) L).inv ≫
          ((h.addIso n (k : ℤ)).hom ▷ L) ≫
            (h.succIso (n + (k : ℤ))).inv ≫
              (reindex L h.inv (show n + (k : ℤ) + 1 = n + ((k : ℤ) + 1) from by omega)).hom :=
  congrArg Iso.hom (addNatIso_succ h n k)

/-- The successor equation for the addition law at a negative second exponent: this is
`Stacks.TensorPowers.TensorInverse.subNatIso_succ`, read through
`Stacks.TensorPowers.TensorInverse.addIso_neg_natCast`. -/
theorem addIso_succ_neg_natCast {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (n : ℤ) (k : ℕ) :
    (h.addIso n (-(k : ℤ))).hom =
      (intTensorPow L h.inv n ◁
          ((reindex L h.inv (show -(k : ℤ) = -((k : ℤ) + 1) + 1 from by omega)).hom ≫
            (h.succIso (-((k : ℤ) + 1))).hom)) ≫
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv (-((k : ℤ) + 1))) L).inv ≫
          ((h.addIso n (-((k : ℤ) + 1))).hom ▷ L) ≫
            (h.succIso (n + -((k : ℤ) + 1))).inv ≫
              (reindex L h.inv
                (show n + -((k : ℤ) + 1) + 1 = n + -(k : ℤ) from by omega)).hom := by
  have e0 : (h.addIso n (-(k : ℤ))).hom =
      (h.subNatIso n k).hom ≫
        (reindex L h.inv (show n - (k : ℤ) = n + -(k : ℤ) from by omega)).hom :=
    addIso_neg_natCast h n k
  have e1 : (h.addIso n (-((k : ℤ) + 1))).hom =
      (h.subNatIso n (k + 1)).hom ≫
        (reindex L h.inv
          (show n - ((k : ℤ) + 1) = n + -((k : ℤ) + 1) from by omega)).hom :=
    addIso_neg_natCast h n (k + 1)
  have key := subNatIso_succ h hs n k
    ((reindex L h.inv (show -(k : ℤ) = -((k : ℤ) + 1) + 1 from by omega)).hom ≫
      (h.succIso (-((k : ℤ) + 1))).hom)
    (((reindex L h.inv
          (show n - ((k : ℤ) + 1) = n + -((k : ℤ) + 1) from by omega)).hom ▷ L) ≫
      (h.succIso (n + -((k : ℤ) + 1))).inv ≫
        (reindex L h.inv
          (show n + -((k : ℤ) + 1) + 1 = n - (k : ℤ) from by omega)).hom)
    (by
      rw [reindex_whiskerRight_succIso h
            (show -((k : ℤ) + 1) = -(k : ℤ) - 1 from by omega)
            (show -(k : ℤ) - 1 + 1 = -(k : ℤ) from by omega)
            (show -((k : ℤ) + 1) + 1 = -((k : ℤ) + 1) + 1 from rfl)
            (show -((k : ℤ) + 1) + 1 = -(k : ℤ) from by omega), reindex_self,
        Category.id_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [reindex_comp_reindex, reindex_self])
    (by
      rw [← reindex_comp_reindex h
            (show n - ((k : ℤ) + 1) = n - (k : ℤ) - 1 from by omega)
            (show n - (k : ℤ) - 1 = n + -((k : ℤ) + 1) from by omega),
        MonoidalCategory.comp_whiskerRight]
      simp only [Category.assoc]
      rw [reindex_whiskerRight_succIso h
            (show n - (k : ℤ) - 1 = n + -((k : ℤ) + 1) from by omega)
            (show n + -((k : ℤ) + 1) + 1 = n - (k : ℤ) from by omega)
            (show n - (k : ℤ) - 1 + 1 = n - (k : ℤ) from by omega)
            (show n - (k : ℤ) = n - (k : ℤ) from rfl), reindex_self, Category.comp_id])
  rw [e0, ← key, e1, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [reindex_comp_reindex]

/-- The successor equation for the addition law, uniformly in the integer second exponent `m`:
multiplication by `L ^⊗ m'`, `m' = m + 1`, is multiplication by `L ^⊗ m` with one factor of `L`
split off by `Stacks.TensorPowers.TensorInverse.succIso` at the second exponent and put back by
the same comparison at the total degree. -/
theorem addIso_succ {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (n m m' : ℤ) (hm : m + 1 = m') :
    (h.addIso n m').hom =
      (intTensorPow L h.inv n ◁ ((reindex L h.inv hm.symm).hom ≫ (h.succIso m).hom)) ≫
        (α_ (intTensorPow L h.inv n) (intTensorPow L h.inv m) L).inv ≫
          ((h.addIso n m).hom ▷ L) ≫
            (h.succIso (n + m)).inv ≫
              (reindex L h.inv (show n + m + 1 = n + m' from by omega)).hom := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ :
      (∃ k : ℕ, m = (k : ℤ)) ∨ (∃ k : ℕ, m = -((k : ℤ) + 1)) := by
    rcases m with k | k
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, Int.negSucc_eq k⟩
  · obtain rfl : m' = (k : ℤ) + 1 := hm.symm
    rw [reindex_self, Category.id_comp]
    exact addIso_succ_natCast h n k
  · obtain rfl : m' = -(k : ℤ) := by omega
    exact addIso_succ_neg_natCast h hs n k

end Stacks.TensorPowers.TensorInverse

end
