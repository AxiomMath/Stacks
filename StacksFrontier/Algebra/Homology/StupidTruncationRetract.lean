module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.Algebra.Homology.StupidTruncationLE

/-!
# A complex homotopic to an endomorphism vanishing in high degrees is a retract of a truncation

Let `C` be a cochain complex indexed by `ℤ` and let `e : C ⟶ C` be a chain map whose components
vanish in all degrees above `N`. Then `e` factors through the quotient stupid truncation
`σ^{≤N}C`: there is a chain map `σ^{≤N}C ⟶ C` whose composite with the projection
`C ⟶ σ^{≤N}C` is `e`. If moreover `e` is homotopic to the identity, then `C` is, in the homotopy
category, a retract of the bounded above complex `σ^{≤N}C`.

## Main definitions

* `StacksDraft.StupidTruncation.descOfVanishing`: the factorization of `e` through `σ^{≤N}C`.
* `StacksDraft.StupidTruncation.retractOfHomotopy`: `C` as a retract of `σ^{≤N}C` in the
  homotopy category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

noncomputable section

variable {V : Type*} [Category* V] [Preadditive V] [HasZeroObject V] (C : CochainComplex V ℤ)
  (e : C ⟶ C) (N : ℤ) (he : ∀ n, N < n → e.f n = 0)

/-- The components of `descOfVanishing`. -/
def descOfVanishingF (n : ℤ) : (C.stupidTrunc (embeddingUpIntLE N)).X n ⟶ C.X n :=
  if h : n ≤ N then
    (haveI := isIso_πStupidTruncLE_f C N n h; inv ((C.πStupidTrunc (embeddingUpIntLE N)).f n)) ≫
      e.f n
  else 0

/-- In degrees `n ≤ N`, `descOfVanishingF` is the inverse of the projection `C ⟶ σ^{≤N}C`
followed by `e`. -/
theorem descOfVanishingF_of_le (n : ℤ) (h : n ≤ N) :
    haveI := isIso_πStupidTruncLE_f C N n h
    descOfVanishingF C e N n = inv ((C.πStupidTrunc (embeddingUpIntLE N)).f n) ≫ e.f n := by
  rw [descOfVanishingF, dite_eq_left h]

/-- In degrees `n > N`, `descOfVanishingF` is zero. -/
theorem descOfVanishingF_of_lt (n : ℤ) (h : N < n) : descOfVanishingF C e N n = 0 := by
  rw [descOfVanishingF, dite_eq_right (not_le.2 h)]

include he in
/-- **A chain map vanishing above degree `N` factors through `σ^{≤N}C`.** -/
def descOfVanishing : C.stupidTrunc (embeddingUpIntLE N) ⟶ C where
  f := descOfVanishingF C e N
  comm' i j hij := by
    change i + 1 = j at hij
    subst hij
    by_cases h₁ : i + 1 ≤ N
    · have h₀ : i ≤ N := by omega
      have := isIso_πStupidTruncLE_f C N i h₀
      have := isIso_πStupidTruncLE_f C N (i + 1) h₁
      rw [descOfVanishingF_of_le C e N i h₀, descOfVanishingF_of_le C e N (i + 1) h₁,
        Category.assoc, e.comm, IsIso.inv_comp_eq, ← Category.assoc,
        (C.πStupidTrunc (embeddingUpIntLE N)).comm, Category.assoc, IsIso.hom_inv_id_assoc]
    · rw [descOfVanishingF_of_lt C e N (i + 1) (by omega), comp_zero]
      by_cases h₀ : i ≤ N
      · have := isIso_πStupidTruncLE_f C N i h₀
        rw [descOfVanishingF_of_le C e N i h₀, Category.assoc, e.comm, he (i + 1) (by omega),
          comp_zero, comp_zero]
      · rw [descOfVanishingF_of_lt C e N i (by omega), zero_comp]

include he in
/-- The factorization of `e` through `σ^{≤N}C`. -/
theorem πStupidTrunc_comp_descOfVanishing :
    C.πStupidTrunc (embeddingUpIntLE N) ≫ descOfVanishing C e N he = e := by
  ext n
  change _ ≫ descOfVanishingF C e N n = _
  by_cases h : n ≤ N
  · have := isIso_πStupidTruncLE_f C N n h
    rw [descOfVanishingF_of_le C e N n h, IsIso.hom_inv_id_assoc]
  · simp [descOfVanishingF_of_lt C e N n (by omega), he n (by omega)]

include he in
/-- **A complex homotopic, through an endomorphism vanishing above degree `N`, to its identity is
a retract of `σ^{≤N}C` in the homotopy category.** -/
def retractOfHomotopy (H : Homotopy e (𝟙 C)) :
    Retract ((HomotopyCategory.quotient V (up ℤ)).obj C)
      ((HomotopyCategory.quotient V (up ℤ)).obj (C.stupidTrunc (embeddingUpIntLE N))) where
  i := (HomotopyCategory.quotient V (up ℤ)).map (C.πStupidTrunc (embeddingUpIntLE N))
  r := (HomotopyCategory.quotient V (up ℤ)).map (descOfVanishing C e N he)
  retract := by
    rw [← Functor.map_comp, πStupidTrunc_comp_descOfVanishing,
      ← (HomotopyCategory.quotient V (up ℤ)).map_id]
    exact HomotopyCategory.eq_of_homotopy _ _ H

end

end StacksDraft.StupidTruncation
