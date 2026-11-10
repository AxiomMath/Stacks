module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingProjectionFormula.PairingAssociativity

/-!
# Associativity of the multiplication of Stacks 0FA0

The common term `Stacks.Chow.localizedGradingMulAssocTerm` of the two groupings of a triple
product, each grouping as a double convolution of those terms, and from them
`Stacks.Chow.localizedBivariantGradingMul_assoc` and
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc` (Stacks 0FA0); the graded algebra as a
bundled `Semigroup` and `Monoid`; and the same associativity at the Gysin system of the first
Chern class rule.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section RestrictionPushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-! ### The common term of the two groupings of a triple product -/

/-- **The `(m, j, l)` term of a triple product of Stacks 0FA0**, in the total degree
`n = m + (j + l)` at or above the cutoff `r` of the target: `m`, `j`, `l` are the degrees of the
factors taken from `a`, `b`, `c`.

It is the value both groupings `(a · b) · c` and `a · (b · c)` give that term, which is what
associativity says; the degrees are written as a separate decomposition of `n` so that the type
does not depend on them, two decompositions of one `n` therefore giving equal terms by
`Stacks.Chow.localizedGradingMulAssocTerm_congr`.

Which of the pairings of Stacks 0FA0 applies is decided by the first two factors alone: by the
first pairing applied to the product in `A^*(X)` of the other two when `m` reaches the cutoff `p`
of `a`; otherwise by the second pairing applied to the first pairing of the other two when `j`
reaches the cutoff `q` of `b`; and otherwise by the second pairing twice, `l` then reaching the
cutoff `s` of `c` of itself, since the target is admissible. -/
def localizedGradingMulAssocTerm (p q s r : ℕ) (hpqs : p + q + s ≤ r + 2)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n)
    (m j l : ℤ) (hl : m + (j + l) = n) : BivariantClass C G (f ≫ sX) sX f rfl n :=
  bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hl
    (if hm : (p : ℤ) ≤ m then
      localizedMulBivariantChow C G sX f hgys hgysc m (j + l) (a.2 ⟨m, hm⟩)
        (chowCohomologyComposite C G sX hgys hgysc j l
          (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc q b j)
          (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c l))
    else if hj : (q : ℤ) ≤ j then
      localizedMulChowBivariant C G sX f hgys hgysc m (j + l) (a.1 ⟨m, not_le.1 hm⟩)
        (localizedMulBivariantChow C G sX f hgys hgysc j l (b.2 ⟨j, hj⟩)
          (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c l))
    else
      localizedMulChowBivariant C G sX f hgys hgysc m (j + l) (a.1 ⟨m, not_le.1 hm⟩)
        (localizedMulChowBivariant C G sX f hgys hgysc j l (b.1 ⟨j, not_le.1 hj⟩)
          (c.2 ⟨l, by omega⟩)))

/-- Two decompositions of one total degree give the same term of a triple product: the type of
`Stacks.Chow.localizedGradingMulAssocTerm` does not depend on the decomposition, so an equality of
degrees is an equality of terms. This is what reconciles the decomposition `(m, i - m, n - i)`
that the grouping `(a · b) · c` produces with the decomposition `(m, j, n - m - j)` of
`a · (b · c)`. -/
theorem localizedGradingMulAssocTerm_congr (p q s r : ℕ) (hpqs : p + q + s ≤ r + 2)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n)
    (m j l l' : ℤ) (h : l = l') (hl : m + (j + l) = n) (hl' : m + (j + l') = n) :
    localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r hpqs a b c n hn m j l
        hl =
      localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r hpqs a b c n hn m j l'
        hl' := by
  subst h
  rfl

/-- The term of a triple product whose factor from `a` reaches the cutoff of `a`. -/
theorem localizedGradingMulAssocTerm_of_le (p q s r : ℕ) (hpqs : p + q + s ≤ r + 2)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n)
    (m j l : ℤ) (hl : m + (j + l) = n) (hm : (p : ℤ) ≤ m) :
    localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r hpqs a b c n hn m j l hl =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hl
        (localizedMulBivariantChow C G sX f hgys hgysc m (j + l) (a.2 ⟨m, hm⟩)
          (chowCohomologyComposite C G sX hgys hgysc j l
            (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc q b j)
            (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c l))) := by
  unfold localizedGradingMulAssocTerm
  rw [dite_eq_left hm]

/-- The term of a triple product whose factor from `a` is below the cutoff of `a` and whose factor
from `b` reaches the cutoff of `b`. -/
theorem localizedGradingMulAssocTerm_of_lt_of_le (p q s r : ℕ) (hpqs : p + q + s ≤ r + 2)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n)
    (m j l : ℤ) (hl : m + (j + l) = n) (hm : m < (p : ℤ)) (hj : (q : ℤ) ≤ j) :
    localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r hpqs a b c n hn m j l hl =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hl
        (localizedMulChowBivariant C G sX f hgys hgysc m (j + l) (a.1 ⟨m, hm⟩)
          (localizedMulBivariantChow C G sX f hgys hgysc j l (b.2 ⟨j, hj⟩)
            (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c l))) := by
  unfold localizedGradingMulAssocTerm
  rw [dite_eq_right (not_le.2 hm), dite_eq_left hj]

/-- The term of a triple product whose factors from `a` and from `b` are both below the cutoff:
the factor from `c` then reaches the cutoff of `c` of itself. -/
theorem localizedGradingMulAssocTerm_of_lt_of_lt (p q s r : ℕ) (hpqs : p + q + s ≤ r + 2)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n)
    (m j l : ℤ) (hl : m + (j + l) = n) (hm : m < (p : ℤ)) (hj : j < (q : ℤ)) :
    localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r hpqs a b c n hn m j l hl =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hl
        (localizedMulChowBivariant C G sX f hgys hgysc m (j + l) (a.1 ⟨m, hm⟩)
          (localizedMulChowBivariant C G sX f hgys hgysc j l (b.1 ⟨j, hj⟩)
            (c.2 ⟨l, by omega⟩))) := by
  unfold localizedGradingMulAssocTerm
  rw [dite_eq_right (not_le.2 hm), dite_eq_right (not_le.2 hj)]

/-! ### The grouping that multiplies the last two factors first -/

/-- **The degree `n` component of `a · (b · c)`, for `n` at or above the cutoff of the target, is
the double convolution of the terms of the triple product** over the index range of the sums at
`n` and then at `n - m`, which for `n ≥ r ≥ 0` is `0 ≤ m ≤ n`, `0 ≤ j ≤ n - m`.
This grouping needs no input beyond the two component formulas and the uniform form
`Stacks.Chow.localizedGradingMulLocalizedTerm_of_le` of a term: the pairings it applies are
already the ones `Stacks.Chow.localizedGradingMulAssocTerm` names. -/
theorem localizedBivariantGradingMul_snd_right (p q s r₂ r : ℕ) (h₃ : q + s ≤ r₂ + 1)
    (h₄ : p + r₂ ≤ r + 1) (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p r₂ r a
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc q s r₂ b c)).2 ⟨n, hn⟩ =
      ∑ m ∈ Finset.Icc (min 0 n) (max 0 n), ∑ j ∈ Finset.Icc (min 0 (n - m)) (max 0 (n - m)),
        localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c n hn
          m j (n - m - j) (by ring) := by
  rw [localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc p r₂ r a _ ⟨n, hn⟩]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases hm : (p : ℤ) ≤ m
  · rw [localizedGradingMulLocalizedTerm_of_le C G sX f hRG hgysP hgys hgysc p r₂ a _ n
      m hm, localizedBivariantGradingMul_isAmbientConvolution C G sX f hRG hgysP hgys hgysc q s r₂
      h₃ b c (n - m), localizedMulBivariantChow_sum_right, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [localizedGradingMulAssocTerm_of_le C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c
      n hn m j (n - m - j) (by ring) hm]
    unfold localizedGradingMulAmbientTerm
    exact bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _
      (localizedMulBivariantChow_bivariantClassDegreeCongr_right C G sX f hgys hgysc (by ring) m
        (a.2 ⟨m, hm⟩) _)
  · rw [localizedGradingMulLocalizedTerm_of_lt C G sX f hgys hgysc p r₂ a _ n m
      (not_le.1 hm) (by omega),
      localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc q s r₂ b c
        ⟨n - m, by omega⟩, localizedMulChowBivariant_sum_right, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : (q : ℤ) ≤ j
    · rw [localizedGradingMulLocalizedTerm_of_le C G sX f hRG hgysP hgys hgysc q s b c
        (n - m) j hj,
        localizedGradingMulAssocTerm_of_lt_of_le C G sX f hRG hgysP hgys hgysc p q s r (by omega)
          a b c n hn m j (n - m - j) (by ring) (not_le.1 hm) hj]
      exact bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _
        (localizedMulChowBivariant_bivariantClassDegreeCongr_right C G sX f hgys hgysc (by ring) m
          (a.1 ⟨m, not_le.1 hm⟩) _)
    · rw [localizedGradingMulLocalizedTerm_of_lt C G sX f hgys hgysc q s b c (n - m)
        j (not_le.1 hj) (by omega),
        localizedGradingMulAssocTerm_of_lt_of_lt C G sX f hRG hgysP hgys hgysc p q s r (by omega)
          a b c n hn m j (n - m - j) (by ring) (not_le.1 hm) (not_le.1 hj)]
      exact bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _
        (localizedMulChowBivariant_bivariantClassDegreeCongr_right C G sX f hgys hgysc (by ring) m
          (a.1 ⟨m, not_le.1 hm⟩) _)

/-! ### The grouping that multiplies the first two factors first -/

/-- **The `(i, m)` term of the grouping `(a · b) · c` is the term of the triple product, in a
degree `i` of the inner product at or above the cutoff `r₁` of its target.** There the inner
product's degree `i` component is localized, and the identity is the associativity of Stacks 0B75
at the first pairing (`Stacks.Chow.localizedMulBivariantChow_localizedMulBivariantChow_heq`) for
`m ≥ p` and at the first and the second pairing
(`Stacks.Chow.localizedMulBivariantChow_localizedMulChowBivariant_heq`) for `m < p`, where the
second factor's degree `i - m` reaches `q` of itself. -/
theorem localizedGradingMulAssocTerm_eq_of_le (p q s r₁ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (h₂ : r₁ + s ≤ r + 1) (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n) (i : ℤ)
    (hi : (r₁ : ℤ) ≤ i) (m : ℤ) :
    bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulBivariantChow C G sX f hgys hgysc i (n - i)
          (localizedGradingMulLocalizedTerm C G sX f hgys hgysc p q a b i m)
          (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c (n - i))) =
      localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c n hn m
        (i - m) (n - i) (by ring) := by
  by_cases hm : (p : ℤ) ≤ m
  · rw [localizedGradingMulLocalizedTerm_of_le C G sX f hRG hgysP hgys hgysc p q a b i
      m hm, localizedGradingMulAssocTerm_of_le C G sX f hRG hgysP hgys hgysc p q s r (by omega)
      a b c n hn m (i - m) (n - i) (by ring) hm]
    refine bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _ ?_
    refine HEq.trans (localizedMulBivariantChow_bivariantClassDegreeCongr_left C G sX f hgys
      hgysc (by ring : m + (i - m) = i) (n - i) _ _) ?_
    exact localizedMulBivariantChow_localizedMulBivariantChow_heq C G sX f hgys hgysc m (i - m)
      (n - i) (a.2 ⟨m, hm⟩) _ _
  · rw [localizedGradingMulLocalizedTerm_of_lt C G sX f hgys hgysc p q a b i m
      (not_le.1 hm) (by omega),
      localizedGradingMulAssocTerm_of_lt_of_le C G sX f hRG hgysP hgys hgysc p q s r
      (by omega) a b c n hn m (i - m) (n - i) (by ring) (not_le.1 hm)
      (show (q : ℤ) ≤ i - m by omega)]
    refine bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _ ?_
    refine HEq.trans (localizedMulBivariantChow_bivariantClassDegreeCongr_left C G sX f hgys
      hgysc (by ring : m + (i - m) = i) (n - i) _ _) ?_
    exact localizedMulBivariantChow_localizedMulChowBivariant_heq C G sX f hgys hgysc m (i - m)
      (n - i) _ _ _

/-- Associating a product `u · v` in `A^*(X)` through the second pairing, up to the transports of
the degrees. -/
private theorem localizedMulChowBivariant_degreeCongr_composite_eq {m j l i n : ℤ}
    {hi : m + j = i} {hn : i + l = n} {he : m + (j + l) = n}
    (u : chowCohomologyComponent C G sX m) (v : chowCohomologyComponent C G sX j)
    (w : BivariantClass C G (f ≫ sX) sX f rfl l)
    (R : BivariantClass C G (f ≫ sX) sX f rfl (m + (j + l))) (hR : R =
      localizedMulChowBivariant C G sX f hgys hgysc m (j + l) u
        (localizedMulChowBivariant C G sX f hgys hgysc j l v w)) :
    bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hn
        (localizedMulChowBivariant C G sX f hgys hgysc i l
          (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hi
            (chowCohomologyComposite C G sX hgys hgysc m j u v)) w) =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl he R := by
  subst hi hn
  exact bivariantClassDegreeCongr_eq_of_heq C G (f ≫ sX) sX f rfl _ _ _ _
    ((localizedMulChowBivariant_bivariantClassDegreeCongr_left C G sX f hgys hgysc _ _ _ _).trans
      ((localizedMulChowBivariant_chowCohomologyComposite_heq C G sX f hgys hgysc m j l _ _ _).trans
        (heq_of_eq hR.symm)))

/-- **The `(i, m)` term of the grouping `(a · b) · c` is the term of the triple product, in a
degree `i` of the inner product below the cutoff `r₁` of its target.** There the inner product's
degree `i` component has been read in `A^*(X)` by Stacks 0EPK, and the identity is the
associativity of Stacks 0B75 at the second pairing
(`Stacks.Chow.localizedMulChowBivariant_chowCohomologyComposite_heq`) followed, in the two cases
where a factor of the inner product was localized, by
`Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward_eq`: reading that factor in
`A^*(X)` loses nothing. -/
theorem localizedGradingMulAssocTerm_eq_of_lt (p q s r₁ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (h₂ : r₁ + s ≤ r + 1) (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n) (i : ℤ)
    (m : ℤ) (hs : (s : ℤ) ≤ n - i) :
    bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i + (n - i) = n)
        (localizedMulChowBivariant C G sX f hgys hgysc i (n - i)
          (localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b i m)
          (c.2 ⟨n - i, hs⟩)) =
      localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c n hn m
        (i - m) (n - i) (by ring) := by
  unfold localizedGradingMulAmbientTerm
  by_cases hm : (p : ℤ) ≤ m
  · rw [localizedGradingMulAssocTerm_of_le C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c
      n hn m (i - m) (n - i) (by ring) hm]
    refine localizedMulChowBivariant_degreeCongr_composite_eq C G sX f hgys hgysc _ _ _ _ ?_
    rw [localizedGradingComponentOnAmbient_of_le C G sX f hRG hgysP hgysc p a m hm,
      localizedMulChowBivariant_localizedGradingPushforward_eq C G sX f hRG hgysP hgys hgysc m
        ((i - m) + (n - i)) (a.2 ⟨m, hm⟩) _,
      localizedGradingPushforward_localizedMulChowBivariant C G sX f hRG hgysP hgys hgysc (i - m)
        (n - i) _ (c.2 ⟨n - i, hs⟩),
      ← localizedGradingComponentOnAmbient_of_le C G sX f hRG hgysP hgysc s c (n - i) hs]
  · by_cases hj : (q : ℤ) ≤ i - m
    · rw [localizedGradingMulAssocTerm_of_lt_of_le C G sX f hRG hgysP hgys hgysc p q s r
        (by omega) a b c n hn m (i - m) (n - i) (by ring) (not_le.1 hm) hj]
      refine localizedMulChowBivariant_degreeCongr_composite_eq C G sX f hgys hgysc _ _ _ _ ?_
      rw [localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p a m (not_le.1 hm),
        localizedGradingComponentOnAmbient_of_le C G sX f hRG hgysP hgysc q b (i - m) hj,
        localizedMulChowBivariant_localizedGradingPushforward_eq C G sX f hRG hgysP hgys hgysc
          (i - m) (n - i) (b.2 ⟨i - m, hj⟩) (c.2 ⟨n - i, hs⟩),
        ← localizedGradingComponentOnAmbient_of_le C G sX f hRG hgysP hgysc s c (n - i) hs]
    · rw [localizedGradingMulAssocTerm_of_lt_of_lt C G sX f hRG hgysP hgys hgysc p q s r
        (by omega) a b c n hn m (i - m) (n - i) (by ring) (not_le.1 hm) (not_le.1 hj)]
      refine localizedMulChowBivariant_degreeCongr_composite_eq C G sX f hgys hgysc _ _ _ _ ?_
      rw [localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p a m (not_le.1 hm),
        localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc q b (i - m)
          (not_le.1 hj)]

/-! ### The two groupings in the degrees below the cutoff -/

/-- The multiplication of `A^*(X)` commutes with a finite sum in its left argument. -/
theorem chowCohomologyComposite_sum_left {ι : Type*} (s : Finset ι) (i j : ℤ)
    (u : ι → chowCohomologyComponent C G sX i) (v : chowCohomologyComponent C G sX j) :
    chowCohomologyComposite C G sX hgys hgysc i j (∑ m ∈ s, u m) v =
      ∑ m ∈ s, chowCohomologyComposite C G sX hgys hgysc i j (u m) v :=
  map_sum (AddMonoidHom.mk' (fun w ↦ chowCohomologyComposite C G sX hgys hgysc i j w v)
    fun w w' ↦ chowCohomologyComposite_add_left C G sX hgys hgysc i j w w' v) u s

/-- The multiplication of `A^*(X)` commutes with a finite sum in its right argument. -/
theorem chowCohomologyComposite_sum_right {ι : Type*} (s : Finset ι) (i j : ℤ)
    (u : chowCohomologyComponent C G sX i) (v : ι → chowCohomologyComponent C G sX j) :
    chowCohomologyComposite C G sX hgys hgysc i j u (∑ m ∈ s, v m) =
      ∑ m ∈ s, chowCohomologyComposite C G sX hgys hgysc i j u (v m) :=
  map_sum (AddMonoidHom.mk' (fun w ↦ chowCohomologyComposite C G sX hgys hgysc i j u w)
    fun w w' ↦ chowCohomologyComposite_add_right C G sX hgys hgysc i j u w w') v s

/-- Transport of the left argument of the multiplication of `A^*(X)`. -/
theorem chowCohomologyComposite_bivariantClassDegreeCongr_left {d d' : ℤ} (h : d = d') (l : ℤ)
    (u : chowCohomologyComponent C G sX d) (v : chowCohomologyComponent C G sX l) :
    chowCohomologyComposite C G sX hgys hgysc d' l
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h u) v ≍
      chowCohomologyComposite C G sX hgys hgysc d l u v := by
  subst h
  rfl

/-- Transport of the right argument of the multiplication of `A^*(X)`. -/
theorem chowCohomologyComposite_bivariantClassDegreeCongr_right {d d' : ℤ} (h : d = d') (m : ℤ)
    (u : chowCohomologyComponent C G sX m) (v : chowCohomologyComponent C G sX d) :
    chowCohomologyComposite C G sX hgys hgysc m d' u
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h v) ≍
      chowCohomologyComposite C G sX hgys hgysc m d u v := by
  subst h
  rfl

/-- **The `(m, j, l)` term of a triple product of Stacks 0FA0 read in `A^*(X)`**, in the total
degree `n = m + (j + l)`: the product in `A^*(X)` of the three factors' components read in
`A^*(X)` by Stacks 0EPK, bracketed to the right. As with
`Stacks.Chow.localizedGradingMulAssocTerm`, the degrees are a separate decomposition of `n`, so
that the type does not depend on them. -/
def localizedGradingMulAssocAmbientTerm (p q s : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n m j l : ℤ)
    (hl : m + (j + l) = n) : chowCohomologyComponent C G sX n :=
  bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hl
    (chowCohomologyComposite C G sX hgys hgysc m (j + l)
      (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p a m)
      (chowCohomologyComposite C G sX hgys hgysc j l
        (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc q b j)
        (localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc s c l)))

/-- Two decompositions of one total degree give the same term of a triple product read in
`A^*(X)`. -/
theorem localizedGradingMulAssocAmbientTerm_congr (p q s : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n m j l l' : ℤ) (h : l = l')
    (hl : m + (j + l) = n) (hl' : m + (j + l') = n) :
    localizedGradingMulAssocAmbientTerm C G sX f hRG hgysP hgys hgysc p q s a b c n m j l hl =
      localizedGradingMulAssocAmbientTerm C G sX f hRG hgysP hgys hgysc p q s a b c n m j l'
        hl' := by
  subst h
  rfl

/-- **The degree `n` component of `(a · b) · c`, for `n` below the cutoff of the target, is the
double convolution in `A^*(X)` of the three factors' components read there.** The inner product is
read in `A^*(X)` by `Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution` and the
bracketing is moved by the associativity of the multiplication of `A^*(X)`,
`Stacks.Chow.chowCohomologyComposite_assoc`. -/
theorem localizedBivariantGradingMul_fst_left (p q s r₁ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : n < (r : ℤ)) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc r₁ s r
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r₁ a b) c).1
        ⟨n, hn⟩ =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n), ∑ m ∈ Finset.Icc (min 0 i) (max 0 i),
        localizedGradingMulAssocAmbientTerm C G sX f hRG hgysP hgys hgysc p q s a b c n m (i - m)
          (n - i) (by ring) := by
  rw [localizedBivariantGradingMul_fst C G sX f hRG hgysP hgys hgysc r₁ s r _ c ⟨n, hn⟩]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold localizedGradingMulAmbientTerm
  rw [localizedBivariantGradingMul_isAmbientConvolution C G sX f hRG hgysP hgys hgysc p q r₁ h₁
    a b i, chowCohomologyComposite_sum_left, map_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  unfold localizedGradingMulAssocAmbientTerm localizedGradingMulAmbientTerm
  refine bivariantClassDegreeCongr_eq_of_heq C G sX sX (𝟙 X) (Category.id_comp sX) _ _ _ _ ?_
  refine HEq.trans (chowCohomologyComposite_bivariantClassDegreeCongr_left C G sX hgys hgysc
    (by ring : m + (i - m) = i) (n - i) _ _) ?_
  exact chowCohomologyComposite_assoc C G sX hgys hgysc m (i - m) (n - i) _ _ _

/-- **The degree `n` component of `a · (b · c)`, for `n` below the cutoff of the target, is the
same double convolution in `A^*(X)`**, in the decomposition the other grouping produces. -/
theorem localizedBivariantGradingMul_fst_right (p q s r₂ r : ℕ) (h₃ : q + s ≤ r₂ + 1)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : n < (r : ℤ)) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p r₂ r a
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc q s r₂ b c)).1 ⟨n, hn⟩ =
      ∑ m ∈ Finset.Icc (min 0 n) (max 0 n), ∑ j ∈ Finset.Icc (min 0 (n - m)) (max 0 (n - m)),
        localizedGradingMulAssocAmbientTerm C G sX f hRG hgysP hgys hgysc p q s a b c n m j
          (n - m - j) (by ring) := by
  rw [localizedBivariantGradingMul_fst C G sX f hRG hgysP hgys hgysc p r₂ r a _ ⟨n, hn⟩]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  unfold localizedGradingMulAmbientTerm
  rw [localizedBivariantGradingMul_isAmbientConvolution C G sX f hRG hgysP hgys hgysc q s r₂ h₃
    b c (n - m), chowCohomologyComposite_sum_right, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  unfold localizedGradingMulAssocAmbientTerm localizedGradingMulAmbientTerm
  refine bivariantClassDegreeCongr_eq_of_heq C G sX sX (𝟙 X) (Category.id_comp sX) _ _ _ _ ?_
  exact chowCohomologyComposite_bivariantClassDegreeCongr_right C G sX hgys hgysc
    (by ring : j + (n - m - j) = n - m) m _ _

/-- **The degree `n` component of `(a · b) · c`, for `n` at or above the cutoff of the target, is
the double convolution of the terms of the triple product** over the index range of the sums at
`n` and then at `i`, which for `n ≥ r ≥ 0` is `0 ≤ i ≤ n`, `0 ≤ m ≤ i`, where `i` is the total
degree of the inner product `a · b` and `m` the degree of the factor from `a`.
This is where the three instances of the associativity of Stacks 0B75 for the pairings are
consumed, through `Stacks.Chow.localizedGradingMulAssocTerm_eq_of_le` and
`Stacks.Chow.localizedGradingMulAssocTerm_eq_of_lt`. -/
theorem localizedBivariantGradingMul_snd_left (p q s r₁ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (h₂ : r₁ + s ≤ r + 1) (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) (n : ℤ) (hn : (r : ℤ) ≤ n) :
    (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc r₁ s r
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r₁ a b) c).2
        ⟨n, hn⟩ =
      ∑ i ∈ Finset.Icc (min 0 n) (max 0 n), ∑ m ∈ Finset.Icc (min 0 i) (max 0 i),
        localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c n hn
          m (i - m) (n - i) (by ring) := by
  rw [localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc r₁ s r _ c ⟨n, hn⟩]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : (r₁ : ℤ) ≤ i
  · rw [localizedGradingMulLocalizedTerm_of_le C G sX f hRG hgysP hgys hgysc r₁ s _ c n
      i hi, localizedBivariantGradingMul_snd C G sX f hRG hgysP hgys hgysc p q r₁ a b ⟨i, hi⟩,
      localizedMulBivariantChow_sum_left, map_sum]
    exact Finset.sum_congr rfl fun m _ ↦
      localizedGradingMulAssocTerm_eq_of_le C G sX f hRG hgysP hgys hgysc p q s r₁ r h₁ h₂ a b c
        n hn i hi m
  · rw [localizedGradingMulLocalizedTerm_of_lt C G sX f hgys hgysc r₁ s _ c n i
      (not_le.1 hi) (by omega),
      localizedBivariantGradingMul_fst C G sX f hRG hgysP hgys hgysc p q r₁ a b
        ⟨i, not_le.1 hi⟩, localizedMulChowBivariant_sum_left, map_sum]
    exact Finset.sum_congr rfl fun m _ ↦
      localizedGradingMulAssocTerm_eq_of_lt C G sX f hRG hgysP hgys hgysc p q s r₁ r h₁ h₂ a b c
        n hn i m (by omega)

/-! ### Associativity -/

/-- **Stacks 0FA0, associativity of the canonical multiplication**
`A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)`: for `a ∈ A⁽ᵖ⁾(Z ⟶ X)`, `b ∈ A⁽ᑫ⁾(Z ⟶ X)`,
`c ∈ A⁽ˢ⁾(Z ⟶ X)` the two groupings `(a · b) · c` and `a · (b · c)` of a triple product agree, at
every pair of intermediate targets `A⁽ʳ¹⁾(Z ⟶ X)`, `A⁽ʳ²⁾(Z ⟶ X)` and every common target
`A⁽ʳ⁾(Z ⟶ X)` whose cutoffs satisfy the four inequalities below, which together come to
`p + q + s ≤ r + 2`. This is "the verification that these multiplications are associative in a
suitable sense" that the source omits, carried out in the range where every term of every grouping
is one of the source's own three pairings — no pair of degrees the remark leaves unprescribed
occurs. That covers every product the chapter forms: `r₁ = max(p, q)`, the target the source
displays (`Stacks.Chow.localizedBivariantGradingMulMax`), qualifies for `min(p, q) ≤ 1`, and so
does `r₁ = p + q`, the target at which Stacks 0FAL and Stacks 0FAY state their products. The
product internal to `A⁽ᵖ⁾(Z ⟶ X)` of the source's graded algebra, where all six targets are
`p ≤ 1`, is the corollary `Stacks.Chow.localizedBivariantGradingInternalMul_assoc`; what
associativity of that product would come to for `p ≥ 2` is
`Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc`.

It is an equality and not a heterogeneous equality because the common target `r` is a parameter;
the degrees of the intermediate products are the arguments `r₁`, `r₂`, which the two groupings
bracket differently. Degreewise the two sides are the same double convolution of the three
factors' components written in the two decompositions `(m, i - m, n - i)` and `(m, j, n - m - j)`
of the total degree `n`, and the proof is exactly the two pieces the implementation notes name:
the reindexing `Stacks.Chow.sum_Icc_diag_flip` of that double convolution, and — term by term —
the three instances of the associativity of Stacks 0B75 for the pairings, read through the
transports the pairings carry by `Stacks.Chow.bivariantClassDegreeCongr_eq_of_heq`. Below the
cutoff of the target both sides are the double convolution in `A^*(X)`
(`Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution`) and the input is the
associativity of the multiplication of `A^*(X)`,
`Stacks.Chow.chowCohomologyComposite_assoc`; at or above it one of the three pairings applies to
each term, and where an intermediate product was read in `A^*(X)` the comparison also needs
`Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward_eq`, that a localized factor
may be pushed forward by Stacks 0EPK before it is multiplied on the left. -/
@[stacks 0FA0 "associativity of the canonical multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ \
A^(r)(Z ⟶ X) of the remark -- the verification the source omits -- for every triple of factors \
and every choice of intermediate targets r₁, r₂ and common target r with p + q + s ≤ r + 2, where \
every term of a triple product is one of the remark's three pairings; this covers the displayed \
target max(p,q) and the product internal to A^(p)(Z ⟶ X) of the graded algebra"]
theorem localizedBivariantGradingMul_assoc (p q s r₁ r₂ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (h₂ : r₁ + s ≤ r + 1) (h₃ : q + s ≤ r₂ + 1) (h₄ : p + r₂ ≤ r + 1)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl s) :
    localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc r₁ s r
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r₁ a b) c =
      localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p r₂ r a
        (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc q s r₂ b c) := by
  refine Prod.ext (funext fun n ↦ ?_) (funext fun n ↦ ?_)
  · rw [localizedBivariantGradingMul_fst_left C G sX f hRG hgysP hgys hgysc p q s r₁ r h₁ a b c
      n.1 n.2, localizedBivariantGradingMul_fst_right C G sX f hRG hgysP hgys hgysc p q s r₂ r h₃
      a b c n.1 n.2]
    refine Eq.trans ?_ (sum_Icc_diag_flip n.1 fun m j ↦
      localizedGradingMulAssocAmbientTerm C G sX f hRG hgysP hgys hgysc p q s a b c n.1 m j
        (n.1 - m - j) (by ring))
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun m _ ↦
      localizedGradingMulAssocAmbientTerm_congr C G sX f hRG hgysP hgys hgysc p q s a b c n.1 m
        (i - m) (n.1 - i) (n.1 - m - (i - m)) (by ring) _ _
  · rw [localizedBivariantGradingMul_snd_left C G sX f hRG hgysP hgys hgysc p q s r₁ r h₁ h₂ a b c
      n.1 n.2, localizedBivariantGradingMul_snd_right C G sX f hRG hgysP hgys hgysc p q s r₂ r h₃
      h₄ a b c n.1 n.2]
    refine Eq.trans ?_ (sum_Icc_diag_flip n.1 fun m j ↦
      localizedGradingMulAssocTerm C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c n.1 n.2
        m j (n.1 - m - j) (by ring))
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun m _ ↦
      localizedGradingMulAssocTerm_congr C G sX f hRG hgysP hgys hgysc p q s r (by omega) a b c
        n.1 n.2 m (i - m) (n.1 - i) (n.1 - m - (i - m)) (by ring) _ _

/-- **Stacks 0FA0, associativity of the multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)`**, which is the
associativity the source's "`A⁽ᵖ⁾(Z ⟶ X)` canonically comes equipped with the structure of a
graded algebra" asks for, for `p ≤ 1` — the `p` at which a triple product of the internal
multiplication (`Stacks.Chow.localizedBivariantGradingInternalMul`, defined for every `p ≥ 0`)
meets no pair of degrees the remark leaves unprescribed,
`Stacks.Chow.localizedGrading_self_admissible_iff`. With
`Stacks.Chow.localizedBivariantGradingMul_add_left`,
`Stacks.Chow.localizedBivariantGradingMul_add_right` and the two unit laws
`Stacks.Chow.localizedBivariantGradingInternalMul_one_left` and `_one_right` this completes the
graded-algebra axioms for that product. For `p ≥ 2` the content of associativity is
`Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc`. -/
@[stacks 0FA0 "associativity of the multiplication internal to A^(p)(Z ⟶ X) of the remark's \
graded algebra, for p ≤ 1, where no pair of degrees the remark leaves unprescribed occurs in a \
triple product"]
theorem localizedBivariantGradingInternalMul_assoc (p : ℕ) (hp : p ≤ 1)
    (a b c : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
        (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p a b) c =
      localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p a
        (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p b c) :=
  localizedBivariantGradingMul_assoc C G sX f hRG hgysP hgys hgysc p p p p p p (by omega)
    (by omega) (by omega) (by omega) a b c

end RestrictionPushforward

/-! ### The graded algebra of Stacks 0FA0 as a bundled structure -/

section Bundled

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)
  (hgysinX : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
  (hgysinZ : IdentityCapRule.TransportGysinNaturality C (f ≫ sX) 0
    (identityCapRule C (f ≫ sX)) G)

/-- **Stacks 0FA0, the multiplicative structure of the remark's graded algebra on `A⁽ᵖ⁾(Z ⟶ X)`
as a bundled `Semigroup`**, on all of `A⁽ᵖ⁾(Z ⟶ X)` for `p ≤ 1`, which is where associativity of
the internal product is proved. Nothing beyond the Gysin compatibilities of the product itself is
assumed: the multiplication is `Stacks.Chow.localizedBivariantGradingInternalMul`, which is defined
for every `p ≥ 0`, and the associativity is
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc`.

The unit of the algebra needs `p ≥ 1`, so the bundled `Monoid` is at `p = 1`:
`Stacks.Chow.localizedBivariantGradingMonoid`. -/
@[stacks 0FA0 "the multiplicative structure of the remark's graded algebra on A^(p)(Z ⟶ X) as a \
bundled Semigroup, on all of A^(p)(Z ⟶ X) for p ≤ 1, where associativity of the internal product \
is proved: the multiplication of the remark together with its associativity, with no hypothesis \
beyond the Gysin compatibilities the product itself carries", instance_reducible]
def localizedBivariantGradingSemigroup (p : ℕ) (hp : p ≤ 1) :
    Semigroup (localizedBivariantGrading C G (f ≫ sX) sX f rfl p) where
  mul a b := localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p a b
  mul_assoc a b c :=
    localizedBivariantGradingInternalMul_assoc C G sX f hRG hgysP hgys hgysc p hp a b c

include hgysinZ in
/-- **Stacks 0FA0, the remark's graded algebra on `A⁽¹⁾(Z ⟶ X)` as a bundled `Monoid`:** the
multiplication internal to `A⁽¹⁾(Z ⟶ X)`, its unit, and the three laws. This is the structure the
source's "`A⁽ᵖ⁾(Z ⟶ X)` canonically comes equipped with the structure of a graded algebra" asserts
on the multiplicative side. Its fields are
`Stacks.Chow.localizedBivariantGradingInternalMul`,
`Stacks.Chow.localizedBivariantGradingOne`,
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc`,
`Stacks.Chow.localizedBivariantGradingInternalMul_one_left` and
`Stacks.Chow.localizedBivariantGradingInternalMul_one_right`; the additive side of the algebra is
the `AddCommGroup` the grading carries, with the distributive law
`Stacks.Chow.localizedBivariantGradingInternalMulHom`.

`p = 1` is where the three laws meet. The multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)` is defined for
every `p ≥ 0` and the two unit laws hold for every `p ≥ 1`, the degree `0` slot where the unit sits
being `A⁰(X)` exactly then; associativity is proved for `p ≤ 1`
(`Stacks.Chow.localizedGrading_self_admissible_iff`), and what it would come to for `p ≥ 2` is
`Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc`.

The carrier is **all** of `A⁽¹⁾(Z ⟶ X)`, the group the source asserts the algebra on. That rests
on the index range of the sums the product is formed from: a degree `n` component is the sum over
`Finset.Icc (min 0 n) (max 0 n)`, the pairs `i + j = n` whose two degrees both have the sign of
`n`, and that range contains `i = 0` and `i = n` in every degree
(`Stacks.Chow.zero_mem_Icc_min_max`, `Stacks.Chow.self_mem_Icc_min_max`) — the two indices
carrying the surviving term of a product with the unit on the left and on the right. The range is a
reading of the source's `∑_{i + j = n}`, which runs over an infinite index set; the reading and the
witness that the index set is infinite with independent summands are in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`. -/
@[stacks 0FA0 "the remark's graded algebra on A^(1)(Z ⟶ X) as a bundled Monoid -- the \
multiplication internal to A^(1)(Z ⟶ X), the class 1 of A^0(X) in degree 0 as its unit, \
associativity and the two unit laws -- at p = 1, where the unit's degree 0 slot is A^0(X) and \
associativity is proved, on all of A^(1)(Z ⟶ X)",
  instance_reducible]
def localizedBivariantGradingMonoid :
    Monoid (localizedBivariantGrading C G (f ≫ sX) sX f rfl 1) where
  mul a b := localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc 1 a b
  one := localizedBivariantGradingOne C G sX f hgysinX 1
  mul_assoc a b c :=
    localizedBivariantGradingInternalMul_assoc C G sX f hRG hgysP hgys hgysc 1 (by omega) a b c
  one_mul a :=
    localizedBivariantGradingInternalMul_one_left C G sX f hRG hgysP hgys hgysc hgysinX hgysinZ
      1 le_rfl a
  mul_one a :=
    localizedBivariantGradingInternalMul_one_right C G sX f hRG hgysP hgys hgysc hgysinX
      1 le_rfl a

end Bundled

/-! ### Associativity at the Gysin system of the first Chern class rule -/

section OfInvertible

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Z ⟶ X) [IsClosedImmersion f]

/-- **Stacks 0FA0, associativity of the canonical multiplication at the Gysin system of the first
Chern class rule, with nothing assumed:** there every Gysin compatibility that Stacks 0F9Z,
Stacks 0B75 and Stacks 0EPK carry for an arbitrary Gysin system is a theorem, and so is Stacks
02RG on Chow groups, which the pushforward of Stacks 0EPK costs. See
`Stacks.Chow.localizedBivariantGradingMul_assoc`. -/
@[stacks 0FA0 "associativity of the canonical multiplication of the remark -- the verification \
the source omits -- at every choice of intermediate and common targets with p + q + s ≤ r + 2, at \
the Gysin system of the first Chern class rule, with NOTHING ASSUMED"]
theorem localizedBivariantGradingMulOfInvertible_assoc (p q s r₁ r₂ r : ℕ) (h₁ : p + q ≤ r₁ + 1)
    (h₂ : r₁ + s ≤ r + 1) (h₃ : q + s ≤ r₂ + 1) (h₄ : p + r₂ ≤ r + 1)
    (a : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl q)
    (c : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl s) :
    localizedBivariantGradingMulOfInvertible C sX f r₁ s r
        (localizedBivariantGradingMulOfInvertible C sX f p q r₁ a b) c =
      localizedBivariantGradingMulOfInvertible C sX f p r₂ r a
        (localizedBivariantGradingMulOfInvertible C sX f q s r₂ b c) :=
  localizedBivariantGradingMul_assoc C (gysinSystemOfInvertible C) sX f
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p q s r₁ r₂ r h₁ h₂ h₃ h₄
    a b c

/-- **Stacks 0FA0, associativity of the multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)` at the Gysin
system of the first Chern class rule, with nothing assumed.** This is the associativity of the
source's graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` for `p ≤ 1`, with no hypothesis of any kind beyond that
bound. -/
@[stacks 0FA0 "associativity of the multiplication internal to A^(p)(Z ⟶ X) of the remark's \
graded algebra, for p ≤ 1, at the Gysin system of the first Chern class rule with NOTHING ASSUMED"]
theorem localizedBivariantGradingInternalMulOfInvertible_assoc (p : ℕ) (hp : p ≤ 1)
    (a b c : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMulOfInvertible C sX f p
        (localizedBivariantGradingInternalMulOfInvertible C sX f p a b) c =
      localizedBivariantGradingInternalMulOfInvertible C sX f p a
        (localizedBivariantGradingInternalMulOfInvertible C sX f p b c) :=
  localizedBivariantGradingMulOfInvertible_assoc C sX f p p p p p p (by omega) (by omega)
    (by omega) (by omega) a b c

end OfInvertible

end Stacks.Chow

end
