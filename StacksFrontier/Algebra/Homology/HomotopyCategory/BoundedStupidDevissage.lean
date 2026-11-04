module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# Dévissage of a bounded complex in the homotopy category

Let `A` be an additive category and let `α : F ⟶ G` be a natural transformation between
triangulated functors out of the homotopy category `K(A)`. If `α` is invertible at every complex
concentrated in one degree whose term satisfies a predicate `P`, then it is invertible at every
strictly bounded complex whose terms in its range satisfy `P`.

The proof is by induction on the length of the range, along the degreewise split short exact
sequences of stupid truncations `σ^{≥n+1}K ⟶ σ^{≥n}K ⟶ Kⁿ[-n]`. Each gives a distinguished
triangle of `K(A)`, and
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts` propagates
invertibility at all shifts of the two outer vertices to all shifts of the middle one.
Unlike `Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex`, nothing here needs
`A` to be abelian. This matters because the category of finite-order differential operators is
only additive.

## Main results

* `Stacks.HomotopyDevissage.stupidTruncGESplittingOfPreadditive`: the canonical degreewise
  splitting of the stupid truncation sequence, in an additive category.
* `Stacks.HomotopyDevissage.isIso_app_quotient_obj_of_isStrictlyLE`: **the dévissage.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape StacksDraft.StupidTruncation

namespace Stacks.HomotopyDevissage

variable {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A]

open Classical in
/-- The canonical degreewise splitting of the short exact sequence
`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]`, in an additive category: in degree `p` the first term vanishes and
the projection is an isomorphism, in every other degree the first map is an isomorphism and the
last term vanishes. -/
def stupidTruncGESplittingOfPreadditive (K : CochainComplex A ℤ) (p n : ℤ) :
    ((stupidTruncGEShortComplex K p).map (eval A (.up ℤ) n)).Splitting :=
  if hn : n = p then
    ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1)
        n (by omega))
      (by
        subst hn
        change IsIso ((stupidTruncGEπ K n).f n)
        rw [stupidTruncGEπ_f]
        infer_instance)
  else
    ShortComplex.Splitting.ofIsIsoOfIsZero _
      (by
        change IsIso ((stupidTruncGEMapLE K (show p ≤ p + 1 by omega)).f n)
        by_cases hpn : p < n
        · rw [stupidTruncGEMapLE_f K _ n (by omega)]
          infer_instance
        · exact IsZero.isIso
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1) n (by omega))
            (CochainComplex.isZero_of_isStrictlyGE
              (K.stupidTrunc (embeddingUpIntGE p)) p n (by omega)) _)
      (isZero_single_obj_X (.up ℤ) p (K.X p) n hn)

omit [HasZeroObject A] in
/-- A complex all of whose terms are zero is a zero object. -/
theorem isZero_of_isZero_X (K : CochainComplex A ℤ) (h : ∀ i, IsZero (K.X i)) : IsZero K := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (h i).eq_of_src _ _

/-- The stupid truncation `σ^{≥a}K` of a complex vanishing above `b` vanishes above `b`. -/
theorem isStrictlyLE_stupidTruncGE (K : CochainComplex A ℤ) (a b : ℤ) [K.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (K.stupidTrunc (embeddingUpIntGE a)) b where
  isZero i hi := by
    have hbi : b < i := by
      by_contra h
      exact hi (b - i).toNat (by simp; omega)
    by_cases ha : a ≤ i
    · exact (K.isZero_of_isStrictlyLE b i hbi).of_iso (stupidTruncGEXIso K a i ha)
    · exact CochainComplex.isZero_of_isStrictlyGE _ a i (by omega)

/-- The inclusion `σ^{≥a}K ⟶ K` is an isomorphism when `K` vanishes below `a`. -/
theorem isIso_ιStupidTruncGE (K : CochainComplex A ℤ) (a : ℤ) [K.IsStrictlyGE a] :
    IsIso (ιStupidTrunc K (embeddingUpIntGE a)) := by
  have (i : ℤ) : IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f i) := by
    by_cases h : a ≤ i
    · rw [ιStupidTruncGE_f K a i h]
      infer_instance
    · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega))
        (K.isZero_of_isStrictlyGE a i (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

section Devissage

variable [HasBinaryBiproducts A]
  {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (α : F ⟶ G)

omit [HasBinaryBiproducts A] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- If `α` is invertible at a single complex, it is invertible at all its shifts. -/
theorem isIso_app_shift_quotient_single (i : ℤ) (E : A)
    (h : ∀ j : ℤ, IsIso (α.app ((HomotopyCategory.quotient A _).obj ((single A _ j).obj E))))
    (s : ℤ) :
    IsIso (α.app (((HomotopyCategory.quotient A _).obj ((single A _ i).obj E))⟦s⟧)) := by
  let e : ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj ((single A _ i).obj E))⟦s⟧ ≅
      (HomotopyCategory.quotient A _).obj ((single A _ (i - s)).obj E) :=
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso s).symm.app _ ≪≫
      (HomotopyCategory.quotient A _).mapIso
        (((CochainComplex.singleFunctors A).shiftIso s (i - s) i (by omega)).app E)
  exact (NatTrans.isIso_app_iff_of_iso α e).2 (h (i - s))

/-- **The dévissage, with the length of the range as the induction variable.** -/
theorem isIso_app_shift_quotient_obj_of_length (P : A → Prop)
    (hsingle : ∀ (i : ℤ) (E : A), P E →
      IsIso (α.app ((HomotopyCategory.quotient A _).obj ((single A _ i).obj E)))) :
    ∀ (k : ℕ) (K : CochainComplex A ℤ) (n : ℤ), K.IsStrictlyGE n → K.IsStrictlyLE (n + k - 1) →
      (∀ i, n ≤ i → i ≤ n + k - 1 → ∃ E, P E ∧ Nonempty (K.X i ≅ E)) →
      ∀ s : ℤ, IsIso (α.app (((HomotopyCategory.quotient A _).obj K)⟦s⟧)) := by
  intro k
  induction k with
  | zero =>
    intro K n hge hle _ s
    have hK : IsZero K := isZero_of_isZero_X K fun i => by
      by_cases hi : n ≤ i
      · exact K.isZero_of_isStrictlyLE (n + (0 : ℕ) - 1) i (by omega)
      · exact K.isZero_of_isStrictlyGE n i (by omega)
    have hX : IsZero (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)⟦s⟧) :=
      Functor.map_isZero _ (Functor.map_isZero _ hK)
    exact IsZero.isIso (Functor.map_isZero F hX) (Functor.map_isZero G hX) _
  | succ k ih =>
    intro K n hge hle hK s
    let S := stupidTruncGEShortComplex K n
    let σ := stupidTruncGESplittingOfPreadditive K n
    have h₁ : ∀ t : ℤ, IsIso (α.app
        ((CochainComplex.trianglehOfDegreewiseSplit S σ).obj₁⟦t⟧)) := by
      have hle' : CochainComplex.IsStrictlyLE (K.stupidTrunc (embeddingUpIntGE (n + 1)))
          (n + 1 + k - 1) := by
        have := isStrictlyLE_stupidTruncGE K (n + 1) (n + (k + 1 : ℕ) - 1)
        exact CochainComplex.isStrictlyLE_of_le _ (n + (k + 1 : ℕ) - 1) (n + 1 + k - 1)
          (by push_cast; omega)
      refine ih (K.stupidTrunc (embeddingUpIntGE (n + 1))) (n + 1) inferInstance hle'
        fun i hi₁ hi₂ => ?_
      obtain ⟨E, hE, ⟨e⟩⟩ := hK i (by omega) (by push_cast; omega)
      exact ⟨E, hE, ⟨stupidTruncGEXIso K (n + 1) i hi₁ ≪≫ e⟩⟩
    have h₃ : ∀ t : ℤ, IsIso (α.app
        ((CochainComplex.trianglehOfDegreewiseSplit S σ).obj₃⟦t⟧)) := by
      obtain ⟨E, hE, ⟨e⟩⟩ := hK n le_rfl (by push_cast; omega)
      intro t
      exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctor _ t).mapIso
        ((HomotopyCategory.quotient A _).mapIso ((single A _ n).mapIso e)))).2
        (isIso_app_shift_quotient_single F G α n E (fun j => hsingle j E hE) t)
    have := isIso_ιStupidTruncGE K n
    exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctor _ s).mapIso
      ((HomotopyCategory.quotient A _).mapIso (asIso (ιStupidTrunc K (embeddingUpIntGE n)))))).1
      (Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts F G α _
        (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ) h₁ h₃ s)

/-- **Dévissage in the homotopy category.** Let `α : F ⟶ G` be a natural transformation between
triangulated functors out of `K(A)`. If `α` is invertible at every complex `E[-i]` concentrated
in one degree with `P E`, then it is invertible at every complex `K` strictly concentrated in
degrees `[n, m]` whose terms in those degrees satisfy `P`. -/
theorem isIso_app_quotient_obj_of_isStrictlyLE (P : A → Prop)
    (hsingle : ∀ (i : ℤ) (E : A), P E →
      IsIso (α.app ((HomotopyCategory.quotient A _).obj ((single A _ i).obj E))))
    (K : CochainComplex A ℤ) (n m : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE m]
    (hK : ∀ i, n ≤ i → i ≤ m → P (K.X i)) :
    IsIso (α.app ((HomotopyCategory.quotient A _).obj K)) := by
  have hle : K.IsStrictlyLE (n + ((m - n + 1).toNat : ℕ) - 1) :=
    CochainComplex.isStrictlyLE_of_le _ m _ (by omega)
  exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorZero _ ℤ).app _)).1
    (isIso_app_shift_quotient_obj_of_length F G α P hsingle ((m - n + 1).toNat) K n
      inferInstance hle (fun i hi₁ hi₂ => ⟨K.X i, hK i hi₁ (by omega), ⟨Iso.refl _⟩⟩) 0)

end Devissage

end Stacks.HomotopyDevissage
