module

public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Invertibility on bounded complexes from invertibility on single complexes

Let `C` be an additive category with a zero object and let `α : F ⟶ G` be a natural
transformation between two exact functors from the homotopy category `K(C)` of cochain complexes
of `C` to a pretriangulated category.  If `α` is invertible at every complex concentrated in a
single degree on an object with a property `P`, then it is invertible at every bounded complex
all of whose terms have `P`.

The proof is the induction on the number of nonzero terms through the stupid truncations
`σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]`, which are degreewise split and hence give distinguished triangles
of `K(C)`; the induction hypothesis is invertibility at every shift, which is what
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts` consumes and
returns.  No compatibility of `α` with the shifts is needed.

## Main results

* `Stacks.CategoryTheory.HomotopyBoundedInvertibility.isIso_app_quotient_of_finite`:
  invertibility at a complex with finitely many nonzero terms.

## References

* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
  ComplexShape

namespace Stacks.CategoryTheory.HomotopyBoundedInvertibility

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F G : HomotopyCategory C (up ℤ) ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] (α : F ⟶ G)

/-- The stupid truncation short complex is split in every degree. -/
noncomputable def stupidTruncGEShortComplexSplitting (K : CochainComplex C ℤ) (p n : ℤ) :
    ((StacksDraft.StupidTruncation.stupidTruncGEShortComplex K p).map
      (HomologicalComplex.eval C (up ℤ) n)).Splitting := by
  by_cases hn : n = p
  · subst hn
    refine ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_
    · exact CochainComplex.isZero_of_isStrictlyGE
        (K.stupidTrunc (embeddingUpIntGE (n + 1))) (n + 1) n (by omega)
    · change IsIso ((StacksDraft.StupidTruncation.stupidTruncGEπ K n).f n)
      rw [StacksDraft.StupidTruncation.stupidTruncGEπ_f]
      infer_instance
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_
    · change IsIso ((StacksDraft.StupidTruncation.stupidTruncGEMapLE K
        (show p ≤ p + 1 by omega)).f n)
      by_cases hpn : p < n
      · rw [StacksDraft.StupidTruncation.stupidTruncGEMapLE_f K _ n (by omega)]
        infer_instance
      · exact IsZero.isIso
          (CochainComplex.isZero_of_isStrictlyGE
            (K.stupidTrunc (embeddingUpIntGE (p + 1))) (p + 1) n (by omega))
          (CochainComplex.isZero_of_isStrictlyGE
            (K.stupidTrunc (embeddingUpIntGE p)) p n (by omega)) _
    · exact isZero_single_obj_X (up ℤ) p (K.X p) n hn

/-- The property that `α` is invertible at every shift of an object. -/
def AllShifts (X : HomotopyCategory C (up ℤ)) : Prop :=
  ∀ n : ℤ, IsIso (α.app (X⟦n⟧))

omit [HasZeroObject C] [HasBinaryBiproducts C] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- `AllShifts` is invariant under isomorphism. -/
theorem allShifts_of_iso {X Y : HomotopyCategory C (up ℤ)} (e : X ≅ Y)
    (h : AllShifts F G α X) : AllShifts F G α Y := fun n =>
  (NatTrans.isIso_app_iff_of_iso α ((shiftFunctor _ n).mapIso e)).1 (h n)

/-- `AllShifts` holds at a zero object. -/
theorem allShifts_of_isZero {X : HomotopyCategory C (up ℤ)} (hX : IsZero X) :
    AllShifts F G α X := fun n => by
  have h : IsZero (X⟦n⟧) := (shiftFunctor _ n).map_isZero hX
  exact IsZero.isIso (F.map_isZero h) (G.map_isZero h) _

omit [HasBinaryBiproducts C] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.CommShift ℤ] [G.CommShift ℤ]
  [F.IsTriangulated] [G.IsTriangulated] in
/-- At a single complex on an object with a property `P`, invertibility in every degree at the
objects with `P` gives `AllShifts`. -/
theorem allShifts_single (P : C → Prop)
    (hsingle : ∀ (i : ℤ) (E : C), P E → IsIso (α.app ((HomotopyCategory.quotient C (up ℤ)).obj
      ((HomologicalComplex.single C (up ℤ) i).obj E))))
    (i : ℤ) (E : C) (hE : P E) :
    AllShifts F G α ((HomotopyCategory.quotient C (up ℤ)).obj
      ((HomologicalComplex.single C (up ℤ) i).obj E)) := fun n =>
  (NatTrans.isIso_app_iff_of_iso α
    (((HomotopyCategory.singleFunctors C).shiftIso n (i - n) i (by omega)).app E)).2
    (hsingle (i - n) E hE)

/-- **Invertibility on bounded complexes.**  A natural transformation between exact functors
out of `K(C)`, invertible at every complex concentrated in a single degree on an object with a
property `P`, is invertible at every complex with finitely many nonzero terms, all with `P`. -/
theorem isIso_app_quotient_of_finite (P : C → Prop)
    (hsingle : ∀ (i : ℤ) (E : C), P E → IsIso (α.app ((HomotopyCategory.quotient C (up ℤ)).obj
      ((HomologicalComplex.single C (up ℤ) i).obj E))))
    (K : CochainComplex C ℤ) (hP : ∀ n, P (K.X n)) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) :
    IsIso (α.app ((HomotopyCategory.quotient C (up ℤ)).obj K)) := by
  classical
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := hK.bddBelow
  have outside (i : ℤ) (hi : b < i ∨ i < a) : IsZero (K.X i) :=
    by_contra fun h => by have := hb h; have := ha h; omega
  have trunc (m : ℕ) (p : ℤ) (hp : b < p + m) :
      AllShifts F G α ((HomotopyCategory.quotient C (up ℤ)).obj
        (K.stupidTrunc (embeddingUpIntGE p))) := by
    induction m generalizing p with
    | zero =>
      apply allShifts_of_isZero
      apply Functor.map_isZero
      apply (IsZero.iff_id_eq_zero _).2
      ext i
      apply IsZero.eq_of_src
      show IsZero ((K.stupidTrunc (embeddingUpIntGE p)).X i)
      by_cases hpi : p ≤ i
      · exact (outside i (by omega)).of_iso
          (StacksDraft.StupidTruncation.stupidTruncGEXIso K p i hpi)
      · exact CochainComplex.isZero_of_isStrictlyGE _ p i (by omega)
    | succ m ih =>
      have hT := CochainComplex.trianglehOfDegreewiseSplit_distinguished
        (StacksDraft.StupidTruncation.stupidTruncGEShortComplex K p)
        (stupidTruncGEShortComplexSplitting K p)
      exact Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts
        F G α _ hT (ih (p + 1) (by omega)) (allShifts_single F G α P hsingle p (K.X p) (hP p))
  have hι : IsIso (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE a)) := by
    have hcomp : ∀ i, IsIso ((HomologicalComplex.ιStupidTrunc K
        (embeddingUpIntGE a)).f i) := by
      intro i
      by_cases hai : a ≤ i
      · rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K a i hai]
        infer_instance
      · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega))
          (outside i (by omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have h := allShifts_of_iso F G α ((HomotopyCategory.quotient C (up ℤ)).mapIso
    (asIso (HomologicalComplex.ιStupidTrunc K (embeddingUpIntGE a))))
    (trunc ((b - a).toNat + 1) a (by omega)) 0
  exact (NatTrans.isIso_app_iff_of_iso α ((shiftFunctorZero _ ℤ).app _)).1 h

end Stacks.CategoryTheory.HomotopyBoundedInvertibility

end
