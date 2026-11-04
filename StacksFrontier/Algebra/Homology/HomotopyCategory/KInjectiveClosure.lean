module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Algebra.Homology.ReindexCochainComplex

/-!
# Closure properties of K-injectivity

Let `C` be an abelian category. This file records the operations on cochain complexes in `C`
under which K-injectivity is inherited: the zero complex is K-injective, a retract of a
K-injective complex is K-injective, the middle term of a degreewise split short complex whose
outer terms are K-injective is K-injective, a binary biproduct of K-injective complexes is
K-injective, and a sign-free reindexing of a K-injective complex is K-injective.

All of these are elementary, and two of them are read off Mathlib's description of
K-injectivity as right orthogonality to the acyclic complexes in the homotopy category
(`CochainComplex.isKInjective_iff_rightOrthogonal`): a right orthogonal class contains zero,
is closed under isomorphisms and shifts, and satisfies two out of three in a distinguished
triangle. The degreewise split case is that last closure applied to the distinguished triangle
Mathlib attaches to a degreewise split short complex
(`CochainComplex.trianglehOfDegreewiseSplit_distinguished`), and the binary biproduct is in turn
the degreewise split case applied to `X ⟶ X ⊞ Y ⟶ Y`. The zero and retract cases are shorter
read directly off the definition, since a morphism into a zero complex is zero and a homotopy to
zero may be transported through a retraction.

The reindexing is the sign-free translation `CochainComplex.reindexBy`, which is isomorphic to
the shift by `CochainComplex.reindexByIsoShift`; the shift case is already an instance in
Mathlib.

## Main results

* `CochainComplex.isKInjective_of_isZero`
* `CochainComplex.isKInjective_of_retract`
* `CochainComplex.isKInjective_X₂_of_degreewiseSplit`
* `CochainComplex.isKInjective_biprod`
* `CochainComplex.isKInjective_reindexBy`
-/

@[expose] public noncomputable section

open CategoryTheory Limits CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A zero complex is K-injective**, since every morphism into it is zero and is therefore
equal to, hence homotopic to, the zero morphism. -/
theorem isKInjective_of_isZero {L : CochainComplex C ℤ} (hL : IsZero L) : L.IsKInjective where
  nonempty_homotopy_zero {_} f _ := ⟨Homotopy.ofEq (hL.eq_of_tgt f 0)⟩

/-- **A retract of a K-injective complex is K-injective.** A morphism from an acyclic complex
into the retract becomes, after the inclusion, homotopic to zero; composing that homotopy with
the retraction and using the retract identity brings it back. -/
theorem isKInjective_of_retract {L L' : CochainComplex C ℤ} (ρ : Retract L L')
    [L'.IsKInjective] : L.IsKInjective where
  nonempty_homotopy_zero {_} f hK := by
    obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero (f ≫ ρ.i) hK
    refine ⟨(Homotopy.ofEq ?_).trans ((h.compRight ρ.r).trans (Homotopy.ofEq (zero_comp)))⟩
    rw [Category.assoc, ρ.retract, Category.comp_id]

/-- **Two out of three for K-injectivity along a degreewise split short complex.** If the outer
terms of a short complex of cochain complexes which is split in every degree are K-injective,
so is the middle term. This is the two-out-of-three closure of a right orthogonal class, applied
to the distinguished triangle of the degreewise splitting. -/
theorem isKInjective_X₂_of_degreewiseSplit (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting)
    [S.X₁.IsKInjective] [S.X₃.IsKInjective] : S.X₂.IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal]
  have h := ObjectProperty.ext_of_isTriangulatedClosed₂'
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
    (trianglehOfDegreewiseSplit S σ) (trianglehOfDegreewiseSplit_distinguished S σ)
    (IsKInjective.rightOrthogonal S.X₁) (IsKInjective.rightOrthogonal S.X₃)
  rwa [ObjectProperty.isoClosure_eq_self] at h

/-- The short complex `X ⟶ X ⊞ Y ⟶ Y` given by the inclusion of the first summand and the
projection to the second. -/
abbrev biprodShortComplex (L L' : CochainComplex C ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (biprod.inl : L ⟶ L ⊞ L') (biprod.snd : L ⊞ L' ⟶ L') (by simp)

/-- The short complex `X ⟶ X ⊞ Y ⟶ Y` is split in every degree, by the other inclusion and
projection of the biproduct, which are computed degreewise. -/
def biprodShortComplexSplitting (L L' : CochainComplex C ℤ) (n : ℤ) :
    ((biprodShortComplex L L').map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting where
  r := (biprod.fst : L ⊞ L' ⟶ L).f n
  s := (biprod.inr : L' ⟶ L ⊞ L').f n
  f_r := by
    simp
  s_g := by
    simp
  id := by
    simp

/-- **A binary biproduct of K-injective complexes is K-injective**, by two out of three along the
degreewise split short complex `X ⟶ X ⊞ Y ⟶ Y`. -/
theorem isKInjective_biprod (L L' : CochainComplex C ℤ) [L.IsKInjective] [L'.IsKInjective] :
    (L ⊞ L').IsKInjective :=
  isKInjective_X₂_of_degreewiseSplit (biprodShortComplex L L') (biprodShortComplexSplitting L L')

/-- **A sign-free reindexing of a K-injective complex is K-injective**, because it is isomorphic
to a shift of it. -/
theorem isKInjective_reindexBy (L : CochainComplex C ℤ) [L.IsKInjective] (k : ℤ) :
    (reindexBy L k).IsKInjective :=
  isKInjective_of_iso (reindexByIsoShift L k).symm

end CochainComplex

end
