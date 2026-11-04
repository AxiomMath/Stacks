module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# Induction on a bounded complex through its stupid truncations

A property of objects of the derived category of an abelian category that is invariant under
isomorphism, holds for the zero object, and is stable under the extension given by a short exact
sequence of complexes, holds for every bounded complex as soon as it holds for each of the
complex's terms placed in its own degree.

## Main results

* `Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex`: the induction
  principle.

## Implementation notes

The induction is over the number of nonzero terms, using the stupid truncations `K ≥ p` of
`StacksFrontier/Algebra/Homology/StupidTruncation.lean`: the short exact sequence
`StacksDraft.StupidTruncation.stupidTruncGEShortComplex` presents `K ≥ p` as an extension of the
single term `K p` by `K ≥ p+1`, so the stability hypothesis advances `p` by one.  Above the
upper bound of the support the truncation is the zero complex, which starts the induction; below
the lower bound the inclusion of the truncation into `K` is an isomorphism, which ends it.

Stupid rather than canonical truncation is what the statement needs: a canonical truncation of a
complex has the complex's cohomology, not its terms, in the role the hypothesis `hsingle`
addresses.

The property is taken as a bare `DerivedCategory C → Prop` rather than as an
`ObjectProperty` closed under isomorphisms, because the application is "a fixed natural
transformation is invertible at every shift of this object", which is a property of the object
and not of its isomorphism class in any canonical way; the invariance is supplied as the explicit
hypothesis `hiso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.StupidTruncation HomologicalComplex ComplexShape

namespace Stacks.DerivedCategory.BoundedInduction

/-- **Induction on a bounded complex through its stupid truncations.**  A property of objects of
`D(C)` invariant under isomorphism, holding at zero objects, stable under the extension given by
a short exact sequence of complexes, and holding at each term of a bounded complex `K` placed in
its own degree, holds at `K`. -/
theorem property_of_bounded_complex {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (P : DerivedCategory C → Prop)
    (hiso : ∀ {A B : DerivedCategory C}, (A ≅ B) → P A → P B)
    (hzero : ∀ A : DerivedCategory C, IsZero A → P A)
    (hext : ∀ S : ShortComplex (CochainComplex C ℤ), S.ShortExact →
      P (DerivedCategory.Q.obj S.X₁) → P (DerivedCategory.Q.obj S.X₃) →
      P (DerivedCategory.Q.obj S.X₂))
    (K : CochainComplex C ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hsingle : ∀ i, P ((DerivedCategory.singleFunctor C i).obj (K.X i))) :
    P (DerivedCategory.Q.obj K) := by
  classical
  obtain ⟨b, hb⟩ := hK.bddAbove
  obtain ⟨a, ha⟩ := hK.bddBelow
  have outside (i : ℤ) (hi : i < a ∨ b < i) : IsZero (K.X i) := by
    by_contra h
    have := ha h
    have := hb h
    omega
  have trunc (n : ℕ) (p : ℤ) (hp : b < p + n) :
      P (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE p))) := by
    induction n generalizing p with
    | zero =>
      apply hzero
      apply Functor.map_isZero
      apply (IsZero.iff_id_eq_zero _).2
      ext i
      apply IsZero.eq_of_src
      show IsZero ((K.stupidTrunc (embeddingUpIntGE p)).X i)
      by_cases hpi : p ≤ i
      · exact (outside i (by omega)).of_iso (stupidTruncGEXIso K p i hpi)
      · exact CochainComplex.isZero_of_isStrictlyGE _ p i (by omega)
    | succ n ih =>
      exact hext (stupidTruncGEShortComplex K p)
        (stupidTruncGEShortComplex_shortExact K p)
        (ih (p + 1) (by omega)) (hsingle p)
  have hι : IsIso (ιStupidTrunc K (embeddingUpIntGE a)) := by
    have hcomp : ∀ i, IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f i) := by
      intro i
      by_cases hai : a ≤ i
      · rw [ιStupidTruncGE_f K a i hai]
        infer_instance
      · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE _ a i (by omega))
          (outside i (by omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  exact hiso (DerivedCategory.Q.mapIso (asIso (ιStupidTrunc K (embeddingUpIntGE a))))
    (trunc ((b - a).toNat + 1) a (by omega))

end Stacks.DerivedCategory.BoundedInduction

end
