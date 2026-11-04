module

public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Module

@[expose] public section

/-!
# Relative pseudo-coherence of a bounded-above complex

A bounded-above complex whose terms are relatively pseudo-coherent in the shifted degrees is
relatively pseudo-coherent.

## Main results

* `PseudoCoherence.relativelyPseudoCoherentFrom_and_relativelyPseudoCoherent_of_boundedAbove`
  (Stacks 0677).

## Implementation notes

The proof fixes one polynomial presentation and reduces to the absolute statement over the
polynomial algebra, which is what relative pseudo-coherence quantifies over. Restriction of
scalars commutes with the single-object functor and with passage to the derived category, which
carries the absolute statement across.

The absolute statement is Stacks 064Y,
`StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove` in
`StacksFrontier/Homology/PseudoCoherent/Module.lean`. That tag belongs to Chapter 15 section 65;
this module cites it rather than carrying a second copy.

## References

* [The Stacks Project, Lemma 15.82.9 (0677)](https://stacks.math.columbia.edu/tag/0677)
-/

open CategoryTheory
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0677.** A bounded-above complex with suitably relatively pseudo-coherent terms is
relatively pseudo-coherent in the corresponding degrees. In particular, relative
pseudo-coherence of every term implies relative pseudo-coherence of the complex. -/
@[stacks 0677]
public theorem relativelyPseudoCoherentFrom_and_relativelyPseudoCoherent_of_boundedAbove
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∃ b : ℤ, K.IsStrictlyLE b) :
    (∀ m : ℤ,
      (∀ i : ℤ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) (K.X i) (m - i)) →
        IsRelativelyPseudoCoherentFrom (R := R) (DerivedCategory.Q.obj K) m) ∧
    ((∀ i : ℤ, IsModuleRelativelyPseudoCoherent (R := R) (A := A) (K.X i)) →
      IsRelativelyPseudoCoherent (R := R) (DerivedCategory.Q.obj K)) := by
  have hmain : ∀ m : ℤ,
      (∀ i : ℤ, IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) (K.X i) (m - i)) →
        IsRelativelyPseudoCoherentFrom (R := R) (DerivedCategory.Q.obj K) m := by
    intro m hterms n f hf
    let F := ModuleCat.restrictScalars.{u} f.toRingHom
    let L : CochainComplex (ModuleCat.{u} (MvPolynomial (Fin n) R)) ℤ :=
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    obtain ⟨b, hb⟩ := hK
    have hbL : ∃ c : ℤ, L.IsStrictlyLE c :=
      ⟨b, (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K F b).2 hb⟩
    have htermsL : ∀ i : ℤ,
        IsModulePseudoCoherentFrom (R := MvPolynomial (Fin n) R) (L.X i) (m - i) := fun i =>
      IsPseudoCoherentFrom.ofIso (hterms i n f hf)
        ((F.mapDerivedCategorySingleFunctor 0).app (K.X i))
    exact IsPseudoCoherentFrom.ofIso
      ((pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove L hbL).1 m htermsL)
      (F.mapDerivedCategoryFactors.app K).symm
  exact ⟨hmain, fun hterms m => hmain m fun i => hterms i (m - i)⟩

end PseudoCoherence
