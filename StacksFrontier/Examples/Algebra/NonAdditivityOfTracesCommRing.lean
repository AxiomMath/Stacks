module

public import StacksFrontier.Examples.Algebra.NonAdditivityOfTraces
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity

/-!
# Nonadditivity of traces over a commutative ring

Stacks 087L in the form the Stacks project states it: its rings are commutative, and the trace of
an endomorphism of a perfect complex over a commutative ring `R` lies in `R`. The alternating trace
of the library lies in the additive commutator quotient `R/[R,R]`, which for a commutative ring is
`R` itself through `Stacks.Trace.commutativeAdditiveCommutatorQuotientEval`; the traces are
compared after this evaluation. The witness is the dual numbers over `ℚ`, from
`ulift_dualNumber_distinguished_triangle_trace_nonadditive`.

## Main results

* `Stacks.Examples.exists_commRing_distinguished_triangle_trace_nonadditive`: a commutative ring,
  a distinguished triangle of perfect complexes in `K(R)` and an endomorphism `(a, b, c)` of it
  with `Tr(a) + Tr(c) ≠ Tr(b)` in `R`.

## References

* [Stacks Project, Tag 087L](https://stacks.math.columbia.edu/tag/087L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

namespace Stacks.Examples

universe u v

/-- The image of an element of the additive commutator quotient of a commutative ring under the
evaluation in the ring, mapped back to the quotient, is the element itself. -/
private lemma additiveCommutatorQuotientMk_eval (R : Type u) [CommRing R]
    (x : CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient R) :
    CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk R
      (Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H y => rfl

/-- **Stacks 087L.** There exist a commutative ring `R`, a distinguished triangle of perfect
complexes in the homotopy category `K(R)` and an endomorphism `(a, b, c)` of this triangle with
`Tr(a) + Tr(c) ≠ Tr(b)`, the traces taken in `R` itself. The vertices are bounded complexes of
finite projective `R`-modules and `a`, `b`, `c` are presented by cochain maps; the trace in `R` is
the alternating trace evaluated by `Stacks.Trace.commutativeAdditiveCommutatorQuotientEval`, which
for a commutative ring identifies `R/[R,R]` with `R`. The witness is the dual numbers over `ℚ`. -/
@[stacks 087L "Stacks' rings are commutative and its traces of perfect complexes lie in `R`: \
  here `R` is a `CommRing` and the alternating traces are evaluated in `R`."]
public theorem exists_commRing_distinguished_triangle_trace_nonadditive :
    ∃ (R : Type u) (hR : CommRing R),
      letI : CommRing R := hR
      ∃ (P Q S : CochainComplex (ModuleCat.{v} R) ℤ)
        (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex R P)
        (hQ : CategoryTheory.FilteredDerived.finiteProjectiveComplex R Q)
        (hS : CategoryTheory.FilteredDerived.finiteProjectiveComplex R S),
        let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
        ∃ (f : q.obj P ⟶ q.obj Q) (g : q.obj Q ⟶ q.obj S)
          (h : q.obj S ⟶ (q.obj P)⟦(1 : ℤ)⟧)
          (a : P ⟶ P) (b : Q ⟶ Q) (c : S ⟶ S),
          (Triangle.mk f g h ∈ distTriang _) ∧
          (∃ t : Triangle.mk f g h ⟶ Triangle.mk f g h,
            t.hom₁ = q.map a ∧ t.hom₂ = q.map b ∧ t.hom₃ = q.map c) ∧
          Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
              (CategoryTheory.FilteredDerived.alternatingTrace R P hP a) +
            Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
              (CategoryTheory.FilteredDerived.alternatingTrace R S hS c) ≠
            Stacks.Trace.commutativeAdditiveCommutatorQuotientEval R
              (CategoryTheory.FilteredDerived.alternatingTrace R Q hQ b) := by
  obtain ⟨P, Q, S, hP, hQ, hS, f, g, h, a, b, c, hdist, ht, hne⟩ :=
    ulift_dualNumber_distinguished_triangle_trace_nonadditive.{u, v}
  refine ⟨ULift.{u} (DualNumber ℚ), inferInstance, P, Q, S, hP, hQ, hS, f, g, h, a, b, c, hdist, ht,
    ?_⟩
  intro heq
  apply hne
  rw [← additiveCommutatorQuotientMk_eval _ (_ + _), map_add, heq,
    additiveCommutatorQuotientMk_eval]

end Stacks.Examples

end
