module

public import StacksFrontier.Algebra.DifferentialGraded.Module.EndomorphismBimodule
public import StacksFrontier.Algebra.DifferentialGraded.NonpositiveTruncation

/-! # The degree-`≤ 0` truncation of the endomorphism algebra of a differential graded module

Let `(B, d)` be a differential graded algebra over a commutative ring `R` and let `Q` be a right
differential graded `B`-module with property (P). Put `E = End(Q)`, its endomorphism differential
graded algebra (Tag 09LE), and let `E'` be the endomorphism algebra of `Q` in the degree-`≤ 0`
truncation of the differential graded category of right differential graded `B`-modules, so that
$$(E')^i = \begin{cases} E^i & i < 0\\ \Ker(E^0 \to E^1) & i = 0\\ 0 & i > 0.\end{cases}$$

If `Hom_{D(B, d)}(Q, Q[k]) = 0` for every `k > 0`, then the inclusion `E' → E` is a
quasi-isomorphism of differential graded algebras. This is the quasi-isomorphism
`(E', d) → (E, d)` of the proof of [Stacks, Tag 09SA].

## Main results

* `DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap`: the
  quasi-isomorphism `E' → E`, in the form `∀ k, Function.Bijective (φ.cohomologyMap k)` that
  [Stacks, Tag 09S6] (`DifferentialGraded.Bimodule.derivedExtensionEquivalence`) consumes.

## Implementation notes

This composes two results. `DGCategory.exists_hom_nonpositive_bijective_cohomologyMap` asks for
the vanishing of `H^k(E)` for `k > 0`, i.e. that every closed homogeneous element of `E` of
positive degree is a coboundary; and
`DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_endomorphism` identifies
`H^k(E)` with `Hom_{D(B, d)}(Q, Q[k])` for `Q` with property (P). So the hypothesis is
transported from the algebra to the derived category, where it is the one available in practice:
for `Q` representing `F(A)` with `F` an equivalence and `A = H^0(A)`, it is
`DifferentialGradedModule.eq_zero_of_hom_obj_q_regularModule_shift`.

The hypothesis asks for vanishing only in *positive* degrees, which is all the truncation needs;
the source has vanishing in every nonzero degree available, and uses the negative half for the
second quasi-isomorphism `(E', d) → (A, d)` instead.

## References

* [Stacks Project, Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), in whose proof this
  quasi-isomorphism appears, and [Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), which is
  what identifies `H^k(E)` with `Hom_{D(B, d)}(Q, Q[k])`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **The quasi-isomorphism `E' → End(Q)`, with its formula.** The quasi-isomorphism of
`DifferentialGradedModule.exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap` may be
taken to be the inclusion: it sends an endomorphism of `Q` in the degree-`≤ 0` truncation to the
same endomorphism, read in `End(Q)`. -/
theorem exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap_algebraHom
    (B : DifferentialGradedAlgebra.{u, u} R) (Q : DifferentialGradedModule.{u, u, u} B)
    (hQ : Nonempty (PropertyPFiltration Q))
    (hvanish : ∀ k : ℤ, 0 < k →
      ∀ f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ⟶
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (Q.shift k), f = 0) :
    ∃ φ : (DGCategory.homRepresentation
        (DGCategory.nonpositive (dgCategory.{u, u, u} B)) Q).algebra.Hom (endomorphismDGA B Q),
      (∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) ∧
        ∀ (n : ℤ) (a : (DGCategory.homRepresentation
            (DGCategory.nonpositive (dgCategory.{u, u, u} B)) Q).algebra.grading n),
          endomorphismAlgebraHom B Q n ⟨φ.toAlgebraHom a, φ.map_grading n a a.property⟩ =
            ((DGCategory.homRepresentation
              (DGCategory.nonpositive (dgCategory.{u, u, u} B)) Q).algebraHom n a).1 := by
  refine DGCategory.exists_hom_nonpositive_bijective_cohomologyMap_algebraHom
    (dgCategory.{u, u, u} B) Q (endomorphismRepresentation B Q) ?_
  intro n hn a ha
  have heq : (DifferentialGraded.Bimodule.endomorphism B Q).cohomologyEndomorphismComparison n
        (Quotient.mk _ ⟨a, ha⟩) =
      (DifferentialGraded.Bimodule.endomorphism B Q).cohomologyEndomorphismComparison n
        (Quotient.mk _ ⟨0, by rw [Submodule.coe_zero, map_zero]⟩) :=
    (hvanish n hn _).trans (hvanish n hn _).symm
  have hbij := DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_endomorphism
    B Q hQ n
  obtain ⟨c, hc⟩ := Quotient.exact (hbij.injective heq)
  exact ⟨c, by simpa using hc⟩

/-- **The quasi-isomorphism `E' → End(Q)`.** Let `Q` be a right differential graded `B`-module
with property (P) such that `Hom_{D(B, d)}(Q, Q[k]) = 0` for every `k > 0`. Then the inclusion of
the endomorphism algebra of `Q` in the degree-`≤ 0` truncation of the differential graded category
of right differential graded `B`-modules into `End(Q)` is bijective on cohomology in every degree,
i.e. a quasi-isomorphism of differential graded algebras.

Through [Stacks, Tag 09S6] (`DifferentialGraded.Bimodule.derivedExtensionEquivalence`) this gives
an equivalence `D(E', d) ≌ D(End(Q), d)`.

The hypothesis of `DGCategory.exists_hom_nonpositive_bijective_cohomologyMap` is the vanishing of
`H^k(End(Q))` for `k > 0`; it is read off the derived-category hypothesis through
`DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_endomorphism`, which is
injective, so a cohomology class whose image in `Hom_{D(B, d)}(Q, Q[k])` agrees with that of zero
is itself zero. -/
theorem exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap
    (B : DifferentialGradedAlgebra.{u, u} R) (Q : DifferentialGradedModule.{u, u, u} B)
    (hQ : Nonempty (PropertyPFiltration Q))
    (hvanish : ∀ k : ℤ, 0 < k →
      ∀ f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj Q ⟶
        (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj (Q.shift k), f = 0) :
    ∃ φ : (DGCategory.homRepresentation
        (DGCategory.nonpositive (dgCategory.{u, u, u} B)) Q).algebra.Hom (endomorphismDGA B Q),
      ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k) :=
  (exists_hom_nonpositiveEndomorphismDGA_bijective_cohomologyMap_algebraHom B Q hQ hvanish).imp
    fun _ h => h.1

end DifferentialGradedModule

end
