module

public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Scheme
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation

/-!
# Homogeneous products in the two graded rings of sections

Both relative-`Proj` substrates of this repository build the graded ring of sections of a graded
`𝒪_S`-algebra over an open as the direct sum `⨁_{n ≥ 0} 𝒜ₙ(U)` of its homogeneous section
groups, and both carry the same homogeneous multiplication; but
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.instGCommRing` *constructs* the
graded-ring structure while `Stacks.RelativeProj.Situation.sectionRingGradedRing` selects it from
an existence statement with `Classical.choice`. The two `CommRing` instances on the one carrier
are therefore not definitionally equal, and a proof that mentions both — such as a comparison of
the two relative `Proj`s — asks the elaborator to unfold a `Classical.choice` whenever a lemma's
instance argument has to be guessed from the goal.

This file removes that guessing from the two places a comparison needs it: the product of two
homogeneous sections and the unit. Each statement names its substrate's multiplication, so its
instance argument is fixed by the statement, and each right-hand side is written with the
*algebra's* multiplication and unit, which belong to neither substrate.

## Main definitions

* `Stacks.SymGraded.symSituation`: the relative `Proj` situation of `Sym(E)` with its base
  spelled as the scheme itself, which is what lets the two substrates' statements have the same
  types at `instances` transparency.
* `Stacks.SymGraded.situationSheafGradedAlgebra`: `Sym(E)` as sheaf-level graded algebra data
  read off the *situation*'s algebra. Reading it off the situation is what makes the two
  substrates' homogeneous pieces agree by a single projection instead of by unfolding two
  constructions of `Sym(E)`, which is the difference between a comparison that elaborates and one
  that exhausts the heartbeat budget.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.of_mul_of` and
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.one_eq`: the product of two
  homogeneous sections and the unit, for the constructed graded-ring structure.
* `Stacks.RelativeProj.Situation.of_mul_of` and `Stacks.RelativeProj.Situation.one_eq`: the same,
  for the selected one. These are the characterizing equations
  `Stacks.RelativeProj.Situation.SectionRingStructure.mul_homogeneous` and `one_homogeneous`,
  read in the direct sum rather than in a homogeneous piece.
* `Stacks.SymGraded.symSituation_eq` and `Stacks.SymGraded.situationSheafGradedAlgebra_eq`: the
  two are `Stacks.RelativeProj.symmetricSituationOfQuasicoherent` and
  `Stacks.SymGraded.schemeSheafGradedAlgebra`, by `rfl`.

## Implementation notes

The degree bookkeeping is definitional: the product of a degree-`i` and a degree-`j` homogeneous
section lands in the piece of degree `(i : ℤ) + (j : ℤ)`, while the summand it is placed in is
indexed by `i + j : ℕ`, and `Int.ofNat i + Int.ofNat j` reduces to `Int.ofNat (i + j)`. So no
transport appears in either statement.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- **The product of two homogeneous sections** in the constructed graded ring of sections is the
algebra's homogeneous multiplication. -/
public theorem of_mul_of {i j : ℕ} (a : A.sectionPieces U i) (b : A.sectionPieces U j) :
    DirectSum.of (A.sectionPieces U) i a * DirectSum.of (A.sectionPieces U) j b =
      DirectSum.of (A.sectionPieces U) (i + j) ((A.mul (i : ℤ) (j : ℤ)).app U a b) :=
  DirectSum.of_mul_of a b

/-- **The unit of the constructed graded ring of sections** is the algebra's unit, in degree
`0`. -/
public theorem one_eq : (1 : A.sectionRing U) = DirectSum.of (A.sectionPieces U) 0 (A.one U) :=
  DirectSum.one_def _

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (U : s.base.Opens)

/-- **The product of two homogeneous sections** in the selected graded ring of sections is the
algebra's homogeneous multiplication. This is
`Stacks.RelativeProj.Situation.SectionRingStructure.mul_homogeneous`, read in the direct sum. -/
public theorem of_mul_of (i j : ℕ) (a : s.sectionPieces U i) (b : s.sectionPieces U j) :
    DirectSum.of (s.sectionPieces U) i a * DirectSum.of (s.sectionPieces U) j b =
      DirectSum.of (s.sectionPieces U) (i + j)
        ((s.algebra.mul (i : ℤ) (j : ℤ)).app (op U) a b) :=
  (DirectSum.of_mul_of a b).trans
    (congrArg (DirectSum.of (s.sectionPieces U) (i + j))
      (eq_of_heq ((sectionRingStructure s).mul_homogeneous U i j a b)))

/-- **The unit of the selected graded ring of sections** is the algebra's unit, in degree `0`.
This is `Stacks.RelativeProj.Situation.SectionRingStructure.one_homogeneous`, read in the direct
sum. -/
public theorem one_eq :
    (1 : s.sectionRing U) = DirectSum.of (s.sectionPieces U) 0 (s.algebra.one.eval (op U)) :=
  (DirectSum.one_def _).trans
    (congrArg (DirectSum.of (s.sectionPieces U) 0)
      ((sectionRingStructure s).one_homogeneous U))

end Stacks.RelativeProj.Situation

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- **The relative `Proj` situation of `Sym(E)`, with its base spelled as `X`.** This is
`Stacks.RelativeProj.symmetricSituationOfQuasicoherent` — see
`Stacks.SymGraded.symSituation_eq` — and it is `@[reducible]` for one reason: the base of
`symmetricSituationOfQuasicoherent X E` is `X` only after unfolding two semireducible
definitions, so a term of type `(symmetricSituationOfQuasicoherent X E).base.Opens` and one of
type `X.Opens` are interchangeable at default transparency and *not* at the `instances`
transparency that typeclass synthesis and `rw` work at. Writing the situation this way makes the
two spellings one. -/
@[reducible] public def symSituation : Stacks.RelativeProj.Situation.{u} where
  base := X
  algebra := (Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E).algebra
  mul_comm := (Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E).mul_comm
  negative_isZero := (Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E).negative_isZero
  isQuasicoherent := (Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E).isQuasicoherent

/-- **It is the situation of Tag 01OB**, so it has the same relative `Proj`. -/
public theorem symSituation_eq :
    symSituation E = Stacks.RelativeProj.symmetricSituationOfQuasicoherent X E := rfl

/-- **`Sym(E)` as sheaf-level graded algebra data, read off the relative `Proj` situation of
`E`.** This is `Stacks.SymGraded.schemeSheafGradedAlgebra` — see
`Stacks.SymGraded.situationSheafGradedAlgebra_eq` — but written over
`Stacks.RelativeProj.Situation.algebra`, so that its homogeneous pieces are the situation's by a
projection rather than by unfolding two constructions of `Sym(E)`. -/
public def situationSheafGradedAlgebra :
    Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X :=
  Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra (symSituation E).algebra
    (isCommutative_symmetricAlgebra E) (vanishesInNegativeDegrees_symmetricAlgebra E) hqc

/-- **It is the same graded algebra data**, so it builds the same projective bundle. -/
public theorem situationSheafGradedAlgebra_eq :
    situationSheafGradedAlgebra E hqc = schemeSheafGradedAlgebra E hqc := rfl

end Stacks.SymGraded

end
