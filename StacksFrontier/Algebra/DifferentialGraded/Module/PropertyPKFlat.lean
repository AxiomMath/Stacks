module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConnectingHomBoundary
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DirectSumCochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Module.DistinguishedTriangle
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyPFiltrationInduction
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
public import StacksFrontier.Homology.KFlat.Closure

/-! # A module with property (P) is K-flat over the base ring

Let `(A, d)` be a differential graded algebra over a commutative ring `R` which is K-flat as a
complex of `R`-modules, and let `P` be a right differential graded `A`-module carrying a
property-(P) filtration. Then `P` is itself K-flat as a complex of `R`-modules.

This is the K-flatness half of the claim the source makes inside the proof of Stacks 0BYZ: *"Let
`P` be a differential graded `A`-module with property (P). We claim that `c_P` is an isomorphism
and that `P` is K-flat as a complex of `R`-modules."* It is proved exactly as the source does it,
by induction along the filtration: `A` itself is K-flat by hypothesis, hence so is every direct
sum of shifts of `A`, hence so is every stage of the filtration because the stages sit in short
exact sequences which are split as sequences of graded modules, and hence so is `P`, which is the
quotient term of such a sequence whose outer terms are the direct sum of the stages.

## Main results

* `DifferentialGradedModule.kFlat_toCochainComplex_of_propertyPFiltration`: the statement above.

## Implementation notes

*Where the hypothesis on `A` is used.* Only in the base case of the induction, the one about a
direct sum of shifts `⨁ᵢ A[kᵢ]`: `CochainComplex.KFlat.kFlat_shift` takes K-flatness of `A^•` to
K-flatness of each `A[kᵢ]^•` and `CochainComplex.KFlat.kFlat_coproduct` assembles those. The two
sequence steps and the telescope step use no flatness at all, which is why the source's induction
needs nothing beyond its three closure properties.

*Why the two-out-of-three used here is the split one.* A direct sum of translates of a merely
K-flat complex is not termwise flat, so `CochainComplex.KFlat.kFlat_two_out_of_three` (Stacks
0BYH) does not apply to the sequences of the filtration. The source cites Tag 06Y2 instead, and
the form of it available here is
`CochainComplex.KFlat.kFlat_two_out_of_three_of_degreewiseSplit`, whose degreewise splitting is
produced from the graded splittings of an admissible short exact sequence by
`DifferentialGradedModule.splittingOfGradedSplittings`.

*Why the induction is the elementwise one.* K-flatness is a property of a cochain complex, not of
an object of the derived category, so the dévissage of Tag 0FQE does not apply; the statement
needed is `DifferentialGradedModule.propertyPFiltration_induction`, which stays in
`Mod_{(A,d)}`.

## References

* [Stacks Project, Tag 0BYZ](https://stacks.math.columbia.edu/tag/0BYZ), whose proof contains
  this claim.
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P).
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ), K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The sequence of cochain complexes underlying an admissible short exact sequence of
differential graded modules, split in every degree. The splitting is read off graded splittings
of the original sequence, which admissibility supplies. -/
def degreewiseSplittingOfIsAdmissibleShortExact {K L M : DifferentialGradedModule A}
    (i : K ⟶ L) (p : L ⟶ M) (hip : IsAdmissibleShortExact i p) (n : ℤ) :
    ((admissibleCochainShortComplex A i p hip).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)).Splitting :=
  letI sp := (nonempty_compatibleSplittings A i p hip).some
  splittingOfGradedSplittings
    (ShortComplex.mk i p (comp_eq_zero_of_isAdmissibleShortExact A i p hip))
    sp.s sp.π sp.hs sp.hπ (hip.decomposition sp.hs sp.hπ sp.hker) n

/-- **A differential graded module with property (P) over a differential graded algebra which is
K-flat as a complex of `R`-modules is itself K-flat as a complex of `R`-modules.** This is the
K-flatness half of the claim in the proof of Stacks 0BYZ.

The induction is `DifferentialGradedModule.propertyPFiltration_induction`; its five obligations
are, in order, that K-flatness is invariant under isomorphism, that it holds on a direct sum of
shifts of `A`, that it is stable under countable direct sums, and the two directions of
two-out-of-three along an admissible short exact sequence. The hypothesis on `A` enters only in
the second. -/
@[stacks 0BYZ "the K-flatness half of the claim in the PROOF — a differential graded A-module \
with property (P) is K-flat as a complex of R-modules. Not any of parts (1), (2), (3); part (1) \
is DifferentialGraded.Bimodule.derivedBaseChangeFunctor_isLeftDerivedFunctor"]
theorem kFlat_toCochainComplex_of_propertyPFiltration
    (hA : CochainComplex.KFlat.{u, u} (regularModule A).toCochainComplex)
    {P : DifferentialGradedModule A} (F : PropertyPFiltration P) :
    CochainComplex.KFlat.{u, u} P.toCochainComplex := by
  classical
  refine propertyPFiltration_induction
    (fun M : DifferentialGradedModule A => CochainComplex.KFlat.{u, u} M.toCochainComplex)
    (fun {M M'} e h => CochainComplex.kFlat_of_iso.{u, u}
      ((forgetToCochainComplex A).mapIso e) h)
    (fun ι _ k => ?_) (fun N hN => ?_) (fun {K L M} i p hip hK hM => ?_)
    (fun {K L M} i p hip hK hL => ?_) F
  · have hshift : ∀ j : ι,
        CochainComplex.KFlat.{u, u} (shift (regularModule A) (k j)).toCochainComplex :=
      fun j => CochainComplex.kFlat_of_iso.{u, u}
        (dgShiftToCochainShiftIso A (regularModule A) (k j)).symm
        (CochainComplex.KFlat.kFlat_shift.{u, u} _ hA (k j))
    exact CochainComplex.kFlat_of_iso.{u, u}
      ((forgetToCochainComplex A).mapIso (directSumObjIsoDirectSumShifts A k))
      (CochainComplex.kFlat_of_iso.{u, u}
        (directSumObjToCochainComplexIso (fun j => shift (regularModule A) (k j))).symm
        (CochainComplex.KFlat.kFlat_coproduct.{u, u} _ hshift))
  · exact CochainComplex.kFlat_of_iso.{u, u}
      (directSumObjToCochainComplexIso (fun j : ULift.{u} ℕ => N j.down)).symm
      (CochainComplex.KFlat.kFlat_coproduct.{u, u} _ (fun j => hN j.down))
  · exact (CochainComplex.KFlat.kFlat_two_out_of_three_of_degreewiseSplit
      (admissibleCochainShortComplex A i p hip)
      (degreewiseSplittingOfIsAdmissibleShortExact i p hip)).2.1 hK hM
  · exact (CochainComplex.KFlat.kFlat_two_out_of_three_of_degreewiseSplit
      (admissibleCochainShortComplex A i p hip)
      (degreewiseSplittingOfIsAdmissibleShortExact i p hip)).2.2 hK hL

end DifferentialGradedModule

end
