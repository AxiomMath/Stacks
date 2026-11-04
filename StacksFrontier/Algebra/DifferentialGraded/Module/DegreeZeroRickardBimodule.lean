module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroDerivedStructure
public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroKFlat
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimoduleExistence

/-! # Rickard's criterion for ordinary algebras: the bimodule clause

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras, not assumed commutative.
[Stacks, Tag 09SC] adds to its two equivalent conditions a third one, available when `B` is flat
as an `R`-module: the existence of an `(A, B)`-bimodule `N` for which `- ⊗_A^𝐋 N : D(A) → D(B)`
is an equivalence.

This file proves the implication `(1) ⇒ (3)`: from an additive, `R`-linear, shift-commuting
equivalence of the derived categories of right modules, and flatness of `B` over `R`, it
produces such an `N`. The bimodule is the one [Stacks, Tag 09SA] produces in the differential
graded world, carried to the ordinary derived categories along the degree-zero comparison
`DifferentialGradedModule.degreeZeroDerivedEquivalence`.

## Main results

* `DifferentialGradedModule.exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence`:
  **Stacks 09SC, the implication (1) ⇒ (3).**

## Implementation notes

*Which notion of bimodule.* The source's part (3) reads, verbatim: "Moreover, if `B` is flat as
an `R`-module, then this is also equivalent to (3) there exists an `(A, B)`-bimodule `N` such
that `- ⊗_A^𝐋 N : D(A) → D(B)` is an equivalence." The phrase "`(A, B)`-bimodule" carries no
differential graded qualifier there. The reading formalized here is the *differential graded*
one: `N` is a differential graded `(A, B)`-bimodule over the degree-zero algebras, in the sense
of the chapter ([Stacks, Tag 0FQI], `DifferentialGraded.Bimodule`).

That is the reading the source's own proof supports. Its argument for (3) goes through
[Stacks, Tag 09SA], whose statement asks for "an `(A, B)`-bimodule `N` as in Lemma 09S7" for
*differential graded* algebras, so what the cited proof delivers is a differential graded
bimodule and nothing more. The literal reading, with `N` an ordinary `(A, B)`-bimodule — a
differential graded bimodule concentrated in degree zero — would be **strictly stronger**, and it
is not established by anything the source cites; it is therefore neither claimed nor proved
below. Equally, the differential graded reading is not used silently: it is what the statement
of
`DifferentialGradedModule.exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence`
literally says, since its `N` has type `DifferentialGraded.Bimodule (degreeZero R A)
(degreeZero R B)`.

*The literal reading is not merely unproved: it is false.* Suppose `N` were an ordinary
`(A, B)`-bimodule with `- ⊗_A^𝐋 N : D(A) → D(B)` an equivalence. The equivalence carries the
compact generator `A` of `D(A)` to `A ⊗_A^𝐋 N = N`, so `N` is a compact object of `D(B)`, hence
perfect ([Stacks, Tag 09RB]); a module which is perfect as a complex is finitely generated of
finite projective dimension. Moreover `H^k(A) = Hom_{D(B)}(N, N[k])`, which is `A` for `k = 0`
and `0` otherwise, and `Hom_{D(B)}(N, K[k]) = 0` for all `k` forces `K = 0`. So such an `N` is a
one-sided tilting *module* with `End_B(N) = A`. Now take `R = k` a field and `B` a
finite-dimensional self-injective `k`-algebra. Over such a `B` a finitely generated module of
finite projective dimension is projective, because the last term of a minimal projective
resolution is injective and the resolution therefore splits; so `N` is a finitely generated
projective generator and `A = End_B(N)` is Morita equivalent to `B`. The literal clause would
thus assert that derived equivalent self-injective algebras are Morita equivalent, and that is
false: Brauer tree algebras with the same number of edges and the same multiplicity are all
derived equivalent (Rickard, *Derived categories and stable equivalence*), while their Morita
class remembers the tree. In other words the tilting complex `P` of the source's part (2) cannot
always be chosen to be a module, which is exactly what the literal reading of (3) demands.

*Why the unqualified phrase is the differential graded one.* The chapter's Definition
[Stacks, Tag 0FQH] gives all three notions — ordinary, graded and differential graded
`(A, B)`-bimodule — so the phrase in part (3) does have a literal referent. But the chapter also
uses the unqualified phrase for the differential graded notion: Tag 09SA, from which part (3) is
deduced, concludes "there exists an `(A, B)`-bimodule `N` as in Lemma 09S7", and the `N` of
Tag 09S7 is a *differential graded* `(A, B)`-bimodule; Remark [Stacks, Tag 09ST] in turn glosses
what Tag 09SA produces as "a differential graded `(A, B)`-bimodule `Ω`". With the previous
paragraph, the differential graded reading is the only one under which part (3) is true.

*What "`- ⊗_A^𝐋 N : D(A) → D(B)` is an equivalence" says.* Two things are recorded, and the
second is the ordinary-derived-category reading of the source's phrase. First, the derived tensor
functor `DifferentialGraded.Bimodule.derivedTensorFunctor N` between the differential graded
derived categories `D(degreeZero R A, d) ⥤ D(degreeZero R B, d)` is an equivalence — this is
Tag 09SA's own conclusion. Second, its conjugate along the degree-zero comparisons,
`D(Mod-A) ⥤ D(Mod-B)`, is an equivalence; the conjugate is the functor the source names, under
the identification of `D(A)` with `D(degreeZero R A, d)`.

*Flatness.* The source's hypothesis for (3) is flatness of `B` as an `R`-module; Tag 09SA's is
K-flatness of `B` as a complex of `R`-modules. The two are bridged by
`DifferentialGradedModule.kFlat_regularModule_degreeZero_of_flat`, which is [Stacks, Tag 064K] for
a complex concentrated in degree zero.

*Which derived category `D(A)` is, and universes.* As in
`StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroRickard`, a differential graded module
is a right module throughout Chapter 22, so `D(A)` for an ordinary algebra `A` is
`DerivedCategory (ModuleCat Aᵐᵒᵖ)`, reached through the instance
`DifferentialGradedAlgebra.instIsOppositeAlgebraOp`; the base ring, the algebras and the modules
live in a single universe `u`, and the two ordinary derived categories are the standard models,
`HasDerivedCategory.standard`.

*What is assumed of the equivalence, against the source's condition (1).* The source's (1) is an
`R`-linear equivalence of triangulated categories. What is assumed below is additivity,
`R`-linearity and commutation with the translation, which is all Tag 09SA needs;
`CategoryTheory.Functor.IsTriangulated` is not used.

*The converse is not proved here.* Deducing `(3) ⇒ (1)` needs the degree-zero comparison to be
triangulated, not merely shift-commuting, in order to turn the differential graded equivalence
back into a triangulated equivalence of the ordinary derived categories. That exactness is
`DifferentialGradedModule.degreeZeroDerivedEquivalence_functor_exact`, and the converse itself is
`DifferentialGradedModule.exists_derivedEquivalence_of_bimodule`, in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardConverse.lean`, which also
packages the equivalence of (1) and (3) as
`DifferentialGradedModule.derivedEquivalence_iff_exists_bimodule`.

*The priority of the standard derived category.* `HasDerivedCategory.standard` is made a local
instance here at a raised priority. Without that it loses to another `HasDerivedCategory`
instance reachable through this file's imports, whose model has its morphisms one universe lower,
so the statement below would be about *that* model rather than the standard one this note claims
— and it would then not be the same clause (1) as in
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickard.lean`, where `standard` wins
unaided. The raised priority is what makes the two files speak about the same two derived
categories, which is what the equivalences of
`StacksFrontier/Algebra/DifferentialGraded/Module/DegreeZeroRickardConverse.lean` need.

## References

* [Stacks Project, Tag 09SC](https://stacks.math.columbia.edu/tag/09SC), the lemma whose part (3)
  is proved here, and [Tag 09SA](https://stacks.math.columbia.edu/tag/09SA), the source of the
  bimodule.
* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the criterion the
  bimodule satisfies, [Tag 0FQI](https://stacks.math.columbia.edu/tag/0FQI) for differential
  graded bimodules and [Tag 064K](https://stacks.math.columbia.edu/tag/064K) for the flatness
  bridge.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

open DifferentialGradedAlgebra DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {B : Type u} [Ring B] [Algebra R B]

/-- **Stacks 09SC, the implication (1) ⇒ (3).** Let `R` be a commutative ring, let `A` and `B`
be `R`-algebras, not assumed commutative, and assume `B` is flat as an `R`-module. Let

`E : D(Mod-A) ≌ D(Mod-B)`

be an additive, `R`-linear, shift-commuting equivalence of the derived categories of right
modules. Then there is a differential graded `(A, B)`-bimodule `N` over the degree-zero algebras
`degreeZero R A` and `degreeZero R B` such that

* `- ⊗_A^𝐋 N : D(degreeZero R A, d) ⥤ D(degreeZero R B, d)` is an equivalence, and
* so is the functor `D(Mod-A) ⥤ D(Mod-B)` it induces along the degree-zero comparisons, which is
  what the source's `- ⊗_A^𝐋 N : D(A) → D(B)` names.

The bimodule is the one of [Stacks, Tag 09SA], applied to the equivalence `E` conjugated into the
differential graded derived categories; its hypothesis `A = H^0(A)` holds because the degree-zero
grading vanishes away from degree zero, and its K-flatness hypothesis is supplied from flatness
of `B` over `R` by `DifferentialGradedModule.kFlat_regularModule_degreeZero_of_flat`.

The source writes "`(A, B)`-bimodule" with no differential graded qualifier. What is proved here
is the differential graded reading, which is what the proof the source cites — Tag 09SA, via
Tag 09S7 — actually yields; the literal ordinary-bimodule reading is strictly stronger, is not
established by anything the source cites, and is in fact false, by the self-injective
counterexample in the implementation notes of this file. -/
@[stacks 09SC "(1) ⇒ (3) under B flat over R, with N a DIFFERENTIAL GRADED (A,B)-bimodule -- the \
chapter's own unqualified sense in 09SA/09S7, which 09SC(3) cites, and the ONLY reading under \
which (3) is true. The literal ordinary-bimodule reading is not merely unproved but FALSE: such \
an N would be a one-sided tilting module with End_B(N) = A, hence projective and a progenerator \
over a finite-dimensional self-injective B, forcing A Morita equivalent to B -- so (3) would say \
derived equivalent self-injective algebras are Morita equivalent, refuted by Brauer tree algebras \
(Rickard). D(A) is the derived category of right A-modules. NOT (3) ⇒ (1)"]
theorem exists_bimodule_derivedTensorEquivalence_of_derivedEquivalence [Module.Flat R B]
    (E : DerivedCategory (ModuleCat.{u} Aᵐᵒᵖ) ≌ DerivedCategory (ModuleCat.{u} Bᵐᵒᵖ))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    ∃ N : DifferentialGraded.Bimodule (degreeZero R A) (degreeZero R B),
      (derivedTensorFunctor N).IsEquivalence ∧
        ((degreeZeroDerivedEquivalence (R := R) (S := A) (A := Aᵐᵒᵖ)).inverse ⋙
          derivedTensorFunctor N ⋙
            (degreeZeroDerivedEquivalence (R := R) (S := B)
              (A := Bᵐᵒᵖ)).functor).IsEquivalence := by
  let EA := degreeZeroDerivedEquivalence (R := R) (S := A) (A := Aᵐᵒᵖ)
  let EB := degreeZeroDerivedEquivalence (R := R) (S := B) (A := Bᵐᵒᵖ)
  have := EB.commShiftInverse ℤ
  let G : derivedCategory' (degreeZero R A) ≌ derivedCategory' (degreeZero R B) :=
    EA.trans (E.trans EB.symm)
  have : G.functor.Additive := by
    show (EA.functor ⋙ E.functor ⋙ EB.inverse).Additive
    infer_instance
  have : G.functor.Linear R := by
    show (EA.functor ⋙ E.functor ⋙ EB.inverse).Linear R
    infer_instance
  have : G.functor.CommShift ℤ := by
    show (EA.functor ⋙ E.functor ⋙ EB.inverse).CommShift ℤ
    infer_instance
  obtain ⟨N, -, -, -, hN, -⟩ :=
    exists_bimodule_of_derivedEquivalence (degreeZero R A) (degreeZero R B)
      (fun i hi => degreeZeroGrading_eq_bot R A hi) (kFlat_regularModule_degreeZero_of_flat R B) G
  refine ⟨N, hN, ?_⟩
  have := hN
  infer_instance

end DifferentialGradedModule

end
