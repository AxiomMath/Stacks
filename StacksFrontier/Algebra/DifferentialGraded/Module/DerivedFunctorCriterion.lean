module

public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions

/-!
# Derived functors on the homotopy category of differential graded modules

Let `(A, d)` be a differential graded algebra and let `K(A)` be the homotopy category of right
differential graded `A`-modules. This file specialises the criteria of
`StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions` to the multiplicative system
`Qis(A)` of quasi-isomorphisms, so that for an arbitrary functor out of `K(A)` the existence of
its left, resp. right, derived functor is reduced to the single statement that *resolutions
exist*: every differential graded module receives a quasi-isomorphism from a module orthogonal
on the left to the acyclic modules, resp. admits a quasi-isomorphism into a module orthogonal on
the right to them.

That is the shape in which Stacks 09LS and 09LI use Stacks 06XN, with the objects having
property (P), resp. property (I), as the orthogonal modules — their orthogonality being
Stacks 09KM, resp. 09KS. Nothing below mentions property (P) or (I): the criteria hold for any
supply of resolutions by orthogonal modules, and the two cited lemmas are exactly what makes the
hypothesis available.

## Main results

* `DifferentialGradedModule.isLeftDerivable_of_exists_quasiIso_leftOrthogonal` and
  `DifferentialGradedModule.hasLeftDerivedFunctor_of_exists_quasiIso_leftOrthogonal`: from
  resolutions on the left, the left derived functor of any `F : K(A) ⥤ ℋ` is everywhere defined
  in the sense of Stacks 05SV, and `F` has a left derived functor in Mathlib's Kan extension
  sense.
* `DifferentialGradedModule.isRightDerivable_of_exists_quasiIso_rightOrthogonal` and
  `DifferentialGradedModule.hasRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal`: the dual
  statements.
* `DifferentialGradedModule.quasiIsomorphisms_isSaturatedMultiplicative'`: the quasi-isomorphisms
  satisfy axiom MS4 together with multiplicativity, which is the form in which Stacks 06XN
  consumes their saturation.

## Implementation notes

*The hypothesis is stated on differential graded modules, not on `K(A)`.* The resolutions that
Stacks 09KP and 09KU produce are homomorphisms of differential graded modules which are
quasi-isomorphisms of the underlying cochain complexes, so the hypothesis below is phrased that
way, with Mathlib's `QuasiIso` applied to the image under `forgetToCochainComplex`. The passage
to `K(A)` uses that every object of `K(A)` is the image of a differential graded module and that
`DifferentialGradedModule.quasiIsomorphisms_map_iff'` identifies the two notions of
quasi-isomorphism. Only the orthogonality is stated on `K(A)`, since that is where it lives.

*Universes.* The differential graded algebra and its modules are taken at main's single-universe
encoding `StacksDraft.Ch22.Sec4.Tag09JJ`, in which `DifferentialGradedAlgebra : Type u → Type u`
and a module over it again lies in `Type u`. The Stacks source is universe-polymorphic in the
algebra and the module separately, and so are the statements this one rests on; matching that needs the
encoding widened, which is not done here. Nothing below depends on the universes being equal,
so the widening is an addition of universe parameters rather than a change of content.

## Naming

`DifferentialGradedModule.quasiIsomorphisms_isSaturatedMultiplicative'` is primed to keep it
apart from the homonymous theorem in `StacksFrontier/Algebra/DGA/QuasiIsomorphismFractions.lean`, which
is the same statement for the parallel Tag 09KW/09KX treatment in `StacksDraft/Ch22/`. The two
rest on different pretriangulated structures on `K(A, d)`; see the naming note in
`StacksFrontier/Algebra/DifferentialGraded/Module/QuasiIsomorphism.lean`.

## References

* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN), the criterion; it is
  applied in this form in [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGradedModule

universe u v' u'

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- The quasi-isomorphisms of `K(A)` are multiplicative and satisfy axiom MS4. This is the
form of saturation that Stacks 06XN consumes. -/
theorem quasiIsomorphisms_isSaturatedMultiplicative' :
    (quasiIsomorphisms' A).IsSaturatedMultiplicative :=
  (quasiIsomorphisms_isSaturated' A).isSaturatedMultiplicative

/-- The quasi-isomorphisms, viewed as the multiplicative system attached to the triangulated
subcategory of acyclic modules, are multiplicative and satisfy axiom MS4. -/
theorem acyclic_trW_isSaturatedMultiplicative :
    (acyclic' A).trW.IsSaturatedMultiplicative := by
  rw [acyclic_trW_eq_quasiIsomorphisms']
  exact quasiIsomorphisms_isSaturatedMultiplicative' A

section Resolutions

variable {H : Type u'} [Category.{v'} H]

/-- Resolutions of differential graded modules by modules orthogonal on the left to the acyclic
ones, transported to the homotopy category and to the multiplicative system attached to the
acyclic modules. -/
theorem exists_trW_leftOrthogonal_of_exists_quasiIso_leftOrthogonal
    (hres : ∀ M : DifferentialGradedModule A, ∃ (P : DifferentialGradedModule A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P))
    (X : HomotopyCategory A) :
    ∃ (P : HomotopyCategory A) (s : P ⟶ X),
      (acyclic' A).trW s ∧ (acyclic' A).leftOrthogonal P := by
  obtain ⟨M⟩ := X
  obtain ⟨P, f, hf, hP⟩ := hres M
  refine ⟨(toHomotopyCategory A).obj P, (toHomotopyCategory A).map f, ?_, hP⟩
  rwa [acyclic_trW_eq_quasiIsomorphisms', quasiIsomorphisms_map_iff']

/-- Resolutions of differential graded modules by modules orthogonal on the right to the acyclic
ones, transported to the homotopy category and to the multiplicative system attached to the
acyclic modules. -/
theorem exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal
    (hres : ∀ M : DifferentialGradedModule A, ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I))
    (X : HomotopyCategory A) :
    ∃ (I : HomotopyCategory A) (s : X ⟶ I),
      (acyclic' A).trW s ∧ (acyclic' A).rightOrthogonal I := by
  obtain ⟨M⟩ := X
  obtain ⟨I, f, hf, hI⟩ := hres M
  refine ⟨(toHomotopyCategory A).obj I, (toHomotopyCategory A).map f, ?_, hI⟩
  rwa [acyclic_trW_eq_quasiIsomorphisms', quasiIsomorphisms_map_iff']

/-- **Stacks 06XN(2)** on `K(A)`. If every differential graded `A`-module receives a
quasi-isomorphism from a module whose class in `K(A)` is orthogonal on the left to the acyclic
modules, then the left derived functor of any `F : K(A) ⥤ ℋ` is everywhere defined with respect
to the quasi-isomorphisms, in the sense of Stacks 05SV. -/
theorem isLeftDerivable_of_exists_quasiIso_leftOrthogonal (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A, ∃ (P : DifferentialGradedModule A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P)) :
    F.IsLeftDerivable (quasiIsomorphisms' A) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms']
  exact (acyclic' A).isLeftDerivable_of_leftOrthogonal_resolutions F
    (exists_trW_leftOrthogonal_of_exists_quasiIso_leftOrthogonal A hres)
    (acyclic_trW_isSaturatedMultiplicative A)

/-- **Stacks 06XN(1)** on `K(A)`. If every differential graded `A`-module admits a
quasi-isomorphism into a module whose class in `K(A)` is orthogonal on the right to the acyclic
modules, then the right derived functor of any `F : K(A) ⥤ ℋ` is everywhere defined with respect
to the quasi-isomorphisms, in the sense of Stacks 05SV. -/
theorem isRightDerivable_of_exists_quasiIso_rightOrthogonal (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A, ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I)) :
    F.IsRightDerivable (quasiIsomorphisms' A) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms']
  exact (acyclic' A).isRightDerivable_of_rightOrthogonal_resolutions F
    (exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal A hres)
    (acyclic_trW_isSaturatedMultiplicative A)

/-- Under the same resolution hypothesis, any `F : K(A) ⥤ ℋ` has a left derived functor in
Mathlib's sense: a right Kan extension along a localization functor for the
quasi-isomorphisms. -/
theorem hasLeftDerivedFunctor_of_exists_quasiIso_leftOrthogonal (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A, ∃ (P : DifferentialGradedModule A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P)) :
    F.HasLeftDerivedFunctor (quasiIsomorphisms' A) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms']
  exact (acyclic' A).hasLeftDerivedFunctor_of_leftOrthogonal_resolutions F
    (exists_trW_leftOrthogonal_of_exists_quasiIso_leftOrthogonal A hres)

/-- Under the same resolution hypothesis, any `F : K(A) ⥤ ℋ` has a right derived functor in
Mathlib's sense: a left Kan extension along a localization functor for the
quasi-isomorphisms. -/
theorem hasRightDerivedFunctor_of_exists_quasiIso_rightOrthogonal (F : HomotopyCategory A ⥤ H)
    (hres : ∀ M : DifferentialGradedModule A, ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧
        (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I)) :
    F.HasRightDerivedFunctor (quasiIsomorphisms' A) := by
  rw [← acyclic_trW_eq_quasiIsomorphisms']
  exact (acyclic' A).hasRightDerivedFunctor_of_rightOrthogonal_resolutions F
    (exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal A hres)

end Resolutions

end DifferentialGradedModule

end
