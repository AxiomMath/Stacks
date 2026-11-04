module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.AlgebraHom
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.CochainDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation

/-!
# The endomorphism differential graded algebra of a complex

Let `R` be a commutative ring and `M` a cochain complex of `R`-modules. The endomorphisms of `M`
in the differential graded category of cochain complexes form a differential graded `R`-algebra
`End(M)`, whose degree-`n` part is the degree-`n` cochains `M → M`, whose multiplication is
composition of cochains and whose differential is the graded commutator differential. For a
differential graded `R`-algebra `A`, giving a left differential graded action of `A` on `M` is
then the same as giving a homomorphism of differential graded algebras `A ⟶ End(M)`.

## Main definitions

* `CochainComplex.endomorphismDGA`: the endomorphism differential graded algebra of `M`,
  presented as in `CochainComplex.EndomorphismDGA`.

## Main results

* `DifferentialGradedAlgebra.leftActionEquivHom`: left differential graded actions of `A` on `M`
  correspond to homomorphisms `A ⟶ End(M)`, canonically: the homomorphism attached to an action
  sends a homogeneous element to its action as a cochain.

## Implementation notes

The algebra is obtained by specialising the representable differential graded module functor of
Tag 09LE to the differential graded category `CochainComplex.moduleCatDGCategory R` of cochain
complexes of `R`-modules and to the object `M`; its homogeneous pieces are then the Hom modules of
that category, which are by construction Mathlib's cochains. The correspondence with algebra
homomorphisms is the general one of
`StacksFrontier.Algebra.DifferentialGraded.Endomorphism.AlgebraHom`, instantiated here.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [CommRing R]

namespace CochainComplex

/-- The endomorphism differential graded algebra of a cochain complex of `R`-modules, with its
canonical identification of homogeneous pieces with cochains. -/
@[stacks 0FQ3 "endomorphism algebra"]
noncomputable def endomorphismDGA (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    EndomorphismDGA M := by
  let X := moduleCatDGCategory R
  let h := DGCategory.homRepresentation X M
  refine ⟨h.algebra, h.algebraHom, ?_, ?_, ?_⟩
  · obtain ⟨e, he, hunit⟩ := h.algebra_one
    have he' : (⟨1, SetLike.one_mem_graded h.algebra.grading⟩ : h.algebra.grading 0) = e :=
      Subtype.ext he.symm
    exact (congrArg (h.algebraHom 0) he').trans hunit
  · intro n m a b
    obtain ⟨c, hc, hcomp⟩ := h.algebra_mul n m (n + m) rfl a b
    have hc' : (⟨(a : h.algebra.A) * (b : h.algebra.A),
        SetLike.mul_mem_graded a.property b.property⟩ : h.algebra.grading (n + m)) = c :=
      Subtype.ext hc.symm
    rw [hc']
    change h.algebraHom (n + m) c =
      X.comp (show n + m = n + m from rfl) (h.algebraHom n a) (h.algebraHom m b)
    exact hcomp
  · intro n a
    change h.algebraHom (n + 1) ⟨h.algebra.d a, h.algebra.d_mem n a a.property⟩ =
      δ n (n + 1) (h.algebraHom n a)
    exact h.algebra_d n a

end CochainComplex

namespace DifferentialGradedAlgebra

/-- Left differential graded actions of `A` on a cochain complex `M` of `R`-modules correspond
canonically to homomorphisms of differential graded algebras from `A` into the endomorphism
differential graded algebra of `M`. The specification identifies the image of each homogeneous
element with its action as a cochain. -/
@[stacks 0FQ3 "left module structures and algebra homomorphisms"]
noncomputable def leftActionEquivHom (A : DifferentialGradedAlgebra R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    { e : A.LeftAction M ≃ A.Hom (endomorphismDGA M).algebra //
      ∀ (L : A.LeftAction M) (n : ℤ) (a : A.grading n),
        (endomorphismDGA M).cochainEquiv n
          ⟨(e L).toAlgebraHom a, (e L).map_grading n a a.property⟩ = L.action n a } := by
  refine ⟨{
    toFun := fun L => EndomorphismDGA.ofLeftAction A (endomorphismDGA M) L
    invFun := fun φ => EndomorphismDGA.toLeftAction A (endomorphismDGA M) φ
    left_inv := fun L => LeftAction.ext_action fun n a =>
      EndomorphismDGA.ofLeftAction_cochainEquiv A (endomorphismDGA M) L n a
    right_inv := fun φ =>
      EndomorphismDGA.hom_ext A
        (EndomorphismDGA.toAlgHom_toLeftAction A (endomorphismDGA M) φ) }, ?_⟩
  intro L n a
  exact EndomorphismDGA.ofLeftAction_cochainEquiv A (endomorphismDGA M) L n a

end DifferentialGradedAlgebra
