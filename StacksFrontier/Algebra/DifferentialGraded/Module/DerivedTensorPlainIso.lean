module

public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated

/-!
# Comparing two derived tensor products through their plain ones

Let `(A, d)`, `(A', d)` and `(B, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule and `N'` a differential graded
`(A', B)`-bimodule. If a differential graded `A`-module `X` is orthogonal on the left to the
acyclic modules then the comparison `X ⊗_A^𝐋 N ⟶ X ⊗_A N` of Tag 0BZ2 is invertible, so the
derived tensor product is computed by the plain one. Consequently two such derived tensor
products, over possibly different algebras, are isomorphic as soon as their plain tensor products
are.

This is the shape in which an identity `M ⊗_R^𝐋 K = M ⊗_{K_n}^𝐋 (K_n ⊗_R K) ` is obtained: one
exhibits both modules as orthogonal on the left to the acyclic modules and identifies the two
plain tensor products. Which bimodule is which is immaterial here, and in particular the two
algebras need not be related.

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain`: for `X` orthogonal on the left to the
  acyclic modules, the isomorphism `X ⊗_A^𝐋 N ≅ X ⊗_A N` in `D(B, d)`.
* `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso`: two derived tensor products with
  orthogonal modules are isomorphic once their plain tensor products are.

## Implementation notes

The invertibility of the comparison at an orthogonal object is
`DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal`, which puts
its hypothesis on the object and leaves the bimodule arbitrary; that is the variance needed here,
where the bimodule is the one being carried along and the module is the one being changed. The
target of the comparison is the plain tensor functor followed by localization, whose value at the
class of `X` is identified with the class of `X ⊗_A N` by the compatibility of the plain tensor
functor with the passage to homotopy classes, `Tag 09LM`
(`DifferentialGraded.Bimodule.tensorCompFunctor_quotient`).

## References

* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) is the comparison from
  the derived to the plain tensor product, [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS)
  the derived tensor product, [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) the plain one
  and its compatibility with homotopy classes, and
  [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) the orthogonality that the hypothesis is
  usually verified through.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A A' B : DifferentialGradedAlgebra.{u, u} R}

/-- **The derived tensor product with `N` at an orthogonal module is the plain one.** For a
differential graded `A`-module `X` whose class in `K(A, d)` is orthogonal on the left to the
acyclic modules, the comparison of Tag 0BZ2 is an isomorphism `X ⊗_A^𝐋 N ≅ X ⊗_A N` in
`D(B, d)`. -/
def derivedTensorObjIsoPlain (N : Bimodule A B) (X : DifferentialGradedModule.{u, u, u} A)
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    (derivedTensorFunctor N).obj
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ≅
      (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (tensorObj N X)) :=
  haveI := isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N
    ((toHomotopyCategory A).obj X) hX
  asIso ((derivedTensorFunctorCounit N).app ((toHomotopyCategory A).obj X)) ≪≫
    ((quasiIsomorphisms' B).Q.mapIso ((tensorCompFunctor_quotient N).app X)).symm

/-- **Two derived tensor products whose plain tensor products agree.** If `X` and `X'` are
orthogonal on the left to the acyclic modules over their respective algebras and the plain tensor
products `X ⊗_A N` and `X' ⊗_{A'} N'` are isomorphic as differential graded `B`-modules, then
`X ⊗_A^𝐋 N` and `X' ⊗_{A'}^𝐋 N'` are isomorphic in `D(B, d)`. -/
def derivedTensorObjIsoOfTensorIso (N : Bimodule A B) (N' : Bimodule A' B)
    (X : DifferentialGradedModule.{u, u, u} A) (X' : DifferentialGradedModule.{u, u, u} A')
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X))
    (hX' : (acyclic' A').leftOrthogonal ((toHomotopyCategory A').obj X'))
    (e : tensorObj N X ≅ tensorObj N' X') :
    (derivedTensorFunctor N).obj
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj X)) ≅
      (derivedTensorFunctor N').obj
        ((quasiIsomorphisms' A').Q.obj ((toHomotopyCategory A').obj X')) :=
  derivedTensorObjIsoPlain N X hX ≪≫
    (quasiIsomorphisms' B).Q.mapIso ((toHomotopyCategory B).mapIso e) ≪≫
    (derivedTensorObjIsoPlain N' X' hX').symm

end DifferentialGraded.Bimodule

end
