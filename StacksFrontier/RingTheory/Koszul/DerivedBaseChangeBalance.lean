module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIso
public import StacksFrontier.RingTheory.Koszul.BaseChangeBalance

/-!
# One derived tensor product over two algebras

Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras, let
`K` be the Koszul algebra of a functional `φ : Rʳ → R` and let `N` be a differential graded
`(A, B)`-bimodule. The two derived tensor products

* `(A ⊗_R K) ⊗^𝐋_A N`, over `A`, of the right differential graded `A`-module `A ⊗_R K`, and
* `K ⊗^𝐋_R N`, over `R` placed in degree zero, of `K` read as a right differential graded module
  over `R`,

are isomorphic in `D(B, d)`. Both modules are orthogonal on the left to the acyclic modules —
`Koszul.leftOrthogonal_acyclic_tensorModule` and `Koszul.leftOrthogonal_acyclic_baseModule` — so
each derived tensor product is computed by the plain one, and the two plain tensor products agree
by `DifferentialGraded.tensorObjIsoOfBaseChange`.

At `A = K_n` and `K = K_t`, the Koszul algebras on `f₁ⁿ, …, f_rⁿ` and on `f₁ᵗ, …, f_rᵗ`, this is
the levelwise step of Tag 0GZJ: the term `M_n ⊗^𝐋_{K_n} (K_n ⊗_R K_t)` of the base-changed tower
is the term `M_n ⊗^𝐋_R K_t` of the tower over the base ring.

## Main results

* `Koszul.derivedTensorObjIso_tensorModule_baseModule`: the isomorphism
  `(A ⊗_R K) ⊗^𝐋_A N ≅ K ⊗^𝐋_R N` in `D(B, d)`.
* `Koszul.derivedTensorObjIso_powAlgebra`: the same at the Koszul algebras of the `n`-th and
  `t`-th powers of a finite sequence, which is the levelwise step of Tag 0GZJ.

## Implementation notes

*Which variance is used.* `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso` puts its
orthogonality hypotheses on the two *modules* and leaves the two bimodules arbitrary. That is the
variance available here: the modules are the Koszul objects, whose triangular cell decompositions
give the orthogonality, and the bimodule is the one that is carried along unchanged — in Tag 0GZJ
it is the term `M_n` of the system being quantified over, about which nothing is known.

*No naturality is claimed.* The isomorphism below is an isomorphism of objects of `D(B, d)` at
each fixed `n`. It is not asserted to be compatible with the transition maps of an inverse system
in `n`, and `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso` provides no such
compatibility; identifying two *towers* would need that, and it is not available here.

## References

* [Stacks Project, Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) is the comparison of the
  derived with the plain tensor product, [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) the
  derived tensor product and [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) the
  orthogonality through which the comparison is inverted.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is where the isomorphism
  is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule

variable {R : Type u} [CommRing R] {r : ℕ} (A B : DifferentialGradedAlgebra.{u, u} R)
  (φ : Module.Dual R (Fin r → R))

/-- **The two derived tensor products agree.** For a differential graded `(A, B)`-bimodule `N`,
the derived tensor product over `A` of `A ⊗_R K` with `N` is isomorphic in `D(B, d)` to the
derived tensor product over `R` placed in degree zero of `K` with `N`.

Both modules are orthogonal on the left to the acyclic modules, so both derived tensor products
are computed by the plain ones, and the plain ones agree by
`DifferentialGraded.tensorObjIsoOfBaseChange`. -/
def derivedTensorObjIso_tensorModule_baseModule (N : Bimodule A B) :
    (Bimodule.derivedTensorFunctor N).obj
        ((quasiIsomorphisms' A).Q.obj ((toHomotopyCategory A).obj (tensorModule A φ))) ≅
      (Bimodule.derivedTensorFunctor (absBaseBimodule A B N)).obj
        ((quasiIsomorphisms' (degreeZero R R)).Q.obj
          ((toHomotopyCategory (degreeZero R R)).obj (baseModule φ))) :=
  Bimodule.derivedTensorObjIsoOfTensorIso N (absBaseBimodule A B N) (tensorModule A φ)
    (baseModule φ) (leftOrthogonal_acyclic_tensorModule A φ)
    (leftOrthogonal_acyclic_baseModule φ) (tensorObjIso_tensorModule_baseModule A B φ N)

/-- **The levelwise step of Tag 0GZJ.** For a differential graded `(K_n, B)`-bimodule `M`, the
derived tensor product `(K_n ⊗_R K_t) ⊗^𝐋_{K_n} M` over the Koszul algebra of the `n`-th powers
is isomorphic in `D(B, d)` to the derived tensor product `K_t ⊗^𝐋_R M` over `R` placed in degree
zero. This identifies the terms of the two towers whose derived limits Tag 0GZJ compares. -/
def derivedTensorObjIso_powAlgebra (f : Fin r → R) (n t : ℕ)
    (M : Bimodule (powAlgebra f n) B) :
    (Bimodule.derivedTensorFunctor M).obj
        ((quasiIsomorphisms' (powAlgebra f n)).Q.obj
          ((toHomotopyCategory (powAlgebra f n)).obj
            (tensorModule (powAlgebra f n) (seqDual fun i => f i ^ t)))) ≅
      (Bimodule.derivedTensorFunctor (absBaseBimodule (powAlgebra f n) B M)).obj
        ((quasiIsomorphisms' (degreeZero R R)).Q.obj
          ((toHomotopyCategory (degreeZero R R)).obj
            (baseModule (seqDual fun i => f i ^ t)))) :=
  derivedTensorObjIso_tensorModule_baseModule (powAlgebra f n) B
    (seqDual fun i => f i ^ t) M

end Koszul

end
