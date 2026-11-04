module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.CupProductOnCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeMonoidalIdentities
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalPairingLaws

/-!
# The cup product on de Rham cohomology is associative and graded commutative

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex of `φ`. The cup product

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`

of `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup` is the cup product of Cohomology,
Section 0FKU composed with the wedge product `∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of Tag 0FM2. Tag 0FM3:
it is associative and graded commutative.

The proof is the source's: Cohomology, Lemmas 0FP4 and 0FP5 — here
`AlgebraicGeometry.SheafOfModules.canonicalPairingModule_assoc` and
`AlgebraicGeometry.SheafOfModules.canonicalPairingModule_comm`, the associativity and graded
commutativity of the cup product along any multiplications satisfying the corresponding
identities — together with the fact that `∧` is associative and graded commutative, in the form
of the two identities `AlgebraicGeometry.SheafOfModules.wedgeProductInt_assoc` and
`AlgebraicGeometry.SheafOfModules.wedgeProductInt_braiding` of the extended wedge product in the
symmetric monoidal category of complexes of Tag 0FPQ. Nothing is assumed: the cup product is
constructed, with no parameter, and both inputs are proved.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_assoc`: **the cup product on `H^*_{dR}`
  is associative**, `(ξ ∪ η) ∪ ζ = ξ ∪ (η ∪ ζ)`.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_comm`: **the cup product on `H^*_{dR}` is
  graded commutative**, `ξ ∪ η = (-1)^{ij} η ∪ ξ` for `ξ` of degree `i` and `η` of degree `j`.

## Implementation notes

The two sides of either law live in cohomology modules of degrees, `(i + j) + k` and
`i + (j + k)`, or `i + j` and `j + i`, that are equal but not syntactically equal; as in
`AlgebraicGeometry.SheafOfModules.deRhamCupProduct_assoc` the left-hand side, respectively the
transposed product, is transported along the equality of degrees by
`AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology`.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyCast)
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The transport of a de Rham cohomology class along an equality of degrees is the
identification of cohomology modules in equal degrees. -/
theorem reindexDeRhamCohomology_eq_cohomologyCast {m n : ℤ} (h : m = n)
    (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h x =
      (cohomologyCast (moduleDerived (deRhamComplex B D)) h).hom
        (deRhamCohomologyToModule B D m x) := by
  subst h
  rfl

/-- **Stacks Project, Tag 0FM3.** The cup product on `H^*_{dR}(X/S)` is **associative**:
`(ξ ∪ η) ∪ ζ = ξ ∪ (η ∪ ζ)`, the left-hand side transported from degree `(i + j) + k` to degree
`i + (j + k)`. This is Cohomology, Lemma 0FP4 together with the associativity of the wedge
product. -/
@[stacks 0FM3 "the cup product on H^*_dR(X/S), the cup product of Cohomology Section 0FKU \
composed with the wedge product of 0FM2, is associative; no parameter, no hypothesis"]
theorem deRhamCohomologyCup_assoc (i j k : ℤ) (ξ : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) (ζ : deRhamCohomology B D k) :
    reindexDeRhamCohomology B D (add_assoc i j k)
        (deRhamCohomologyCup B D (i + j) k (deRhamCohomologyCup B D i j ξ η) ζ) =
      deRhamCohomologyCup B D i (j + k) ξ (deRhamCohomologyCup B D j k η ζ) :=
  (reindexDeRhamCohomology_eq_cohomologyCast B D (add_assoc i j k) _).trans
    (canonicalPairingModule_assoc (wedgeProduct B D) (wedgeProduct B D) (wedgeProduct B D)
      (wedgeProduct B D) (wedgeProductInt_assoc B D) i j k ξ η ζ)

/-- **Stacks Project, Tag 0FM3.** The cup product on `H^*_{dR}(X/S)` is **graded commutative**:
`ξ ∪ η = (-1)^{ij} η ∪ ξ` for `ξ` of degree `i` and `η` of degree `j`, the right-hand side
transported from degree `j + i` to degree `i + j`. This is Cohomology, Lemma 0FP5 together with
the graded commutativity of the wedge product. -/
@[stacks 0FM3 "the cup product on H^*_dR(X/S), the cup product of Cohomology Section 0FKU \
composed with the wedge product of 0FM2, is graded commutative with sign (-1)^(ij); no \
parameter, no hypothesis"]
theorem deRhamCohomologyCup_comm (i j : ℤ) (ξ : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) :
    deRhamCohomologyCup B D i j ξ η =
      ((i * j).negOnePow : ℤ) • reindexDeRhamCohomology B D (add_comm j i)
        (deRhamCohomologyCup B D j i η ξ) :=
  (canonicalPairingModule_comm (wedgeProduct B D) (wedgeProduct B D)
      (wedgeProductInt_braiding B D) i j ξ η).trans
    (congrArg (fun t => ((i * j).negOnePow : ℤ) • t)
      (reindexDeRhamCohomology_eq_cohomologyCast B D (add_comm j i) _).symm)

end AlgebraicGeometry.SheafOfModules

end
