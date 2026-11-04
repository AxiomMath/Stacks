module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic

/-!
# The cup product on de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. Combining the wedge product

`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`

of Tag 0FM2 with the cup product of Cohomology, Section 0FKU gives a bilinear cup product

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`

on relative de Rham cohomology, and Tag 0FM3 says that it is associative and graded commutative.
Its proof is the conjunction of two inputs: Cohomology, Lemmas 0FP4 and 0FP5, which say that the
cup product in cohomology is associative and commutative for the symmetric monoidal structure, and
the fact that `∧` is associative and graded commutative, which is
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity`.

The pairing on hypercohomology is the content of Cohomology, Section 0FKU, which the library does
not yet have: the global cup product is still gated on `OnePointComparison` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/GlobalCupProduct.lean`. Lemmas 0FP4
and 0FP5 are *not* missing and carry no hypothesis of their own:
`Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_assoc` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductAssociativity.lean`
and `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_braiding` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`
state them for the relative cup product of Tag 0B68, for an arbitrary morphism of ringed spaces
and arbitrary objects of `D(𝒪_X)`. What is missing is their transport along Section 0FKU to a
pairing on `RΓ`. The pairing is therefore carried here as one explicit named parameter,
`AlgebraicGeometry.SheafOfModules.HypercohomologyCupProduct`, whose two laws are *conditional* on
the corresponding laws of the multiplication inducing the product: the de Rham statements below are
obtained from it by feeding in the wedge product together with the proofs that the wedge product is
associative and graded commutative, and are not assumed.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.IsAssociativeOnSummands` and
  `AlgebraicGeometry.SheafOfModules.IsGradedCommutativeOnSummands`: associativity and graded
  commutativity of a multiplication `Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` on the summands of the total complex.
* `AlgebraicGeometry.SheafOfModules.HypercohomologyCupProduct`: **the parameter**, the cup product
  of Cohomology, Section 0FKU on de Rham hypercohomology together with its associativity and
  commutativity, the hypercohomology shadow of Tags 0FP4 and 0FP5, in the form Tag 0FM3 uses:
  each law conditional on the corresponding law of the multiplication inducing the product. The
  condition is on the multiplication, not on Tags 0FP4 and 0FP5, which carry no
  hypothesis.
* `AlgebraicGeometry.SheafOfModules.deRhamCupProduct`: **the cup product on de Rham cohomology**,
  the pairing applied to the wedge product of Tag 0FM2.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamCupProduct_assoc`: **the cup product on `H^*_{dR}` is
  associative.**
* `AlgebraicGeometry.SheafOfModules.deRhamCupProduct_comm`: **the cup product on `H^*_{dR}` is
  graded commutative**, `ξ ∪ ζ = (-1)^{ij} ζ ∪ ξ` for `ξ` of degree `i` and `ζ` of degree `j`.

## Implementation notes

The sign convention for graded commutativity is the standard one, `ξ ∪ ζ = (-1)^{ij} ζ ∪ ξ`; it is
the cohomological shadow of the convention `ω ∧ η = (-1)^{pq} η ∧ ω` used for forms in
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity`.

De Rham cohomology is the one of
`AlgebraicGeometry.SheafOfModules.deRhamCohomology`: the hypercohomology of the relative de Rham
complex, a module over the ring `A(X)` of global sections of the base ring sheaf. The source states
the cup product to be `H^0(S, 𝒪_S)`-bilinear; over a ringed space the ring acting on
hypercohomology is `A(X)`, and that is the bilinearity recorded here.

Both laws are stated with an explicit transport `reindexDeRhamCohomology` along the equality of
degrees, because `(i + j) + k` and `i + (j + k)`, and `i + j` and `j + i`, are equal but not
syntactically equal, so the two sides of either law live in cohomology modules of degrees that
agree only propositionally.

The two conditions `IsAssociativeOnSummands` and `IsGradedCommutativeOnSummands` are stated on the
summands of the total complex rather than through an associator and a braiding of total complexes,
because that is the form in which the wedge product satisfies them unconditionally; a braiding on
`Tot(Ω^• ⊗_A Ω^•)` is not available in the library.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The two laws of a multiplication on the de Rham complex -/

/-- A multiplication `Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` on the relative de Rham complex is **associative on
summands** when the two bracketings of a triple product of local differential forms agree. The
wedge product of Tag 0FM2 has this property
(`AlgebraicGeometry.SheafOfModules.isAssociativeOnSummands_wedgeProduct`). -/
def IsAssociativeOnSummands (m : tensorSquare B D ⟶ deRhamComplex B D) : Prop :=
  ∀ (p q r : ℕ) (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B q).val.obj U) (ζ : (deRhamTerm B r).val.obj U),
    HEq (summandValue B D m (p + q) r U (summandValue B D m p q U ω η) ζ)
      (summandValue B D m p (q + r) U ω (summandValue B D m q r U η ζ))

/-- A multiplication `Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` on the relative de Rham complex is **graded
commutative on summands** when its value on the local pure tensor of a `p`-form and a `q`-form is
`(-1)^{pq}` times its value on the transposed pure tensor. The wedge product of Tag 0FM2 has this
property (`AlgebraicGeometry.SheafOfModules.isGradedCommutativeOnSummands_wedgeProduct`). -/
def IsGradedCommutativeOnSummands (m : tensorSquare B D ⟶ deRhamComplex B D) : Prop :=
  ∀ (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B q).val.obj U),
    HEq (summandValue B D m p q U ω η)
      ((-1 : ℤ) ^ (p * q) • summandValue B D m q p U η ω)

/-- **The wedge product of Tag 0FM2 is associative on summands.** -/
theorem isAssociativeOnSummands_wedgeProduct :
    IsAssociativeOnSummands B D (wedgeProduct B D) :=
  wedgeProduct_summand_assoc B D

/-- **The wedge product of Tag 0FM2 is graded commutative on summands.** -/
theorem isGradedCommutativeOnSummands_wedgeProduct :
    IsGradedCommutativeOnSummands B D (wedgeProduct B D) :=
  wedgeProduct_summand_comm B D

/-! ### The cup product on de Rham cohomology -/

/-- A de Rham cohomology class read in another, equal, degree. -/
def reindexDeRhamCohomology {m n : ℤ} (h : m = n) (x : deRhamCohomology B D m) :
    deRhamCohomology B D n :=
  cast (congrArg (fun k : ℤ => ((deRhamCohomology B D k : Type u))) h) x

/-- Reindexing a de Rham cohomology class along `rfl : m = m` is the identity. -/
@[simp]
theorem reindexDeRhamCohomology_rfl {m : ℤ} (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D (rfl : m = m) x = x := rfl

/-- **The cup product of Cohomology, Section 0FKU on de Rham hypercohomology, with its two laws.**

A term of this structure provides, for every multiplication `m : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` on the
relative de Rham complex, the `A(X)`-bilinear pairing

`∪ : H^i_{dR} × H^j_{dR} ⟶ H^{i + j}_{dR}`

which Cohomology, Section 0FKU produces by composing the cup product in cohomology with `m`,
together with the two statements that Cohomology, Lemmas 0FP4 and 0FP5 turn into: the pairing is
associative and graded commutative **as soon as `m` is**. Both laws are therefore conditional, and
the de Rham statements `AlgebraicGeometry.SheafOfModules.deRhamCupProduct_assoc` and
`AlgebraicGeometry.SheafOfModules.deRhamCupProduct_comm` are deductions from them and from the
associativity and graded commutativity of the wedge product, exactly as in the proof of Tag 0FM3.

This is the one parameter of this file: Section 0FKU and Lemmas 0FP4, 0FP5 are not in the library,
and a second construction of a cup product on hypercohomology is deliberately not given
here. -/
structure HypercohomologyCupProduct where
  /-- The cup product of Section 0FKU, composed with a multiplication on the de Rham complex. -/
  cup (m : tensorSquare B D ⟶ deRhamComplex B D) (i j : ℤ) :
    deRhamCohomology B D i → deRhamCohomology B D j → deRhamCohomology B D (i + j)
  /-- The pairing is additive in its first variable. -/
  cup_add_left (m : tensorSquare B D ⟶ deRhamComplex B D) (i j : ℤ)
      (ξ ξ' : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    cup m i j (ξ + ξ') η = cup m i j ξ η + cup m i j ξ' η
  /-- The pairing is additive in its second variable. -/
  cup_add_right (m : tensorSquare B D ⟶ deRhamComplex B D) (i j : ℤ)
      (ξ : deRhamCohomology B D i) (η η' : deRhamCohomology B D j) :
    cup m i j ξ (η + η') = cup m i j ξ η + cup m i j ξ η'
  /-- The pairing is linear over the global sections of the base ring sheaf in its first
  variable. -/
  cup_smul_left (m : tensorSquare B D ⟶ deRhamComplex B D) (i j : ℤ)
      (a : (underlyingRingSheaf A).obj.obj (op ⊤)) (ξ : deRhamCohomology B D i)
      (η : deRhamCohomology B D j) :
    cup m i j (a • ξ) η = a • cup m i j ξ η
  /-- The pairing is linear over the global sections of the base ring sheaf in its second
  variable. -/
  cup_smul_right (m : tensorSquare B D ⟶ deRhamComplex B D) (i j : ℤ)
      (a : (underlyingRingSheaf A).obj.obj (op ⊤)) (ξ : deRhamCohomology B D i)
      (η : deRhamCohomology B D j) :
    cup m i j ξ (a • η) = a • cup m i j ξ η
  /-- Cohomology, Lemma 0FP4: the pairing is associative whenever the multiplication is. -/
  cup_assoc (m : tensorSquare B D ⟶ deRhamComplex B D) (hm : IsAssociativeOnSummands B D m)
      (i j k : ℤ) (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j)
      (ζ : deRhamCohomology B D k) :
    reindexDeRhamCohomology B D (add_assoc i j k) (cup m (i + j) k (cup m i j ξ η) ζ) =
      cup m i (j + k) ξ (cup m j k η ζ)
  /-- Cohomology, Lemma 0FP5: the pairing is graded commutative whenever the multiplication is. -/
  cup_comm (m : tensorSquare B D ⟶ deRhamComplex B D) (hm : IsGradedCommutativeOnSummands B D m)
      (i j : ℤ) (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    cup m i j ξ η =
      ((i * j).negOnePow : ℤ) • reindexDeRhamCohomology B D (add_comm j i) (cup m j i η ξ)

variable (c : HypercohomologyCupProduct B D)

/-- **Stacks Project, Tag 0FM3.** The cup product

`∪ : H^i_{dR}(X/S) × H^j_{dR}(X/S) ⟶ H^{i + j}_{dR}(X/S)`

on relative de Rham cohomology: the cup product of Cohomology, Section 0FKU paired with the wedge
product of Tag 0FM2. It is bilinear over the ring of global sections of the base ring sheaf. -/
@[stacks 0FM3 "the cup product on de Rham cohomology, from the wedge product of 0FM2"]
noncomputable def deRhamCupProduct (i j : ℤ) :
    deRhamCohomology B D i → deRhamCohomology B D j → deRhamCohomology B D (i + j) :=
  c.cup (wedgeProduct B D) i j

/-- The cup product on de Rham cohomology is additive in its first variable. -/
theorem deRhamCupProduct_add_left (i j : ℤ) (ξ ξ' : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) :
    deRhamCupProduct B D c i j (ξ + ξ') η =
      deRhamCupProduct B D c i j ξ η + deRhamCupProduct B D c i j ξ' η :=
  c.cup_add_left (wedgeProduct B D) i j ξ ξ' η

/-- The cup product on de Rham cohomology is additive in its second variable. -/
theorem deRhamCupProduct_add_right (i j : ℤ) (ξ : deRhamCohomology B D i)
    (η η' : deRhamCohomology B D j) :
    deRhamCupProduct B D c i j ξ (η + η') =
      deRhamCupProduct B D c i j ξ η + deRhamCupProduct B D c i j ξ η' :=
  c.cup_add_right (wedgeProduct B D) i j ξ η η'

/-- The cup product on de Rham cohomology is linear over the global sections of the base ring
sheaf in its first variable. -/
theorem deRhamCupProduct_smul_left (i j : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCupProduct B D c i j (a • ξ) η = a • deRhamCupProduct B D c i j ξ η :=
  c.cup_smul_left (wedgeProduct B D) i j a ξ η

/-- The cup product on de Rham cohomology is linear over the global sections of the base ring
sheaf in its second variable. -/
theorem deRhamCupProduct_smul_right (i j : ℤ) (a : (underlyingRingSheaf A).obj.obj (op ⊤))
    (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCupProduct B D c i j ξ (a • η) = a • deRhamCupProduct B D c i j ξ η :=
  c.cup_smul_right (wedgeProduct B D) i j a ξ η

/-- **Stacks Project, Tag 0FM3.** The cup product on `H^*_{dR}(X/S)` is **associative**. This is
Cohomology, Lemma 0FP4 together with the associativity of the wedge product. -/
@[stacks 0FM3 "the cup product on de Rham cohomology is associative"]
theorem deRhamCupProduct_assoc (i j k : ℤ) (ξ : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) (ζ : deRhamCohomology B D k) :
    reindexDeRhamCohomology B D (add_assoc i j k)
        (deRhamCupProduct B D c (i + j) k (deRhamCupProduct B D c i j ξ η) ζ) =
      deRhamCupProduct B D c i (j + k) ξ (deRhamCupProduct B D c j k η ζ) :=
  c.cup_assoc (wedgeProduct B D) (isAssociativeOnSummands_wedgeProduct B D) i j k ξ η ζ

/-- **Stacks Project, Tag 0FM3.** The cup product on `H^*_{dR}(X/S)` is **graded commutative**:
`ξ ∪ η = (-1)^{ij} η ∪ ξ` for `ξ` of degree `i` and `η` of degree `j`. This is Cohomology, Lemma
0FP5 together with the graded commutativity of the wedge product. -/
@[stacks 0FM3 "the cup product on de Rham cohomology is graded commutative, sign (-1)^(ij)"]
theorem deRhamCupProduct_comm (i j : ℤ) (ξ : deRhamCohomology B D i)
    (η : deRhamCohomology B D j) :
    deRhamCupProduct B D c i j ξ η =
      ((i * j).negOnePow : ℤ) • reindexDeRhamCohomology B D (add_comm j i)
        (deRhamCupProduct B D c j i η ξ) :=
  c.cup_comm (wedgeProduct B D) (isGradedCommutativeOnSummands_wedgeProduct B D) i j ξ η

end AlgebraicGeometry.SheafOfModules

end
