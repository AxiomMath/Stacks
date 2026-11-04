module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic

/-!
# The cup product on Hodge cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^p` be the exterior powers of the sheaf of relative differentials. The **Hodge cohomology** of
`X` over the base is the bigraded family `H^q(X, Ω^p)`, assembled in total degree `n` into

`H^n_{Hodge}(X/S) = ⨁_{p + q = n} H^q(X, Ω^p_{X/S})`.

The wedge product `Ω^p ⊗_A Ω^{p'} ⟶ Ω^{p + p'}` of Tag 0FM2 combined with the cup product of
Cohomology, Section 0FKU gives a pairing

`∪ : H^i_{Hodge} × H^j_{Hodge} ⟶ H^{i + j}_{Hodge}`,

and Tag 0FM5 says that it is associative and graded commutative. Its proof is the proof of
Tag 0FM3: Cohomology, Lemmas 0FP4 and 0FP5 together with the fact that `∧` is associative and
graded commutative. Both lemmas are proved for the relative cup product of Tag 0B68, with no
hypothesis — `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_assoc` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductAssociativity.lean`
and `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_braiding` in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/RelativeCupProductCommutativity.lean`
— so what is carried as a parameter below is Section 0FKU's pairing on `RΓ`, not those lemmas.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.hodgeCohomologyComponent`: the group `H^q(X, Ω^p)`, as a
  module over the global sections of the base ring sheaf.
* `AlgebraicGeometry.SheafOfModules.hodgeCohomology`: **Hodge cohomology in total degree `n`**,
  the direct sum of the `H^q(X, Ω^p)` with `p + q = n`.
* `AlgebraicGeometry.SheafOfModules.FormsMultiplication` and
  `AlgebraicGeometry.SheafOfModules.multValue`: a multiplication `Ω^p ⊗_A Ω^{p'} ⟶ Ω^r` of
  differential forms and its value on a local pure tensor.
* `AlgebraicGeometry.SheafOfModules.IsAssociativeTriple` and
  `AlgebraicGeometry.SheafOfModules.IsScaledTranspose`: the two compatibilities of
  multiplications of forms that the pairing below is conditional on. They are what the
  Hodge-cohomology shadow of Cohomology, Lemmas 0FP4 and 0FP5 needs as input here; Lemmas 0FP4
  and 0FP5 themselves carry no hypothesis of any kind.
* `AlgebraicGeometry.SheafOfModules.HodgeCohomologyCupProduct`: **the parameter**, the cup product
  of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)` together with its associativity and
  commutativity, the Hodge shadow of Tags 0FP4 and 0FP5, in the form Tag 0FM5 uses: each law
  conditional on the corresponding law of the multiplication of forms.
* `AlgebraicGeometry.SheafOfModules.hodgeCupProduct`: **the cup product on Hodge cohomology**.

## Main results

* `AlgebraicGeometry.SheafOfModules.isAssociativeTriple_exteriorProductComponent` and
  `AlgebraicGeometry.SheafOfModules.isScaledTranspose_exteriorProductComponent`: the two laws of
  the wedge product of Tag 0FM2, `(ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)` and `ω ∧ η = (-1)^{pp'} η ∧ ω`, read
  as compatibilities of the multiplications of forms that induce the pairing.
* `AlgebraicGeometry.SheafOfModules.hodgeCupProduct_assoc`: **the cup product on `H^*_{Hodge}` is
  associative.**
* `AlgebraicGeometry.SheafOfModules.hodgeCupProduct_comm`: **the cup product on `H^*_{Hodge}` is
  graded commutative** for the total degree, `ξ ∪ ζ = (-1)^{(p + q)(p' + q')} ζ ∪ ξ` for `ξ` in
  `H^q(X, Ω^p)` and `ζ` in `H^{q'}(X, Ω^{p'})`.

## Implementation notes

**The grading and the sign.** A class in `H^q(X, Ω^p)` has total degree `p + q`, because `Ω^p` is
the degree-`p` term of the de Rham complex; the grading of the source is this one. Graded
commutativity is therefore the sign `(-1)^{(p + q)(p' + q')}` of the total degrees, which is the
convention of Tag 0FM3 on `H^*_{dR}`. Reading `H^q(X, Ω^p)` as the degree-`p + q` cohomology of
`Ω^p[-p]` puts the Koszul sign `(-1)^{qp'}` into the identification, and
`AlgebraicGeometry.SheafOfModules.hodgeCupProduct` carries that sign: the cup product of
Section 0FKU paired with `∧` alone obeys the bigraded law
`ξ ∪ ζ = (-1)^{pp' + qq'} ζ ∪ ξ`, which is not the law of the total degree, and the two differ by
exactly `(-1)^{qp'}` on each side. The passage between the two is
`AlgebraicGeometry.SheafOfModules.hodgeCupProduct_comm`.

**What is a parameter.** The cup product of Cohomology, Section 0FKU and its Lemmas 0FP4 and 0FP5
are not in the library, so they are carried as the single named parameter
`AlgebraicGeometry.SheafOfModules.HodgeCohomologyCupProduct`, whose two laws are *conditional* on
the corresponding compatibilities of the multiplication of forms that induces the pairing. Those
two compatibilities are then discharged for the wedge product of Tag 0FM2 from
`AlgebraicGeometry.SheafOfModules.formProduct_assoc` and
`AlgebraicGeometry.SheafOfModules.formProduct_comm`, so the statements of Tag 0FM5 below carry no
hypothesis beyond the parameter. Nothing below assumes either conclusion of Tag 0FM5: the
parameter gives Lemma 0FP5 for a transposed pair of multiplications and Lemma 0FP4 for an
associative quadruple, and the passage from those to the laws of the total degree is the sign
computation of each proof.

**Pure bidegrees.** Both laws are stated for classes of pure bidegree, which is where the grading
lives: the pairing is additive in each variable and every class in `H^n_{Hodge}` is a finite sum
of ones of pure bidegree, so the two laws on pure bidegrees are the two laws of the graded
pairing. The totalization of the pairing to the direct sum
`AlgebraicGeometry.SheafOfModules.hodgeCohomology` is not formed here.

**Degrees.** The exterior degrees `p + p'` and `p' + p`, and `(p + p') + p''` and
`p + (p' + p'')`, are equal but not syntactically equal, and likewise for the cohomological
degrees, so the two sides of either law live in groups that agree only propositionally;
`AlgebraicGeometry.SheafOfModules.reindexHodge` transports between them. The two compatibilities
of multiplications are stated with `HEq` for the same reason, as the corresponding conditions of
Tag 0FM3 are.

**Linearity.** Cohomology of the sheaves `Ω^p` of `A`-modules is taken with the derived global
sections of `AlgebraicGeometry.SheafOfModules.derivedSectionsBase`, so the ring acting is the
ring `A(X)` of global sections of the base ring sheaf. The source states the cup product to be
`H^0(X, 𝒪_X)`-bilinear; `A(X)`-bilinearity is what is recorded here, as in Tag 0FM3.

## References

* [Stacks Project, Tag 0FM5](https://stacks.math.columbia.edu/tag/0FM5)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct DirectSum

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Hodge cohomology -/

/-- The Hodge cohomology group `H^q(X, Ω^p_{X/S})`, as a module over the ring of global sections
of the base ring sheaf: the `q`-th cohomology of the derived global sections of `Ω^p`. -/
noncomputable abbrev hodgeCohomologyComponent (p : ℕ) (q : ℤ) :
    ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor _ q).obj
    ((derivedSectionsBase A).obj ((DerivedCategory.singleFunctor _ 0).obj (deRhamTerm B p)))

/-- **Hodge cohomology in total degree `n`**, `H^n_{Hodge}(X/S) = ⨁_{p + q = n} H^q(X, Ω^p)`: the
direct sum over the bidegrees of total degree `n`. -/
noncomputable abbrev hodgeCohomology (n : ℕ) :=
  DirectSum {i : ℕ × ℕ // i.1 + i.2 = n} fun i =>
    (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)

/-- A Hodge cohomology class read in another, equal, exterior degree. -/
noncomputable def reindexHodgeForm {p p' : ℕ} {q : ℤ} (h : p = p')
    (x : hodgeCohomologyComponent B p q) : hodgeCohomologyComponent B p' q :=
  cast (congrArg (fun k : ℕ => ((hodgeCohomologyComponent B k q : Type u))) h) x

/-- A Hodge cohomology class read in another, equal, cohomological degree. -/
noncomputable def reindexHodgeDeg {p : ℕ} {q q' : ℤ} (h : q = q')
    (x : hodgeCohomologyComponent B p q) : hodgeCohomologyComponent B p q' :=
  cast (congrArg (fun k : ℤ => ((hodgeCohomologyComponent B p k : Type u))) h) x

/-- A Hodge cohomology class read in another, equal, bidegree. -/
noncomputable def reindexHodge {p p' : ℕ} {q q' : ℤ} (hp : p = p') (hq : q = q')
    (x : hodgeCohomologyComponent B p q) : hodgeCohomologyComponent B p' q' :=
  reindexHodgeDeg B hq (reindexHodgeForm B hp x)

/-- Reindexing a Hodge cohomology class along `rfl` in the exterior degree is the identity. -/
@[simp]
theorem reindexHodgeForm_rfl {p : ℕ} {q : ℤ} (x : hodgeCohomologyComponent B p q) :
    reindexHodgeForm B (rfl : p = p) x = x := rfl

/-- Reindexing a Hodge cohomology class along `rfl` in the cohomological degree is the identity. -/
@[simp]
theorem reindexHodgeDeg_rfl {p : ℕ} {q : ℤ} (x : hodgeCohomologyComponent B p q) :
    reindexHodgeDeg B (rfl : q = q) x = x := rfl

/-- Reindexing a Hodge cohomology class along `rfl` in both degrees is the identity. -/
@[simp]
theorem reindexHodge_rfl {p : ℕ} {q : ℤ} (x : hodgeCohomologyComponent B p q) :
    reindexHodge B (rfl : p = p) (rfl : q = q) x = x := rfl

/-- Reindexing a Hodge cohomology class commutes with scaling by an integer. -/
theorem reindexHodge_zsmul {p p' : ℕ} {q q' : ℤ} (hp : p = p') (hq : q = q') (k : ℤ)
    (x : hodgeCohomologyComponent B p q) :
    reindexHodge B hp hq (k • x) = k • reindexHodge B hp hq x := by
  subst hp; subst hq; rfl

/-! ### Multiplications of differential forms -/

/-- A multiplication `Ω^p ⊗_A Ω^{p'} ⟶ Ω^r` of relative differential forms. The wedge product
of Tag 0FM2 is the one with `r = p + p'`. -/
abbrev FormsMultiplication (p p' r : ℕ) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj (deRhamTerm B p)).obj
    (deRhamTerm B p') ⟶ deRhamTerm B r

/-- The value of a multiplication of forms on a local pure tensor `ω ⊗ η`. -/
noncomputable def multValue {p p' r : ℕ} (m : FormsMultiplication B p p' r)
    (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B p').val.obj U) : (deRhamTerm B r).val.obj U :=
  m.val.app U (((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
    (PresheafOfModules.tensorObj ((deRhamTerm B p)).val ((deRhamTerm B p')).val)).app U (ω
      ⊗ₜ[A.obj.obj U] η))

/-- On a local pure tensor the wedge multiplication of Tag 0FM2 is the wedge product of forms. -/
theorem multValue_exteriorProductComponent (p p' : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B p').val.obj U) :
    multValue B (exteriorProductComponent B p p') U ω η = formProduct B p p' U ω η :=
  exteriorProductComponent_unit_apply B p p' U ω η

/-- Four multiplications of forms **associate** when the two bracketings of a triple product of
local forms agree. The two sides are forms of equal, but not syntactically equal, exterior
degree. -/
def IsAssociativeTriple {p p' p'' r s s' t : ℕ} (m₁ : FormsMultiplication B p p' r)
    (m₂ : FormsMultiplication B r p'' s) (m₃ : FormsMultiplication B p' p'' t)
    (m₄ : FormsMultiplication B p t s') : Prop :=
  ∀ (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B p').val.obj U) (ζ : (deRhamTerm B p'').val.obj U),
    HEq (multValue B m₂ U (multValue B m₁ U ω η) ζ)
      (multValue B m₄ U ω (multValue B m₃ U η ζ))

/-- A multiplication of forms is `k` times the **transpose** of another when its value on a local
pure tensor is `k` times the other's value on the transposed tensor. -/
def IsScaledTranspose {p p' r r' : ℕ} (m : FormsMultiplication B p p' r)
    (m' : FormsMultiplication B p' p r') (k : ℤ) : Prop :=
  ∀ (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B p').val.obj U),
    HEq (multValue B m U ω η) (k • multValue B m' U η ω)

/-! ### The two laws of the wedge product of forms -/

/-- **The wedge product of Tag 0FM2 is associative**, so that the four wedge multiplications of a
triple product form an associative quadruple. This is the associativity clause of the proof of
Tag 0FM3, `AlgebraicGeometry.SheafOfModules.formProduct_assoc`. -/
theorem isAssociativeTriple_exteriorProductComponent (p p' p'' : ℕ) :
    IsAssociativeTriple B (exteriorProductComponent B p p')
      (exteriorProductComponent B (p + p') p'') (exteriorProductComponent B p' p'')
      (exteriorProductComponent B p (p' + p'')) := by
  intro U ω η ζ
  rw [multValue_exteriorProductComponent, multValue_exteriorProductComponent,
    multValue_exteriorProductComponent, multValue_exteriorProductComponent,
    formProduct_assoc B p p' p'' U ω η ζ]
  exact reindexForm_heq B (Nat.add_assoc p p' p'').symm U _

/-- **The wedge product of Tag 0FM2 is graded commutative**, `ω ∧ η = (-1)^{pp'} η ∧ ω`, so that
the wedge multiplication is the `(-1)^{pp'}` multiple of the transpose of the wedge multiplication
in the opposite order. This is the graded commutativity clause of the proof of Tag 0FM3,
`AlgebraicGeometry.SheafOfModules.formProduct_comm`. -/
theorem isScaledTranspose_exteriorProductComponent (p p' : ℕ) :
    IsScaledTranspose B (exteriorProductComponent B p p') (exteriorProductComponent B p' p)
      (((p * p' : ℕ) : ℤ).negOnePow : ℤ) := by
  intro U ω η
  rw [multValue_exteriorProductComponent, multValue_exteriorProductComponent,
    formProduct_comm B p p' U ω η, ← reindexForm_zsmul]
  refine HEq.trans (reindexForm_heq B (Nat.add_comm p' p) U _) (heq_of_eq ?_)
  exact congrArg (fun k : ℤ => k • formProduct B p' p U η ω)
    (Int.coe_negOnePow_natCast (p * p')).symm

/-! ### The cup product of Cohomology, Section 0FKU on Hodge cohomology -/

/-- **The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)`, with its two
laws.**

A term of this structure provides, for every multiplication `m : Ω^p ⊗_A Ω^{p'} ⟶ Ω^r` of
relative differential forms, the `A(X)`-bilinear pairing

`∪ : H^q(X, Ω^p) × H^{q'}(X, Ω^{p'}) ⟶ H^{q + q'}(X, Ω^r)`

which Cohomology, Section 0FKU produces by composing the cup product in cohomology with `m`,
together with the two statements that Cohomology, Lemmas 0FP4 and 0FP5 turn into: the pairing
associates and transposes **as soon as the multiplications do**. Both laws are therefore
conditional, and the statements of Tag 0FM5 below are deductions from them and from the
associativity and graded commutativity of the wedge product, exactly as in the proof of
Tag 0FM3.

This is the one parameter of this file: Section 0FKU and Lemmas 0FP4, 0FP5 are not in the
library, and a second construction of a cup product in cohomology is deliberately not given
here. -/
structure HodgeCohomologyCupProduct where
  /-- The cup product of Section 0FKU, composed with a multiplication of forms. -/
  cup {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ) :
    hodgeCohomologyComponent B p q → hodgeCohomologyComponent B p' q' →
      hodgeCohomologyComponent B r (q + q')
  /-- The pairing is additive in its first variable. -/
  cup_add_left {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
      (ξ ξ' : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    cup m q q' (ξ + ξ') ζ = cup m q q' ξ ζ + cup m q q' ξ' ζ
  /-- The pairing is additive in its second variable. -/
  cup_add_right {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
      (ξ : hodgeCohomologyComponent B p q) (ζ ζ' : hodgeCohomologyComponent B p' q') :
    cup m q q' ξ (ζ + ζ') = cup m q q' ξ ζ + cup m q q' ξ ζ'
  /-- The pairing is linear over the global sections of the base ring sheaf in its first
  variable. -/
  cup_smul_left {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
      (a : (underlyingRingSheaf A).obj.obj (op ⊤)) (ξ : hodgeCohomologyComponent B p q)
      (ζ : hodgeCohomologyComponent B p' q') :
    cup m q q' (a • ξ) ζ = a • cup m q q' ξ ζ
  /-- The pairing is linear over the global sections of the base ring sheaf in its second
  variable. -/
  cup_smul_right {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ)
      (a : (underlyingRingSheaf A).obj.obj (op ⊤)) (ξ : hodgeCohomologyComponent B p q)
      (ζ : hodgeCohomologyComponent B p' q') :
    cup m q q' ξ (a • ζ) = a • cup m q q' ξ ζ
  /-- Cohomology, Lemma 0FP4: the pairing associates whenever the multiplications do. -/
  cup_assoc {p p' p'' r s s' t : ℕ} (hs : s = s') (m₁ : FormsMultiplication B p p' r)
      (m₂ : FormsMultiplication B r p'' s) (m₃ : FormsMultiplication B p' p'' t)
      (m₄ : FormsMultiplication B p t s') (h : IsAssociativeTriple B m₁ m₂ m₃ m₄)
      (q q' q'' : ℤ) (ξ : hodgeCohomologyComponent B p q)
      (ζ : hodgeCohomologyComponent B p' q') (θ : hodgeCohomologyComponent B p'' q'') :
    reindexHodge B hs (add_assoc q q' q'') (cup m₂ (q + q') q'' (cup m₁ q q' ξ ζ) θ) =
      cup m₄ q (q' + q'') ξ (cup m₃ q' q'' ζ θ)
  /-- Cohomology, Lemma 0FP5: transposing the multiplication transposes the pairing, at the cost
  of the sign `(-1)^{qq'}` of the cohomological degrees. -/
  cup_comm {p p' r r' : ℕ} (hr : r' = r) (m : FormsMultiplication B p p' r)
      (m' : FormsMultiplication B p' p r') (k : ℤ) (h : IsScaledTranspose B m m' k) (q q' : ℤ)
      (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    cup m q q' ξ ζ =
      (k * ((q * q').negOnePow : ℤ)) • reindexHodge B hr (add_comm q' q) (cup m' q' q ζ ξ)

namespace HodgeCohomologyCupProduct

variable (c : HodgeCohomologyCupProduct B)

/-- The pairing is linear over the integers in its first variable. -/
theorem cup_zsmul_left {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ) (k : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    c.cup m q q' (k • ξ) ζ = k • c.cup m q q' ξ ζ :=
  map_zsmul
    (AddMonoidHom.mk' (fun ξ => c.cup m q q' ξ ζ) fun ξ ξ' => c.cup_add_left m q q' ξ ξ' ζ) k ξ

/-- The pairing is linear over the integers in its second variable. -/
theorem cup_zsmul_right {p p' r : ℕ} (m : FormsMultiplication B p p' r) (q q' : ℤ) (k : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    c.cup m q q' ξ (k • ζ) = k • c.cup m q q' ξ ζ :=
  map_zsmul
    (AddMonoidHom.mk' (fun ζ => c.cup m q q' ξ ζ) fun ζ ζ' => c.cup_add_right m q q' ξ ζ ζ') k ζ

end HodgeCohomologyCupProduct

/-! ### The cup product on Hodge cohomology -/

variable (c : HodgeCohomologyCupProduct B)

/-- **The cup product on Hodge cohomology**

`∪ : H^q(X, Ω^p) × H^{q'}(X, Ω^{p'}) ⟶ H^{q + q'}(X, Ω^{p + p'})`,

the cup product of Cohomology, Section 0FKU paired with the wedge product of Tag 0FM2, carrying
the Koszul sign `(-1)^{qp'}` of the reading of `H^q(X, Ω^p)` as the degree-`p + q` cohomology of
`Ω^p[-p]`. -/
noncomputable def hodgeCupProduct (p p' : ℕ) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyComponent B (p + p') (q + q') :=
  (((q * (p' : ℤ)).negOnePow : ℤ)) • c.cup (exteriorProductComponent B p p') q q' ξ ζ

/-- **Stacks Project, Tag 0FM5.** The cup product on `H^*_{Hodge}(X/S)` is **associative**. This
is Cohomology, Lemma 0FP4 together with the associativity of the wedge product. -/
@[stacks 0FM5 "the cup product on Hodge cohomology is associative, on classes of pure bidegree; \
the 0FKU pairing with its 0FP4 law is the carried parameter HodgeCohomologyCupProduct"]
theorem hodgeCupProduct_assoc (p p' p'' : ℕ) (q q' q'' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q')
    (θ : hodgeCohomologyComponent B p'' q'') :
    reindexHodge B (Nat.add_assoc p p' p'') (add_assoc q q' q'')
        (hodgeCupProduct B c (p + p') p'' (q + q') q''
          (hodgeCupProduct B c p p' q q' ξ ζ) θ) =
      hodgeCupProduct B c p (p' + p'') q (q' + q'')
        ξ (hodgeCupProduct B c p' p'' q' q'' ζ θ) := by
  have hexp : (q + q') * (p'' : ℤ) + q * (p' : ℤ) =
      q * ((p' + p'' : ℕ) : ℤ) + q' * (p'' : ℤ) := by push_cast; ring
  have hsign : (((q + q') * (p'' : ℤ)).negOnePow : ℤ) * ((q * (p' : ℤ)).negOnePow : ℤ) =
      ((q * ((p' + p'' : ℕ) : ℤ)).negOnePow : ℤ) * ((q' * (p'' : ℤ)).negOnePow : ℤ) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add, hexp]
  rw [hodgeCupProduct, hodgeCupProduct, hodgeCupProduct, hodgeCupProduct,
    c.cup_zsmul_left B, c.cup_zsmul_right B, smul_smul, smul_smul, reindexHodge_zsmul,
    c.cup_assoc (Nat.add_assoc p p' p'') (exteriorProductComponent B p p')
      (exteriorProductComponent B (p + p') p'') (exteriorProductComponent B p' p'')
      (exteriorProductComponent B p (p' + p''))
      (isAssociativeTriple_exteriorProductComponent B p p' p'') q q' q'' ξ ζ θ,
    hsign]

/-- **Stacks Project, Tag 0FM5.** The cup product on `H^*_{Hodge}(X/S)` is **graded
commutative**: `ξ ∪ ζ = (-1)^{(p + q)(p' + q')} ζ ∪ ξ` for `ξ` in `H^q(X, Ω^p)` and `ζ` in
`H^{q'}(X, Ω^{p'})`, the sign of the total degrees. This is Cohomology, Lemma 0FP5 together with
the graded commutativity of the wedge product. -/
@[stacks 0FM5 "the cup product on Hodge cohomology is graded commutative for the total degree \
p + q, sign (-1)^((p+q)(p'+q')), on classes of pure bidegree; the 0FKU pairing with its 0FP5 law \
is the carried parameter HodgeCohomologyCupProduct"]
theorem hodgeCupProduct_comm (p p' : ℕ) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCupProduct B c p p' q q' ξ ζ =
      (((((p : ℤ) + q) * ((p' : ℤ) + q')).negOnePow : ℤ)) •
        reindexHodge B (Nat.add_comm p' p) (add_comm q' q)
          (hodgeCupProduct B c p' p q' q ζ ξ) := by
  have hsign : ((q * (p' : ℤ)).negOnePow : ℤ) *
        ((((p * p' : ℕ) : ℤ).negOnePow : ℤ) * ((q * q').negOnePow : ℤ)) =
      (((((p : ℤ) + q) * ((p' : ℤ) + q')).negOnePow : ℤ)) * ((q' * (p : ℤ)).negOnePow : ℤ) := by
    have key : ∀ a k : ℤ, (a + 2 * k).negOnePow = a.negOnePow := fun a k => by
      rw [Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    have hsplit : ((p : ℤ) + q) * ((p' : ℤ) + q') + q' * (p : ℤ) =
        (q * (p' : ℤ) + (((p * p' : ℕ) : ℤ) + q * q')) + 2 * ((p : ℤ) * q') := by
      push_cast
      ring
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    rw [hsplit, key]
  rw [hodgeCupProduct, hodgeCupProduct,
    c.cup_comm (Nat.add_comm p' p) (exteriorProductComponent B p p')
      (exteriorProductComponent B p' p) (((p * p' : ℕ) : ℤ).negOnePow : ℤ)
      (isScaledTranspose_exteriorProductComponent B p p') q q' ξ ζ,
    reindexHodge_zsmul, smul_smul, smul_smul, hsign]

end AlgebraicGeometry.SheafOfModules

end
