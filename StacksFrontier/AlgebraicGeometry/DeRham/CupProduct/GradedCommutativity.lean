module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeProduct

/-!
# Associativity and graded commutativity of the wedge product

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials and
let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`.

The wedge product of relative differential forms is associative and graded commutative,

`(ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)`,    `ω ∧ η = (-1)^{pq} η ∧ ω`   for `ω ∈ Ωᵖ`, `η ∈ Ωᵠ`,

and this file proves both, for arbitrary local sections and then on the summands of the total
complex, for the morphism of complexes `∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of Tag 0FM2. Together with the
cup product of Cohomology, Section 0FKU and its two laws, Tags 0FP4 and 0FP5, this is what Tag
0FM3 reduces the associativity and graded commutativity of the cup product on de Rham cohomology
to: it is the clause "the fact that `∧` is associative and graded commutative" of that proof.

Associativity is the associativity of the graded algebra `⋀(Ω)` and only has to be moved across
the normalization of degrees. Graded commutativity is not a property of a general graded algebra:
it holds here because `⋀(Ω)` is generated in degree one by sections of square zero, so two exact
differentials anticommute, and an exact wedge of degree `p` therefore passes an exact wedge of
degree `q` at the cost of the `pq` transpositions of their factors.

## Main results

* `AlgebraicGeometry.SheafOfModules.formProduct_assoc` and
  `AlgebraicGeometry.SheafOfModules.ofGradedForm_mul_assoc`: **the wedge product is associative**,
  with degrees normalized and in the ring of all local forms.
* `AlgebraicGeometry.SheafOfModules.formProduct_comm` and
  `AlgebraicGeometry.SheafOfModules.ofGradedForm_mul_comm`: **the wedge product is graded
  commutative**, `ω ∧ η = (-1)^{pq} η ∧ ω`, in the same two readings.
* `AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_assoc` and
  `AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_comm`: the same two laws read on the
  summands of the total complex, for the wedge product of Tag 0FM2.

## Implementation notes

The sign convention is the standard one: `ω ∧ η = (-1)^{pq} η ∧ ω` for `ω` of exterior degree `p`
and `η` of exterior degree `q`, so that degree-one forms anticommute and a form of even degree is
central.

The two laws are stated in two readings. The *degree-normalized* reading uses
`AlgebraicGeometry.SheafOfModules.formProduct`, whose target is `Ωᵖ⁺ᵠ` for `p + q` computed in `ℕ`;
the two sides of either law then live in exterior powers whose degrees are equal but not
syntactically so, and `AlgebraicGeometry.SheafOfModules.reindexForm` transports between them. The
*total* reading places everything in the ring `totalForms` of all local forms of
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms`, where no transport is needed
because
the degree is carried by the element.

Graded commutativity is proved first for exact wedges, by induction on the degree of the second
factor using `AlgebraicGeometry.SheafOfModules.mul_exactForm_of_isExactWedge`, and is then extended
to all local sections by `AlgebraicGeometry.SheafOfModules.tensorForms_hom_ext`: both sides are the
values of morphisms out of the tensor product of the underlying presheaves, so agreement on pure
tensors of multiples of exact wedges is agreement everywhere. That is what keeps the locality
argument out of this file.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct DirectSum
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing

/-! ### Transporting a form along an equality of exterior degrees -/

/-- A local differential form read in another, equal, exterior degree. The degree-normalized wedge
product `AlgebraicGeometry.SheafOfModules.formProduct` of a `p`-form and a `q`-form lands in
`Ωᵖ⁺ᵠ`, so the two sides of associativity and of graded commutativity live in exterior powers
whose degrees agree only up to the commutativity and associativity of addition in `ℕ`. -/
def reindexForm {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) : (B.exteriorPower n).val.obj U :=
  cast (congrArg (fun k : ℕ => ((B.exteriorPower k).val.obj U : Type u)) h) x

/-- Reindexing a form along the reflexive equality `m = m` is the identity. -/
@[simp]
theorem reindexForm_rfl {m : ℕ} (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower m).val.obj U) :
    reindexForm B (rfl : m = m) U x = x := rfl

/-- Reindexing a form is additive. -/
theorem reindexForm_add {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x y : (B.exteriorPower m).val.obj U) :
    reindexForm B h U (x + y) = reindexForm B h U x + reindexForm B h U y := by
  subst h
  rfl

/-- Reindexing a form commutes with scaling by a local section of the structure sheaf. -/
theorem reindexForm_smul {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.sheaf.obj.obj U) (x : (B.exteriorPower m).val.obj U) :
    reindexForm B h U (a • x) = a • reindexForm B h U x := by
  subst h
  rfl

/-- Reindexing a form commutes with scaling by an integer. -/
theorem reindexForm_zsmul {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ) (k : ℤ)
    (x : (B.exteriorPower m).val.obj U) :
    reindexForm B h U (k • x) = k • reindexForm B h U x := by
  subst h
  rfl

/-- Reindexing a form commutes with restriction to a smaller open set. -/
theorem reindexForm_map {m n : ℕ} (h : m = n) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (x : (B.exteriorPower m).val.obj U) :
    (B.exteriorPower n).val.map f (reindexForm B h U x) =
      reindexForm B h V ((B.exteriorPower m).val.map f x) := by
  subst h
  rfl

/-- Reindexing a form does not change its image in the ring of all local forms. -/
theorem ofGradedForm_reindexForm {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) :
    ofGradedForm B U ((n : ℕ) : ℤ) (reindexForm B h U x) =
      ofGradedForm B U ((m : ℕ) : ℤ) x := by
  subst h
  rfl

/-- Scaling a form by an integer commutes with scaling it by a local section of the structure
sheaf. -/
theorem zsmul_smul_form_comm (n : ℕ) (U : (Opens X.carrier)ᵒᵖ) (k : ℤ)
    (r : X.sheaf.obj.obj U) (x : (B.exteriorPower n).val.obj U) :
    k • (r • x) = r • (k • x) :=
  smul_comm k r x

/-- A form and its reindexing are heterogeneously equal. -/
theorem reindexForm_heq {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) : HEq (reindexForm B h U x) x := by
  subst h
  rfl

/-! ### Associativity -/

/-- **The wedge product is associative**, in the ring of all local forms. -/
theorem ofGradedForm_mul_assoc (p q r : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (ζ : (B.exteriorPower r).val.obj U) :
    ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η * ofGradedForm B U (r : ℤ) ζ =
      ofGradedForm B U (p : ℤ) ω * (ofGradedForm B U (q : ℤ) η * ofGradedForm B U (r : ℤ) ζ) :=
  mul_assoc _ _ _

/-- **The wedge product is associative**: `(ω ∧ η) ∧ ζ = ω ∧ (η ∧ ζ)` for local sections `ω` of
`Ωᵖ`, `η` of `Ωᵠ` and `ζ` of `Ω^r`, with the exterior degrees normalized. -/
theorem formProduct_assoc (p q r : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (ζ : (B.exteriorPower r).val.obj U) :
    formProduct B (p + q) r U (formProduct B p q U ω η) ζ =
      reindexForm B (Nat.add_assoc p q r).symm U
        (formProduct B p (q + r) U ω (formProduct B q r U η ζ)) := by
  refine DirectSum.of_injective (β := gradedForms B U) ((p + q + r : ℕ) : ℤ) ?_
  have hl : ofGradedForm B U ((p + q + r : ℕ) : ℤ)
        (formProduct B (p + q) r U (formProduct B p q U ω η) ζ) =
      ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η *
        ofGradedForm B U (r : ℤ) ζ := by
    refine Eq.trans
      (ofGradedForm_mul B U ((p + q : ℕ) : ℤ) (r : ℤ) (formProduct B p q U ω η) ζ) ?_
    exact congrArg (fun z : totalForms B U => z * ofGradedForm B U (r : ℤ) ζ)
      (ofGradedForm_mul B U (p : ℤ) (q : ℤ) ω η)
  have hr : ofGradedForm B U ((p + q + r : ℕ) : ℤ)
        (reindexForm B (Nat.add_assoc p q r).symm U
          (formProduct B p (q + r) U ω (formProduct B q r U η ζ))) =
      ofGradedForm B U (p : ℤ) ω *
        (ofGradedForm B U (q : ℤ) η * ofGradedForm B U (r : ℤ) ζ) := by
    refine Eq.trans (ofGradedForm_reindexForm B (Nat.add_assoc p q r).symm U _) ?_
    refine Eq.trans
      (ofGradedForm_mul B U (p : ℤ) ((q + r : ℕ) : ℤ) ω (formProduct B q r U η ζ)) ?_
    exact congrArg (fun z : totalForms B U => ofGradedForm B U (p : ℤ) ω * z)
      (ofGradedForm_mul B U (q : ℤ) (r : ℤ) η ζ)
  exact hl.trans ((mul_assoc _ _ _).trans hr.symm)

/-! ### Graded commutativity -/

/-- **Graded commutativity on exact wedges.** An exact wedge of degree `p` passes an exact wedge of
degree `q` at the cost of the sign `(-1)^{pq}`: each of the `p` exact factors of the first is
transposed past each of the `q` exact factors of the second. -/
private theorem ofGradedForm_mul_comm_of_isExactWedge (p : ℕ) :
    ∀ (q : ℕ) (U : (Opens X.carrier)ᵒᵖ) (ω : (B.exteriorPower p).val.obj U)
      (η : (B.exteriorPower q).val.obj U), IsExactWedge B U p ω → IsExactWedge B U q η →
      ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η =
        (-1 : ℤ) ^ (p * q) • (ofGradedForm B U (q : ℤ) η * ofGradedForm B U (p : ℤ) ω) := by
  intro q
  induction q with
  | zero =>
      intro U ω η _ hη
      obtain rfl : η = B.exterior.one.eval U := hη
      rw [show ofGradedForm B U ((0 : ℕ) : ℤ) (B.exterior.one.eval U) = 1 from
        ofGradedForm_one B U, mul_one, one_mul, Nat.mul_zero, pow_zero, one_zsmul]
  | succ q ih =>
      intro U ω η hω hη
      obtain ⟨b, θ, hθ, hHEq⟩ := hη
      have hw : ofGradedForm B U ((q + 1 : ℕ) : ℤ) η =
          exactForm B U b * ofGradedForm B U (q : ℤ) θ := by
        rw [← ofGradedForm_mul]
        exact ofGradedForm_heq B (by omega) hHEq
      rw [hw]
      calc ofGradedForm B U (p : ℤ) ω * (exactForm B U b * ofGradedForm B U (q : ℤ) θ)
          = ofGradedForm B U (p : ℤ) ω * exactForm B U b * ofGradedForm B U (q : ℤ) θ :=
            (mul_assoc _ _ _).symm
        _ = (-1 : ℤ) ^ p • (exactForm B U b *
              (ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) θ)) := by
            rw [mul_exactForm_of_isExactWedge B p U ω hω b, smul_mul_assoc, mul_assoc]
        _ = ((-1 : ℤ) ^ p * (-1 : ℤ) ^ (p * q)) • (exactForm B U b *
              (ofGradedForm B U (q : ℤ) θ * ofGradedForm B U (p : ℤ) ω)) := by
            rw [ih U ω θ hω hθ, mul_smul_comm, smul_smul]
        _ = (-1 : ℤ) ^ (p * (q + 1)) •
              (exactForm B U b * ofGradedForm B U (q : ℤ) θ * ofGradedForm B U (p : ℤ) ω) := by
            rw [← pow_add, ← mul_assoc, show p + p * q = p * (q + 1) by ring]

/-- The wedge product of a `q`-form with a `p`-form, scaled by `(-1)^{pq}` and read in exterior
degree `p + q`: the right-hand side of graded commutativity. -/
private noncomputable def swapFormProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower p).val.obj U) (y : (B.exteriorPower q).val.obj U) :
    (B.exteriorPower (p + q)).val.obj U :=
  (-1 : ℤ) ^ (p * q) •
    reindexForm B (Nat.add_comm q p) U ((B.exterior.mul (q : ℤ) (p : ℤ)).app U y x)

/-- In the ring of all local forms, `swapFormProduct` is `(-1)^{pq}` times the product `η ∧ ω`. -/
private theorem ofGradedForm_swapFormProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    ofGradedForm B U ((p + q : ℕ) : ℤ) (swapFormProduct B p q U ω η) =
      (-1 : ℤ) ^ (p * q) • (ofGradedForm B U (q : ℤ) η * ofGradedForm B U (p : ℤ) ω) := by
  refine Eq.trans ((ofGradedForm B U ((p + q : ℕ) : ℤ)).map_zsmul _ _) ?_
  refine congrArg (fun z : totalForms B U => (-1 : ℤ) ^ (p * q) • z) ?_
  refine Eq.trans (ofGradedForm_reindexForm B (Nat.add_comm q p) U _) ?_
  exact ofGradedForm_mul B U (q : ℤ) (p : ℤ) η ω

/-- **Graded commutativity on exact wedges**, in the degree-normalized reading. -/
private theorem formProduct_comm_of_isExactWedge (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (hω : IsExactWedge B U p ω) (hη : IsExactWedge B U q η) :
    formProduct B p q U ω η = swapFormProduct B p q U ω η := by
  refine DirectSum.of_injective (β := gradedForms B U) ((p + q : ℕ) : ℤ) ?_
  have hl : ofGradedForm B U ((p + q : ℕ) : ℤ) (formProduct B p q U ω η) =
      ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η :=
    ofGradedForm_mul B U (p : ℤ) (q : ℤ) ω η
  have hr := ofGradedForm_swapFormProduct B p q U ω η
  exact hl.trans ((ofGradedForm_mul_comm_of_isExactWedge B p q U ω η hω hη).trans hr.symm)

/-- The right-hand side of graded commutativity, as a morphism out of the tensor product of the
underlying **presheaves** of `A`-modules, so that
`AlgebraicGeometry.SheafOfModules.tensorForms_hom_ext` applies to it. -/
private noncomputable def swapExteriorProductPresheafMap (p q : ℕ) :
    PresheafOfModules.tensorObj (O := A.obj) (deRhamTerm B p).val (deRhamTerm B q).val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj
        (deRhamTerm B (p + q)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun x y => swapFormProduct B p q U x y)
    (by
      intro x x' y
      refine Eq.trans (congrArg (fun z =>
        (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U z)
          (((B.exterior.mul (q : ℤ) (p : ℤ)).app U y).map_add x x')) ?_
      refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
        (reindexForm_add B (Nat.add_comm q p) U _ _)) ?_
      exact smul_add _ _ _)
    (by
      intro r x y
      refine Eq.trans (congrArg (fun z =>
        (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U z)
          ((B.exterior.mul (q : ℤ) (p : ℤ)).map_smul_right U (φ.hom.app U r) y x)) ?_
      refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
        (reindexForm_smul B (Nat.add_comm q p) U (φ.hom.app U r) _)) ?_
      exact zsmul_smul_form_comm B (p + q) U ((-1 : ℤ) ^ (p * q)) (φ.hom.app U r) _)
    (by
      intro x y y'
      refine Eq.trans (congrArg (fun z =>
        (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U z)
          (congrArg (fun k : (B.exteriorPower p).val.obj U →+ _ => k x)
            (((B.exterior.mul (q : ℤ) (p : ℤ)).app U).map_add y y'))) ?_
      refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
        (reindexForm_add B (Nat.add_comm q p) U _ _)) ?_
      exact smul_add _ _ _)
    (by
      intro r x y
      refine Eq.trans (congrArg (fun z =>
        (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U z)
          ((B.exterior.mul (q : ℤ) (p : ℤ)).map_smul_left U (φ.hom.app U r) y x)) ?_
      refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
        (reindexForm_smul B (Nat.add_comm q p) U (φ.hom.app U r) _)) ?_
      exact zsmul_smul_form_comm B (p + q) U ((-1 : ℤ) ^ (p * q)) (φ.hom.app U r) _)
  naturality {U V} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
    refine Eq.trans (congrArg (fun z =>
      (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) V z)
        ((B.exterior.mul (q : ℤ) (p : ℤ)).naturality f y x).symm) ?_
    refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
      (reindexForm_map B (Nat.add_comm q p) f
        ((B.exterior.mul (q : ℤ) (p : ℤ)).app U y x)).symm) ?_
    exact ((((B.exteriorPower (p + q)).val.map f).hom.toAddMonoidHom).map_zsmul _ _).symm

/-- The swapped product of a multiple of a `p`-form with a multiple of a `q`-form is the
corresponding multiple of the swapped product of the two forms. -/
private theorem swapFormProduct_smul_smul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (η : (B.exteriorPower q).val.obj U) :
    swapFormProduct B p q U (a • ω) (b • η) = (a * b) • swapFormProduct B p q U ω η := by
  have h1 : (B.exterior.mul (q : ℤ) (p : ℤ)).app U (b • η) (a • ω) =
      (b * a) • (B.exterior.mul (q : ℤ) (p : ℤ)).app U η ω := by
    refine Eq.trans ((B.exterior.mul (q : ℤ) (p : ℤ)).map_smul_left U b η (a • ω)) ?_
    refine Eq.trans (congrArg (fun z => b • z)
      ((B.exterior.mul (q : ℤ) (p : ℤ)).map_smul_right U a η ω)) ?_
    exact smul_smul b a _
  change (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U
      ((B.exterior.mul (q : ℤ) (p : ℤ)).app U (b • η) (a • ω)) =
    (a * b) • ((-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U
      ((B.exterior.mul (q : ℤ) (p : ℤ)).app U η ω))
  refine Eq.trans
    (congrArg (fun z => (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U z) h1) ?_
  refine Eq.trans (congrArg (fun z => (-1 : ℤ) ^ (p * q) • z)
    (reindexForm_smul B (Nat.add_comm q p) U (b * a) _)) ?_
  refine Eq.trans (zsmul_smul_form_comm B (p + q) U ((-1 : ℤ) ^ (p * q)) (b * a) _) ?_
  exact congrArg (fun r : X.sheaf.obj.obj U => r • ((-1 : ℤ) ^ (p * q) •
    reindexForm B (Nat.add_comm q p) U ((B.exterior.mul (q : ℤ) (p : ℤ)).app U η ω)))
    (mul_comm b a)

/-- The wedge product, read on a pure tensor of the underlying presheaves. -/
private theorem exteriorProductPresheafMap_tmul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower p).val.obj U) (y : (B.exteriorPower q).val.obj U) :
    (exteriorProductPresheafMap B p q).app U (x ⊗ₜ[A.obj.obj U] y) =
      formProduct B p q U x y := rfl

/-- The swapped wedge product, read on a pure tensor of the underlying presheaves. -/
private theorem swapExteriorProductPresheafMap_tmul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower p).val.obj U) (y : (B.exteriorPower q).val.obj U) :
    (swapExteriorProductPresheafMap B p q).app U (x ⊗ₜ[A.obj.obj U] y) =
      swapFormProduct B p q U x y := rfl

/-- The two sides of graded commutativity agree as morphisms out of the tensor product of the
underlying presheaves, because they agree on the pure tensors of multiples of exact wedges. -/
private theorem exteriorProductPresheafMap_eq_swap (p q : ℕ) :
    exteriorProductPresheafMap B p q = swapExteriorProductPresheafMap B p q := by
  refine tensorForms_hom_ext B p q (deRhamTerm B (p + q)) _ _ fun U a b ω η hω hη => ?_
  refine (exteriorProductPresheafMap_tmul B p q U (a • ω) (b • η)).trans
    (Eq.trans ?_ (swapExteriorProductPresheafMap_tmul B p q U (a • ω) (b • η)).symm)
  rw [formProduct_smul_smul, swapFormProduct_smul_smul,
    formProduct_comm_of_isExactWedge B p q U ω η hω hη]

/-- **The wedge product of relative differential forms is graded commutative**:
`ω ∧ η = (-1)^{pq} η ∧ ω` for arbitrary local sections `ω` of `Ωᵖ` and `η` of `Ωᵠ`, with the
exterior degrees normalized. -/
theorem formProduct_comm (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U ω η =
      (-1 : ℤ) ^ (p * q) • reindexForm B (Nat.add_comm q p) U (formProduct B q p U η ω) :=
  congrArg (fun k : PresheafOfModules.tensorObj (O := A.obj) (deRhamTerm B p).val
      (deRhamTerm B q).val ⟶
      (PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A).obj)).obj
        (deRhamTerm B (p + q)).val => k.app U (ω ⊗ₜ[A.obj.obj U] η))
    (exteriorProductPresheafMap_eq_swap B p q)

/-- **The wedge product of relative differential forms is graded commutative**, in the ring of all
local forms: `ω ∧ η = (-1)^{pq} η ∧ ω`. -/
theorem ofGradedForm_mul_comm (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η =
      (-1 : ℤ) ^ (p * q) • (ofGradedForm B U (q : ℤ) η * ofGradedForm B U (p : ℤ) ω) := by
  have hl : ofGradedForm B U ((p + q : ℕ) : ℤ) (formProduct B p q U ω η) =
      ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η :=
    ofGradedForm_mul B U (p : ℤ) (q : ℤ) ω η
  have hr := ofGradedForm_swapFormProduct B p q U ω η
  exact hl.symm.trans
    ((congrArg (ofGradedForm B U ((p + q : ℕ) : ℤ)) (formProduct_comm B p q U ω η)).trans hr)

/-- Graded commutativity, as a heterogeneous equality of the two wedge products in their own
exterior degrees `p + q` and `q + p`. -/
theorem formProduct_heq_comm (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    HEq (formProduct B p q U ω η) ((-1 : ℤ) ^ (p * q) • formProduct B q p U η ω) := by
  rw [formProduct_comm B p q U ω η, ← reindexForm_zsmul]
  exact reindexForm_heq B (Nat.add_comm q p) U _

/-! ### The two laws for the wedge product of Tag 0FM2 -/

variable (D : DeRhamDifferential B)

/-- The value of a morphism out of the total complex `Tot(Ω^• ⊗_A Ω^•)` on the local pure tensor
`ω ⊗ η` of a `p`-form and a `q`-form, i.e. its restriction to the `(p, q)` summand evaluated on a
pure tensor. For the wedge product of Tag 0FM2 this is `ω ∧ η`
(`AlgebraicGeometry.SheafOfModules.summandValue_wedgeProduct`). -/
noncomputable def summandValue (m : tensorSquare B D ⟶ deRhamComplex B D) (p q : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (ω : (deRhamTerm B p).val.obj U)
    (η : (deRhamTerm B q).val.obj U) : ((deRhamComplex B D).X (p + q)).val.obj U :=
  (HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      (deRhamComplex B D) (deRhamComplex B D)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℕ) p q (p + q) rfl ≫ m.f (p + q)).val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
      (PresheafOfModules.tensorObj (deRhamTerm B p).val (deRhamTerm B q).val)).app U
        (ω ⊗ₜ[A.obj.obj U] η))

/-- On a local pure tensor the wedge product of Tag 0FM2 is the wedge product of forms. -/
theorem summandValue_wedgeProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B q).val.obj U) :
    summandValue B D (wedgeProduct B D) p q U ω η = formProduct B p q U ω η :=
  eq_of_heq (wedgeProduct_summand_unit_apply B D p q U ω η)

/-- **Stacks Project, Tag 0FM3.** The wedge product of Tag 0FM2 is **associative** on the summands
of the total complex: the two bracketings of a triple wedge of local forms agree.

This is the associativity clause of the proof of Tag 0FM3, "the fact that `∧` is associative"; the
associativity of the cup product on `H^*_{dR}` is this together with Cohomology, Tag 0FP4. -/
@[stacks 0FM3 "the wedge product of 0FM2 is associative"]
theorem wedgeProduct_summand_assoc (p q r : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B q).val.obj U)
    (ζ : (deRhamTerm B r).val.obj U) :
    HEq (summandValue B D (wedgeProduct B D) (p + q) r U
        (summandValue B D (wedgeProduct B D) p q U ω η) ζ)
      (summandValue B D (wedgeProduct B D) p (q + r) U ω
        (summandValue B D (wedgeProduct B D) q r U η ζ)) := by
  rw [summandValue_wedgeProduct B D (p + q) r U
      (summandValue B D (wedgeProduct B D) p q U ω η) ζ,
    summandValue_wedgeProduct B D p (q + r) U ω
      (summandValue B D (wedgeProduct B D) q r U η ζ),
    summandValue_wedgeProduct B D p q U ω η, summandValue_wedgeProduct B D q r U η ζ,
    formProduct_assoc B p q r U ω η ζ]
  exact reindexForm_heq B (Nat.add_assoc p q r).symm U _

/-- **Stacks Project, Tag 0FM3.** The wedge product of Tag 0FM2 is **graded commutative** on the
summands of the total complex: on the local pure tensor `ω ⊗ η` of a `p`-form and a `q`-form its
value is `(-1)^{pq}` times its value on `η ⊗ ω`.

This is the graded commutativity clause of the proof of Tag 0FM3, "the fact that `∧` is graded
commutative"; the graded commutativity of the cup product on `H^*_{dR}` is this together with
Cohomology, Tag 0FP5. -/
@[stacks 0FM3 "the wedge product of 0FM2 is graded commutative, with the sign (-1)^(pq)"]
theorem wedgeProduct_summand_comm (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B q).val.obj U) :
    HEq (summandValue B D (wedgeProduct B D) p q U ω η)
      ((-1 : ℤ) ^ (p * q) • summandValue B D (wedgeProduct B D) q p U η ω) := by
  simp only [summandValue_wedgeProduct]
  exact formProduct_heq_comm B p q U ω η

end AlgebraicGeometry.SheafOfModules

end
