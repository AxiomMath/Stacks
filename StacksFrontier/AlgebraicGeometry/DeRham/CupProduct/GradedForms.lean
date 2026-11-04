module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness

/-!
# The local ring of differential forms, and the graded Leibniz rule

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B`
the structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative
differentials and let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω`, so that the exterior powers `⋀ᵖ Ω` are available.

Over a fixed open set the homogeneous local sections `(⋀ⁱ Ω)(U)`, `i : ℤ`, form an internally
graded ring. This file assembles them into the honest ring `⨁ i, (⋀ⁱ Ω)(U)` so that the graded
identities of the exterior algebra — associativity, unitality, vanishing of the square of an exact
differential — can be used as *ring* identities instead of being transported through the degree
arithmetic by hand. In that ring a de Rham differential satisfies the graded Leibniz rule

`d (ω ∧ η) = d ω ∧ η + (-1)^{deg ω} ω ∧ d η`

on products of multiples of exact wedges, which is `localLeibniz_smul_exactWedge` below. Because
the exact wedges generate `⋀ᵖ Ω` locally, that special case determines the Leibniz rule
everywhere, and it is in this form that the wedge product of
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic` is shown to be a morphism of complexes.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.gradedForms`: the degree-`i` local sections of the exterior
  algebra over an open set.
* `AlgebraicGeometry.SheafOfModules.totalForms`: their direct sum, a ring.
* `AlgebraicGeometry.SheafOfModules.ofGradedForm`: the inclusion of a homogeneous piece.
* `AlgebraicGeometry.SheafOfModules.scalarForm` and
  `AlgebraicGeometry.SheafOfModules.exactForm`: the degree-zero form `b · 1` and the degree-one
  form `d b` attached to a local section `b` of the target ring.
* `AlgebraicGeometry.SheafOfModules.formProduct`: the wedge product of a `p`-form and a `q`-form,
  landing in degree `((p + q : ℕ) : ℤ)` on the nose rather than in degree `(p : ℤ) + q`.
* `AlgebraicGeometry.SheafOfModules.prependExact`: the product `d a ∧ η` of an exact differential
  with a `p`-form, again with its degree normalized.
* `AlgebraicGeometry.SheafOfModules.localDifferential`: a de Rham differential out of degree `p`,
  read as an additive map into the ring of all local sections.

## Main results

* `AlgebraicGeometry.SheafOfModules.exteriorPower_induction`: **a property of local sections of
  `⋀ᵖ Ω` that is additive, local, and holds on multiples of exact wedges holds on every local
  section.** This is the local generation of `⋀ᵖ Ω` by exact wedges, packaged as an induction
  principle.
* `AlgebraicGeometry.SheafOfModules.exactForm_mul_self` and
  `AlgebraicGeometry.SheafOfModules.exactForm_anticomm`: `d b ∧ d b = 0`, and the
  anticommutativity it forces.
* `AlgebraicGeometry.SheafOfModules.mul_exactForm_of_isExactWedge`: an exact wedge of degree `p`
  anticommutes with an exact differential up to the sign `(-1)^p`.
* `AlgebraicGeometry.SheafOfModules.isExactWedge_formProduct`: the product of two exact wedges is
  an exact wedge.
* `AlgebraicGeometry.SheafOfModules.localLeibniz_smul_exactWedge`: **the graded Leibniz rule on a
  product of multiples of exact wedges.**

## Implementation notes

The package of algebras is a hypothesis, as everywhere in this group of files, and so is the de
Rham differential: every statement below holds for an arbitrary
`AlgebraicGeometry.SheafOfModules.DeRhamDifferential` and therefore for the one
`AlgebraicGeometry.SheafOfModules.deRhamDifferential` constructs. Uniqueness
(`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq`) makes the two readings agree.

`AlgebraicGeometry.SheafOfModules.gradedForms` is indexed by `ℤ` and not by `ℕ`, because that is
the indexing of the graded algebra: multiplication adds degrees in `ℤ`, and the point of passing
to the total ring is to avoid carrying the coercion `((p + q : ℕ) : ℤ) = (p : ℤ) + q` through
every identity. The degree-normalized products
`AlgebraicGeometry.SheafOfModules.formProduct` and
`AlgebraicGeometry.SheafOfModules.prependExact` are where that coercion is paid for, once each.

The graded unit and multiplication are supplied as separate local instances before the graded ring
itself, because the power operation of `DirectSum.GRing` has a default value which is only
synthesized once `GradedMonoid.GOne` and `GradedMonoid.GMul` are available.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Induction on local sections of `⋀ᵖ Ω` -/

/-- **A property of local sections of `⋀ᵖ Ω` which is additive, local, and holds on every
multiple of an exact wedge holds on every local section.**

The exact wedges generate `⋀ᵖ Ω` locally
(`AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`), so a local section restricts,
along a covering family, into the subgroup generated by the multiples of the exact wedges; the
additivity hypotheses then propagate the property through that subgroup. -/
theorem exteriorPower_induction (p : ℕ)
    (P : ∀ U : (Opens X.carrier)ᵒᵖ, (B.exteriorPower p).val.obj U → Prop)
    (hzero : ∀ U, P U 0)
    (hadd : ∀ U x y, P U x → P U y → P U (x + y))
    (hneg : ∀ U x, P U x → P U (-x))
    (hlocal : ∀ (U : (Opens X.carrier)ᵒᵖ) x (S : Sieve U.unop),
      S ∈ Opens.grothendieckTopology X.carrier U.unop →
      (∀ V (g : V ⟶ U.unop), S g → P (op V) ((B.exteriorPower p).val.map g.op x)) → P U x)
    (hgen : ∀ U (b : X.sheaf.obj.obj U) ω, IsExactWedge B U p ω → P U (b • ω))
    (U : (Opens X.carrier)ᵒᵖ) (ω : (B.exteriorPower p).val.obj U) : P U ω := by
  obtain ⟨S, hS, hcov⟩ := locallyGeneratedByExactWedges B p U ω
  refine hlocal U ω S hS fun V f hf => ?_
  refine AddSubgroup.closure_induction (p := fun z _ => P (op V) z) ?_ ?_ ?_ ?_ (hcov f hf)
  · rintro z ⟨b, η, hη, rfl⟩
    exact hgen (op V) b η hη
  · exact hzero (op V)
  · exact fun x y _ _ hx hy => hadd (op V) x y hx hy
  · exact fun x _ hx => hneg (op V) x hx

/-! ### The local ring of forms -/

/-- The degree-`i` local sections of the exterior algebra of `Ω` over an open set. -/
abbrev gradedForms (U : (Opens X.carrier)ᵒᵖ) (i : ℤ) : Type u :=
  (B.exterior.piece i).val.obj U

/-- The graded unit on the homogeneous local sections: the global unit of the exterior algebra,
evaluated on the open set. -/
@[instance_reducible]
noncomputable def gradedFormsGOne (U : (Opens X.carrier)ᵒᵖ) :
    GradedMonoid.GOne (gradedForms B U) where
  one := B.exterior.one.eval U

attribute [local instance] gradedFormsGOne

/-- The graded multiplication on the homogeneous local sections: the multiplication of the
exterior algebra. -/
@[instance_reducible]
noncomputable def gradedFormsGMul (U : (Opens X.carrier)ᵒᵖ) :
    GradedMonoid.GMul (gradedForms B U) where
  mul {i j} a b := (B.exterior.mul i j).app U a b

attribute [local instance] gradedFormsGMul

/-- The graded-ring structure on the homogeneous local sections of the exterior algebra of `Ω`
over an open set, given by its multiplication and its unit. -/
@[instance_reducible]
noncomputable def gradedFormsGRing (U : (Opens X.carrier)ᵒᵖ) :
    DirectSum.GRing (gradedForms B U) where
  mul {i j} a b := (B.exterior.mul i j).app U a b
  one := B.exterior.one.eval U
  mul_zero _ := map_zero _
  zero_mul := by intro i j b; simp
  mul_add _ _ _ := map_add _ _ _
  add_mul := by intro i j a b c; simp
  one_mul := by
    rintro ⟨i, a⟩
    exact Sigma.ext (zero_add i) (B.exterior.one_mul i U a)
  mul_one := by
    rintro ⟨i, a⟩
    exact Sigma.ext (add_zero i) (B.exterior.mul_one i U a)
  mul_assoc := by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    exact Sigma.ext (add_assoc i j k) (B.exterior.mul_assoc i j k U a b c)
  natCast n := n • B.exterior.one.eval U
  natCast_zero := zero_smul _ _
  natCast_succ n := by simp [add_smul]
  intCast n := n • B.exterior.one.eval U
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc_ofNat n := by simp

attribute [local instance] gradedFormsGRing

/-- The ring of all local sections of the exterior algebra of `Ω` over an open set: the direct
sum of its homogeneous pieces, with the multiplication of the graded algebra. -/
abbrev totalForms (U : (Opens X.carrier)ᵒᵖ) : Type u :=
  ⨁ i, gradedForms B U i

/-- The inclusion of the degree-`i` local sections into the ring of all local sections. -/
noncomputable abbrev ofGradedForm (U : (Opens X.carrier)ᵒᵖ) (i : ℤ) :
    gradedForms B U i →+ totalForms B U :=
  DirectSum.of (fun i => gradedForms B U i) i

/-- Two homogeneous local sections of equal degree which are heterogeneously equal have the same
image in the ring of all local sections. -/
theorem ofGradedForm_heq {U : (Opens X.carrier)ᵒᵖ} {i j : ℤ} (h : i = j)
    {a : gradedForms B U i} {b : gradedForms B U j} (hab : HEq a b) :
    ofGradedForm B U i a = ofGradedForm B U j b := by
  subst j
  cases eq_of_heq hab
  rfl

/-- Two homogeneous local sections of equal degree with the same image in the ring of all local
sections are heterogeneously equal. -/
theorem heq_of_ofGradedForm_eq {U : (Opens X.carrier)ᵒᵖ} {i j : ℤ} (h : i = j)
    {a : gradedForms B U i} {b : gradedForms B U j}
    (hab : ofGradedForm B U i a = ofGradedForm B U j b) : HEq a b := by
  subst j
  exact heq_of_eq (DirectSum.of_injective (β := gradedForms B U) i hab)

/-- The inclusion turns the graded multiplication into the ring multiplication. -/
theorem ofGradedForm_mul (U : (Opens X.carrier)ᵒᵖ) (i j : ℤ) (a : gradedForms B U i)
    (b : gradedForms B U j) :
    ofGradedForm B U (i + j) ((B.exterior.mul i j).app U a b) =
      ofGradedForm B U i a * ofGradedForm B U j b :=
  (DirectSum.of_mul_of (A := gradedForms B U) a b).symm

/-- The image of the global unit is the unit of the ring of all local sections. -/
theorem ofGradedForm_one (U : (Opens X.carrier)ᵒᵖ) :
    ofGradedForm B U 0 (B.exterior.one.eval U) = 1 := rfl

/-- The degree-zero form `b · 1` attached to a local section `b` of the target ring. -/
noncomputable abbrev scalarForm (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    totalForms B U :=
  ofGradedForm B U 0 (b • B.exterior.one.eval U)

/-- The degree-one form `d b` attached to a local section `b` of the target ring, read in the
ring of all local sections. -/
noncomputable abbrev exactForm (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    totalForms B U :=
  ofGradedForm B U 1 (exactOne B U b)

/-- Scaling commutes with a heterogeneous equality of homogeneous sections. -/
theorem smul_heq_smul {U : (Opens X.carrier)ᵒᵖ} {i j : ℤ} (h : i = j)
    {a : gradedForms B U i} {b : gradedForms B U j} (hab : HEq a b) (r : X.sheaf.obj.obj U) :
    HEq (r • a) (r • b) := by
  subst j
  cases eq_of_heq hab
  rfl

/-- Multiplying by `b · 1` on the left is scaling by `b`. -/
theorem scalarForm_mul (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (i : ℤ)
    (ω : gradedForms B U i) :
    scalarForm B U b * ofGradedForm B U i ω = ofGradedForm B U i (b • ω) := by
  rw [← ofGradedForm_mul, (B.exterior.mul 0 i).map_smul_left]
  exact ofGradedForm_heq B (zero_add i) (smul_heq_smul B (zero_add i) (B.exterior.one_mul i U ω) b)

/-- Multiplying by `b · 1` on the right is scaling by `b`. -/
theorem mul_scalarForm (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) (i : ℤ)
    (ω : gradedForms B U i) :
    ofGradedForm B U i ω * scalarForm B U b = ofGradedForm B U i (b • ω) := by
  rw [← ofGradedForm_mul, (B.exterior.mul i 0).map_smul_right]
  exact ofGradedForm_heq B (add_zero i) (smul_heq_smul B (add_zero i) (B.exterior.mul_one i U ω) b)

/-! ### Exact differentials -/

/-- `d` is additive on local sections of the target ring. -/
theorem exactOne_add (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) :
    exactOne B U (a + b) = exactOne B U a + exactOne B U b := by
  simp only [exactOne, ((universalDerivation.{u, u, u} φ).app U).d_add, map_add]

/-- The Leibniz rule for `d` on local sections of the target ring. -/
theorem exactOne_mul (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) :
    exactOne B U (a * b) = a • exactOne B U b + b • exactOne B U a := by
  simp only [exactOne, ((universalDerivation.{u, u, u} φ).app U).d_mul, map_add, map_smul]

/-- `d` is additive, read in the ring of all local sections. -/
theorem exactForm_add (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) :
    exactForm B U (a + b) = exactForm B U a + exactForm B U b := by
  rw [exactForm, exactOne_add, map_add]

/-- The Leibniz rule for `d`, read in the ring of all local sections. -/
theorem exactForm_mul (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) :
    exactForm B U (a * b) =
      scalarForm B U a * exactForm B U b + scalarForm B U b * exactForm B U a := by
  rw [scalarForm_mul, scalarForm_mul, exactForm, exactOne_mul, map_add]

/-- `d b ∧ d b = 0`: the defining relation of the exterior algebra, read in the ring of all local
sections. -/
theorem exactForm_mul_self (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U) :
    exactForm B U b * exactForm B U b = 0 := by
  rw [← ofGradedForm_mul]
  refine Eq.trans (congrArg (ofGradedForm B U (1 + 1)) ?_) (map_zero _)
  exact B.squareZero_exteriorGenerator U (((universalDerivation.{u, u, u} φ).app U).d b)

/-- Exact differentials anticommute. -/
theorem exactForm_anticomm (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) :
    exactForm B U a * exactForm B U b = -(exactForm B U b * exactForm B U a) := by
  have h := exactForm_mul_self B U (a + b)
  rw [exactForm_add, add_mul, mul_add, mul_add, exactForm_mul_self, exactForm_mul_self,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Restriction commutes with a heterogeneous equality of homogeneous sections. -/
theorem map_heq_map {i j : ℤ} (h : i = j) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    {ω : gradedForms B U i} {η : gradedForms B U j} (he : HEq ω η) :
    HEq ((B.exterior.piece i).val.map f ω) ((B.exterior.piece j).val.map f η) := by
  subst j
  cases eq_of_heq he
  rfl

/-- `d` commutes with restriction. -/
theorem exactOne_map {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) (b : X.sheaf.obj.obj U) :
    (B.exteriorPower 1).val.map f (exactOne B U b) = exactOne B V (X.sheaf.obj.map f b) :=
  (PresheafOfModules.naturality_apply B.exteriorGenerator.val f
      ((universalDerivation.{u, u, u} φ).d b)).symm.trans
    (congrArg (fun z => ConcreteCategory.hom (B.exteriorGenerator.val.app V) z)
      ((universalDerivation.{u, u, u} φ).d_map f b).symm)

/-! ### Degree-normalized products -/

/-- The wedge product of a `p`-form and a `q`-form, with its degree normalized to the coerced
natural number `((p + q : ℕ) : ℤ)` rather than `(p : ℤ) + q`. -/
noncomputable abbrev formProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    (B.exteriorPower (p + q)).val.obj U :=
  (B.exterior.mul (p : ℤ) (q : ℤ)).app U ω η

/-- The wedge product of a multiple of a `p`-form with a multiple of a `q`-form is the
corresponding multiple of the wedge product of the two forms. -/
theorem formProduct_smul_smul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (a • ω) (b • η) = (a * b) • formProduct B p q U ω η := by
  rw [formProduct, (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_left,
    (B.exterior.mul (p : ℤ) (q : ℤ)).map_smul_right, smul_smul]

/-- The product of an exact differential with a `p`-form, with its degree normalized to the
coerced natural number `((p + 1 : ℕ) : ℤ)` rather than `1 + (p : ℤ)`. -/
noncomputable def prependExact (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (η : (B.exteriorPower p).val.obj U) : (B.exteriorPower (p + 1)).val.obj U :=
  cast (congrArg (gradedForms B U) (show 1 + (p : ℤ) = ((p + 1 : ℕ) : ℤ) by omega))
    ((B.exterior.mul 1 (p : ℤ)).app U (exactOne B U a) η)

/-- Prepending an exact differential to an exact wedge gives an exact wedge: this is the
recursive step of `AlgebraicGeometry.SheafOfModules.IsExactWedge`, with the degree transport
performed. -/
theorem isExactWedge_prependExact (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (η : (B.exteriorPower p).val.obj U) (hη : IsExactWedge B U p η) :
    IsExactWedge B U (p + 1) (prependExact B p U a η) :=
  ⟨a, η, hη, cast_heq _ _⟩

/-- The inclusion of `d a ∧ η` is the product of the inclusions. -/
theorem ofGradedForm_prependExact (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (η : (B.exteriorPower p).val.obj U) :
    ofGradedForm B U ((p + 1 : ℕ) : ℤ) (prependExact B p U a η) =
      exactForm B U a * ofGradedForm B U (p : ℤ) η := by
  rw [← ofGradedForm_mul]
  exact ofGradedForm_heq B (by omega) (cast_heq _ _)

/-- Being an exact wedge transports along a heterogeneous equality of forms of equal degree. -/
theorem isExactWedge_of_heq {p q : ℕ} (h : p = q) {U : (Opens X.carrier)ᵒᵖ}
    {ω : (B.exteriorPower p).val.obj U} {η : (B.exteriorPower q).val.obj U} (he : HEq ω η)
    (hω : IsExactWedge B U p ω) : IsExactWedge B U q η := by
  subst q
  cases eq_of_heq he
  exact hω

/-- **The restriction of an exact wedge is an exact wedge.** -/
theorem isExactWedge_map (p : ℕ) {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (ω : (B.exteriorPower p).val.obj U) (hω : IsExactWedge B U p ω) :
    IsExactWedge B V p ((B.exteriorPower p).val.map f ω) := by
  induction p with
  | zero =>
      subst ω
      exact B.exterior.one.property f
  | succ p ih =>
      obtain ⟨b, η, hη, hω⟩ := hω
      have he : ω = prependExact B p U b η := eq_of_heq (hω.trans (cast_heq _ _).symm)
      subst ω
      refine ⟨X.sheaf.obj.map f b, (B.exteriorPower p).val.map f η, ih η hη, ?_⟩
      refine HEq.trans
        (map_heq_map B (show ((p + 1 : ℕ) : ℤ) = 1 + (p : ℤ) by omega) f (cast_heq _ _)) ?_
      refine heq_of_eq
        (((B.exterior.mul 1 (p : ℤ)).naturality f (exactOne B U b) η).trans ?_)
      exact congrArg
        (fun z => (B.exterior.mul 1 (p : ℤ)).app V z ((B.exteriorPower p).val.map f η))
        (exactOne_map B f b)

/-- **The product of two exact wedges is an exact wedge, up to the normalization of its degree.**
This is the inductive form: an exact wedge of degree `p + q` whose inclusion is the product of
the two inclusions. -/
theorem exists_isExactWedge_ofGradedForm_eq_mul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (hω : IsExactWedge B U p ω) (hη : IsExactWedge B U q η) :
    ∃ ζ : (B.exteriorPower (p + q)).val.obj U, IsExactWedge B U (p + q) ζ ∧
      ofGradedForm B U ((p + q : ℕ) : ℤ) ζ =
        ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η := by
  induction p with
  | zero =>
      subst ω
      refine ⟨cast (congrArg (gradedForms B U) (show (q : ℤ) = ((0 + q : ℕ) : ℤ) by omega)) η,
        isExactWedge_of_heq B (Nat.zero_add q).symm (cast_heq _ _).symm hη, ?_⟩
      rw [show ofGradedForm B U ((0 : ℕ) : ℤ) (B.exterior.one.eval U) = 1 from
        ofGradedForm_one B U, one_mul]
      exact ofGradedForm_heq B (by omega) (cast_heq _ _)
  | succ p ih =>
      obtain ⟨a, θ, hθ, hω⟩ := hω
      obtain ⟨ζ, hζ, hprod⟩ := ih θ hθ
      have hw : ofGradedForm B U ((p + 1 : ℕ) : ℤ) ω =
          exactForm B U a * ofGradedForm B U (p : ℤ) θ := by
        rw [← ofGradedForm_mul]
        exact ofGradedForm_heq B (by omega) hω
      rw [show p + 1 + q = p + q + 1 by omega]
      refine ⟨prependExact B (p + q) U a ζ,
        isExactWedge_prependExact B (p + q) U a ζ hζ, ?_⟩
      rw [ofGradedForm_prependExact, hprod, hw, mul_assoc]

/-- **The product of two exact wedges is an exact wedge.** -/
theorem isExactWedge_formProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U)
    (hω : IsExactWedge B U p ω) (hη : IsExactWedge B U q η) :
    IsExactWedge B U (p + q) (formProduct B p q U ω η) := by
  obtain ⟨ζ, hζ, he⟩ := exists_isExactWedge_ofGradedForm_eq_mul B p q U ω η hω hη
  have h : ζ = formProduct B p q U ω η :=
    DirectSum.of_injective (β := gradedForms B U) ((p + q : ℕ) : ℤ)
      (he.trans (ofGradedForm_mul B U (p : ℤ) (q : ℤ) ω η).symm)
  exact h ▸ hζ

/-! ### Two identities in an arbitrary ring

The algebra behind the graded Leibniz rule is carried out here, in an arbitrary ring, so that it
is not entangled with the degree bookkeeping of the exterior algebra. -/

/-- Transposing an exact differential past a product: if `x` anticommutes with `db` up to the
sign `t`, and `da` anticommutes with `db`, then `da * x` anticommutes with `db` up to `-t`. -/
private theorem mul_anticomm_step {R : Type*} [Ring R] (da db x : R) (t : ℤ)
    (hx : x * db = t • (db * x)) (hanti : da * db = -(db * da)) :
    da * x * db = (-t) • (db * (da * x)) := by
  rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, hanti, neg_mul, smul_neg, mul_assoc, neg_zsmul]

/-- The ring-theoretic content of the graded Leibniz rule: the two sides agree as soon as `cb`
commutes with `w` and with `da`, `w` anticommutes with `db` up to a sign `t` squaring to one. -/
private theorem leibniz_identity {R : Type*} [Ring R] (ca cb da db w e : R) (t : ℤ)
    (hbw : Commute cb w) (hbda : Commute cb da) (hwd : w * db = t • (db * w))
    (htt : t * t = 1) :
    (ca * db + cb * da) * (w * e) = da * w * (cb * e) + t • (ca * w * (db * e)) := by
  have hfirst : da * w * (cb * e) = cb * da * (w * e) := by
    rw [← mul_assoc, mul_assoc da w cb, hbw.eq.symm, ← mul_assoc da cb w, hbda.eq.symm, mul_assoc]
  have hsecond : t • (ca * w * (db * e)) = ca * db * (w * e) := by
    rw [← mul_assoc, mul_assoc ca w db, hwd, mul_smul_comm, smul_mul_assoc, ← mul_smul, htt,
      one_smul, mul_assoc]
    simp only [mul_assoc]
  rw [hfirst, hsecond, add_mul, add_comm]

/-! ### The differential in the local ring of forms -/

variable (D : DeRhamDifferential B)

/-- A de Rham differential out of degree `p`, read as an additive map into the ring of all local
sections of the exterior algebra. -/
noncomputable def localDifferential (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) :
    (B.exteriorPower p).val.obj U →+ totalForms B U :=
  (ofGradedForm B U ((p + 1 : ℕ) : ℤ)).comp
    (((deRhamComplex B D).d p (p + 1)).val.app U).hom.toAddMonoidHom

/-- **The de Rham rule in the ring of all local sections**: on a multiple of an exact wedge the
differential is the product of the exact differential of the coefficient with the wedge. -/
theorem localDifferential_smul_exactWedge (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U) (hω : IsExactWedge B U p ω) :
    localDifferential B D p U (b • ω) = exactForm B U b * ofGradedForm B U (p : ℤ) ω := by
  rw [← ofGradedForm_mul]
  exact ofGradedForm_heq B (by omega) (deRhamComplex_exactWedge B D p U b ω hω)

/-- **An exact wedge of degree `p` anticommutes with an exact differential up to the sign
`(-1)^p`.** Each of the `p` exact factors of the wedge contributes one transposition. -/
theorem mul_exactForm_of_isExactWedge (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (hω : IsExactWedge B U p ω) (b : X.sheaf.obj.obj U) :
    ofGradedForm B U (p : ℤ) ω * exactForm B U b =
      (-1 : ℤ) ^ p • (exactForm B U b * ofGradedForm B U (p : ℤ) ω) := by
  induction p with
  | zero =>
      subst ω
      rw [show ofGradedForm B U ((0 : ℕ) : ℤ) (B.exterior.one.eval U) = 1 from
        ofGradedForm_one B U, one_mul, mul_one, pow_zero, one_zsmul]
  | succ p ih =>
      obtain ⟨a, η, hη, hω⟩ := hω
      have hw : ofGradedForm B U ((p + 1 : ℕ) : ℤ) ω =
          exactForm B U a * ofGradedForm B U (p : ℤ) η := by
        rw [← ofGradedForm_mul]
        exact ofGradedForm_heq B (by omega) hω
      have hsign : (-1 : ℤ) ^ (p + 1) = -((-1 : ℤ) ^ p) := by rw [pow_succ, mul_neg_one]
      refine (congrArg (fun z => z * exactForm B U b) hw).trans ?_
      refine Eq.trans ?_
        (congrArg (fun z => (-1 : ℤ) ^ (p + 1) • (exactForm B U b * z)) hw.symm)
      refine Eq.trans (mul_anticomm_step (exactForm B U a) (exactForm B U b)
        (ofGradedForm B U (p : ℤ) η) ((-1 : ℤ) ^ p) (ih η hη)
        (exactForm_anticomm B U a b)) ?_
      exact congrArg (fun s : ℤ => s • (exactForm B U b * (exactForm B U a *
        ofGradedForm B U (p : ℤ) η))) hsign.symm

/-- The common value of the two sides of the graded Leibniz rule on multiples of exact wedges:
the Leibniz expansion of `d (a b)` multiplied by the wedge `ω ∧ η`. This is the left-hand side,
`d (a ω ∧ b η)`. -/
theorem localDifferential_formProduct_smul_smul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (η : (B.exteriorPower q).val.obj U) (hω : IsExactWedge B U p ω)
    (hη : IsExactWedge B U q η) :
    localDifferential B D (p + q) U (formProduct B p q U (a • ω) (b • η)) =
      (scalarForm B U a * exactForm B U b + scalarForm B U b * exactForm B U a) *
        (ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η) := by
  rw [formProduct_smul_smul, localDifferential_smul_exactWedge B D _ _ _ _
      (isExactWedge_formProduct B p q U ω η hω hη),
    show ofGradedForm B U ((p + q : ℕ) : ℤ) (formProduct B p q U ω η) =
        ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η from
      ofGradedForm_mul B U (p : ℤ) (q : ℤ) ω η,
    exactForm_mul]

/-- The right-hand side of the graded Leibniz rule on multiples of exact wedges has the same
value as the left-hand side of
`AlgebraicGeometry.SheafOfModules.localDifferential_formProduct_smul_smul`: moving the
degree-zero coefficients to the front costs nothing because they are central, and the sign
`(-1)^p` is cancelled by the `p` transpositions needed to move `d b` across `ω`. -/
theorem localDifferential_mul_add_zsmul_mul_localDifferential (p q : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (a b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (η : (B.exteriorPower q).val.obj U) (hω : IsExactWedge B U p ω)
    (hη : IsExactWedge B U q η) :
    localDifferential B D p U (a • ω) * ofGradedForm B U (q : ℤ) (b • η) +
        (-1 : ℤ) ^ p •
          (ofGradedForm B U (p : ℤ) (a • ω) * localDifferential B D q U (b • η)) =
      (scalarForm B U a * exactForm B U b + scalarForm B U b * exactForm B U a) *
        (ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η) := by
  have hbw : Commute (scalarForm B U b) (ofGradedForm B U (p : ℤ) ω) :=
    (scalarForm_mul B U b (p : ℤ) ω).trans (mul_scalarForm B U b (p : ℤ) ω).symm
  have hbda : Commute (scalarForm B U b) (exactForm B U a) :=
    (scalarForm_mul B U b 1 (exactOne B U a)).trans (mul_scalarForm B U b 1 (exactOne B U a)).symm
  have hwd : ofGradedForm B U (p : ℤ) ω * exactForm B U b =
      (-1 : ℤ) ^ p • (exactForm B U b * ofGradedForm B U (p : ℤ) ω) :=
    mul_exactForm_of_isExactWedge B p U ω hω b
  have htt : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by rw [← mul_pow]; simp
  have hfirst : (exactForm B U a * ofGradedForm B U (p : ℤ) ω) *
      (scalarForm B U b * ofGradedForm B U (q : ℤ) η) =
      (scalarForm B U b * exactForm B U a) *
        (ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η) := by
    rw [← mul_assoc, mul_assoc (exactForm B U a) (ofGradedForm B U (p : ℤ) ω) (scalarForm B U b),
      hbw.eq.symm, ← mul_assoc (exactForm B U a) (scalarForm B U b), hbda.eq.symm, mul_assoc]
  have hsecond : (-1 : ℤ) ^ p • ((scalarForm B U a * ofGradedForm B U (p : ℤ) ω) *
      (exactForm B U b * ofGradedForm B U (q : ℤ) η)) =
      (scalarForm B U a * exactForm B U b) *
        (ofGradedForm B U (p : ℤ) ω * ofGradedForm B U (q : ℤ) η) := by
    rw [← mul_assoc, mul_assoc (scalarForm B U a) (ofGradedForm B U (p : ℤ) ω) (exactForm B U b),
      hwd, mul_smul_comm, smul_mul_assoc, ← mul_smul, htt, one_smul, mul_assoc]
    simp only [mul_assoc]
  rw [localDifferential_smul_exactWedge B D p U a ω hω,
    localDifferential_smul_exactWedge B D q U b η hη,
    ← scalarForm_mul B U b (q : ℤ) η, ← scalarForm_mul B U a (p : ℤ) ω,
    hfirst, hsecond, add_mul, add_comm]

/-- **The graded Leibniz rule on a product of multiples of exact wedges.**

This is the identity that makes the wedge product a morphism of complexes. The exact wedges
generate `⋀ᵖ Ω` locally, so this special case determines the rule on arbitrary local sections. -/
theorem localLeibniz_smul_exactWedge (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a b : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (η : (B.exteriorPower q).val.obj U) (hω : IsExactWedge B U p ω)
    (hη : IsExactWedge B U q η) :
    localDifferential B D (p + q) U (formProduct B p q U (a • ω) (b • η)) =
      localDifferential B D p U (a • ω) * ofGradedForm B U (q : ℤ) (b • η) +
        (-1 : ℤ) ^ p •
          (ofGradedForm B U (p : ℤ) (a • ω) * localDifferential B D q U (b • η)) :=
  (localDifferential_formProduct_smul_smul B D p q U a b ω η hω hη).trans
    (localDifferential_mul_add_zsmul_mul_localDifferential B D p q U a b ω η hω hη).symm

end AlgebraicGeometry.SheafOfModules

end
