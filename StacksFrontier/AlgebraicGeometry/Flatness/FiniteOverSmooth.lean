module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.MvPolynomial.Localization
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFiniteAffineSpace

/-!
# Finite-over-smooth structure of a finite-type morphism at a point

A morphism locally of finite type is, étale locally on source and target, the composition of a
finite morphism with a smooth morphism whose relative dimension is the local dimension of the
original fibre, and the residue field of the intermediate point is purely transcendental over the
residue field of the base point ([Stacks, Tag 052E]).

This module proves, on affine charts, the identification of the scheme-theoretic fibre dimension
with the ring-theoretic relative dimension, and the identification of the residue field of the
ideal `(𝔭, x_i : i ∈ s)` of a polynomial ring as a purely transcendental extension of the residue
field of `𝔭`. It also shows that affine `n`-space over an affine scheme is smooth of relative
dimension `n`.

## Main results

* `Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt` identifies the local
  dimension of a scheme-theoretic fibre with `Algebra.relativeDimensionAt` for the induced map
  of coordinate rings on a compatible pair of affine charts.
* `Stacks.Flatness.purelyTranscendental_of_mvPolynomialRingHom` is a criterion for a field
  extension to be purely transcendental: it suffices that the big field be generated, as a
  field, by the image of an injective ring map from a polynomial ring over a domain whose
  fraction field is the small field.
* `Stacks.Flatness.purelyTranscendental_residueField_sup_map_C_span_X` applies that criterion
  to the ideal `(𝔭, x_i : i ∈ s)` of `MvPolynomial σ A`: its residue field is purely
  transcendental over the residue field of `𝔭`.
* `Stacks.Flatness.comap_C_sup_map_C_span_X` and `Stacks.Flatness.isPrime_sup_map_C_span_X`
  record that this ideal is prime and contracts to `𝔭` along the constants.
* `Stacks.Flatness.isStandardSmoothOfRelativeDimension_mvPolynomial` and
  `Stacks.Flatness.smoothOfRelativeDimension_SpecMap_C` state that a polynomial ring in `n`
  variables is standard smooth of relative dimension `n` over its coefficient ring, and that
  affine `n`-space over an affine scheme is therefore smooth of relative dimension `n`.

## Implementation notes

The scheme-side fibre dimension is `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, where
`AlgebraicGeometry.Scheme.Hom.asFiber` is the canonical representative of `x` in the fibre through
it.

The criterion `Stacks.Flatness.purelyTranscendental_of_mvPolynomialRingHom` is stated with every
ring behind a variable rather than with the ideal `(𝔭, x_i : i ∈ s)` written out; writing the ideal
out in the statement makes the elaborator unfold the residue field at every occurrence and exhausts
the heartbeat budget.

The algebra structure relating the two residue fields is taken as a hypothesis together with its
compatibility with the constants, rather than being fixed to one particular construction, so
that a consumer holding any compatible structure — for instance one obtained from a morphism of
schemes — can apply the result directly.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
* [Stacks Project, Tag 0520](https://stacks.math.columbia.edu/tag/0520)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

universe u

namespace Stacks.Flatness

open AlgebraicGeometry

/-! ### Fibre dimension on affine charts -/

/-- On a compatible pair of affine charts `V ≤ f ⁻¹ᵁ U`, the local dimension of the
scheme-theoretic fibre of `f` at a point `x ∈ V` equals the relative dimension of the algebra
`Γ(X, V)` over `Γ(S, U)` at the prime of `Γ(X, V)` corresponding to `x`. -/
alias topologicalKrullDimAt_fiber_eq_relativeDimensionAt :=
  AlgebraicGeometry.fiberDimensionAt_eq_relativeDimensionAt_chart

/-! ### Purely transcendental residue fields of the ideal `(𝔭, x_i : i ∈ s)` -/

section PurelyTranscendental

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **A criterion for a purely transcendental extension.** Let `D` be a domain with fraction
field `k`, let `L` be a field extension of `k`, and let `e` be an injective ring map from a
polynomial ring over `D` to `L` which carries constants to the image of `k` in the expected way
and whose image generates `L` as a field. Then `L` is purely transcendental over `k`, the
variables forming a transcendence basis. -/
theorem purelyTranscendental_of_mvPolynomialRingHom {D k L ι : Type*} [CommRing D] [IsDomain D]
    [Field k] [Field L] [Algebra D k] [IsFractionRing D k] [Algebra k L]
    (e : MvPolynomial ι D →+* L) (he : Function.Injective e)
    (hC : ∀ d : D, e (C d) = algebraMap k L (algebraMap D k d))
    (hdiv : ∀ y : L, ∃ a b : MvPolynomial ι D, y = e a / e b) :
    PurelyTranscendental k L := by
  classical
  set xf : ι → L := fun j => e (X j) with hxf
  have hcomp : ∀ p : MvPolynomial ι D,
      aeval xf (algebraMap (MvPolynomial ι D) (MvPolynomial ι k) p) = e p := by
    have h := MvPolynomial.ringHom_ext
      (f := (aeval xf : MvPolynomial ι k →ₐ[k] L).toRingHom.comp
        (algebraMap (MvPolynomial ι D) (MvPolynomial ι k)))
      (g := e)
      (fun d => by
        simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, hC])
      (fun j => by
        simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hxf])
    exact fun p => congrArg (fun φ : MvPolynomial ι D →+* L => φ p) h
  have hmem : ∀ p : MvPolynomial ι D, e p ∈ IntermediateField.adjoin k (Set.range xf) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C d => rw [hC d]; exact (IntermediateField.adjoin k (Set.range xf)).algebraMap_mem _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  refine PurelyTranscendental.of_algebraicIndependent (x := xf) ?_ ?_
  · rw [algebraicIndependent_iff]
    intro p hp
    obtain ⟨⟨q, m⟩, hqm⟩ := IsLocalization.surj ((nonZeroDivisors D).map (C (σ := ι))) p
    have h1 : e q = 0 := by rw [← hcomp q, ← hqm, map_mul, hp, zero_mul]
    have h2 : q = 0 := he (by rw [h1, map_zero])
    rw [h2, map_zero] at hqm
    have hu := IsLocalization.map_units (M := (nonZeroDivisors D).map (C (σ := ι)))
      (MvPolynomial ι k) m
    exact hu.mul_left_eq_zero.mp hqm
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, b, rfl⟩ := hdiv y
    exact div_mem (hmem a) (hmem b)

end PurelyTranscendental

section StandardIdeal

variable {A : Type u} [CommRing A] {σ : Type*}

open scoped Classical in
/-- The map from `MvPolynomial σ A` to the polynomial ring over `A ⧸ 𝔭` on the variables
outside `s`, sending a constant to its class and killing the variables in `s`. Its kernel is
the ideal `(𝔭, x_i : i ∈ s)`. -/
private noncomputable def toQuotientOutside (P : Ideal A) (s : Set σ) :
    MvPolynomial σ A →+* MvPolynomial {i : σ // i ∉ s} (A ⧸ P) :=
  eval₂Hom (C.comp (Ideal.Quotient.mk P)) fun i => if h : i ∈ s then 0 else X ⟨i, h⟩

private lemma toQuotientOutside_C (P : Ideal A) (s : Set σ) (a : A) :
    toQuotientOutside P s (C a) = C (Ideal.Quotient.mk P a) := by
  simp [toQuotientOutside]

private lemma toQuotientOutside_X_mem (P : Ideal A) (s : Set σ) {i : σ} (h : i ∈ s) :
    toQuotientOutside P s (X i) = 0 := by
  simp [toQuotientOutside, h]

private lemma toQuotientOutside_X_notMem (P : Ideal A) (s : Set σ) {i : σ} (h : i ∉ s) :
    toQuotientOutside P s (X i) = X ⟨i, h⟩ := by
  simp [toQuotientOutside, h]

/-- A constant coming from `𝔭` lies in the ideal `(𝔭, x_i : i ∈ s)`. -/
theorem C_mem_sup_map_C_span_X (P : Ideal A) (s : Set σ) {a : A} (ha : a ∈ P) :
    C a ∈ (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)) :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

/-- A variable indexed by `s` lies in the ideal `(𝔭, x_i : i ∈ s)`. -/
theorem X_mem_sup_map_C_span_X (P : Ideal A) (s : Set σ) {i : σ} (hi : i ∈ s) :
    X i ∈ (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)) :=
  Ideal.mem_sup_right (Ideal.subset_span (Set.mem_image_of_mem _ hi))

private lemma le_ker_toQuotientOutside (P : Ideal A) (s : Set σ) :
    (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)) ≤
      RingHom.ker (toQuotientOutside P s) := by
  refine sup_le ?_ (Ideal.span_le.mpr ?_)
  · refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    simp only [Ideal.mem_comap, RingHom.mem_ker, toQuotientOutside_C]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · rintro _ ⟨i, hi, rfl⟩
    exact RingHom.mem_ker.mpr (toQuotientOutside_X_mem P s hi)

/-- The inverse of `Stacks.Flatness.toQuotientOutside` on the quotient by `(𝔭, x_i : i ∈ s)`. -/
private noncomputable def ofQuotientOutside (P : Ideal A) (s : Set σ) :
    MvPolynomial {i : σ // i ∉ s} (A ⧸ P) →+*
      MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s)) :=
  eval₂Hom (Ideal.Quotient.lift P ((Ideal.Quotient.mk _).comp C) fun _ ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (C_mem_sup_map_C_span_X P s ha))
    fun j => Ideal.Quotient.mk _ (X j.1)

private lemma ofQuotientOutside_C (P : Ideal A) (s : Set σ) (a : A) :
    ofQuotientOutside P s (C (Ideal.Quotient.mk P a)) = Ideal.Quotient.mk _ (C a) := by
  simp [ofQuotientOutside]

private lemma ofQuotientOutside_X (P : Ideal A) (s : Set σ) (j : {i : σ // i ∉ s}) :
    ofQuotientOutside P s (X j) = Ideal.Quotient.mk _ (X j.1) := by
  simp [ofQuotientOutside]

/-- `Stacks.Flatness.toQuotientOutside` descends to the quotient by `(𝔭, x_i : i ∈ s)`. -/
private noncomputable def quotientOutsideHom (P : Ideal A) (s : Set σ) :
    (MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s))) →+*
      MvPolynomial {i : σ // i ∉ s} (A ⧸ P) :=
  Ideal.Quotient.lift _ (toQuotientOutside P s) fun _ hz => le_ker_toQuotientOutside P s hz

private lemma quotientOutsideHom_mk (P : Ideal A) (s : Set σ) (p : MvPolynomial σ A) :
    quotientOutsideHom P s (Ideal.Quotient.mk _ p) = toQuotientOutside P s p := rfl

/-- **The quotient by `(𝔭, x_i : i ∈ s)` is a polynomial ring.** The quotient of
`MvPolynomial σ A` by the ideal generated by a prime `𝔭 ⊆ A` and the variables indexed by `s` is
the polynomial ring over `A ⧸ 𝔭` on the variables indexed by the complement of `s`. -/
private noncomputable def quotientOutsideEquiv (P : Ideal A) (s : Set σ) :
    (MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s))) ≃+*
      MvPolynomial {i : σ // i ∉ s} (A ⧸ P) :=
  RingEquiv.ofRingHom (quotientOutsideHom P s) (ofQuotientOutside P s)
    (MvPolynomial.ringHom_ext
      (fun a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        simp only [RingHom.comp_apply, ofQuotientOutside_C, quotientOutsideHom_mk,
          toQuotientOutside_C, RingHom.id_apply])
      (fun j => by
        simp only [RingHom.comp_apply, ofQuotientOutside_X, quotientOutsideHom_mk,
          toQuotientOutside_X_notMem P s j.2, RingHom.id_apply]))
    (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
      (fun a => by
        simp only [RingHom.comp_apply, quotientOutsideHom_mk, toQuotientOutside_C,
          ofQuotientOutside_C, RingHom.id_apply])
      (fun i => by
        by_cases h : i ∈ s
        · simp only [RingHom.comp_apply, quotientOutsideHom_mk, toQuotientOutside_X_mem P s h,
            map_zero, RingHom.id_apply]
          exact (Ideal.Quotient.eq_zero_iff_mem.mpr (X_mem_sup_map_C_span_X P s h)).symm
        · simp only [RingHom.comp_apply, quotientOutsideHom_mk,
            toQuotientOutside_X_notMem P s h, ofQuotientOutside_X, RingHom.id_apply])))

/-- The ideal `(𝔭, x_i : i ∈ s)` of `MvPolynomial σ A` contracts to `𝔭` along the constants. -/
theorem comap_C_sup_map_C_span_X (P : Ideal A) (s : Set σ) :
    (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).comap C = P := by
  ext a
  simp only [Ideal.mem_comap]
  refine ⟨fun ha => ?_, C_mem_sup_map_C_span_X P s⟩
  have h : toQuotientOutside P s (C a) = 0 := le_ker_toQuotientOutside P s ha
  rwa [toQuotientOutside_C, MvPolynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h

/-- The ideal `(𝔭, x_i : i ∈ s)` of `MvPolynomial σ A` is prime when `𝔭` is. -/
instance isPrime_sup_map_C_span_X (P : Ideal A) [P.IsPrime] (s : Set σ) :
    (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  have : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  exact (quotientOutsideEquiv P s).toMulEquiv.isDomain _

/-- The embedding of the polynomial ring over `A ⧸ 𝔭` on the variables outside `s` into the
residue field of the ideal `(𝔭, x_i : i ∈ s)`. -/
private noncomputable def residueEmbedding (P : Ideal A) [P.IsPrime] (s : Set σ) :
    MvPolynomial {i : σ // i ∉ s} (A ⧸ P) →+*
      (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).ResidueField :=
  (algebraMap (MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s)))
    _).comp (quotientOutsideEquiv P s).symm.toRingHom

private lemma residueEmbedding_injective (P : Ideal A) [P.IsPrime] (s : Set σ) :
    Function.Injective (residueEmbedding P s) :=
  (Ideal.injective_algebraMap_quotient_residueField _).comp
    (quotientOutsideEquiv P s).symm.injective

private lemma residueEmbedding_quotientOutsideEquiv (P : Ideal A) [P.IsPrime] (s : Set σ)
    (z : MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s))) :
    residueEmbedding P s (quotientOutsideEquiv P s z) = algebraMap _ _ z := by
  change algebraMap _ _ ((quotientOutsideEquiv P s).symm (quotientOutsideEquiv P s z)) = _
  rw [RingEquiv.symm_apply_apply]

private lemma residueEmbedding_C (P : Ideal A) [P.IsPrime] (s : Set σ) (a : A) :
    residueEmbedding P s (C (Ideal.Quotient.mk P a)) =
      algebraMap (MvPolynomial σ A) _ (C a) := by
  rw [← toQuotientOutside_C P s a]
  exact residueEmbedding_quotientOutsideEquiv P s (Ideal.Quotient.mk _ (C a))

/-- **The residue field of `(𝔭, x_i : i ∈ s)` is purely transcendental over `κ(𝔭)`.** For a
prime `𝔭` of `A` and a set `s` of variables, the residue field of the prime
`(𝔭, x_i : i ∈ s)` of `MvPolynomial σ A` is purely transcendental over the residue field of
`𝔭`, the variables outside `s` forming a transcendence basis.

The algebra structure on the two residue fields is a hypothesis, required only to be compatible
with the constants; any structure induced by the inclusion of the constants satisfies this. -/
theorem purelyTranscendental_residueField_sup_map_C_span_X (P : Ideal A) [P.IsPrime] (s : Set σ)
    [Algebra P.ResidueField
      (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).ResidueField]
    (hcompat : ∀ a : A,
      algebraMap P.ResidueField
          (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).ResidueField
          (algebraMap A P.ResidueField a) =
        algebraMap (MvPolynomial σ A)
          (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).ResidueField (C a)) :
    PurelyTranscendental P.ResidueField
      (Ideal.map C P ⊔ Ideal.span (X '' s) : Ideal (MvPolynomial σ A)).ResidueField := by
  refine purelyTranscendental_of_mvPolynomialRingHom (residueEmbedding P s)
    (residueEmbedding_injective P s) (fun d => ?_) (fun y => ?_)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [residueEmbedding_C, Ideal.algebraMap_quotient_residueField_mk, hcompat a]
  · obtain ⟨z₁, z₂, -, rfl⟩ := IsFractionRing.div_surjective
      (A := MvPolynomial σ A ⧸ (Ideal.map C P ⊔ Ideal.span (X '' s))) y
    exact ⟨quotientOutsideEquiv P s z₁, quotientOutsideEquiv P s z₂, by
      rw [residueEmbedding_quotientOutsideEquiv, residueEmbedding_quotientOutsideEquiv]⟩

end StandardIdeal

/-! ### Affine space over an affine base is smooth of its relative dimension -/

section AffineSpace

/-- The presentation of the polynomial ring `MvPolynomial ι R` as an `R`-algebra on the variables
`ι` with no relations. -/
private noncomputable def mvPolynomialPresentation (R : Type u) [CommRing R] (ι : Type*) :
    Algebra.Presentation R (MvPolynomial ι R) ι PEmpty.{1} where
  __ := Algebra.Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp [Algebra.Generators.ker_mvPolynomial]

/-- `Stacks.Flatness.mvPolynomialPresentation` as a pre-submersive presentation; the empty map
from the relations to the variables is injective. -/
private noncomputable def mvPolynomialPreSubmersivePresentation (R : Type u) [CommRing R]
    (ι : Type*) :
    Algebra.PreSubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  __ := mvPolynomialPresentation R ι
  map := PEmpty.elim
  map_inj := fun a => a.elim

/-- `Stacks.Flatness.mvPolynomialPresentation` is submersive. -/
private noncomputable def mvPolynomialSubmersivePresentation (R : Type u) [CommRing R]
    (ι : Type*) :
    Algebra.SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  __ := mvPolynomialPreSubmersivePresentation R ι
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Matrix.det_isEmpty, map_one]
    exact isUnit_one

/-- **A polynomial ring in `n` variables is standard smooth of relative dimension `n`.** -/
theorem isStandardSmoothOfRelativeDimension_mvPolynomial (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) :=
  (mvPolynomialSubmersivePresentation R (Fin n)).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

/-- **Affine `n`-space over an affine scheme is smooth of relative dimension `n`.** The
structure morphism `Spec (R[x_1, …, x_n]) ⟶ Spec R`, that is `Spec.map` of the inclusion of the
constants, is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_SpecMap_C (R : CommRingCat.{u}) (n : ℕ) :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact MvPolynomial.algebraMap_eq (R := (R : Type u)) (σ := Fin n) ▸
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr
      (isStandardSmoothOfRelativeDimension_mvPolynomial R n)

end AffineSpace

end Stacks.Flatness

end
