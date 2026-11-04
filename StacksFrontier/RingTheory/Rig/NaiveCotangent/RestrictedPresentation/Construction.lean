module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.PresentationIndependence
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings

/-!
# Restricted power series presentations and their naive cotangent complex

The `A`-algebra structure on `A{x₁, …, x_r}`, presentations `B = A{x₁, …, x_r} / J` of a
topological `A`-algebra by a closed ideal, the complex `J / J² → ⨁ i, B dxᵢ` attached to a
presentation together with its construction, and the existence of a presentation for an adic,
topologically finite type arrow. Part of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory
open ComplexShape (upIntRelNegOneZero)

universe u v

namespace TopologicalRing

/-! ### Restricted power series as an `A`-algebra -/

/-- `A{x_i}` is an `A`-algebra through the coefficient map. -/
public instance restrictedPowerSeriesAlgebra (A : Type u) [CommRing A] [TopologicalSpace A]
    (σ : Type v) : Algebra A (RestrictedPowerSeries A σ) :=
  (coeffToRestrictedPowerSeries A σ).toAlgebra

/-- The structure map `A → A{x_i}` is the coefficient map. -/
public theorem algebraMap_restrictedPowerSeries (A : Type u) [CommRing A] [TopologicalSpace A]
    (σ : Type v) :
    algebraMap A (RestrictedPowerSeries A σ) = coeffToRestrictedPowerSeries A σ :=
  rfl


end TopologicalRing

namespace Rig

open TopologicalRing

-- `Algebra.Extension.ofSurjective` has to reduce at `implicit` transparency for the ring of
-- `RestrictedPowerSeriesPresentation.extension` to be recognised as the restricted power series
-- ring; without it `rw` and `simp` decline on goals that print as well-typed.
attribute [local implicit_reducible] Algebra.Extension.ofSurjective
  AdicFiniteTypeAlgebra.of


/-- `-2` precedes `-1` in the cochain-complex indexing of `ℤ`. -/
public theorem upRel_negTwo_negOne : (ComplexShape.up ℤ).Rel (-2) (-1) := by norm_num

/-- `0` precedes `1` in the cochain-complex indexing of `ℤ`. -/
public theorem upRel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by norm_num

/-! ### Presentations by restricted power series -/

/-- A presentation `B = A{x₁, …, x_r} / J` of `B` as a topological `A`-algebra: a closed ideal
`J` of a restricted power series ring in finitely many variables, together with a ring
equivalence from the quotient to `B` which is a homeomorphism and is compatible with the
coefficient maps. These are exactly the witnesses of condition (7) of Tag 0GBW. -/
@[ega "I 10.13.1" "(c)"]
public structure RestrictedPowerSeriesPresentation
    (A : Type u) [CommRing A] [TopologicalSpace A]
    (B : Type v) [CommRing B] [TopologicalSpace B] [Algebra A B] where
  /-- The number `r` of variables. -/
  variableCount : ℕ
  /-- The ideal `J`. -/
  ideal : Ideal (RestrictedPowerSeries A (Fin variableCount))
  /-- `J` is closed. -/
  ideal_isClosed : IsClosed (ideal : Set (RestrictedPowerSeries A (Fin variableCount)))
  /-- The quotient is `B`. -/
  quotientEquiv : (RestrictedPowerSeries A (Fin variableCount) ⧸ ideal) ≃+* B
  /-- The identification is continuous. -/
  continuous_quotientEquiv : Continuous quotientEquiv
  /-- Its inverse is continuous. -/
  continuous_quotientEquiv_symm : Continuous quotientEquiv.symm
  /-- The identification is one of `A`-algebras. -/
  quotientEquiv_comp :
    quotientEquiv.toRingHom.comp
        ((Ideal.Quotient.mk ideal).comp (coeffToRestrictedPowerSeries A (Fin variableCount))) =
      algebraMap A B

section Presentation

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]

/-- A presentation by restricted power series is the same thing as a witness of condition (7)
of Tag 0GBW for the structure map of `B`. -/
public theorem nonempty_restrictedPowerSeriesPresentation_iff :
    Nonempty (RestrictedPowerSeriesPresentation A B) ↔
      HasRestrictedPowerSeriesPresentation (algebraMap A B) :=
  ⟨fun ⟨P⟩ => ⟨P.variableCount, P.ideal, P.ideal_isClosed, P.quotientEquiv,
      P.continuous_quotientEquiv, P.continuous_quotientEquiv_symm, P.quotientEquiv_comp⟩,
   fun ⟨n, K, hK, e, he, he', hcomp⟩ => ⟨⟨n, K, hK, e, he, he', hcomp⟩⟩⟩

namespace RestrictedPowerSeriesPresentation

variable (P : RestrictedPowerSeriesPresentation A B)

/-- The restricted power series ring `A{x₁, …, x_r}` of a presentation. -/
public abbrev ring := RestrictedPowerSeries A (Fin P.variableCount)

/-- The variable `xᵢ`. -/
public abbrev var (i : Fin P.variableCount) : P.ring :=
  polynomialToRestrictedPowerSeries A (Fin P.variableCount) (MvPolynomial.X i)

/-- The surjection `A{x₁, …, x_r} → B` of a presentation. -/
@[implicit_reducible] public def toAlgHom : P.ring →ₐ[A] B :=
  { P.quotientEquiv.toRingHom.comp (Ideal.Quotient.mk P.ideal) with
    commutes' := fun a => DFunLike.congr_fun P.quotientEquiv_comp a }

/-- The map `A{x₁, …, x_r} → B` of a presentation is surjective. -/
public theorem toAlgHom_surjective : Function.Surjective P.toAlgHom := by
  intro b
  obtain ⟨q, rfl⟩ := P.quotientEquiv.surjective b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨p, rfl⟩

/-- The extension `A{x₁, …, x_r} → B` whose cotangent module is `J / J²`. -/
@[implicit_reducible] public def extension : Algebra.Extension A B :=
  Algebra.Extension.ofSurjective P.toAlgHom P.toAlgHom_surjective

/-- The ideal `J` viewed as the kernel of the presentation. -/
public abbrev ker : Ideal P.ring := RingHom.ker P.toAlgHom.toRingHom

end RestrictedPowerSeriesPresentation

/-! ### The complex -/

open RestrictedPowerSeriesPresentation in
/-- The data of the completed naive cotangent complex `J / J² → ⨁ i, B dxᵢ` belonging to a
fixed presentation `P`. The maps `partialDeriv i` are the formal partial derivatives, pinned
as the unique continuous derivations of `A{x₁, …, x_r}` extending the partial derivatives of
polynomials, and `differential_mk` pins the differential by the source's formula
`dg = ∑ (∂g/∂xᵢ) dxᵢ`. -/
public structure RestrictedNaiveCotangentComplex
    (P : RestrictedPowerSeriesPresentation A B) where
  /-- The formal partial derivative `∂/∂xᵢ`. -/
  partialDeriv : Fin P.variableCount → Derivation A P.ring P.ring
  /-- It is continuous. -/
  partialDeriv_continuous : ∀ i, Continuous (partialDeriv i)
  /-- It extends the partial derivative of polynomials. -/
  partialDeriv_polynomial : ∀ (i : Fin P.variableCount)
      (f : MvPolynomial (Fin P.variableCount) A),
    partialDeriv i (polynomialToRestrictedPowerSeries A (Fin P.variableCount) f) =
      polynomialToRestrictedPowerSeries A (Fin P.variableCount) (MvPolynomial.pderiv i f)
  /-- These two properties determine it. -/
  partialDeriv_unique : ∀ (i : Fin P.variableCount) (D : Derivation A P.ring P.ring),
    Continuous D →
    (∀ f : MvPolynomial (Fin P.variableCount) A,
      D (polynomialToRestrictedPowerSeries A (Fin P.variableCount) f) =
        polynomialToRestrictedPowerSeries A (Fin P.variableCount) (MvPolynomial.pderiv i f)) →
    D = partialDeriv i
  /-- The differential `J / J² → ⨁ i, B dxᵢ`. -/
  differential : P.extension.Cotangent →ₗ[B] (Fin P.variableCount → B)
  /-- It sends the class of `g ∈ J` to `(∂g/∂xᵢ)ᵢ`. -/
  differential_mk : ∀ g : P.extension.ker,
    differential (Algebra.Extension.Cotangent.mk g) =
      fun i => P.toAlgHom (partialDeriv i g.1)

namespace RestrictedNaiveCotangentComplex

variable {P : RestrictedPowerSeriesPresentation A B}

/-- The data of the complex is determined by the presentation: nothing in
`RestrictedNaiveCotangentComplex` is left free. -/
public theorem ext (K L : RestrictedNaiveCotangentComplex P) :
    K.partialDeriv = L.partialDeriv ∧ K.differential = L.differential := by
  have hd : K.partialDeriv = L.partialDeriv := by
    funext i
    exact L.partialDeriv_unique i (K.partialDeriv i) (K.partialDeriv_continuous i)
      (K.partialDeriv_polynomial i)
  refine ⟨hd, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  rw [K.differential_mk, L.differential_mk, hd]

/-- There is at most one completed naive cotangent complex of a given presentation: the
data of `RestrictedNaiveCotangentComplex` is determined by its own fields, so asserting
that one exists already pins which complex is meant. -/
public instance subsingleton : Subsingleton (RestrictedNaiveCotangentComplex P) where
  allEq K L := by
    obtain ⟨pd, hc, hp, hu, dd, hdm⟩ := K
    obtain ⟨pd', hc', hp', hu', dd', hdm'⟩ := L
    have hpd : pd = pd' :=
      (ext ⟨pd, hc, hp, hu, dd, hdm⟩ ⟨pd', hc', hp', hu', dd', hdm'⟩).1
    have hdd : dd = dd' :=
      (ext ⟨pd, hc, hp, hu, dd, hdm⟩ ⟨pd', hc', hp', hu', dd', hdm'⟩).2
    subst hpd
    subst hdd
    rfl

/-- The universe-lifted copy of the conormal module `J / J²`. -/
public abbrev LiftedCotangent := ULift.{v} P.extension.Cotangent

/-- The universe-lifted free module `⨁ i, B dxᵢ`. -/
public abbrev LiftedDifferentials := ULift.{u} (Fin P.variableCount → B)

/-- The differential on the universe-lifted terms. -/
public def liftedDifferential (K : RestrictedNaiveCotangentComplex P) :
    LiftedCotangent (P := P) →ₗ[B] LiftedDifferentials (P := P) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    (K.differential.comp ULift.moduleEquiv.toLinearMap)

/-- The lifted differential acts on `ULift.up x` as the differential on `x`. -/
@[simp]
public theorem liftedDifferential_up (K : RestrictedNaiveCotangentComplex P)
    (x : P.extension.Cotangent) :
    K.liftedDifferential (ULift.up x) = ULift.up (K.differential x) :=
  rfl

/-- `NL^∧_{B/A}` as a cochain complex of `B`-modules, with `J / J²` in degree `-1` and
`⨁ i, B dxᵢ` in degree `0`. -/
public def cochainComplex (K : RestrictedNaiveCotangentComplex P) :
    CochainComplex (ModuleCat.{max u v} B) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom K.liftedDifferential)
    upIntRelNegOneZero

/-- Identification of the degree `-1` term with the lifted conormal module `J / J²`. -/
public def degreeNegOneIso (K : RestrictedNaiveCotangentComplex P) :
    K.cochainComplex.X (-1) ≅ ModuleCat.of B (LiftedCotangent (P := P)) := by
  simpa [cochainComplex] using
    (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom K.liftedDifferential)
      upIntRelNegOneZero)

/-- Identification of the degree `0` term with the lifted free module `⨁ i, B dxᵢ`. -/
public def degreeZeroIso (K : RestrictedNaiveCotangentComplex P) :
    K.cochainComplex.X 0 ≅ ModuleCat.of B (LiftedDifferentials (P := P)) := by
  simpa [cochainComplex] using
    (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom K.liftedDifferential)
      upIntRelNegOneZero (by norm_num))

/-- Under the named term identifications, the differential from degree `-1` to degree `0` is
the lifted formal-derivative differential. -/
public theorem cochainComplex_d (K : RestrictedNaiveCotangentComplex P) :
    K.cochainComplex.d (-1) 0 =
      K.degreeNegOneIso.hom ≫ ModuleCat.ofHom K.liftedDifferential ≫ K.degreeZeroIso.inv := by
  simpa [cochainComplex, degreeNegOneIso, degreeZeroIso] using
    (HomologicalComplex.double_d (ModuleCat.ofHom K.liftedDifferential)
      upIntRelNegOneZero (by norm_num))

end RestrictedNaiveCotangentComplex

/-! ### The polynomial partial derivative on the defining topology -/

private theorem continuous_restrictedPolynomialPDeriv {A : Type u} [CommRing A]
    [TopologicalSpace A] {σ : Type v} (i : σ) :
    @Continuous (MvPolynomial σ A) (MvPolynomial σ A)
      (restrictedPolynomialTopology A σ) (restrictedPolynomialTopology A σ)
      (MvPolynomial.pderiv i) := by
  let R := MvPolynomial σ A
  let C : A →+* R := MvPolynomial.C
  let basis := restrictedPolynomialRingFilterBasis A σ
  let : TopologicalSpace R := restrictedPolynomialTopology A σ
  let : IsTopologicalRing R := restrictedPolynomialIsTopologicalRing A σ
  show Continuous (MvPolynomial.pderiv i)
  let d : Derivation A R R := MvPolynomial.pderiv i
  apply continuous_of_tendsto_nhds_zero d.toLinearMap.toAddMonoidHom
  apply (basis.toAddGroupFilterBasis.nhds_zero_hasBasis.tendsto_iff
    basis.toAddGroupFilterBasis.nhds_zero_hasBasis).mpr
  intro U hU
  change (∃ J : {J : Ideal A // IsOpen (J : Set A)},
    U = (J.1.map C).toAddSubgroup) at hU
  rcases hU with ⟨J, rfl⟩
  let K : Ideal R := J.1.map C
  have hK : K = Ideal.span (C '' (J.1 : Set A)) := by
    calc
      K = Ideal.map C (Ideal.span (J.1 : Set A)) := by simp [K]
      _ = Ideal.span (C '' (J.1 : Set A)) := Ideal.map_span C _
  refine ⟨(K : Set R), ?_, ?_⟩
  · exact ⟨J, rfl⟩
  · intro p hp
    change p ∈ K at hp
    show MvPolynomial.pderiv i p ∈ K
    rw [hK] at hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      rw [MvPolynomial.pderiv_C]
      exact K.zero_mem
    · exact K.zero_mem
    · intro x y hx hy hdx hdy
      simpa using K.add_mem hdx hdy
    · intro r x hx hdx
      show d (r * x) ∈ K
      rw [d.leibniz]
      have hxK : x ∈ K := by rw [hK]; exact hx
      exact K.add_mem (K.mul_mem_left _ hdx) (K.mul_mem_right _ hxK)

private noncomputable def restrictedPowerSeriesPDerivFun {σ : Type v} (i : σ) :
    RestrictedPowerSeries A σ → RestrictedPowerSeries A σ := by
  let R := MvPolynomial σ A
  let : TopologicalSpace R := restrictedPolynomialTopology A σ
  let : UniformSpace R := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.extension
    (polynomialToRestrictedPowerSeries A σ ∘
      (MvPolynomial.pderiv i : MvPolynomial σ A → MvPolynomial σ A))

private theorem uniformContinuous_restrictedPolynomialPDeriv {σ : Type v} (i : σ) :
    @UniformContinuous (MvPolynomial σ A) (MvPolynomial σ A)
      (restrictedPolynomialUniformSpace A σ) (restrictedPolynomialUniformSpace A σ)
      (MvPolynomial.pderiv i) := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  exact uniformContinuous_addMonoidHom_of_continuous
    (f := (MvPolynomial.pderiv i).toAddMonoidHom)
    (continuous_restrictedPolynomialPDeriv i)

private theorem restrictedPowerSeriesPDerivFun_polynomial {σ : Type v}
    (i : σ) (f : MvPolynomial σ A) :
    restrictedPowerSeriesPDerivFun i (polynomialToRestrictedPowerSeries A σ f) =
      polynomialToRestrictedPowerSeries A σ (MvPolynomial.pderiv i f) := by
  let R := MvPolynomial σ A
  let : TopologicalSpace R := restrictedPolynomialTopology A σ
  let : UniformSpace R := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.extension_coe
    (f := polynomialToRestrictedPowerSeries A σ ∘
      (MvPolynomial.pderiv i : MvPolynomial σ A → MvPolynomial σ A))
    ((UniformSpace.Completion.uniformContinuous_coe R).comp
      (uniformContinuous_restrictedPolynomialPDeriv i)) f

private theorem continuous_restrictedPowerSeriesPDerivFun {σ : Type v} (i : σ) :
    @Continuous (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)
      (restrictedPowerSeriesUniformSpace A σ).toTopologicalSpace
      (restrictedPowerSeriesUniformSpace A σ).toTopologicalSpace
      (restrictedPowerSeriesPDerivFun i) := by
  let R := MvPolynomial σ A
  let : TopologicalSpace R := restrictedPolynomialTopology A σ
  let : UniformSpace R := restrictedPolynomialUniformSpace A σ
  show Continuous (UniformSpace.Completion.extension
    (polynomialToRestrictedPowerSeries A σ ∘
      (MvPolynomial.pderiv i : MvPolynomial σ A → MvPolynomial σ A)))
  exact UniformSpace.Completion.continuous_extension

private noncomputable def restrictedPowerSeriesPDeriv {σ : Type v} (i : σ) :
    Derivation A (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ) := by
  let R := MvPolynomial σ A
  let : TopologicalSpace R := restrictedPolynomialTopology A σ
  let : UniformSpace R := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup R :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : IsUniformAddGroup (RestrictedPowerSeries A σ) := by
    change IsUniformAddGroup (UniformSpace.Completion R)
    infer_instance
  let : CommSemiring (RestrictedPowerSeries A σ) :=
    (inferInstance : CommRing (RestrictedPowerSeries A σ)).toCommSemiring
  let : Algebra A (RestrictedPowerSeries A σ) := restrictedPowerSeriesAlgebra A σ
  let : Module A (RestrictedPowerSeries A σ) :=
    Module.compHom (RestrictedPowerSeries A σ) (algebraMap A (RestrictedPowerSeries A σ))
  let : Module (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ) :=
    (inferInstance : Algebra (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)).toModule
  let d : RestrictedPowerSeries A σ → RestrictedPowerSeries A σ :=
    restrictedPowerSeriesPDerivFun i
  have hd : Continuous d := continuous_restrictedPowerSeriesPDerivFun i
  let L : RestrictedPowerSeries A σ →ₗ[A] RestrictedPowerSeries A σ := {
    toFun := d
    map_add' := by
      intro x y
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (hd.comp continuous_add)
          ((hd.comp continuous_fst).add (hd.comp continuous_snd))
      · intro p q
        change d (polynomialToRestrictedPowerSeries A σ p +
          polynomialToRestrictedPowerSeries A σ q) = _
        rw [← (polynomialToRestrictedPowerSeries A σ).map_add]
        change d (polynomialToRestrictedPowerSeries A σ (p + q)) =
          d (polynomialToRestrictedPowerSeries A σ p) +
            d (polynomialToRestrictedPowerSeries A σ q)
        change restrictedPowerSeriesPDerivFun i
            (polynomialToRestrictedPowerSeries A σ (p + q)) =
          restrictedPowerSeriesPDerivFun i (polynomialToRestrictedPowerSeries A σ p) +
            restrictedPowerSeriesPDerivFun i (polynomialToRestrictedPowerSeries A σ q)
        rw [restrictedPowerSeriesPDerivFun_polynomial i (p + q),
          restrictedPowerSeriesPDerivFun_polynomial i p,
          restrictedPowerSeriesPDerivFun_polynomial i q,
          (MvPolynomial.pderiv i).map_add]
        exact (polynomialToRestrictedPowerSeries A σ).map_add _ _
    map_smul' := by
      intro a x
      change d ((coeffToRestrictedPowerSeries A σ a) * x) =
        (coeffToRestrictedPowerSeries A σ a) * d x
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · exact isClosed_eq
          (hd.comp (continuous_const_mul (coeffToRestrictedPowerSeries A σ a)))
          ((continuous_const_mul (coeffToRestrictedPowerSeries A σ a)).comp hd)
      · intro p
        rw [show coeffToRestrictedPowerSeries A σ a =
          polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a) from rfl]
        change d (polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a) *
          polynomialToRestrictedPowerSeries A σ p) = _
        calc
          _ = d (polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a * p)) := by
            rw [(polynomialToRestrictedPowerSeries A σ).map_mul]
          _ = polynomialToRestrictedPowerSeries A σ
              ((MvPolynomial.pderiv i) (MvPolynomial.C a * p)) :=
            restrictedPowerSeriesPDerivFun_polynomial i _
          _ = polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a) *
              polynomialToRestrictedPowerSeries A σ ((MvPolynomial.pderiv i) p) := by
            rw [(MvPolynomial.pderiv i).leibniz]
            simp [map_mul]
          _ = polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a) *
              d (polynomialToRestrictedPowerSeries A σ p) := by
            simpa only [d] using congrArg
              (fun z => polynomialToRestrictedPowerSeries A σ (MvPolynomial.C a) * z)
              (restrictedPowerSeriesPDerivFun_polynomial i p).symm
  }
  refine @Derivation.mk' A (inferInstance : CommSemiring A)
    (RestrictedPowerSeries A σ) (inferInstance : CommSemiring (RestrictedPowerSeries A σ))
    (inferInstance : Algebra A (RestrictedPowerSeries A σ))
    (RestrictedPowerSeries A σ) (inferInstance : AddCancelCommMonoid (RestrictedPowerSeries A σ))
    (inferInstance : Module A (RestrictedPowerSeries A σ))
    (inferInstance : Module (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)) L ?_
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq (hd.comp continuous_mul)
      ((continuous_fst.smul (hd.comp continuous_snd)).add
        (continuous_snd.smul (hd.comp continuous_fst)))
  · intro p q
    change d (polynomialToRestrictedPowerSeries A σ p *
        polynomialToRestrictedPowerSeries A σ q) =
      polynomialToRestrictedPowerSeries A σ p *
          d (polynomialToRestrictedPowerSeries A σ q) +
        polynomialToRestrictedPowerSeries A σ q *
          d (polynomialToRestrictedPowerSeries A σ p)
    simp only [d]
    rw [← (polynomialToRestrictedPowerSeries A σ).map_mul,
      restrictedPowerSeriesPDerivFun_polynomial i (p * q),
      restrictedPowerSeriesPDerivFun_polynomial i q,
      restrictedPowerSeriesPDerivFun_polynomial i p,
      (MvPolynomial.pderiv i).leibniz]
    simp only [smul_eq_mul,
      (polynomialToRestrictedPowerSeries A σ).map_add,
      (polynomialToRestrictedPowerSeries A σ).map_mul]

/-- The `B`-linear map `J / J² → B` attached to a derivation `D` of the restricted power
series ring: it sends the class of `g ∈ J` to the image of `D g` in `B`.  This is the general
construction `Rig.cotangentMapOfDerivation` applied to the extension of the presentation. -/
private noncomputable def restrictedCotangentPartialDerivativeMap
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (P : RestrictedPowerSeriesPresentation A B)
    (D : Derivation A P.ring P.ring) : P.extension.Cotangent →ₗ[B] B :=
  cotangentMapOfDerivation P.extension D

/-- On the class of `g ∈ J`, the map attached to `D` is the image of `D g` under the presenting
surjection. -/
private theorem restrictedCotangentPartialDerivativeMap_mk
    {A : Type u} [CommRing A] [TopologicalSpace A]
    {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]
    (P : RestrictedPowerSeriesPresentation A B)
    (D : Derivation A P.ring P.ring) (g : P.extension.ker) :
    restrictedCotangentPartialDerivativeMap P D (Algebra.Extension.Cotangent.mk g) =
      P.toAlgHom (D g.1) :=
  (cotangentMapOfDerivation_mk P.extension D g).trans rfl

/-- **Stacks Project, Remark 88.14.3 (Tag 0GBX).** For a presentation
`B = A{x₁, …, x_r} / J` of `B` as a topological `A`-algebra, the completed naive cotangent
complex `NL^∧_{B/A} = (J / J² → ⨁ i, B dxᵢ)` exists: the formal partial derivatives of
`A{x₁, …, x_r}` exist, and the differential sending the class of a restricted power series
`g ∈ J` to the tuple of its formal partial derivatives is well defined. Since
`RestrictedNaiveCotangentComplex P` is a subsingleton, this determines the complex. -/
@[stacks 0GBX]
public theorem nonempty_restrictedNaiveCotangentComplex
    (P : RestrictedPowerSeriesPresentation A B) :
    Nonempty (RestrictedNaiveCotangentComplex P) := by
  refine ⟨{
    partialDeriv := restrictedPowerSeriesPDeriv
    partialDeriv_continuous := fun i => continuous_restrictedPowerSeriesPDerivFun i
    partialDeriv_polynomial := fun i f => restrictedPowerSeriesPDerivFun_polynomial i f
    partialDeriv_unique := ?_
    differential := LinearMap.pi (fun i =>
      restrictedCotangentPartialDerivativeMap P (restrictedPowerSeriesPDeriv i))
    differential_mk := ?_ }⟩
  · intro i D hD hpoly
    let R := MvPolynomial (Fin P.variableCount) A
    let basis := restrictedPolynomialRingFilterBasis A (Fin P.variableCount)
    let : TopologicalSpace R := restrictedPolynomialTopology A (Fin P.variableCount)
    let : UniformSpace R := restrictedPolynomialUniformSpace A (Fin P.variableCount)
    let : IsUniformAddGroup R := basis.toAddGroupFilterBasis.isUniformAddGroup
    have hd : DenseRange (polynomialToRestrictedPowerSeries A (Fin P.variableCount)) :=
      UniformSpace.Completion.denseRange_coe
    have hfun : ⇑D = ⇑(restrictedPowerSeriesPDeriv i) :=
      hd.equalizer hD (continuous_restrictedPowerSeriesPDerivFun i) (by
        funext f
        show D (polynomialToRestrictedPowerSeries A (Fin P.variableCount) f) =
          restrictedPowerSeriesPDeriv i
            (polynomialToRestrictedPowerSeries A (Fin P.variableCount) f)
        rw [hpoly]
        show (polynomialToRestrictedPowerSeries A (Fin P.variableCount))
            (MvPolynomial.pderiv i f) =
          restrictedPowerSeriesPDerivFun i
            (polynomialToRestrictedPowerSeries A (Fin P.variableCount) f)
        exact (restrictedPowerSeriesPDerivFun_polynomial i f).symm)
    exact Derivation.ext (congrFun hfun)
  · intro g
    ext i
    simpa only [LinearMap.pi_apply] using
      restrictedCotangentPartialDerivativeMap_mk P (restrictedPowerSeriesPDeriv i) g

/-- The completed naive cotangent complex `NL^∧_{B/A} = (J / J² → ⨁ i, B dxᵢ)` of a
presentation `B = A{x₁, …, x_r} / J`. It is the unique inhabitant of
`RestrictedNaiveCotangentComplex P`, whose fields pin the formal partial derivatives and the
differential; see `RestrictedNaiveCotangentComplex.ext` and the `Subsingleton` instance. -/
public def restrictedNaiveCotangentComplex (P : RestrictedPowerSeriesPresentation A B) :
    RestrictedNaiveCotangentComplex P :=
  Classical.choice (nonempty_restrictedNaiveCotangentComplex P)

end Presentation

/-! ### Existence of a presentation -/

section Existence

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [IsLinearTopology B B] [Algebra A B]

/-- **Stacks Project, Tag 0GBX.** An arrow of `WAdm^{adic*}` which is adic and topologically
of finite type can be written as `B = A{x₁, …, x_r} / J`, so that the construction applies to
it. This is condition (7) of Lemma 0GBW. -/
@[stacks 0GBX "every adic, topologically finite type arrow has a presentation"]
public theorem nonempty_restrictedPowerSeriesPresentation
    (hcont : Continuous (algebraMap A B))
    (hA : TopologicalRing.IsAdic A) (hB : TopologicalRing.IsAdic B)
    (hAfg : ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (hBfg : ∃ J : Ideal B, TopologicalRing.IsIdealOfDefinition J ∧ J.FG)
    (hadic : _root_.RingHom.IsAdic (algebraMap A B))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B)) :
    Nonempty (RestrictedPowerSeriesPresentation A B) := by
  rw [nonempty_restrictedPowerSeriesPresentation_iff]
  have h : _root_.RingHom.IsAdic (algebraMap A B) ∧
      TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B) := ⟨hadic, hft⟩
  exact ((adicFiniteType_tfae (algebraMap A B) hcont hA hB hAfg hBfg).out 1 7).mp h

end Existence

end Rig

end
