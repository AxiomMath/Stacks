module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Jacobson.Nullstellensatz
public import StacksFrontier.RingTheory.Nagata.PthRoot
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.AdicBasic
public import StacksFrontier.RingTheory.Rig.ClosedPoint
public import StacksFrontier.RingTheory.Rig.Flat
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import StacksFrontier.RingTheory.GRing.Criteria
import StacksFrontier.Topology.Algebra.AdicTopology.QuotientAdic

/-!
# Regularity at a rig-closed point

Let `A` be a Noetherian adic topological ring and `p` a rig-closed prime of `A`.  The base
change of the restricted power series ring `A⟨x₁, …, x_n⟩` along `A → A ⧸ p` is canonically
the restricted power series ring over `A ⧸ p`, the canonical map `A ⧸ p → A⟨x⟩ ⊗_A (A ⧸ p)`
is a regular ring homomorphism, and the fibre of `A⟨x⟩` at `p` is geometrically regular over
the residue field of `p`.  The regularity statement rests on the quotient `A ⧸ p` being
excellent, which rig-closedness supplies: it is a complete one-dimensional Noetherian local
domain.

The file closes with the localization statement for a rig-closed point: along an adic,
topologically finite type morphism of Noetherian weakly admissible rings, a rig-closed point
of the target survives a suitable completed principal localization, and the point below it in
the localized source is rig-closed too.

## Main definitions

* `Rig.completionQuotientAlgEquiv`, `Rig.completionAlgEquivOfAlgEquiv` — the comparison
  equivalences for adic completions used to identify the base change.
* `Rig.baseChangeQuotEquiv` — base change of an algebra along `A → A ⧸ p` is the quotient by
  the extension of `p`.
* `Rig.baseChangeChain` — the composite comparison equivalence, over `A`.
* `Rig.restrictedPowerSeriesBaseChangeEquiv` — the identification of the base change with
  restricted power series over the quotient, over `A ⧸ p`.

## Main results

* `Rig.restrictedPowerSeriesBaseChangeEquiv_coefficientProjection` — the identification read
  off at every coefficient quotient.
* `Rig.isRegularRingHom_baseChange_of_rigPoint` — regularity of the canonical map into the
  base change.
* `Rig.isGeometricallyRegular_fibre` — geometric regularity of the fibre at a rig-closed
  prime.
* `Rig.exists_isClosedPointAwayFrom_completedAway_comap` — the completed principal
  localization in which the point below a rig-closed point is again rig-closed.

## Implementation notes

The ideal defining the adic topology of the quotient is the image of an ideal of definition of
`A`.  The base-change identification is an equivalence of `A ⧸ p`-algebras, so it respects the
canonical coefficient maps; its finite-level equation pins the map down on every series,
including the polynomial variables.  Rig-closedness is always expressed by the complete local
quotient condition `Rig.Ideal.IsRigPointLocalCondition` of Tag 0GG8, or by the closed-point
condition away from the topological nilradical.

## References

* [Stacks Project, Tag 0GGG](https://stacks.math.columbia.edu/tag/0GGG)
* [Stacks Project, Tag 0GGJ](https://stacks.math.columbia.edu/tag/0GGJ)
-/

@[expose] public section

namespace Rig

section

open scoped TensorProduct
open TensorProduct

universe u

private theorem eval_completionQuotientAlgEquiv_mk
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I J : Ideal R)
    (a : AdicCompletion I R) (n : ℕ) :
    AdicCompletion.evalₐ (I.map (algebraMap R (R ⧸ J))) n
      (adicCompletionQuotientAlgEquiv I J
        (Ideal.Quotient.mk (J.map (algebraMap R (AdicCompletion I R))) a)) =
      Ideal.quotientMap ((I.map (algebraMap R (R ⧸ J))) ^ n) (algebraMap R (R ⧸ J))
        (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
        (AdicCompletion.evalₐ I n a) := by
  simp only [adicCompletionQuotientAlgEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  change AdicCompletion.evalₐ (I.map (algebraMap R (R ⧸ J))) n
      (ofTensorProductAlgEquiv I (R ⧸ J)
        (a ⊗ₜ[R] (1 : R ⧸ J))) = _
  change AdicCompletion.evalₐ (I.map (algebraMap R (R ⧸ J))) n
      (ofTensorProductLinearEquiv I (R ⧸ J)
        (a ⊗ₜ[R] (1 : R ⧸ J))) = _
  rw [ofTensorProductLinearEquiv_tmul_eval]
  simp

/-- An algebra equivalence carrying one ideal to another induces an equivalence of the
corresponding adic completions. -/
public noncomputable def completionAlgEquivOfAlgEquiv
    {A : Type*} [CommRing A] {R₁ : Type*} [CommRing R₁] [Algebra A R₁]
    {R₂ : Type*} [CommRing R₂] [Algebra A R₂]
    (e : R₁ ≃ₐ[A] R₂) (I₁ : Ideal R₁) (I₂ : Ideal R₂)
    (h : I₂ = Ideal.map (e : R₁ →+* R₂) I₁) :
    AdicCompletion I₁ R₁ ≃ₐ[A] AdicCompletion I₂ R₂ := by
  let hpow (n : ℕ) : I₂ ^ n = Ideal.map (e : R₁ →+* R₂) (I₁ ^ n) := by
    rw [Ideal.map_pow, h]
  let E (n : ℕ) : (R₁ ⧸ I₁ ^ n) ≃ₐ[A] (R₂ ⧸ I₂ ^ n) :=
    Ideal.quotientEquivAlg (I₁ ^ n) (I₂ ^ n) e (hpow n)
  have hE {m n : ℕ} (hmn : m ≤ n) (y : R₁ ⧸ I₁ ^ n) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (E n y) =
        E m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  have hE' {m n : ℕ} (hmn : m ≤ n) (y : R₂ ⧸ I₂ ^ n) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) ((E n).symm y) =
        (E m).symm (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
    obtain ⟨z, rfl⟩ := (E n).surjective y
    rw [AlgEquiv.symm_apply_apply, hE hmn z, AlgEquiv.symm_apply_apply]
  let f (n : ℕ) : AdicCompletion I₁ R₁ →ₐ[A] R₂ ⧸ I₂ ^ n :=
    (E n).toAlgHom.comp ((AdicCompletion.evalₐ I₁ n).restrictScalars A)
  let g (n : ℕ) : AdicCompletion I₂ R₂ →ₐ[A] R₁ ⧸ I₁ ^ n :=
    (E n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I₂ n).restrictScalars A)
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (f n) = f m := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, f, AlgHom.restrictScalars_apply]
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      ((E n) (AdicCompletion.evalₐ I₁ n x)) =
        (E m) (AdicCompletion.evalₐ I₁ m x)
    rw [← AdicCompletion.factor_evalₐ I₁ hmn]
    exact hE hmn _
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (g n) = g m := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, g, AlgHom.restrictScalars_apply]
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      ((E n).symm (AdicCompletion.evalₐ I₂ n x)) =
        (E m).symm (AdicCompletion.evalₐ I₂ m x)
    rw [← AdicCompletion.factor_evalₐ I₂ hmn]
    exact hE' hmn _
  exact AlgEquiv.ofAlgHom
    (AdicCompletion.liftAlgHom I₂ f hf)
    (AdicCompletion.liftAlgHom I₁ g hg)
    (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by
      change AdicCompletion.evalₐ I₂ n
        ((AdicCompletion.liftAlgHom I₂ f hf)
          ((AdicCompletion.liftAlgHom I₁ g hg) x)) = AdicCompletion.evalₐ I₂ n x
      rw [AdicCompletion.evalₐ_liftAlgHom]
      change E n (AdicCompletion.evalₐ I₁ n
        ((AdicCompletion.liftAlgHom I₁ g hg) x)) = _
      rw [AdicCompletion.evalₐ_liftAlgHom]
      simp [g, AlgHom.comp_apply])
    (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => by
      change AdicCompletion.evalₐ I₁ n
        ((AdicCompletion.liftAlgHom I₁ g hg)
          ((AdicCompletion.liftAlgHom I₂ f hf) x)) = AdicCompletion.evalₐ I₁ n x
      rw [AdicCompletion.evalₐ_liftAlgHom]
      change (E n).symm (AdicCompletion.evalₐ I₂ n
        ((AdicCompletion.liftAlgHom I₂ f hf) x)) = _
      rw [AdicCompletion.evalₐ_liftAlgHom]
      simp [f, AlgHom.comp_apply])

private theorem eval_completionAlgEquivOfAlgEquiv
    {A : Type*} [CommRing A] {R₁ : Type*} [CommRing R₁] [Algebra A R₁]
    {R₂ : Type*} [CommRing R₂] [Algebra A R₂]
    (e : R₁ ≃ₐ[A] R₂) (I₁ : Ideal R₁) (I₂ : Ideal R₂)
    (h : I₂ = Ideal.map (e : R₁ →+* R₂) I₁)
  (x : AdicCompletion I₁ R₁) (n : ℕ) :
    AdicCompletion.evalₐ I₂ n (completionAlgEquivOfAlgEquiv e I₁ I₂ h x) =
      Ideal.quotientEquivAlg (I₁ ^ n) (I₂ ^ n) e (by rw [Ideal.map_pow, h])
        (AdicCompletion.evalₐ I₁ n x) := by
  let E (j : ℕ) : (R₁ ⧸ I₁ ^ j) ≃ₐ[A] (R₂ ⧸ I₂ ^ j) :=
    Ideal.quotientEquivAlg (I₁ ^ j) (I₂ ^ j) e (by rw [Ideal.map_pow, h])
  have hE {m n : ℕ} (hmn : m ≤ n) (y : R₁ ⧸ I₁ ^ n) :
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (E n y) =
        E m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) y) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rfl
  have hf : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp
          ((E n).toAlgHom.comp ((AdicCompletion.evalₐ I₁ n).restrictScalars A)) =
        (E m).toAlgHom.comp ((AdicCompletion.evalₐ I₁ m).restrictScalars A) := by
    intro m n hmn
    ext z
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
    change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (E n (AdicCompletion.evalₐ I₁ n z)) = E m (AdicCompletion.evalₐ I₁ m z)
    rw [← AdicCompletion.factor_evalₐ I₁ hmn]
    exact hE hmn _
  change AdicCompletion.evalₐ I₂ n
    (AdicCompletion.liftAlgHom I₂
      (fun j => (E j).toAlgHom.comp
          ((AdicCompletion.evalₐ I₁ j).restrictScalars A)) hf x) = _
  rw [AdicCompletion.evalₐ_liftAlgHom]
  simp [E, AlgHom.comp_apply]

private theorem excellent_of_rigPointLocalCondition
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A] (hA : TopologicalRing.IsAdic A)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.IsRigPointLocalCondition p) :
    IsExcellent (A ⧸ p) := by
  classical
  let B := A ⧸ p
  rcases hA.1 with ⟨J, hJdef, hJadic⟩
  have hIadic : _root_.IsAdic I :=
    (isIdealOfDefinition_iff_isAdic ⟨J, hJadic⟩ I).mp hI
  let Ibar := I.map (Ideal.Quotient.mk p)
  let hlocal : IsLocalRing B := Classical.choose hp
  have hspec := Classical.choose_spec hp
  let : IsLocalRing B := hlocal
  let : IsNoetherianRing B := hspec.2.1
  have hcomplete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) :=
    hspec.2.2.2.1
  have hrad : Ibar.radical = IsLocalRing.maximalIdeal B := hspec.2.2.2.2.2 I hI
  have hIbaradic : _root_.IsAdic Ibar := isAdic_map_quotient_mk I p hIadic
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have hpreIbar : IsPrecomplete Ibar B := hIbaradic.isPrecomplete_iff.mpr hcomplete
  let m := IsLocalRing.maximalIdeal B
  have hIbar_le_m : Ibar ≤ m := Ideal.le_radical.trans hrad.le
  obtain ⟨d₀, hd₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (show m ≤ Ibar.radical by rw [hrad]) m.fg_of_isNoetherianRing
  let d := max d₀ 1
  have hd : m ^ d ≤ Ibar :=
    (Ideal.pow_le_pow_right (Nat.le_max_left d₀ 1)).trans hd₀
  have : IsPrecomplete m B :=
    Stacks.AdicCompletionComparison.prec_imp Ibar m (c := 1) (d := d) (by omega) (by omega)
      (by simpa [m, pow_one] using hIbar_le_m) hd B hpreIbar
  exact (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 B

private theorem mvPolynomial_geometricallyRegular
    {k : Type*} [Field k] (σ : Type*) [Finite σ] :
    Algebra.IsGeometricallyRegular k (MvPolynomial σ k) := by
  constructor
  intro K _ _ _
  let e := MvPolynomial.scalarRTensorAlgEquiv (R := k) (N := K) (σ := σ)
  let : IsRegularRing (MvPolynomial σ K) := inferInstance
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

private theorem isRegularRingHom_mvPolynomial
    {B : Type*} [CommRing B] (σ : Type*) [Finite σ] :
    IsRegularRingHom (algebraMap B (MvPolynomial σ B)) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro q hq
  let e := MvPolynomial.scalarRTensorAlgEquiv (R := B) (N := q.ResidueField) (σ := σ)
  refine ⟨isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv, ?_⟩
  exact isGeometricallyRegular_of_algEquiv
    (h := mvPolynomial_geometricallyRegular (k := q.ResidueField) σ) (e := e.symm)

private theorem noetherian_fiber_of_noetherian_target
    {R : Type u} {S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing S] (p : Ideal R) [p.IsPrime] :
    IsNoetherianRing (p.Fiber S) := by
  have : IsNoetherianRing (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) :=
    inferInstance
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  exact isNoetherianRing_of_ringEquiv _
    (Ideal.Fiber.algEquivQuotient (S := S) p).toRingEquiv.symm

section

variable {A : Type*} [CommRing A]

/-- The `A`-algebra structure on the restricted power series ring over a quotient `A ⧸ p`,
obtained from its `A ⧸ p`-algebra structure along the quotient map. -/
noncomputable local instance reducedRestrictedPowerSeriesAlgebra (I p : Ideal A) (n : ℕ) :
    Algebra A (RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) (Fin n)) :=
  Algebra.compHom (RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) (Fin n))
    (algebraMap A (A ⧸ p))

/-- The scalar tower `A → A ⧸ p → (A ⧸ p)⟨x⟩` for the algebra structure above. -/
local instance reducedRestrictedPowerSeriesTower (I p : Ideal A) (n : ℕ) :
    IsScalarTower A (A ⧸ p) (RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) (Fin n)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Base change of an `A`-algebra `S` along `A → A ⧸ p` is the quotient of `S` by the
extension of `p`, as an `A`-algebra. -/
public noncomputable def baseChangeQuotEquiv (S : Type*) [CommRing S] [Algebra A S]
    (p : Ideal A) : (S ⊗[A] (A ⧸ p)) ≃ₐ[A] (S ⧸ p.map (algebraMap A S)) :=
  AlgEquiv.restrictScalars A (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p).symm

private theorem baseChangeQuotEquiv_includeLeft {S : Type*} [CommRing S] [Algebra A S]
    (p : Ideal A) (f : S) :
    baseChangeQuotEquiv S p (Algebra.TensorProduct.includeLeftRingHom f) =
      Ideal.Quotient.mk (p.map (algebraMap A S)) f := by
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p).symm
    (f ⊗ₜ[A] Ideal.Quotient.mk p (1 : A)) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change Ideal.Quotient.mk (p.map (algebraMap A S)) (1 • f) = _
  rw [one_smul]

section

variable (I p : Ideal A) (n : ℕ)

/-- The identification of restricted power series with the adic completion of a polynomial
ring is the canonical map on constants. -/
public theorem adicCompletionAlgEquiv_comp_algebraMap :
    ((RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin n) :
        RestrictedPowerSeries I (Fin n) →+*
          AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
            (MvPolynomial (Fin n) A))).comp
          (algebraMap A (RestrictedPowerSeries I (Fin n))) =
      (algebraMap (MvPolynomial (Fin n) A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
            (MvPolynomial (Fin n) A))).comp (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) := by
  apply RingHom.ext
  intro a
  calc
    RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin n)
          (algebraMap A (RestrictedPowerSeries I (Fin n)) a) =
        algebraMap A _ a := (RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin n)).commutes' a
    _ = algebraMap (MvPolynomial (Fin n) A) _ (MvPolynomial.C a) :=
      (DFunLike.congr_fun
        (IsScalarTower.algebraMap_eq A (MvPolynomial (Fin n) A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
            (MvPolynomial (Fin n) A))) a).symm

/-- Extending `p` to the restricted power series ring and transporting it along the
identification with an adic completion gives the extension of `p` to that completion. -/
public theorem map_adicCompletionAlgEquiv_ideal :
    (p.map (algebraMap A (RestrictedPowerSeries I (Fin n)))).map
        (RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin n) :
          RestrictedPowerSeries I (Fin n) →+*
            AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
              (MvPolynomial (Fin n) A)) =
      (p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).map
        (algebraMap (MvPolynomial (Fin n) A)
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
            (MvPolynomial (Fin n) A))) := by
  rw [Ideal.map_map, Ideal.map_map, adicCompletionAlgEquiv_comp_algebraMap]

/-- Reducing the coefficients of a polynomial ring modulo `p` and extending `I` afterwards is
the same as extending `I` to the polynomial ring and then passing to the quotient by `p`. -/
public theorem map_quotientEquivQuotientMvPolynomial_ideal :
    (I.map (Ideal.Quotient.mk p)).map
        (MvPolynomial.C : (A ⧸ p) →+* MvPolynomial (Fin n) (A ⧸ p)) =
      ((I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).map
          (algebraMap (MvPolynomial (Fin n) A)
            (MvPolynomial (Fin n) A ⧸
              p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)))).map
        ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).symm :
          (MvPolynomial (Fin n) A ⧸ p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)) →+*
            MvPolynomial (Fin n) (A ⧸ p)) := by
  have hc : (((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).symm :
          (MvPolynomial (Fin n) A ⧸ p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)) →+*
            MvPolynomial (Fin n) (A ⧸ p)).comp
        (algebraMap (MvPolynomial (Fin n) A)
          (MvPolynomial (Fin n) A ⧸
            p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)))).comp
        (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) =
      (MvPolynomial.C : (A ⧸ p) →+* MvPolynomial (Fin n) (A ⧸ p)).comp
        (Ideal.Quotient.mk p) :=
    RingHom.ext fun a =>
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).symm.commutes' a
  rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
  exact congrArg (fun f : A →+* MvPolynomial (Fin n) (A ⧸ p) => I.map f) hc.symm

/-- The chain of comparison equivalences identifying the base change of a restricted power
series ring along `A → A ⧸ p` with restricted power series over `A ⧸ p`, as `A`-algebras. -/
public noncomputable def baseChangeChain [IsNoetherianRing A] :
    (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) ≃ₐ[A]
      RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) (Fin n) :=
  (baseChangeQuotEquiv (RestrictedPowerSeries I (Fin n)) p).trans
    ((Ideal.quotientEquivAlg _ _ (RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin n))
          (map_adicCompletionAlgEquiv_ideal I p n).symm).trans
      (((adicCompletionQuotientAlgEquiv (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))
              (p.map (MvPolynomial.C : A →+* MvPolynomial (Fin n) A))).restrictScalars A).trans
        ((completionAlgEquivOfAlgEquiv
              (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).symm _ _
              (map_quotientEquivQuotientMvPolynomial_ideal I p n)).trans
          ((RestrictedPowerSeries.adicCompletionAlgEquiv
              (I.map (Ideal.Quotient.mk p)) (Fin n)).symm.restrictScalars A))))

end

/-- Base change of a restricted power series ring by a rig-closed quotient is
canonically the restricted power series ring over that quotient. -/
@[stacks 0GGJ "regular_map"]
public noncomputable def restrictedPowerSeriesBaseChangeEquiv
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A]
    (_hA : TopologicalRing.IsAdic A)
    (I : Ideal A) (_hI : TopologicalRing.IsIdealOfDefinition I)
    (p : Ideal A) [p.IsPrime]
    (_hp : Ideal.IsRigPointLocalCondition p)
    (n : ℕ) (_hn : 1 ≤ n) :
    letI : Algebra (A ⧸ p)
      (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) :=
      Algebra.TensorProduct.rightAlgebra
    (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) ≃ₐ[A ⧸ p]
      RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) (Fin n) := by
  letI : Algebra (A ⧸ p) (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) :=
    Algebra.TensorProduct.rightAlgebra
  refine AlgEquiv.ofRingEquiv (f := (baseChangeChain I p n).toRingEquiv) fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hAB : algebraMap (A ⧸ p) (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p))
        (Ideal.Quotient.mk p a) =
      algebraMap A (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) a :=
    Algebra.TensorProduct.includeRight.commutes a
  rw [hAB]
  exact (baseChangeChain I p n).commutes' a

/-- At every finite level, the base-change identification reduces a series
coefficientwise modulo `p`. The polynomial `g` is any lift of that level's
coefficient polynomial, so the equation also asserts independence of lifts. -/
@[stacks 0GGJ "regular_map"]
public lemma restrictedPowerSeriesBaseChangeEquiv_coefficientProjection
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A]
    (hA : TopologicalRing.IsAdic A)
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.IsRigPointLocalCondition p)
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (f : RestrictedPowerSeries I (Fin n))
    (g : MvPolynomial (Fin n) A)
    (hg : RestrictedPowerSeries.coefficientProjection I (Fin n) k f =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) g) :
    letI : Algebra (A ⧸ p)
      (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) :=
      Algebra.TensorProduct.rightAlgebra
    RestrictedPowerSeries.coefficientProjection
      (I.map (Ideal.Quotient.mk p)) (Fin n) k
      (restrictedPowerSeriesBaseChangeEquiv hA I hI p hp n hn
        ((Algebra.TensorProduct.includeLeftRingHom :
            RestrictedPowerSeries I (Fin n) →+*
              (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p))) f)) =
      MvPolynomial.map (Ideal.Quotient.mk
        ((I.map (Ideal.Quotient.mk p)) ^ k))
        (MvPolynomial.map (Ideal.Quotient.mk p) g) := by
  classical
  let σ := Fin n
  let B := A ⧸ p
  let PS := RestrictedPowerSeries I σ
  let Ibar := I.map (Ideal.Quotient.mk p)
  let P := MvPolynomial σ A
  let J : Ideal P := I.map (MvPolynomial.C : A →+* P)
  let K : Ideal P := p.map (MvPolynomial.C : A →+* P)
  let KPS : Ideal PS := p.map (algebraMap A PS)
  let Jbar : Ideal (MvPolynomial σ B) := Ibar.map (MvPolynomial.C : B →+* MvPolynomial σ B)
  let ePoly : (P ⧸ K) ≃ₐ[A] MvPolynomial σ B :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) p).symm
  let ePS := RestrictedPowerSeries.adicCompletionAlgEquiv I σ
  let ePSbar := RestrictedPowerSeries.adicCompletionAlgEquiv Ibar σ
  let qT := baseChangeQuotEquiv PS p
  let qPS := Ideal.quotientEquivAlg KPS (K.map (algebraMap P (AdicCompletion J P))) ePS
    (map_adicCompletionAlgEquiv_ideal I p n).symm
  let qComp := adicCompletionQuotientAlgEquiv J K
  let eComp := completionAlgEquivOfAlgEquiv ePoly (J.map (algebraMap P (P ⧸ K))) Jbar
    (map_quotientEquivQuotientMvPolynomial_ideal I p n)
  have hTensor : qT ((Algebra.TensorProduct.includeLeftRingHom : PS →+* (PS ⊗[A] B)) f) =
      Ideal.Quotient.mk KPS f := baseChangeQuotEquiv_includeLeft p f
  have hchain : ∀ x : PS ⊗[A] B,
      baseChangeChain I p n x = ePSbar.symm (eComp (qComp (qPS (qT x)))) := by
    intro x
    simp only [baseChangeChain, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      qT, qPS, qComp, eComp, ePSbar, ePS, ePoly, Jbar, Ibar, J, K, KPS, PS, P, B, σ]
  have hcancel : ∀ y, RestrictedPowerSeries.adicCompletionEquiv Ibar σ (ePSbar.symm y) = y :=
    ePSbar.apply_symm_apply
  apply (RestrictedPowerSeries.polynomialQuotientEquiv Ibar σ k).injective
  rw [RestrictedPowerSeries.polynomialQuotientEquiv_map_mk]
  change RestrictedPowerSeries.polynomialQuotientProjection Ibar σ k
      (baseChangeChain I p n
        ((Algebra.TensorProduct.includeLeftRingHom : PS →+* (PS ⊗[A] B)) f)) =
    Ideal.Quotient.mk (Jbar ^ k) (MvPolynomial.map (Ideal.Quotient.mk p) g)
  rw [← RestrictedPowerSeries.eval_adicCompletionEquiv, hchain, hcancel, hTensor]
  have hqPS : qPS (Ideal.Quotient.mk KPS f) =
      Ideal.Quotient.mk (K.map (algebraMap P (AdicCompletion J P))) (ePS f) :=
    Ideal.quotientEquivAlg_mk ..
  rw [hqPS]
  rw [eval_completionAlgEquivOfAlgEquiv, eval_completionQuotientAlgEquiv_mk]
  have hevalPS : AdicCompletion.evalₐ J k (ePS f) =
      RestrictedPowerSeries.polynomialQuotientProjection I σ k f :=
    RestrictedPowerSeries.eval_adicCompletionEquiv I σ k f
  rw [hevalPS, RestrictedPowerSeries.polynomialQuotientProjection, RingHom.comp_apply, hg]
  have hpoly : (RestrictedPowerSeries.polynomialQuotientEquiv I σ k).toRingHom
      (MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) g) = Ideal.Quotient.mk (J ^ k) g :=
    RestrictedPowerSeries.polynomialQuotientEquiv_map_mk I σ k g
  rw [hpoly]
  simp [ePoly, Jbar, Ibar, MvPolynomial.quotientEquivQuotientMvPolynomial,
    Ideal.Quotient.lift_mk, MvPolynomial.map_eq_eval₂Hom_C_comp, K]


end

/-- The canonical map from the rig-closed quotient to the base-changed
restricted power series ring is regular. -/
@[stacks 0GGJ "regular_map"]
public lemma isRegularRingHom_baseChange_of_rigPoint
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A]
    (_hA : TopologicalRing.IsAdic A)
    (I : Ideal A) (_hI : TopologicalRing.IsIdealOfDefinition I)
    (p : Ideal A) [p.IsPrime]
    (_hp : Ideal.IsRigPointLocalCondition p)
    (n : ℕ) (_hn : 1 ≤ n) :
    letI : Algebra (A ⧸ p)
      (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p)) :=
      Algebra.TensorProduct.rightAlgebra
    IsRegularRingHom (algebraMap (A ⧸ p)
      (RestrictedPowerSeries I (Fin n) ⊗[A] (A ⧸ p))) := by
  classical
  let B := A ⧸ p
  let σ := Fin n
  let R := MvPolynomial σ B
  let J : Ideal R := (I.map (Ideal.Quotient.mk p)).map (MvPolynomial.C : B →+* R)
  let C := AdicCompletion J R
  let hlocal : IsLocalRing B := Classical.choose _hp
  have hspec := Classical.choose_spec _hp
  let : IsLocalRing B := hlocal
  let : IsNoetherianRing B := hspec.2.1
  have hBexcellent : IsExcellent B := excellent_of_rigPointLocalCondition
    _hA I _hI p _hp
  have hRexcellent : IsExcellent R :=
    (isExcellent_of_standard_classes_and_finiteType.{u_1, u_1}).2.2.2.2
      B R hBexcellent
  let : IsNoetherianRing R := hRexcellent.1.1
  let : IsNoetherianRing C := inferInstance
  have hRg : IsGRing R := hRexcellent.1.2.1
  let f : B →+* R := algebraMap B R
  let g : R →+* C := algebraMap R C
  have hf : IsRegularRingHom f := isRegularRingHom_mvPolynomial σ
  have hg : IsRegularRingHom g := isRegularRingHom_algebraMap_adicCompletion hRg J
  have hcomp : IsRegularRingHom (g.comp f) := by
    let : Algebra B R := f.toAlgebra
    let : Algebra R C := g.toAlgebra
    let : Algebra B C := (g.comp f).toAlgebra
    let : IsScalarTower B R C :=
      IsScalarTower.of_algebraMap_eq (R := B) (S := R) (A := C) fun _ => rfl
    exact isRegularRingHom_comp f g hf hg fun q _ => noetherian_fiber_of_noetherian_target q
  have hBC : IsRegularRingHom (algebraMap B C) := hcomp
  let PSbar := RestrictedPowerSeries (I.map (Ideal.Quotient.mk p)) σ
  let ePSbar : PSbar ≃ₐ[B] C :=
    RestrictedPowerSeries.adicCompletionAlgEquiv
      (I.map (Ideal.Quotient.mk p)) σ
  have hPSbar : IsRegularRingHom (algebraMap B PSbar) := by
    have he : ePSbar.symm.toRingHom.comp (algebraMap B C) = algebraMap B PSbar := by
      ext b
      simp
    rw [← he]
    exact hBC.comp_ringEquiv ePSbar.symm.toRingEquiv
  let PS := RestrictedPowerSeries I σ
  let S := PS ⊗[A] B
  let : Algebra B S := Algebra.TensorProduct.rightAlgebra
  have e : S ≃ₐ[B] PSbar :=
    restrictedPowerSeriesBaseChangeEquiv _hA I _hI p _hp n _hn
  have he : e.symm.toRingHom.comp (algebraMap B PSbar) = algebraMap B S := by
    ext b
    simp
  rw [← he]
  exact hPSbar.comp_ringEquiv e.symm.toRingEquiv

private theorem scalarTower_tensor_of_inverse_algebraMaps
    {R E K S : Type*} [CommRing R] [CommRing E] [CommRing K] [CommRing S]
    [Algebra R E] [Algebra R S] [Algebra K E] [Algebra E K]
    (h : ∀ x : E, algebraMap K E (algebraMap E K x) = x) :
    letI : Algebra K (E ⊗[R] S) := Algebra.restrictScalars K E (E ⊗[R] S)
    IsScalarTower E K (E ⊗[R] S) := by
  apply IsScalarTower.of_algebraMap_smul
  intro x z
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    congr 1
    simp only [Algebra.smul_def, h, Algebra.algebraMap_self_apply]
  | add z w hz hw => simp [smul_add, hz, hw]

/-- The fibre of a restricted power series algebra at a rig-closed prime is
geometrically regular over the residue field. -/
@[stacks 0GGJ "geometrically_regular_fibre"]
public lemma isGeometricallyRegular_fibre
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsNoetherianRing A]
    (_hA : TopologicalRing.IsAdic A)
    (I : Ideal A) (_hI : IsAdic I)
    (p : Ideal A) [p.IsPrime]
    (_hp : Ideal.IsRigPointLocalCondition p)
    (n : ℕ) (_hn : 0 < n) :
    letI : Algebra p.ResidueField
      (RestrictedPowerSeries I (Fin n) ⊗[A]
        p.ResidueField) := Algebra.TensorProduct.rightAlgebra
    Algebra.IsGeometricallyRegular p.ResidueField
      (RestrictedPowerSeries I (Fin n) ⊗[A]
        p.ResidueField) := by
  obtain ⟨J, -, hJ⟩ := _hA.1
  have hIdef : TopologicalRing.IsIdealOfDefinition I :=
    (isIdealOfDefinition_iff_isAdic ⟨J, hJ⟩ I).2 _hI
  let R := A ⧸ p
  let Q := RestrictedPowerSeries I (Fin n)
  let S := Q ⊗[A] R
  have hpbot : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  let := hpbot
  let E := (⊥ : Ideal R).ResidueField
  let : Algebra R S := Algebra.TensorProduct.rightAlgebra
  let : CommRing S := Algebra.TensorProduct.instCommRing
  have hreg : IsRegularRingHom (algebraMap R S) := by
    simpa only [R, S] using
      isRegularRingHom_baseChange_of_rigPoint
        _hA I hIdef p _hp n (Nat.succ_le_iff.mpr _hn)
  have hgeom : Algebra.IsGeometricallyRegular E (Ideal.Fiber (⊥ : Ideal R) S) :=
    (hreg.2 (⊥ : Ideal R)).2
  let e0 : p.ResidueField ≃+* E :=
    IsFractionRing.ringEquivOfRingEquiv (A := R) (K := p.ResidueField)
      (B := R) (L := E) (RingEquiv.refl R)
  let e : p.ResidueField ≃ₐ[R] E :=
    { toRingEquiv := e0
      commutes' := fun r => by
        simp [e0] }
  let : Algebra p.ResidueField E := e.toRingHom.toAlgebra
  let : Algebra E p.ResidueField := e.symm.toRingHom.toAlgebra
  let eSep : E ≃ₐ[E] p.ResidueField :=
    { toRingEquiv := e.symm
      commutes' := fun r => rfl }
  let : Algebra p.ResidueField (Ideal.Fiber (⊥ : Ideal R) S) :=
    Algebra.restrictScalars p.ResidueField E (Ideal.Fiber (⊥ : Ideal R) S)
  have hscalar : IsScalarTower E p.ResidueField (Ideal.Fiber (⊥ : Ideal R) S) :=
    scalarTower_tensor_of_inverse_algebraMaps (R := R) (E := E) (K := p.ResidueField) (S := S)
      fun x => e.apply_symm_apply x
  have hsep : Algebra.IsSeparable E p.ResidueField :=
    AlgEquiv.Algebra.isSeparable eSep
  have hgeom' : Algebra.IsGeometricallyRegular p.ResidueField
      (Ideal.Fiber (⊥ : Ideal R) S) := by
    have hiff := @Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable
      E p.ResidueField
      (Ideal.Fiber (⊥ : Ideal R) S) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hscalar hsep
    exact hiff.mp hgeom
  let T := Q ⊗[A] p.ResidueField
  let : CommRing T := Algebra.TensorProduct.instCommRing
  let : Algebra p.ResidueField T := Algebra.TensorProduct.rightAlgebra
  let eField : E ≃ₐ[p.ResidueField] p.ResidueField :=
    { toRingEquiv := e.symm
      commutes' := fun x => e.symm_apply_apply x }
  have hRPE : IsScalarTower R p.ResidueField E :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (e.commutes' x).symm)
  exact isGeometricallyRegular_of_algEquiv (h := hgeom') (e :=
    ((Algebra.TensorProduct.congr eField (Algebra.TensorProduct.commRight A R Q).symm).trans
      ((Algebra.TensorProduct.cancelBaseChange A R p.ResidueField p.ResidueField Q).trans
        (Algebra.TensorProduct.commRight A p.ResidueField Q))))

end

section

/-- An ideal whose radical is the topological nilradical has the same closed points away from
it as the topological nilradical. -/
private theorem closedPointAway_iff_topologicalNilradical
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (I p : Ideal R) [p.IsPrime] (h : I.radical = topologicalNilradical R) :
    Ideal.IsClosedPointAwayFrom I p ↔
      Ideal.IsClosedPointAwayFrom (topologicalNilradical R) p := by
  unfold Ideal.IsClosedPointAwayFrom
  rw [PrimeSpectrum.zeroLocus_eq_iff (I := I) (J := topologicalNilradical R) |>.mpr (by
    rw [h, (TopologicalRing.topologicalNilradical_isRadical (B := R)).radical])]

private lemma closedPointAway_of_maximalAmongPrimesAvoiding
    {R : Type*} [CommRing R] (I q : Ideal R) [q.IsPrime]
    (hmax : Ideal.IsMaximalAmongPrimesAvoiding I q) :
    Ideal.IsClosedPointAwayFrom I q := by
  refine ⟨?_, ?_⟩
  · simpa [PrimeSpectrum.mem_zeroLocus, Set.mem_compl_iff] using hmax.1
  · let qpt : PrimeSpectrum R := ⟨q, inferInstance⟩
    let qsub : {x : PrimeSpectrum R // x ∈ (PrimeSpectrum.zeroLocus (I : Set R))ᶜ} :=
      ⟨qpt, by simpa [PrimeSpectrum.mem_zeroLocus, Set.mem_compl_iff] using hmax.1⟩
    rw [← closure_subset_iff_isClosed]
    intro x hx
    rw [closure_subtype] at hx
    have hxbase : (x : PrimeSpectrum R) ∈ closure ({qpt} : Set (PrimeSpectrum R)) := by
      simpa [qsub] using hx
    rw [PrimeSpectrum.closure_singleton] at hxbase
    have hle : q ≤ (x : PrimeSpectrum R).asIdeal := by
      have hsubset := (PrimeSpectrum.mem_zeroLocus _ _).mp hxbase
      exact (SetLike.coe_subset_coe.mp hsubset)
    have havoid : ¬ I ≤ (x : PrimeSpectrum R).asIdeal := by
      intro hleI
      have hmem : (x : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus (I : Set R) :=
        (PrimeSpectrum.mem_zeroLocus _ _).2 (SetLike.coe_subset_coe.mpr hleI)
      exact x.2 hmem
    have heq := hmax.2 _ (x : PrimeSpectrum R).2 hle havoid
    exact Subtype.ext (PrimeSpectrum.ext heq)

private lemma maximalAmongPrimesAvoiding_of_quotientEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (q : Ideal R) (q' I : Ideal S) (J : Ideal R) (φ : R →+* S)
    [q.IsPrime] [q'.IsPrime]
    (hq' : q.map φ = q')
    (e : (R ⧸ q) ≃+* (S ⧸ q'))
    (he : ∀ a : R, e (Ideal.Quotient.mk q a) =
      Ideal.Quotient.mk q' (φ a))
    (hI : I = J.map φ)
    (hmax : Ideal.IsMaximalAmongPrimesAvoiding J q) :
    Ideal.IsMaximalAmongPrimesAvoiding I q' := by
  refine ⟨?_, ?_⟩
  · intro hIq'
    apply hmax.1
    intro a ha
    have hφa : φ a ∈ q' := by
      have hmap : φ a ∈ J.map φ := Ideal.mem_map_of_mem φ ha
      rw [← hI] at hmap
      exact hIq' hmap
    have hzero : Ideal.Quotient.mk q a = 0 := by
      apply e.injective
      rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr hφa, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  · intro r hrprime hq'r hrnot
    let s := r.comap φ
    have hsprime : s.IsPrime := by
      let : r.IsPrime := hrprime
      dsimp [s]
      exact Ideal.comap_isPrime φ r
    have hqle : q ≤ s := Ideal.map_le_iff_le_comap.mp (by rwa [hq'])
    have hJnot : ¬ J ≤ s := fun hle => hrnot (by rw [hI]; exact Ideal.map_le_iff_le_comap.mpr hle)
    have hsEq : s = q := hmax.2 s hsprime hqle hJnot
    apply le_antisymm
    · intro y hy
      have hybar : Ideal.Quotient.mk q' y ∈
          Ideal.map (Ideal.Quotient.mk q') r := Ideal.mem_map_of_mem _ hy
      obtain ⟨z, hz⟩ := e.surjective (Ideal.Quotient.mk q' y)
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
      have heq : Ideal.Quotient.mk q' y = Ideal.Quotient.mk q' (φ a) := by
        calc
          Ideal.Quotient.mk q' y = e z := hz.symm
          _ = e (Ideal.Quotient.mk q a) := by rw [ha]
          _ = Ideal.Quotient.mk q' (φ a) := he a
      obtain ⟨b, hb, hby⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk q')
          Ideal.Quotient.mk_surjective).mp hybar
      have hdiff : φ a - b ∈ q' := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        calc
          Ideal.Quotient.mk q' (φ a - b) =
              Ideal.Quotient.mk q' (φ a) - Ideal.Quotient.mk q' b := map_sub _ _ _
          _ = 0 := by rw [← heq, hby]; simp
      have hφaR : φ a ∈ r := by
        have hdiffR : φ a - b ∈ r := hq'r hdiff
        simpa [sub_add_cancel] using r.add_mem hdiffR hb
      have haq : a ∈ q := by
        have hmems : a ∈ s := hφaR
        simpa [s, hsEq] using hmems
      have hyzero : Ideal.Quotient.mk q' y = 0 := by
        calc
        Ideal.Quotient.mk q' y = Ideal.Quotient.mk q' (φ a) := heq
        _ = e (Ideal.Quotient.mk q a) := (he a).symm
        _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr haq, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hyzero
    · exact hq'r

private lemma exists_localization_range_field_finite
    {R K : Type*} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : χ.FiniteType) :
    ∃ r : R, χ r ≠ 0 ∧
      ∃ (_hfield : IsField (Localization.Away (χ.rangeRestrict r)))
        (hAlg : Algebra (Localization.Away (χ.rangeRestrict r)) K)
        (hTower : IsScalarTower χ.range (Localization.Away (χ.rangeRestrict r)) K),
        letI : Algebra (Localization.Away (χ.rangeRestrict r)) K := hAlg
        letI : IsScalarTower χ.range (Localization.Away (χ.rangeRestrict r)) K := hTower
        Module.Finite (Localization.Away (χ.rangeRestrict r)) K := by
  let : Algebra R K := χ.toAlgebra
  let : Algebra R χ.range := χ.rangeRestrict.toAlgebra
  let : Algebra χ.range K := χ.range.subtype.toAlgebra
  let : IsScalarTower R χ.range K := .of_algebraMap_eq fun _ => rfl
  have htype : Algebra.FiniteType R K := hχ
  have htype' : Algebra.FiniteType χ.range K :=
    .of_restrictScalars_finiteType R χ.range K
  obtain ⟨a, hfield, hAlg, hTower, hfinite⟩ :=
    exists_isField_localizationAway_and_finite_of_finiteType χ.range K Subtype.val_injective
  let := hAlg
  let := hTower
  let := hfinite
  obtain ⟨r, hr⟩ := χ.rangeRestrict_surjective a
  subst a
  have hu : IsUnit (algebraMap χ.range K (χ.rangeRestrict r)) := by
    rw [IsScalarTower.algebraMap_apply χ.range (Localization.Away (χ.rangeRestrict r)) K]
    exact (IsLocalization.Away.algebraMap_isUnit (χ.rangeRestrict r)).map _
  change IsUnit (χ r) at hu
  exact ⟨r, hu.ne_zero, hfield, hAlg, hTower, hfinite⟩

private theorem adicCompletion_reduction_equiv
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    let C := AdicCompletion I R
    let I_hat := I.map (algebraMap R C)
    letI : TopologicalSpace C := I_hat.adicTopology
    letI : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology C C := I_hat.isLinearTopology
    ∃ e : C ⧸ topologicalNilradical C ≃+* R ⧸ I.radical,
      ∀ r : R, e (Ideal.Quotient.mk (topologicalNilradical C)
        (algebraMap R C r)) = Ideal.Quotient.mk I.radical r := by
  classical
  let C := AdicCompletion I R
  let I_hat := I.map (algebraMap R C)
  let : TopologicalSpace C := I_hat.adicTopology
  let : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology C C := I_hat.isLinearTopology
  have hradC : topologicalNilradical C = I_hat.radical :=
    (radical_eq_topologicalNilradical_of_isAdic I_hat rfl).symm
  have hIrad : I ≤ I.radical := by
    intro x hx
    rw [Ideal.mem_radical_iff]
    exact ⟨1, by simpa using hx⟩
  let ev : C →+* R ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  let fac : R ⧸ I →+* R ⧸ I.radical :=
    Ideal.Quotient.factor hIrad
  let ρ : C →+* R ⧸ I.radical := fac.comp ev
  have hmapI : Ideal.map (Ideal.Quotient.mk I) I = ⊥ := Ideal.map_quotient_self I
  have hker : RingHom.ker ρ = topologicalNilradical C := by
    change Ideal.comap ev (RingHom.ker fac) = _
    rw [Ideal.Quotient.factor_ker,
      Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]), hmapI,
      Ideal.comap_radical]
    change (Ideal.comap ev ⊥).radical = _
    rw [← RingHom.ker_eq_comap_bot, AdicCompletion.ker_evalOneₐ_eq_map I
      I.fg_of_isNoetherianRing, ← hradC]
  have hsurj : Function.Surjective ρ := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.radical) x
    obtain ⟨z, hz⟩ := AdicCompletion.evalOneₐ_surjective I y
    exact ⟨z, by simp [ρ, fac, ev, hz]⟩
  let e0 : C ⧸ RingHom.ker ρ ≃+* R ⧸ I.radical :=
    RingHom.quotientKerEquivOfSurjective hsurj
  let e : C ⧸ topologicalNilradical C ≃+* R ⧸ I.radical :=
    (Ideal.quotEquivOfEq hker.symm).trans e0
  refine ⟨e, ?_⟩
  intro r
  change e (Ideal.Quotient.mk (topologicalNilradical C)
    (algebraMap R C r)) = _
  simp only [e, e0, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp [ρ, fac, ev]

/-- A continuous ring homomorphism maps topologically nilpotent elements to topologically
nilpotent elements. -/
private theorem topologicalNilradical_le_comap {X Y : Type*} [CommRing X] [TopologicalSpace X]
    [IsLinearTopology X X] [CommRing Y] [TopologicalSpace Y] [IsLinearTopology Y Y]
    (φ : X →+* Y) (hφ : Continuous φ) :
    topologicalNilradical X ≤ (topologicalNilradical Y).comap φ := fun _ hx ↦
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    ((IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp hx).map hφ)

/-- In a linearly topologized ring whose topology is defined by `L`, the residue of a
topologically nilpotent element at a prime whose quotient is local with maximal ideal the
radical of the extension of `L` is zero. -/
private theorem residue_eq_zero_of_mem_topologicalNilradical {C : Type*} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (L : Ideal C) (hLrad : L.radical = topologicalNilradical C)
    (q : Ideal C) [q.IsPrime] [IsLocalRing (C ⧸ q)]
    (hrad : (L.map (Ideal.Quotient.mk q)).radical = IsLocalRing.maximalIdeal (C ⧸ q))
    (x : C) (hx : x ∈ topologicalNilradical C) :
    IsLocalRing.residue (C ⧸ q) (Ideal.Quotient.mk q x) = 0 := by
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  rw [← hrad]
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hLrad ▸ hx : x ∈ L.radical)
  refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk q) hn

/-- **Stacks 0GGG with the ideal of definition named.**  The content of
`Rig.exists_isClosedPointAwayFrom_completedAway_comap`, stated for a given ideal of
definition `I` of `A` whose extension defines the topology of `B`, rather than for the one
extracted from an adicness witness by `Exists.choose`.  Infrastructure: a consumer that
already knows which ideal it is working with cannot use the `Exists.choose` form, because
`Exists.choose ⟨I, _⟩` is not reducible to `I`. -/
public theorem exists_isClosedPointAwayFrom_completedAway_comap_of_isAdic
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (I : Ideal A) (hIadic : _root_.IsAdic I)
    (hJadic : _root_.IsAdic (I.map φ))
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q) :
    let J := I.map φ
    ∃ f : A,
      IsUnit (Ideal.Quotient.mk q (φ f)) ∧
        (let A_f := CompletedAway I f
         let B_f := CompletedAway J (φ f)
         let ψ : A_f →+* B_f := RingHom.completedAwayMap φ I f
         let I_f := I.map (algebraMap A (Localization.Away f))
         let J_f := J.map (algebraMap B (Localization.Away (φ f)))
         let I_hat := I_f.map (algebraMap (Localization.Away f) A_f)
         let J_hat := J_f.map (algebraMap (Localization.Away (φ f)) B_f)
         let q' := extendedIdeal J q (φ f)
         let p' := q'.comap ψ
         ψ.comp (algebraMap A A_f) = (algebraMap B B_f).comp φ ∧
           (∃ hqprime : q'.IsPrime,
             letI : q'.IsPrime := hqprime
             ∃ hpprime : p'.IsPrime,
               letI : p'.IsPrime := hpprime
               Ideal.IsClosedPointAwayFrom J_hat q' ∧
                 Ideal.IsClosedPointAwayFrom I_hat p')) := by
  classical
  let J := I.map φ
  have hJadic : IsAdic J := hJadic
  have hrad : J.radical = topologicalNilradical B :=
    radical_eq_topologicalNilradical_of_isAdic J hJadic
  let : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := hB.2.1
  let : T2Space B := hB.2.2
  have hhadicB : ∃ L : Ideal B, IsAdic L := ⟨J, hJadic⟩
  have hJdef : TopologicalRing.IsIdealOfDefinition J :=
    (isIdealOfDefinition_iff_isAdic hhadicB J).mpr hJadic
  have hqJ : Ideal.IsClosedPointAwayFrom J q :=
    (closedPointAway_iff_topologicalNilradical J q hrad).mpr hq
  have htfae := rigPoint_tfae hhadicB q
  have hcondition2 : ∃ L : Ideal B,
      TopologicalRing.IsIdealOfDefinition L ∧
        Ideal.IsClosedPointAwayFrom L q := ⟨J, hJdef, hqJ⟩
  have hlocal : Ideal.IsRigPointLocalCondition q :=
    (htfae.out 2 8).mp hcondition2
  let : IsLocalRing (B ⧸ q) := hlocal.choose
  have htaut : RingHom.IsTaut φ :=
    RingHom.isTaut_of_isAdic φ ⟨I, hIadic, hJadic⟩
  have hred :=
    isFiniteTypeOnReductions_of_isTaut_of_isTopologicallyOfFiniteType
      φ hφ hA.1 htaut hft
  obtain ⟨χ, hχcomp, hχft⟩ :=
    exists_residueFieldMap_finiteType_of_rigPoint q hlocal φ hφ hred
  let κ := IsLocalRing.ResidueField (B ⧸ q)
  let a := topologicalNilradical A
  let : Algebra (A ⧸ a) κ := χ.toAlgebra
  obtain ⟨r, hrχ, hfield, hAlg, hTower, hfinite⟩ :=
    exists_localization_range_field_finite χ hχft
  obtain ⟨f, hfr⟩ := Ideal.Quotient.mk_surjective r
  have hres : IsLocalRing.residue (B ⧸ q) (Ideal.Quotient.mk q (φ f)) ≠ 0 := by
    have heq := RingHom.congr_fun hχcomp f
    change χ (Ideal.Quotient.mk a f) =
      IsLocalRing.residue (B ⧸ q) (Ideal.Quotient.mk q (φ f)) at heq
    rwa [← heq, hfr]
  have hfunit : IsUnit (Ideal.Quotient.mk q (φ f)) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  let : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let : IsAdicComplete J B :=
    (IsAdic.isAdicComplete_iff hJadic).2 ⟨hB.2.1, hB.2.2⟩
  have hqprime : (extendedIdeal J q (φ f)).IsPrime :=
    extendedIdeal_isPrime J q (φ f) (hp := inferInstance) (hf := hfunit)
  have hmaxJq : Ideal.IsMaximalAmongPrimesAvoiding J q := by
    have hmax_all : ∀ L : Ideal B, TopologicalRing.IsIdealOfDefinition L →
        Ideal.IsMaximalAmongPrimesAvoiding L q :=
      (htfae.out 2 3).mp hcondition2
    exact hmax_all J hJdef
  let B_f := CompletedAway J (φ f)
  let β : B →+* B_f := algebraMap B B_f
  let q' := extendedIdeal J q (φ f)
  let J_f := J.map (algebraMap B (Localization.Away (φ f)))
  let J_hat := J_f.map (algebraMap (Localization.Away (φ f)) B_f)
  let : IsScalarTower B (Localization.Away (φ f)) B_f :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : q'.IsPrime := hqprime
  have hqmap : q.map β = q' := rfl
  have hJhat : J_hat = J.map β := by
    simp [J_hat, J_f, β, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq B (Localization.Away (φ f)) B_f]
  obtain ⟨eBquot, heBquot⟩ :=
    quotient_extendedIdeal_equiv J q (φ f) hfunit
  have hmaxJhat : Ideal.IsMaximalAmongPrimesAvoiding J_hat q' :=
    maximalAmongPrimesAvoiding_of_quotientEquiv q q' J_hat J β hqmap eBquot heBquot
      hJhat hmaxJq
  have hqprimeClosed : Ideal.IsClosedPointAwayFrom J_hat q' :=
    closedPointAway_of_maximalAmongPrimesAvoiding J_hat q' hmaxJhat
  refine ⟨f, hfunit, ?_⟩
  constructor
  · exact RingHom.completedAwayMap_comp_base φ I f
  · refine ⟨hqprime, ?_⟩
    let A_f := CompletedAway I f
    let A_loc := Localization.Away f
    let B_loc := Localization.Away (φ f)
    let ψ := RingHom.completedAwayMap φ I f
    let I_f := I.map (algebraMap A A_loc)
    let J_f := J.map (algebraMap B B_loc)
    let I_hat := I_f.map (algebraMap (Localization.Away f) A_f)
    let J_hat' := J_f.map (algebraMap B_loc (CompletedAway J (φ f)))
    let p' := q'.comap ψ
    have hpprime : p'.IsPrime := Ideal.comap_isPrime ψ q'
    refine ⟨hpprime, ?_⟩
    refine ⟨hqprimeClosed, ?_⟩
    let : TopologicalSpace A_f := I_hat.adicTopology
    let : IsTopologicalRing A_f := I_hat.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology A_f A_f := I_hat.isLinearTopology
    let : TopologicalSpace (CompletedAway J (φ f)) := J_hat'.adicTopology
    let : IsTopologicalRing (CompletedAway J (φ f)) :=
      J_hat'.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology (CompletedAway J (φ f))
      (CompletedAway J (φ f)) := J_hat'.isLinearTopology
    have hweakA : TopologicalRing.IsWeaklyAdmissible A_f :=
      isWeaklyAdmissible_adicCompletion I_f I_f.fg_of_isNoetherianRing
    have hweakB : TopologicalRing.IsWeaklyAdmissible (CompletedAway J (φ f)) :=
      isWeaklyAdmissible_adicCompletion J_f J_f.fg_of_isNoetherianRing
    let φf : A_loc →+* B_loc := IsLocalization.Away.map A_loc B_loc φ f
    let : Algebra A_loc B_loc := φf.toAlgebra
    have hcomp : ψ.comp (algebraMap A_loc A_f) =
        (algebraMap B_loc (CompletedAway J (φ f))).comp φf := by
      ext x : 1
      dsimp [ψ, RingHom.completedAwayMap, RingHom.comp_apply]
      rw [Stacks.Nagata.PthRootDescent.mapAdicCompletion_of]
      rfl
    have hIlocal : I_f.map φf = J_f := by
      dsimp [I_f, J_f, J]
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      ext x
      change φf (algebraMap A A_loc x) = algebraMap B B_loc (φ x)
      dsimp [φf, IsLocalization.Away.map]
      apply IsLocalization.map_eq
    have hmap : I_hat.map ψ = J_hat' := by
      calc
        I_hat.map ψ = I_f.map (ψ.comp (algebraMap A_loc A_f)) := by
          change (I_f.map (algebraMap A_loc A_f)).map ψ = _
          exact Ideal.map_map (algebraMap A_loc A_f) ψ
        _ = I_f.map ((algebraMap B_loc (CompletedAway J (φ f))).comp φf) := by
          rw [hcomp]
        _ = (I_f.map φf).map (algebraMap B_loc (CompletedAway J (φ f))) :=
          (Ideal.map_map φf
            (algebraMap B_loc (CompletedAway J (φ f)))).symm
        _ = J_hat' := by rw [hIlocal]
    have hψcont : Continuous ψ := by
      change @Continuous A_f (CompletedAway J (φ f))
        I_hat.adicTopology J_hat'.adicTopology ψ
      apply continuous_adic_of_map_le I_hat J_hat' ψ
      rw [hmap]
    have hψadic : RingHom.IsAdic ψ := by
      refine ⟨I_hat, rfl, ?_⟩
      rw [hmap]
      rfl
    let a := topologicalNilradical A
    let b := topologicalNilradical B
    let aLoc := a.map (algebraMap A A_loc)
    let bLoc := b.map (algebraMap B B_loc)
    let nilAhat := topologicalNilradical A_f
    let nilBhat := topologicalNilradical (CompletedAway J (φ f))
    let : TopologicalSpace A_loc := I_f.adicTopology
    let : IsTopologicalRing A_loc := I_f.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology A_loc A_loc := I_f.isLinearTopology
    let : TopologicalSpace B_loc := J_f.adicTopology
    let : IsTopologicalRing B_loc := J_f.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology B_loc B_loc := J_f.isLinearTopology
    have hradA : I.radical = a :=
      radical_eq_topologicalNilradical_of_isAdic I hIadic
    have hradIlocal : I_f.radical = aLoc := by
      dsimp [I_f, aLoc]
      rw [← IsLocalization.map_radical (Submonoid.powers f) A_loc I, hradA]
    have hradJlocal : J_f.radical = bLoc := by
      dsimp [J_f, bLoc, J]
      rw [← IsLocalization.map_radical (Submonoid.powers (φ f)) B_loc J, hrad]
    obtain ⟨eA0, heA0⟩ := adicCompletion_reduction_equiv I_f
    obtain ⟨eB0, heB0⟩ := adicCompletion_reduction_equiv J_f
    let eA : A_f ⧸ nilAhat ≃+* A_loc ⧸ aLoc :=
      eA0.trans (Ideal.quotEquivOfEq hradIlocal)
    let eB : CompletedAway J (φ f) ⧸ nilBhat ≃+*
        B_loc ⧸ bLoc :=
      eB0.trans (Ideal.quotEquivOfEq hradJlocal)
    have heA (x : A_loc) :
        eA (Ideal.Quotient.mk nilAhat (algebraMap A_loc A_f x)) =
          Ideal.Quotient.mk aLoc x := by
      change (Ideal.quotEquivOfEq hradIlocal)
        (eA0 (Ideal.Quotient.mk nilAhat (algebraMap A_loc A_f x))) = _
      rw [heA0, Ideal.quotEquivOfEq_mk]
    have heB (x : B_loc) :
        eB (Ideal.Quotient.mk nilBhat
          (algebraMap B_loc (CompletedAway J (φ f)) x)) =
          Ideal.Quotient.mk bLoc x := by
      change (Ideal.quotEquivOfEq hradJlocal)
        (eB0 (Ideal.Quotient.mk nilBhat
          (algebraMap B_loc (CompletedAway J (φ f)) x))) = _
      rw [heB0, Ideal.quotEquivOfEq_mk]
    have hradJhat' : J_hat'.radical = nilBhat :=
      radical_eq_topologicalNilradical_of_isAdic J_hat' rfl
    have hqprimeClosedN : Ideal.IsClosedPointAwayFrom nilBhat q' :=
      (closedPointAway_iff_topologicalNilradical J_hat' q' hradJhat').mp hqprimeClosed
    have hhadicBf : ∃ L : Ideal (CompletedAway J (φ f)), IsAdic L :=
      ⟨J_hat', rfl⟩
    let : @CompleteSpace (CompletedAway J (φ f))
        (IsTopologicalAddGroup.rightUniformSpace
          (CompletedAway J (φ f))) := hweakB.2.1
    let : T2Space (CompletedAway J (φ f)) := hweakB.2.2
    have htfaeBf := rigPoint_tfae hhadicBf q'
    have hJdefBf : TopologicalRing.IsIdealOfDefinition J_hat' :=
      (isIdealOfDefinition_iff_isAdic hhadicBf J_hat').mpr rfl
    have hcondition2Bf : ∃ L : Ideal (CompletedAway J (φ f)),
        TopologicalRing.IsIdealOfDefinition L ∧
          Ideal.IsClosedPointAwayFrom L q' :=
      ⟨J_hat', hJdefBf, hqprimeClosed⟩
    have hlocalBf : Ideal.IsRigPointLocalCondition q' :=
      (htfaeBf.out 2 8).mp hcondition2Bf
    rcases hlocalBf with ⟨hlocalBf, _, _, _, _, _, hradmax⟩
    let : IsLocalRing (CompletedAway J (φ f) ⧸ q') := hlocalBf
    have hresnil (x : CompletedAway J (φ f)) (hx : x ∈ nilBhat) :
        IsLocalRing.residue (CompletedAway J (φ f) ⧸ q')
          (Ideal.Quotient.mk q' x) = 0 :=
      residue_eq_zero_of_mem_topologicalNilradical J_hat' hradJhat' q'
        (hradmax J_hat' hJdefBf) x hx
    have hnil : a ≤ Ideal.comap φ b := topologicalNilradical_le_comap φ hφ
    let φred : A ⧸ a →+* B ⧸ b := Ideal.quotientMap b φ hnil
    change φred.FiniteType at hred
    let SA := A_loc ⧸ aLoc
    let SB := B_loc ⧸ bLoc
    let iotaA : A ⧸ a →+* SA :=
      Ideal.quotientMap aLoc (algebraMap A A_loc) (by
        intro x hx
        exact Ideal.mem_map_of_mem (algebraMap A A_loc) hx)
    let iotaB : B ⧸ b →+* SB :=
      Ideal.quotientMap bLoc (algebraMap B B_loc) (by
        intro x hx
        exact Ideal.mem_map_of_mem (algebraMap B B_loc) hx)
    let : Algebra (A ⧸ a) SA := iotaA.toAlgebra
    let : Algebra (B ⧸ b) SB := iotaB.toAlgebra
    let : Algebra A SA := Algebra.compHom SA (algebraMap A A_loc)
    let : Algebra B SB := Algebra.compHom SB (algebraMap B B_loc)
    have hmapA (x : A) : iotaA (Ideal.Quotient.mk a x) = algebraMap A SA x := by
      change iotaA (Ideal.Quotient.mk a x) =
        Ideal.Quotient.mk aLoc (algebraMap A A_loc x)
      exact RingHom.congr_fun (Ideal.quotientMap_comp_mk
        (J := a) (I := aLoc) (f := algebraMap A A_loc)
        (fun _ hx => Ideal.mem_map_of_mem (algebraMap A A_loc) hx)) x
    have hmapB (x : B) : iotaB (Ideal.Quotient.mk b x) = algebraMap B SB x := by
      change iotaB (Ideal.Quotient.mk b x) =
        Ideal.Quotient.mk bLoc (algebraMap B B_loc x)
      exact RingHom.congr_fun (Ideal.quotientMap_comp_mk
        (J := b) (I := bLoc) (f := algebraMap B B_loc)
        (fun _ hx => Ideal.mem_map_of_mem (algebraMap B B_loc) hx)) x
    have : IsLocalization.Away (Ideal.Quotient.mk a f) SA :=
      isLocalization_away_quotient a f
    have hredf : φred (Ideal.Quotient.mk a f) =
        Ideal.Quotient.mk b (φ f) := by
      simp [φred, Ideal.quotientMap_mk]
    have : IsLocalization.Away (φred (Ideal.Quotient.mk a f)) SB := by
      simpa [hredf] using isLocalization_away_quotient b (φ f)
    have huunit : IsUnit (iotaB (φred (Ideal.Quotient.mk a f))) := by
      rw [hredf]
      exact IsLocalization.Away.algebraMap_isUnit (φred (Ideal.Quotient.mk a f))
    let u : SA →+* SB := IsLocalization.Away.lift (Ideal.Quotient.mk a f)
      (g := iotaB.comp φred) huunit
    have hucomp : u.comp iotaA = iotaB.comp φred := by
      dsimp [u]
      exact IsLocalization.Away.lift_comp (R := A ⧸ a) (S := SA) (P := SB)
        (x := Ideal.Quotient.mk a f) (g := iotaB.comp φred) huunit
    have : IsLocalization.Away (Ideal.Quotient.mk b (φ f)) SB := by
      rw [← hredf]
      infer_instance
    have hsft : (algebraMap (B ⧸ b) SB).FiniteType := by
      rw [RingHom.finiteType_algebraMap]
      exact IsLocalization.finiteType_of_monoid_fg
        (Submonoid.powers (Ideal.Quotient.mk b (φ f))) SB
    have huft : u.FiniteType := by
      have hcompft : (u.comp iotaA).FiniteType := by
        rw [hucomp]
        exact hsft.comp hred
      exact RingHom.FiniteType.of_comp_finiteType (f := iotaA) hcompft
    have hucompat : u.comp (Ideal.Quotient.mk aLoc) =
        (Ideal.Quotient.mk bLoc).comp φf := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
      ext x
      have hquotA := RingHom.congr_fun (Ideal.quotientMap_comp_mk
        (J := a) (I := aLoc) (f := algebraMap A A_loc)
        (fun _ hx => Ideal.mem_map_of_mem (algebraMap A A_loc) hx)) x
      calc
        u (Ideal.Quotient.mk aLoc (algebraMap A A_loc x)) =
            u (iotaA (Ideal.Quotient.mk a x)) :=
          congrArg u hquotA.symm
        _ = iotaB (φred (Ideal.Quotient.mk a x)) :=
          RingHom.congr_fun hucomp (Ideal.Quotient.mk a x)
        _ = iotaB (Ideal.Quotient.mk b (φ x)) := by
          simp [φred, Ideal.quotientMap_mk]
        _ = Ideal.Quotient.mk bLoc (algebraMap B B_loc (φ x)) :=
          RingHom.congr_fun (Ideal.quotientMap_comp_mk (J := b) (I := bLoc)
            (f := algebraMap B B_loc) fun _ hx => Ideal.mem_map_of_mem (algebraMap B B_loc) hx)
            (φ x)
        _ = Ideal.Quotient.mk bLoc (φf (algebraMap A A_loc x)) := by
          congr 1
          dsimp [φf, IsLocalization.Away.map]
          symm
          apply IsLocalization.map_eq
    have hsurjA' : Function.Surjective
        (algebraMap A_loc (A_f ⧸ nilAhat)) := by
      intro x
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := aLoc) (eA x)
      refine ⟨z, eA.injective ?_⟩
      change eA (Ideal.Quotient.mk nilAhat
        (algebraMap A_loc A_f z)) = eA x
      rw [heA]
      exact hz
    let redψ : A_f ⧸ nilAhat →+*
        CompletedAway J (φ f) ⧸ nilBhat :=
      Ideal.quotientMap nilBhat ψ (topologicalNilradical_le_comap ψ hψcont)
    have hredψ : redψ.FiniteType := by
      have hmaps : redψ = eB.symm.toRingHom.comp (u.comp eA.toRingHom) := by
        apply RingHom.ext
        intro x
        obtain ⟨z, rfl⟩ := hsurjA' x
        apply eB.injective
        simp only [RingHom.comp_apply]
        change eB (redψ (Ideal.Quotient.mk nilAhat
          (algebraMap A_loc A_f z))) =
          eB (eB.symm (u (eA (Ideal.Quotient.mk nilAhat
            (algebraMap A_loc A_f z)))))
        rw [RingEquiv.apply_symm_apply]
        change eB (Ideal.Quotient.mk nilBhat
          (ψ (algebraMap A_loc A_f z))) = _
        rw [heA]
        have hψz : ψ (algebraMap A_loc A_f z) =
            algebraMap B_loc (CompletedAway J (φ f)) (φf z) := by
          simpa only [RingHom.comp_apply] using
            congrArg (fun g : A_loc →+* CompletedAway J (φ f) => g z) hcomp
        rw [hψz, heB (φf z)]
        exact (RingHom.congr_fun hucompat z).symm
      have heAft : eA.toRingHom.FiniteType :=
        RingHom.FiniteType.of_surjective _ eA.surjective
      have heBsymmft : eB.symm.toRingHom.FiniteType :=
        RingHom.FiniteType.of_surjective _ eB.symm.surjective
      have hcompft :
          (eB.symm.toRingHom.comp (u.comp eA.toRingHom)).FiniteType :=
        heBsymmft.comp (huft.comp heAft)
      rw [hmaps]
      exact hcompft
    let : IsLocalRing (B_f ⧸ q') := eBquot.isLocalRing
    let κ0 := Localization.Away (χ.rangeRestrict r)
    have : IsLocalization.Away r SA := hfr ▸
      (isLocalization_away_quotient a f)
    let : Algebra (χ.range) κ0 := inferInstance
    let : IsLocalization.Away (χ.rangeRestrict r) κ0 := inferInstance
    let : Algebra κ0 κ := hAlg
    let : IsScalarTower (χ.range) κ0 κ := hTower
    let : Module.Finite κ0 κ := hfinite
    let eκ : κ ≃+* IsLocalRing.ResidueField (B_f ⧸ q') :=
      IsLocalRing.ResidueField.mapEquiv eBquot
    have hvunit : IsUnit
        ((algebraMap (χ.range) κ0) (χ.rangeRestrict r)) :=
      IsLocalization.Away.algebraMap_isUnit (χ.rangeRestrict r)
    let v : SA →+* κ0 := IsLocalization.Away.lift r
      (g := (algebraMap (χ.range) κ0).comp χ.rangeRestrict) hvunit
    have hv_surj : Function.Surjective v :=
      IsLocalization.map_surjective_of_surjective
        (M := Submonoid.powers r) (S := SA) (Q := κ0) (g := χ.rangeRestrict)
        χ.rangeRestrict_surjective
    have hAlgfinite : (algebraMap κ0 κ).Finite := RingHom.finite_algebraMap.mpr hfinite
    let vκ : SA →+* κ := (algebraMap κ0 κ).comp v
    have hvκfinite : vκ.Finite :=
      RingHom.Finite.comp hAlgfinite (RingHom.Finite.of_surjective v hv_surj)
    let η : A_f ⧸ nilAhat →+* IsLocalRing.ResidueField (B_f ⧸ q') :=
      eκ.toRingHom.comp (vκ.comp eA.toRingHom)
    have hηfinite : η.Finite := (RingHom.Finite.of_surjective _ eκ.surjective).comp
      (hvκfinite.comp (RingHom.Finite.of_surjective _ eA.surjective))
    have hcompatLoc :
        (η.comp (Ideal.Quotient.mk nilAhat)).comp (algebraMap A_loc A_f) =
          (IsLocalRing.residue (B_f ⧸ q')).comp
            ((Ideal.Quotient.mk q').comp (ψ.comp (algebraMap A_loc A_f))) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext x
      have hmapv : v.comp iotaA =
          (algebraMap (χ.range) κ0).comp χ.rangeRestrict := by
        dsimp [v, iotaA]
        exact IsLocalization.Away.lift_comp (R := A ⧸ a) (S := SA) (P := κ0)
          (x := r) (g := (algebraMap (χ.range) κ0).comp χ.rangeRestrict) hvunit
      have hleft : vκ (Ideal.Quotient.mk aLoc
          (algebraMap A A_loc x)) = χ (Ideal.Quotient.mk a x) := by
        calc
          vκ (Ideal.Quotient.mk aLoc (algebraMap A A_loc x)) =
              vκ (iotaA (Ideal.Quotient.mk a x)) :=
            congrArg vκ (hmapA x).symm
          _ = algebraMap κ0 κ (v (iotaA (Ideal.Quotient.mk a x))) := rfl
          _ = algebraMap κ0 κ
              (algebraMap (χ.range) κ0 (χ.rangeRestrict (Ideal.Quotient.mk a x))) :=
            congrArg (algebraMap κ0 κ)
              (RingHom.congr_fun hmapv (Ideal.Quotient.mk a x))
          _ = χ (Ideal.Quotient.mk a x) := by
            rw [← IsScalarTower.algebraMap_apply (χ.range) κ0 κ
              (χ.rangeRestrict (Ideal.Quotient.mk a x))]
            rfl
      have hψx : ψ (algebraMap A_loc A_f
          (algebraMap A A_loc x)) = algebraMap B B_f (φ x) := by
        calc
          _ = algebraMap B_loc B_f (φf (algebraMap A A_loc x)) :=
            RingHom.congr_fun hcomp (algebraMap A A_loc x)
          _ = algebraMap B B_f (φ x) := by
            rw [IsScalarTower.algebraMap_apply B B_loc B_f]
            congr 1
            dsimp [φf, IsLocalization.Away.map]
            apply IsLocalization.map_eq
      have hright : IsLocalRing.residue (B_f ⧸ q')
          (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f
            (algebraMap A A_loc x)))) =
          eκ (χ (Ideal.Quotient.mk a x)) := by
        calc
          IsLocalRing.residue (B_f ⧸ q')
              (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f
                (algebraMap A A_loc x)))) =
              eκ (IsLocalRing.residue (B ⧸ q)
                (Ideal.Quotient.mk q (φ x))) := by
            rw [hψx, ← heBquot (φ x), IsLocalRing.ResidueField.mapEquiv_apply,
              IsLocalRing.ResidueField.map_residue]
            rfl
        _ = eκ (χ (Ideal.Quotient.mk a x)) :=
          congrArg eκ (RingHom.congr_fun hχcomp x).symm
      calc
        η (Ideal.Quotient.mk nilAhat
            (algebraMap A_loc A_f (algebraMap A A_loc x))) =
            eκ (χ (Ideal.Quotient.mk a x)) := by
          change eκ (vκ (eA (Ideal.Quotient.mk nilAhat
            (algebraMap A_loc A_f (algebraMap A A_loc x)))) ) = _
          rw [heA, hleft]
        _ = IsLocalRing.residue (B_f ⧸ q')
            (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f
              (algebraMap A A_loc x)))) := hright.symm
    have hηcompat : η.comp (Ideal.Quotient.mk nilAhat) =
        (IsLocalRing.residue (B_f ⧸ q')).comp
          ((Ideal.Quotient.mk q').comp ψ) := by
      apply RingHom.ext
      intro x
      obtain ⟨z, hz⟩ := hsurjA' (Ideal.Quotient.mk nilAhat x)
      have hdiff : algebraMap A_loc A_f z - x ∈ nilAhat :=
        Ideal.Quotient.eq.mp hz
      have hdiffψ : ψ (algebraMap A_loc A_f z) - ψ x ∈ nilBhat := by
        rw [← ψ.map_sub]
        exact topologicalNilradical_le_comap ψ hψcont hdiff
      have hresEq :
          IsLocalRing.residue (B_f ⧸ q') (Ideal.Quotient.mk q'
            (ψ (algebraMap A_loc A_f z))) =
          IsLocalRing.residue (B_f ⧸ q') (Ideal.Quotient.mk q' (ψ x)) := by
        refine sub_eq_zero.mp ?_
        calc IsLocalRing.residue (B_f ⧸ q')
                (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f z))) -
              IsLocalRing.residue (B_f ⧸ q') (Ideal.Quotient.mk q' (ψ x)) =
            IsLocalRing.residue (B_f ⧸ q')
              (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f z)) -
                Ideal.Quotient.mk q' (ψ x)) :=
          ((IsLocalRing.residue (B_f ⧸ q')).map_sub _ _).symm
        _ = IsLocalRing.residue (B_f ⧸ q')
              (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f z) - ψ x)) :=
          congrArg (IsLocalRing.residue (B_f ⧸ q'))
            ((Ideal.Quotient.mk q').map_sub (ψ (algebraMap A_loc A_f z)) (ψ x)).symm
        _ = 0 := hresnil _ hdiffψ
      calc
        η (Ideal.Quotient.mk nilAhat x) =
            η (algebraMap A_loc (A_f ⧸ nilAhat) z) := congrArg η hz.symm
        _ = IsLocalRing.residue (B_f ⧸ q')
            (Ideal.Quotient.mk q' (ψ (algebraMap A_loc A_f z))) :=
          RingHom.congr_fun hcompatLoc z
        _ = IsLocalRing.residue (B_f ⧸ q')
            (Ideal.Quotient.mk q' (ψ x)) := hresEq
    have hcondition0 : ∃ hlocal' : IsLocalRing (B_f ⧸ q'),
        let : IsLocalRing (B_f ⧸ q') := hlocal'
        ∃ ρ : (A_f ⧸ nilAhat) →+* IsLocalRing.ResidueField (B_f ⧸ q'),
          ρ.comp (Ideal.Quotient.mk nilAhat) =
              (IsLocalRing.residue (B_f ⧸ q')).comp
                ((Ideal.Quotient.mk q').comp ψ) ∧ ρ.Finite := by
      refine ⟨eBquot.isLocalRing, η, hηcompat, ?_⟩
      exact hηfinite
    have hψft : TopologicalRing.IsTopologicallyOfFiniteType ψ :=
      isTopologicallyOfFiniteType_of_isFiniteTypeOnReductions
        ψ hψcont hweakB hredψ
    have htfaeψ := rigPoint_relative_tfae
      hweakA hweakB ψ hψcont hψadic hψft q' hqprimeClosedN
    have hpclosedNil : Ideal.IsClosedPointAwayFrom nilAhat p' :=
      (htfaeψ.out 1 2).mp hcondition0
    have hradIhat : I_hat.radical = nilAhat :=
      radical_eq_topologicalNilradical_of_isAdic I_hat rfl
    exact (closedPointAway_iff_topologicalNilradical I_hat p' hradIhat).mpr hpclosedNil

/-- After a suitable completed principal localization, the prime below a
rig-closed point is rig-closed as well. -/
@[stacks 0GGG]
public theorem exists_isClosedPointAwayFrom_completedAway_comap
    {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (φ : A →+* B) (hφ : Continuous φ)
    (hadic : RingHom.IsAdic φ)
    (hft : TopologicalRing.IsTopologicallyOfFiniteType φ)
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.IsClosedPointAwayFrom
      (topologicalNilradical B) q) :
    let I := hadic.choose
    let J := I.map φ
    ∃ f : A,
      IsUnit (Ideal.Quotient.mk q (φ f)) ∧
        (let A_f := CompletedAway I f
         let B_f := CompletedAway J (φ f)
         let ψ : A_f →+* B_f := RingHom.completedAwayMap φ I f
         let I_f := I.map (algebraMap A (Localization.Away f))
         let J_f := J.map (algebraMap B (Localization.Away (φ f)))
         let I_hat := I_f.map (algebraMap (Localization.Away f) A_f)
         let J_hat := J_f.map (algebraMap (Localization.Away (φ f)) B_f)
         let q' := extendedIdeal J q (φ f)
         let p' := q'.comap ψ
         ψ.comp (algebraMap A A_f) = (algebraMap B B_f).comp φ ∧
           (∃ hqprime : q'.IsPrime,
             letI : q'.IsPrime := hqprime
             ∃ hpprime : p'.IsPrime,
               letI : p'.IsPrime := hpprime
               Ideal.IsClosedPointAwayFrom J_hat q' ∧
                 Ideal.IsClosedPointAwayFrom I_hat p')) :=
  exists_isClosedPointAwayFrom_completedAway_comap_of_isAdic hA hB φ hφ hadic.choose
    hadic.choose_spec.1 hadic.choose_spec.2 hft q hq

end

end Rig

end
