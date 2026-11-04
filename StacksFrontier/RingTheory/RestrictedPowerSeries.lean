module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.Topology.Algebra.UniformRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow

/-!
# Restricted power series

The ring of restricted power series over a linearly topologized ring `A` in the variables
`x₁, …, x_n` is the inverse limit of the polynomial rings `A/I[x₁, …, x_n]` over the open
ideals `I` of `A`.  This file constructs that limit as a topological `A`-algebra, identifies it
with the `I`-adic completion of `A[x₁, …, x_n]` when `A` is `I`-adic, and proves its universal
property: a continuous `A`-algebra map out of it is determined by, and exists for, any choice
of topologically nilpotent images of the variables.

## References

* [Stacks Project, Tag 0AJM](https://stacks.math.columbia.edu/tag/0AJM)
* [Stacks Project, Tag 0AL0](https://stacks.math.columbia.edu/tag/0AL0)
-/

@[expose] public section

section

universe u v w

variable {A : Type u} [CommRing A]

namespace RestrictedPowerSeries

/-- The transition map attached to an antitone system of ideals.  Such a system is the algebraic
data of a chosen fundamental system for a linear topology. -/
@[implicit_reducible]
public noncomputable def idealSystemTransition {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) {i j : ι} (hij : i ≤ j) :
    MvPolynomial σ (A ⧸ J j) →+* MvPolynomial σ (A ⧸ J i) :=
  MvPolynomial.map <| Ideal.Quotient.factor (hJ hij)

/-- The inverse-limit subring associated to an antitone system of coefficient ideals.  Taking
the open ideals in a linearly topologized ring (with a cofiltered indexing order) gives its
general restricted power series ring. -/
public noncomputable def idealSystemInverseLimitSubring {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    Subring (∀ i : ι, MvPolynomial σ (A ⧸ J i)) where
  carrier f := ∀ ⦃i j : ι⦄ (hij : i ≤ j), idealSystemTransition J hJ σ hij (f j) = f i
  zero_mem' := fun _ _ _ ↦ map_zero _
  one_mem' := fun _ _ _ ↦ map_one _
  add_mem' hf hg := by
    intro i j hij
    simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hf hij) (hg hij)
  mul_mem' hf hg := by
    intro i j hij
    simpa only [Pi.mul_apply, map_mul] using congrArg₂ (· * ·) (hf hij) (hg hij)
  neg_mem' hf := by
    intro i j hij
    simpa only [Pi.neg_apply, map_neg] using congrArg Neg.neg (hf hij)

/-- The transition map between coefficient-quotient polynomial rings. -/
public noncomputable abbrev coefficientTransition (I : Ideal A) (σ : Type v) {m n : ℕ}
    (hmn : m ≤ n) :
    MvPolynomial σ (A ⧸ I ^ n) →+* MvPolynomial σ (A ⧸ I ^ m) :=
  idealSystemTransition (fun n : ℕ ↦ I ^ n) (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ hmn

/-- The compatible families which form the inverse limit of `(A ⧸ I ^ n)[σ]`. -/
public noncomputable abbrev inverseLimitSubring (I : Ideal A) (σ : Type v) :
    Subring (∀ n : ℕ, MvPolynomial σ (A ⧸ I ^ n)) :=
  idealSystemInverseLimitSubring (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ

end RestrictedPowerSeries

/-- Restricted power series for a chosen fundamental system of ideals in a linearly topologized
ring.  Coefficients live in the corresponding completion: in particular, with no variables this
is the inverse limit of the coefficient quotients, rather than the original ring. -/
@[ega "0 7.5.1"]
public noncomputable abbrev RestrictedPowerSeriesOfIdeals {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) : Type (max u v w) :=
  RestrictedPowerSeries.idealSystemInverseLimitSubring J hJ σ

/-- Restricted power series over `A`: the inverse limit of `(A ⧸ I ^ n)[σ]`. -/
@[ega "0 7.5.1" "special case"]
public noncomputable abbrev RestrictedPowerSeries (I : Ideal A) (σ : Type v) :
    Type (max u v) :=
  RestrictedPowerSeries.inverseLimitSubring I σ

namespace RestrictedPowerSeries

/-- Projection from the restricted series for an ideal system to one coefficient quotient. -/
@[implicit_reducible]
public noncomputable def idealSystemProjection {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) (i : ι) :
    RestrictedPowerSeriesOfIdeals J hJ σ →+* MvPolynomial σ (A ⧸ J i) :=
  (Pi.evalRingHom (fun i ↦ MvPolynomial σ (A ⧸ J i)) i).comp
    (idealSystemInverseLimitSubring J hJ σ).subtype

/-- The limit topology for a chosen fundamental system of ideals. -/
public noncomputable instance idealSystemLimitTopology {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    TopologicalSpace (RestrictedPowerSeriesOfIdeals J hJ σ) :=
  let : ∀ i : ι, TopologicalSpace (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⊥
  inferInstance

/-- Restricted power series for an ideal system form a topological ring in the limit topology. -/
public noncomputable instance idealSystemIsTopologicalRing {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    let _ := idealSystemLimitTopology J hJ σ
    IsTopologicalRing (RestrictedPowerSeriesOfIdeals J hJ σ) := by
  let : ∀ i : ι, TopologicalSpace (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⊥
  let : ∀ i : ι, DiscreteTopology (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⟨rfl⟩
  let : ∀ i : ι, IsTopologicalRing (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ inferInstance
  exact Subring.instIsTopologicalRing (idealSystemInverseLimitSubring J hJ σ)

/-- The canonical additive uniformity of the inverse limit for an ideal system. -/
public noncomputable instance idealSystemUniformSpace {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    UniformSpace (RestrictedPowerSeriesOfIdeals J hJ σ) :=
  IsTopologicalAddGroup.rightUniformSpace _

/-- The inverse-limit uniformity is compatible with the additive group. -/
public instance idealSystemIsUniformAddGroup {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    IsUniformAddGroup (RestrictedPowerSeriesOfIdeals J hJ σ) :=
  isUniformAddGroup_of_addCommGroup

/-- A compatible family is determined by its coefficient-quotient projections. -/
@[ext]
public theorem idealSystem_ext {ι : Type w} [Preorder ι]
    {J : ι → Ideal A} {hJ : Antitone J} {σ : Type v}
    {f g : RestrictedPowerSeriesOfIdeals J hJ σ}
    (h : ∀ i, idealSystemProjection J hJ σ i f = idealSystemProjection J hJ σ i g) :
    f = g :=
  Subtype.ext (funext h)

/-- The canonical map from polynomials into the coefficient-quotient inverse limit. -/
@[implicit_reducible]
public noncomputable def idealSystemPolynomialRingHom {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    MvPolynomial σ A →+* RestrictedPowerSeriesOfIdeals J hJ σ where
  toFun p := ⟨fun i ↦ MvPolynomial.map (Ideal.Quotient.mk (J i)) p, by
    intro i j hij
    simp only [idealSystemTransition, MvPolynomial.map_map, Ideal.Quotient.factor_comp_mk]⟩
  map_one' := Subtype.ext (funext fun i ↦ (MvPolynomial.map (Ideal.Quotient.mk (J i))).map_one)
  map_mul' p q := Subtype.ext (funext fun i ↦
    (MvPolynomial.map (Ideal.Quotient.mk (J i))).map_mul p q)
  map_zero' := Subtype.ext (funext fun i ↦ (MvPolynomial.map (Ideal.Quotient.mk (J i))).map_zero)
  map_add' p q := Subtype.ext (funext fun i ↦
    (MvPolynomial.map (Ideal.Quotient.mk (J i))).map_add p q)

/-- The canonical coefficient algebra structure for any ideal system. -/
public noncomputable instance idealSystemAlgebra {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    Algebra A (RestrictedPowerSeriesOfIdeals J hJ σ) :=
  ((idealSystemPolynomialRingHom J hJ σ).comp MvPolynomial.C).toAlgebra

/-- The polynomial inclusion as an algebra homomorphism for a general ideal system. -/
@[implicit_reducible]
public noncomputable def idealSystemPolynomialAlgHom {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) :
    MvPolynomial σ A →ₐ[A] RestrictedPowerSeriesOfIdeals J hJ σ :=
  { idealSystemPolynomialRingHom J hJ σ with commutes' := fun _ ↦ rfl }

/-- At each level, the canonical polynomial map is coefficient reduction. -/
@[simp]
public theorem idealSystemProjection_polynomialRingHom {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) (i : ι)
    (p : MvPolynomial σ A) :
    idealSystemProjection J hJ σ i (idealSystemPolynomialRingHom J hJ σ p) =
      MvPolynomial.map (Ideal.Quotient.mk (J i)) p := rfl

/-- The coefficient algebra map reduces to the constant polynomial at every level. -/
@[simp]
public theorem idealSystemProjection_algebraMap {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) (i : ι) (a : A) :
    idealSystemProjection J hJ σ i
        (algebraMap A (RestrictedPowerSeriesOfIdeals J hJ σ) a) =
      MvPolynomial.C (Ideal.Quotient.mk (J i) a) :=
  MvPolynomial.map_C _ _

/-- The projections of the general inverse limit commute with its transition maps. -/
public theorem idealSystemTransition_projection {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v) {i j : ι} (hij : i ≤ j)
    (f : RestrictedPowerSeriesOfIdeals J hJ σ) :
    idealSystemTransition J hJ σ hij (idealSystemProjection J hJ σ j f) =
      idealSystemProjection J hJ σ i f := f.property hij

/-- The limit topology is characterized by continuity of all quotient projections. -/
public theorem continuous_idealSystem_iff {ι : Type w} [Preorder ι]
    (J : ι → Ideal A) (hJ : Antitone J) (σ : Type v)
    {X : Type*} [TopologicalSpace X] (f : X → RestrictedPowerSeriesOfIdeals J hJ σ) :
    Continuous f ↔ ∀ i, @Continuous X (MvPolynomial σ (A ⧸ J i))
      _ ⊥ (fun x ↦ idealSystemProjection J hJ σ i (f x)) := by
  let : ∀ i : ι, TopologicalSpace (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⊥
  show Continuous f ↔ ∀ i, Continuous (fun x ↦ (f x).val i)
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- The power system of an ideal gives exactly the adic restricted power series construction. -/
public noncomputable def adicIdealSystemEquiv (I : Ideal A) (σ : Type v) :
    RestrictedPowerSeriesOfIdeals (fun n : ℕ ↦ I ^ n)
        (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ ≃+*
      RestrictedPowerSeries I σ :=
  RingEquiv.refl _

/-- The canonical coefficient homomorphism from `A` to its restricted power series ring. -/
@[implicit_reducible]
public noncomputable def coefficientRingHom (I : Ideal A) (σ : Type v) :
    A →+* RestrictedPowerSeries I σ :=
  (idealSystemPolynomialRingHom (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ).comp MvPolynomial.C

/-- The natural `A`-algebra structure on restricted power series. -/
public noncomputable instance coefficientAlgebra (I : Ideal A) (σ : Type v) :
    Algebra A (RestrictedPowerSeries I σ) :=
  (coefficientRingHom I σ).toAlgebra

/-- The canonical map from polynomials into adic restricted power series. -/
public noncomputable abbrev polynomialRingHom (I : Ideal A) (σ : Type v) :
    MvPolynomial σ A →+* RestrictedPowerSeries I σ :=
  idealSystemPolynomialRingHom (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ

/-- The polynomial inclusion as an algebra homomorphism. -/
public noncomputable abbrev polynomialAlgHom (I : Ideal A) (σ : Type v) :
    MvPolynomial σ A →ₐ[A] RestrictedPowerSeries I σ :=
  idealSystemPolynomialAlgHom (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ

/-- Projection of a restricted power series to the polynomial ring over `A ⧸ I ^ n`. -/
public noncomputable abbrev coefficientProjection (I : Ideal A) (σ : Type v) (n : ℕ) :
    RestrictedPowerSeries I σ →+* MvPolynomial σ (A ⧸ I ^ n) :=
  idealSystemProjection (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ n

/-- Reduction of a polynomial viewed as a restricted power series. -/
@[simp]
public theorem coefficientProjection_polynomialRingHom (I : Ideal A) (σ : Type v) (n : ℕ)
    (p : MvPolynomial σ A) :
    coefficientProjection I σ n (polynomialRingHom I σ p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := rfl

/-- Reduction of a constant restricted power series. -/
@[simp]
public theorem coefficientProjection_algebraMap (I : Ideal A) (σ : Type v) (n : ℕ) (a : A) :
    coefficientProjection I σ n (algebraMap A (RestrictedPowerSeries I σ) a) =
      MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a) :=
  MvPolynomial.map_C _ _

/-- The coefficient projections commute with all transition maps. -/
public theorem coefficientTransition_projection (I : Ideal A) (σ : Type v) {m n : ℕ}
    (hmn : m ≤ n) :
    (coefficientTransition I σ hmn).comp (coefficientProjection I σ n) =
      coefficientProjection I σ m :=
  DFunLike.ext _ _ fun f ↦ f.property hmn

/-- The canonical equivalence between the coefficient quotient at level `n` and the quotient
of the polynomial ring by the `n`-th power of the extended coefficient ideal. -/
@[implicit_reducible, ega "0 10.3.1.1" "partial"]
public noncomputable def polynomialQuotientEquiv (I : Ideal A) (σ : Type v) (n : ℕ) :
    MvPolynomial σ (A ⧸ I ^ n) ≃+*
      MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n :=
  (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (I ^ n)).toRingEquiv.trans
    (Ideal.quotEquivOfEq (Ideal.map_pow (MvPolynomial.C : A →+* MvPolynomial σ A) I n))

/-- The inverse finite-level equivalence sends a polynomial class to coefficient reduction. -/
@[simp]
public theorem polynomialQuotientEquiv_symm_mk (I : Ideal A) (σ : Type v) (n : ℕ)
    (p : MvPolynomial σ A) :
    (polynomialQuotientEquiv I σ n).symm (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p := by
  simp only [polynomialQuotientEquiv, RingEquiv.symm_trans_apply,
    Ideal.quotEquivOfEq_symm, Ideal.quotEquivOfEq_mk]
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

/-- The finite-level equivalence commutes with the canonical polynomial maps. -/
@[simp]
public theorem polynomialQuotientEquiv_map_mk (I : Ideal A) (σ : Type v) (n : ℕ)
    (p : MvPolynomial σ A) :
    polynomialQuotientEquiv I σ n (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p) =
      Ideal.Quotient.mk _ p := by
  rw [← polynomialQuotientEquiv_symm_mk I σ n p, RingEquiv.apply_symm_apply]

/-- The finite-level quotient identifications are natural in the exponent. -/
public theorem polynomialQuotientEquiv_transition (I : Ideal A) (σ : Type v)
    {m n : ℕ} (hmn : m ≤ n) (p : MvPolynomial σ (A ⧸ I ^ n)) :
    polynomialQuotientEquiv I σ m (coefficientTransition I σ hmn p) =
      Ideal.Quotient.factorPow (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) hmn
        (polynomialQuotientEquiv I σ n p) := by
  obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective (polynomialQuotientEquiv I σ n p)
  obtain rfl : p = MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) q := by
    rw [← polynomialQuotientEquiv_symm_mk, hq, RingEquiv.symm_apply_apply]
  simp [coefficientTransition, idealSystemTransition, MvPolynomial.map_map,
    Ideal.Quotient.factor_comp_mk]

/-- Projection to `A[σ] / (I A[σ])^n`.  Together with
`coefficientTransition_projection`, this is the canonical finite-level bridge between the two
inverse-limit descriptions in the source. -/
public noncomputable def polynomialQuotientProjection (I : Ideal A) (σ : Type v) (n : ℕ) :
    RestrictedPowerSeries I σ →+*
      MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n :=
  (polynomialQuotientEquiv I σ n).toRingHom.comp (coefficientProjection I σ n)

/-- The canonical transition map between the polynomial-ring quotients. -/
public noncomputable abbrev polynomialTransition (I : Ideal A) (σ : Type v) {m n : ℕ}
    (hmn : m ≤ n) :
    (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) →+*
      MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ m :=
  Ideal.Quotient.factorPow (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) hmn

/-- The polynomial-quotient projections commute with all transition maps. -/
public theorem polynomialTransition_projection (I : Ideal A) (σ : Type v) {m n : ℕ}
    (hmn : m ≤ n) :
    (polynomialTransition I σ hmn).comp (polynomialQuotientProjection I σ n) =
      polynomialQuotientProjection I σ m := by
  apply DFunLike.ext _ _
  intro f
  show polynomialTransition I σ hmn
      (polynomialQuotientEquiv I σ n (coefficientProjection I σ n f)) = _
  rw [← polynomialQuotientEquiv_transition]
  exact congrArg (polynomialQuotientEquiv I σ m) (f.property hmn)

/-- The canonical map from restricted power series to the completion of the polynomial ring. -/
@[implicit_reducible]
public noncomputable def toAdicCompletion (I : Ideal A) (σ : Type v) :
    RestrictedPowerSeries I σ →+*
      AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) :=
  AdicCompletion.liftRingHom _ (polynomialQuotientProjection I σ)
    (fun hmn ↦ polynomialTransition_projection I σ hmn)

/-- The completion map preserves the canonical quotient projections. -/
@[simp]
public theorem eval_toAdicCompletion (I : Ideal A) (σ : Type v) (n : ℕ)
    (f : RestrictedPowerSeries I σ) :
    AdicCompletion.evalₐ _ n (toAdicCompletion I σ f) =
      polynomialQuotientProjection I σ n f :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ _ _

/-- The canonical map from the polynomial completion to coefficient-quotient families. -/
@[implicit_reducible]
public noncomputable def fromAdicCompletion (I : Ideal A) (σ : Type v) :
    AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) →+*
      RestrictedPowerSeries I σ where
  toFun f := ⟨fun n ↦ (polynomialQuotientEquiv I σ n).symm (AdicCompletion.evalₐ _ n f), by
    intro m n hmn
    apply (polynomialQuotientEquiv I σ m).injective
    rw [polynomialQuotientEquiv_transition, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, AdicCompletion.factorPow_evalₐ]⟩
  map_one' := Subtype.ext <| funext fun _ ↦ map_one _
  map_mul' f g := Subtype.ext <| funext fun n ↦
    ((polynomialQuotientEquiv I σ n).symm.toRingHom.comp
      (AdicCompletion.evalₐ _ n).toRingHom).map_mul f g
  map_zero' := Subtype.ext <| funext fun _ ↦ map_zero _
  map_add' f g := Subtype.ext <| funext fun n ↦
    ((polynomialQuotientEquiv I σ n).symm.toRingHom.comp
      (AdicCompletion.evalₐ _ n).toRingHom).map_add f g

/-- The canonical identification of the two algebraic inverse limits. -/
@[implicit_reducible]
public noncomputable def adicCompletionEquiv (I : Ideal A) (σ : Type v) :
    RestrictedPowerSeries I σ ≃+*
      AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) :=
  { toAdicCompletion I σ with
    invFun := fromAdicCompletion I σ
    left_inv := fun f ↦ by
      apply Subtype.ext
      funext n
      change (polynomialQuotientEquiv I σ n).symm
        (AdicCompletion.evalₐ _ n (toAdicCompletion I σ f)) = f.val n
      rw [eval_toAdicCompletion]
      exact (polynomialQuotientEquiv I σ n).symm_apply_apply _
    right_inv := fun f ↦ by
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ _ n
        (toAdicCompletion I σ (fromAdicCompletion I σ f)) = AdicCompletion.evalₐ _ n f
      rw [eval_toAdicCompletion]
      exact (polynomialQuotientEquiv I σ n).apply_symm_apply _ }

/-- The canonical equivalence commutes with reduction to every polynomial quotient. -/
@[simp]
public theorem eval_adicCompletionEquiv (I : Ideal A) (σ : Type v) (n : ℕ)
    (f : RestrictedPowerSeries I σ) :
    AdicCompletion.evalₐ _ n (adicCompletionEquiv I σ f) =
      polynomialQuotientProjection I σ n f := eval_toAdicCompletion I σ n f

/-- The completion equivalence is canonical on the polynomial subalgebra. -/
@[simp]
public theorem adicCompletionEquiv_polynomialRingHom (I : Ideal A) (σ : Type v)
    (p : MvPolynomial σ A) :
    adicCompletionEquiv I σ (polynomialRingHom I σ p) = AdicCompletion.of _ _ p := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [eval_adicCompletionEquiv, AdicCompletion.evalₐ_of]
  exact polynomialQuotientEquiv_map_mk I σ n p

/-- The canonical completion identification respects the coefficient algebra structures. -/
@[implicit_reducible]
public noncomputable def adicCompletionAlgEquiv (I : Ideal A) (σ : Type v) :
    RestrictedPowerSeries I σ ≃ₐ[A]
      AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) :=
  { adicCompletionEquiv I σ with
    commutes' := fun a ↦ adicCompletionEquiv_polynomialRingHom I σ (MvPolynomial.C a) }

/-- The inverse-limit topology on restricted power series, with every finite-level coefficient
quotient discrete. -/
@[ega "0 7.5.1" "partial"]
public noncomputable instance limitTopology (I : Ideal A) (σ : Type v) :
    TopologicalSpace (RestrictedPowerSeries I σ) :=
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⊥
  inferInstance

/-- The adic specialization equivalence also identifies the two inverse-limit topologies. -/
public noncomputable def adicIdealSystemHomeomorph (I : Ideal A) (σ : Type v) :
    let _ : TopologicalSpace
        (RestrictedPowerSeriesOfIdeals (fun n : ℕ ↦ I ^ n)
          (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ) :=
      idealSystemLimitTopology (fun n : ℕ ↦ I ^ n)
        (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ
    RestrictedPowerSeriesOfIdeals (fun n : ℕ ↦ I ^ n)
        (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ ≃ₜ
      RestrictedPowerSeries I σ :=
  Homeomorph.refl _

/-- With the limit topology, restricted power series form a topological ring. -/
public noncomputable instance limitIsTopologicalRing (I : Ideal A) (σ : Type v) :
    let _ : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
    IsTopologicalRing (RestrictedPowerSeries I σ) := by
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⟨rfl⟩
  let : ∀ n : ℕ, IsTopologicalRing (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ inferInstance
  exact Subring.instIsTopologicalRing (inverseLimitSubring I σ)

/-- The additive uniformity canonically associated to the inverse-limit topology. -/
public noncomputable instance limitUniformSpace (I : Ideal A) (σ : Type v) :
    UniformSpace (RestrictedPowerSeries I σ) := by
  let : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
  let : IsTopologicalRing (RestrictedPowerSeries I σ) := limitIsTopologicalRing I σ
  exact IsTopologicalAddGroup.rightUniformSpace _

/-- The canonical uniformity of the limit topology is compatible with addition. -/
public noncomputable instance limitIsUniformAddGroup (I : Ideal A) (σ : Type v) :
    let _ : UniformSpace (RestrictedPowerSeries I σ) := limitUniformSpace I σ
    IsUniformAddGroup (RestrictedPowerSeries I σ) := by
  let : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
  let : IsTopologicalRing (RestrictedPowerSeries I σ) := limitIsTopologicalRing I σ
  change @IsUniformAddGroup (RestrictedPowerSeries I σ)
    (IsTopologicalAddGroup.rightUniformSpace _) _
  exact isUniformAddGroup_of_addCommGroup

/-- Every coefficient-quotient projection is continuous for the limit topology and the discrete
topology on its target. -/
public theorem continuous_coefficientProjection (I : Ideal A) (σ : Type v) (n : ℕ) :
    @Continuous (RestrictedPowerSeries I σ) (MvPolynomial σ (A ⧸ I ^ n))
      (limitTopology I σ) ⊥ (coefficientProjection I σ n) := by
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⟨rfl⟩
  show Continuous (fun f : inverseLimitSubring I σ ↦ f.val n)
  exact (continuous_apply n).comp continuous_subtype_val

/-- The finite polynomial-quotient projections are continuous for the limit topology. -/
public theorem continuous_polynomialQuotientProjection (I : Ideal A) (σ : Type v) (n : ℕ) :
    @Continuous (RestrictedPowerSeries I σ)
      (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n)
      (limitTopology I σ) ⊥ (polynomialQuotientProjection I σ n) := by
  let : TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := ⊥
  let : DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := ⟨rfl⟩
  let : TopologicalSpace
      (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) := ⊥
  have he : Continuous (polynomialQuotientEquiv I σ n :
      MvPolynomial σ (A ⧸ I ^ n) →
        MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) :=
    continuous_of_discreteTopology
  exact he.comp (continuous_coefficientProjection I σ n)

/-- The inverse-limit topology on the polynomial completion, using its discrete quotients. -/
@[instance_reducible]
public noncomputable def polynomialCompletionLimitTopology (I : Ideal A) (σ : Type v) :
    TopologicalSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)) :=
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) := fun _ ↦ ⊥
  TopologicalSpace.induced (fun f n ↦ AdicCompletion.evalₐ _ n f) inferInstance

/-- **A map of completed polynomial algebras which commutes with the level-`n` reductions is
continuous.**  The limit topology is induced by the maps `AdicCompletion.evalₐ _ n` into the
discrete quotients, so a map that is computed, at each level `n`, by a function of the
level-`m n` reduction of its argument is continuous for no other reason than that.  The index
shift `m` is needed because a map of completions along a homomorphism carrying only a *power*
of one coefficient ideal into the other — the general case of
`AdicCompletion.algHomOfMapPowLe` — reads level `n` of its value off level `a * n` of its
argument. -/
public theorem continuous_of_evalₐ_comm (I : Ideal A) (r : ℕ) {A₂ : Type w} [CommRing A₂]
    (I₂ : Ideal A₂) (s : ℕ)
    (φ : AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A) →
      AdicCompletion (I₂.map (MvPolynomial.C : A₂ →+* MvPolynomial (Fin s) A₂))
        (MvPolynomial (Fin s) A₂))
    (m : ℕ → ℕ)
    (ψ : ∀ n : ℕ,
      (MvPolynomial (Fin r) A ⧸
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ m n) →
      (MvPolynomial (Fin s) A₂ ⧸
        (I₂.map (MvPolynomial.C : A₂ →+* MvPolynomial (Fin s) A₂)) ^ n))
    (hψ : ∀ (n : ℕ) (x : AdicCompletion
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) (MvPolynomial (Fin r) A)),
      AdicCompletion.evalₐ _ n (φ x) = ψ n (AdicCompletion.evalₐ _ (m n) x)) :
    @Continuous _ _ (polynomialCompletionLimitTopology I (Fin r))
      (polynomialCompletionLimitTopology I₂ (Fin s)) φ := by
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial (Fin r) A ⧸
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ n) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial (Fin r) A ⧸
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)) ^ n) := fun _ ↦ ⟨rfl⟩
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial (Fin s) A₂ ⧸
    (I₂.map (MvPolynomial.C : A₂ →+* MvPolynomial (Fin s) A₂)) ^ n) := fun _ ↦ ⊥
  let : TopologicalSpace (AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
      (MvPolynomial (Fin r) A)) := polynomialCompletionLimitTopology I (Fin r)
  let : TopologicalSpace (AdicCompletion
      (I₂.map (MvPolynomial.C : A₂ →+* MvPolynomial (Fin s) A₂))
      (MvPolynomial (Fin s) A₂)) := polynomialCompletionLimitTopology I₂ (Fin s)
  have hp : Continuous (fun f : AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
      (MvPolynomial (Fin r) A) ↦ fun k : ℕ ↦ AdicCompletion.evalₐ _ k f) :=
    continuous_induced_dom
  refine continuous_induced_rng.mpr (continuous_pi fun n ↦ ?_)
  exact ((continuous_of_discreteTopology (f := ψ n)).comp
    ((continuous_apply (m n)).comp hp)).congr fun x ↦ (hψ n x).symm

/-- The two inverse-limit descriptions carry the same limit topology, without any finite
generation or completeness assumption on the coefficient ring. -/
@[implicit_reducible]
public noncomputable def adicCompletionHomeomorph (I : Ideal A) (σ : Type v) :
    let _ := polynomialCompletionLimitTopology I σ
    RestrictedPowerSeries I σ ≃ₜ
      AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) := by
  let : ∀ n : ℕ, TopologicalSpace
      (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) := fun _ ↦ ⊥
  let : TopologicalSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)) := polynomialCompletionLimitTopology I σ
  refine { (adicCompletionEquiv I σ).toEquiv with
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · apply continuous_induced_rng.mpr
    apply continuous_pi
    intro n
    change Continuous (fun f : RestrictedPowerSeries I σ ↦
      AdicCompletion.evalₐ _ n (adicCompletionEquiv I σ f))
    simpa only [eval_adicCompletionEquiv] using
      continuous_polynomialQuotientProjection I σ n
  · apply (continuous_idealSystem_iff _ _ σ _).mpr
    intro n
    let : TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := ⊥
    let : DiscreteTopology
        (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) := ⟨rfl⟩
    have he : Continuous ((polynomialQuotientEquiv I σ n).symm :
        (MvPolynomial σ A ⧸ (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) ^ n) →
          MvPolynomial σ (A ⧸ I ^ n)) := continuous_of_discreteTopology
    have hp : Continuous (fun f :
        AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A) ↦
          fun k : ℕ ↦ AdicCompletion.evalₐ _ k f) := continuous_induced_dom
    exact he.comp ((continuous_apply n).comp hp)

/-- The `I`-adic topology on the polynomial completion has neighbourhoods the powers of the
extended coefficient ideal.  This is not declared equal to its inverse-limit topology. -/
@[instance_reducible]
public noncomputable def polynomialCompletionAdicTopology (I : Ideal A) (σ : Type v) :
    TopologicalSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)) :=
  (I.map (algebraMap A
    (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)))).adicTopology

/-- The adic topology on the completed polynomial ring, defined by the extension of the
coefficient ideal `I`. -/
@[instance_reducible]
public noncomputable def adicTopology (I : Ideal A) (σ : Type v) :
    TopologicalSpace (RestrictedPowerSeries I σ) :=
  (I.map (coefficientRingHom I σ)).adicTopology

/-- The additive uniformity for the adic topology on restricted power series, kept separate
from the default limit uniformity. -/
@[instance_reducible]
public noncomputable def adicUniformSpace (I : Ideal A) (σ : Type v) :
    UniformSpace (RestrictedPowerSeries I σ) :=
  (I.map (coefficientRingHom I σ)).ringFilterBasis.toAddGroupFilterBasis.uniformSpace

/-- Ring operations are continuous for the adic topology as well as for the limit topology. -/
public instance adicIsTopologicalRing (I : Ideal A) (σ : Type v) :
    @IsTopologicalRing (RestrictedPowerSeries I σ) (adicTopology I σ) _ :=
  (I.map (coefficientRingHom I σ)).ringFilterBasis.isTopologicalRing

/-- The adic uniformity is compatible with addition. -/
public instance adicIsUniformAddGroup (I : Ideal A) (σ : Type v) :
    @IsUniformAddGroup (RestrictedPowerSeries I σ) (adicUniformSpace I σ) _ :=
  (I.map (coefficientRingHom I σ)).ringFilterBasis.toAddGroupFilterBasis.isUniformAddGroup

/-- The additive uniformity for the adic topology on the polynomial completion. -/
@[instance_reducible]
public noncomputable def polynomialCompletionAdicUniformSpace (I : Ideal A) (σ : Type v) :
    UniformSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A)) :=
  (I.map (algebraMap A
    (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)))).ringFilterBasis.toAddGroupFilterBasis.uniformSpace

/-- The polynomial completion is a topological ring for its adic topology. -/
public instance polynomialCompletionAdicIsTopologicalRing (I : Ideal A) (σ : Type v) :
    @IsTopologicalRing
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A))
      (polynomialCompletionAdicTopology I σ) _ :=
  (I.map (algebraMap A
    (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)))).ringFilterBasis.isTopologicalRing

/-- The polynomial completion's adic uniformity is compatible with addition. -/
public instance polynomialCompletionAdicIsUniformAddGroup (I : Ideal A) (σ : Type v) :
    @IsUniformAddGroup
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A)) (MvPolynomial σ A))
      (polynomialCompletionAdicUniformSpace I σ) _ :=
  (I.map (algebraMap A
    (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
      (MvPolynomial σ A)))).ringFilterBasis.toAddGroupFilterBasis.isUniformAddGroup

end RestrictedPowerSeries

end

namespace RestrictedPowerSeries

section

open RestrictedPowerSeries


universe u v w x

/-- The universal property of restricted power series: every polynomial algebra map into a
complete linearly topologized algebra extends by a unique continuous algebra map. -/
@[stacks 0AJM, ega "0 7.5.3"]
public theorem existsUnique_continuousAlgHom_extends
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {C : Type x} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [Algebra A C]
    {ι : Type w} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (J : ι → Ideal A) (hJ : Antitone J)
    (_ : ∀ i, IsOpen (J i : Set A))
    (hfund : ∀ U ∈ nhds (0 : A), ∃ i, (J i : Set A) ⊆ U)
    (hAC : Continuous (algebraMap A C))
    (hC : TopologicalRing.IsComplete C)
    {σ : Type v} (f : MvPolynomial σ A →ₐ[A] C) :
    ∃! g : RestrictedPowerSeriesOfIdeals J hJ σ →ₐ[A] C,
      Continuous g ∧ g.comp (idealSystemPolynomialAlgHom J hJ σ) = f := by
  classical
  let e : MvPolynomial σ A →+* RestrictedPowerSeriesOfIdeals J hJ σ :=
    RestrictedPowerSeries.idealSystemPolynomialRingHom J hJ σ
  let : ∀ i : ι, TopologicalSpace (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⊥
  let : ∀ i : ι, DiscreteTopology (MvPolynomial σ (A ⧸ J i)) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace (RestrictedPowerSeriesOfIdeals J hJ σ) :=
    RestrictedPowerSeries.idealSystemLimitTopology J hJ σ
  let : UniformSpace (RestrictedPowerSeriesOfIdeals J hJ σ) :=
    RestrictedPowerSeries.idealSystemUniformSpace J hJ σ
  let : IsTopologicalRing (RestrictedPowerSeriesOfIdeals J hJ σ) :=
    RestrictedPowerSeries.idealSystemIsTopologicalRing J hJ σ
  let : IsUniformAddGroup (RestrictedPowerSeriesOfIdeals J hJ σ) :=
    RestrictedPowerSeries.idealSystemIsUniformAddGroup J hJ σ
  let : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  let : T2Space C := hC.1
  let : CompleteSpace C := hC.2
  have hdense : DenseRange e := by
    show Dense (Set.range e)
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_iff_forall.mpr
    intro x
    rw [mem_closure_iff_nhds]
    intro U hU
    rw [nhds_subtype_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
    rw [nhds_pi] at hV
    obtain ⟨I, hIfin, t, ht, hIV⟩ := Filter.mem_pi.mp hV
    obtain ⟨k, hk⟩ := Finset.exists_le hIfin.toFinset
    have hsurj : Function.Surjective
        (MvPolynomial.map (Ideal.Quotient.mk (J k)) :
          MvPolynomial σ A → MvPolynomial σ (A ⧸ J k)) :=
      MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective)
    obtain ⟨p, hp⟩ := hsurj (x.val k)
    have hcoord : ∀ i ∈ I, (e p).val i = x.val i := by
      intro i hi
      have hik : i ≤ k := hk i (hIfin.mem_toFinset.mpr hi)
      have hx := x.property hik
      have hp' := congrArg (RestrictedPowerSeries.idealSystemTransition J hJ σ hik) hp
      change MvPolynomial.map (Ideal.Quotient.factor (hJ hik))
          (MvPolynomial.map (Ideal.Quotient.mk (J k)) p) = _ at hp'
      rw [MvPolynomial.map_map, Ideal.Quotient.factor_comp_mk] at hp'
      simpa [e, RestrictedPowerSeries.idealSystemPolynomialRingHom] using hp'.trans hx
    have heV : (fun i ↦ (e p).val i) ∈ V := by
      apply hIV
      show ∀ i ∈ I, (e p).val i ∈ t i
      intro i hi
      rw [hcoord i hi]
      exact mem_of_mem_nhds (ht i)
    exact ⟨e p, hVU (by simpa using heV), ⟨p, rfl⟩⟩
  let : UniformSpace (MvPolynomial σ A) := UniformSpace.comap e inferInstance
  have hInd : IsUniformInducing e := IsUniformInducing.mk (by rfl)
  let : IsUniformAddGroup (MvPolynomial σ A) := by
    refine ⟨hInd.uniformContinuous_iff.mpr ?_⟩
    have heuc : UniformContinuous (e : MvPolynomial σ A → _) :=
      uniformContinuous_iff_le_comap.mpr le_rfl
    simpa [Function.comp_def, map_sub] using
      uniformContinuous_sub.comp ((heuc.comp uniformContinuous_fst).prodMk
        (heuc.comp uniformContinuous_snd))
  let : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have hfuc : UniformContinuous (f : MvPolynomial σ A → C) := by
    apply uniformContinuous_of_continuousAt_zero (f.toRingHom.toAddMonoidHom)
    show ContinuousAt (f : MvPolynomial σ A → C) 0
    show Filter.Tendsto (f : MvPolynomial σ A → C) (nhds 0) (nhds (f 0))
    rw [map_zero]
    apply Filter.tendsto_def.mpr
    intro U hU
    obtain ⟨N, hN, hNU⟩ := (IsLinearTopology.hasBasis_submodule C).mem_iff.mp hU
    have hACN : (algebraMap A C) ⁻¹' (N : Set C) ∈ nhds (0 : A) := by
      apply hAC.continuousAt.preimage_mem_nhds
      simpa using hN
    obtain ⟨i, hi⟩ := hfund (algebraMap A C ⁻¹' (N : Set C)) hACN
    let π := RestrictedPowerSeries.idealSystemProjection J hJ σ i
    have hπ : Continuous (π : RestrictedPowerSeriesOfIdeals J hJ σ →
        MvPolynomial σ (A ⧸ J i)) :=
      ((continuous_idealSystem_iff J hJ σ id).mp continuous_id) i
    have heCont : Continuous (e : MvPolynomial σ A →
        RestrictedPowerSeriesOfIdeals J hJ σ) := continuous_induced_dom
    have hker : (fun p : MvPolynomial σ A ↦ π (e p)) ⁻¹' ({0} : Set _) ∈
        nhds (0 : MvPolynomial σ A) := by
      apply (hπ.comp heCont).continuousAt.preimage_mem_nhds
      exact (isOpen_discrete ({0} : Set _)).mem_nhds (by simp)
    apply Filter.mem_of_superset hker
    intro p hp
    have hpzero : MvPolynomial.map (Ideal.Quotient.mk (J i)) p = 0 := by
      simpa [π, e, RestrictedPowerSeries.idealSystemProjection,
        RestrictedPowerSeries.idealSystemPolynomialRingHom] using hp
    have hpmem : p ∈ Ideal.map (MvPolynomial.C : A →+* MvPolynomial σ A) (J i) := by
      have hk : RingHom.ker (Ideal.Quotient.mk (J i)) = J i := by
        ext a
        simp
      rw [← hk, ← MvPolynomial.ker_map]
      exact RingHom.mem_ker.mpr hpzero
    have hmap : Ideal.map (MvPolynomial.C : A →+* MvPolynomial σ A) (J i) ≤
        Ideal.comap f.toRingHom (N : Ideal C) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      show f (MvPolynomial.C a) ∈ N
      show f (algebraMap A (MvPolynomial σ A) a) ∈ N
      rw [f.commutes]
      exact hi ha
    exact hNU (hmap hpmem)
  let gR : RestrictedPowerSeriesOfIdeals J hJ σ →+* C :=
    IsDenseInducing.extendRingHom hInd hdense hfuc
  have hgR_cont : Continuous (gR : RestrictedPowerSeriesOfIdeals J hJ σ → C) := by
    simpa [gR, IsDenseInducing.extendRingHom] using
      (uniformContinuous_uniformly_extend hInd hdense hfuc).continuous
  have hcomp : gR.comp e = f.toRingHom :=
    RingHom.ext fun p ↦ (hInd.isDenseInducing hdense).extend_eq hfuc.continuous p
  let g : RestrictedPowerSeriesOfIdeals J hJ σ →ₐ[A] C :=
    { toRingHom := gR
      commutes' := by
        intro a
        show gR (e (MvPolynomial.C a)) = algebraMap A C a
        exact ((RingHom.ext_iff.mp hcomp) (MvPolynomial.C a)).trans (f.commutes a) }
  have hgcomp : g.comp (idealSystemPolynomialAlgHom J hJ σ) = f :=
    AlgHom.ext fun p ↦ (RingHom.ext_iff.mp hcomp) p
  refine ⟨g, ⟨hgR_cont, hgcomp⟩, fun h hh ↦ AlgHom.ext fun x ↦
    DenseRange.induction_on hdense x (isClosed_eq hh.1 hgR_cont) fun p ↦ ?_⟩
  exact (AlgHom.ext_iff.mp hh.2 p).trans (AlgHom.ext_iff.mp hgcomp p).symm

end

section

add_to_stacks 0AL0 "ring_identification" RestrictedPowerSeries.adicCompletionEquiv

end

section

open RestrictedPowerSeries

universe u v

/-- Restricted power series are complete for their inverse-limit topology. -/
@[stacks 0AL0 "limit_completeness"]
public instance limitCompleteSpace {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) :
    let _ : UniformSpace (RestrictedPowerSeries I σ) :=
      limitUniformSpace I σ
    CompleteSpace (RestrictedPowerSeries I σ) := by
  let P := ∀ n : ℕ, MvPolynomial σ (A ⧸ I ^ n)
  let S := inverseLimitSubring I σ
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⟨rfl⟩
  let : ∀ n : ℕ, UniformSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ ⊥
  let : ∀ n : ℕ, CompleteSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ ↦ inferInstance
  let : UniformSpace P := Pi.uniformSpace _
  have : IsUniformAddGroup P := Pi.instIsUniformAddGroup
  have hclosed : IsClosed (S : Set P) := by
    rw [show (S : Set P) = ⋂ q : ℕ × ℕ,
        {f : P | if h : q.1 ≤ q.2 then
          coefficientTransition I σ h (f q.2) = f q.1 else True} by
      ext f
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hf ⟨m, n⟩
        split_ifs with h
        exact hf h
      · intro hf m n hmn
        simpa [hmn] using hf (m, n)]
    exact isClosed_iInter fun q ↦ by
      by_cases hq : q.1 ≤ q.2
      · simpa [hq] using (isClosed_eq
          ((continuous_of_discreteTopology.comp (continuous_apply q.2)))
          (continuous_apply q.1))
      · simp [hq]
  have : CompleteSpace P := inferInstance
  let : UniformSpace (↑S) :=
    UniformSpace.comap (Subtype.val : (↑S) → P) (inferInstance : UniformSpace P)
  have : IsUniformAddGroup (↑S) := AddSubgroup.isUniformAddGroup S.toAddSubgroup
  change @CompleteSpace (↑S) (limitUniformSpace I σ)
  rw [show limitUniformSpace I σ =
    UniformSpace.comap (Subtype.val : (↑S) → P) (inferInstance : UniformSpace P) from
    IsUniformAddGroup.rightUniformSpace_eq]
  exact hclosed.completeSpace_coe

end

section

open RestrictedPowerSeries

universe u v

private theorem mem_extendedIdeal_pow_iff_eval_eq_zero {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) (hI : I.FG) (n : ℕ) :
    let P := MvPolynomial σ A
    let K := I.map (MvPolynomial.C : A →+* P)
    let C := AdicCompletion K P
    let J := I.map (algebraMap A C)
    ∀ x : C, x ∈ J ^ n ↔ AdicCompletion.evalₐ K n x = 0 := by
  intro P K C J x
  have hcomp : (algebraMap P C).comp (MvPolynomial.C : A →+* P) = algebraMap A C := by
    simpa only [MvPolynomial.C_eq_algebraMap] using (IsScalarTower.algebraMap_eq A P C).symm
  have hJ : J = Ideal.map (algebraMap P C) K := by
    show I.map (algebraMap A C) = _
    rw [Ideal.map_map, hcomp]
  have hK : K.FG := hI.map _
  rw [hJ, ← Ideal.map_pow (algebraMap P C) K n]
  show x ∈ (Submodule.restrictScalars P (Ideal.map (algebraMap P C) (K ^ n)) :
    Submodule P C) ↔ _
  rw [← Ideal.smul_top_eq_map]
  show x ∈ K ^ n • (⊤ : Submodule P C) ↔ AdicCompletion.evalₐ K n x = 0
  have hquot : (K ^ n • (⊤ : Ideal P)) = K ^ n := by ext y; simp
  have heval : AdicCompletion.eval K P n x = 0 ↔ AdicCompletion.evalₐ K n x = 0 := by
    show AdicCompletion.eval K P n x = 0 ↔
      (Ideal.quotientEquivAlgOfEq P hquot) (AdicCompletion.eval K P n x) = 0
    exact (map_eq_zero_iff (Ideal.quotientEquivAlgOfEq P hquot)
      (AlgEquiv.injective (Ideal.quotientEquivAlgOfEq P hquot))).symm
  simpa only [AdicCompletion.pow_smul_top_eq_ker_eval hK, LinearMap.mem_ker] using heval

/-- Two elements of the polynomial completion agree at level `n` iff they differ by an element of
the `n`-th power of the extended ideal. -/
private theorem mem_add_image_pow_iff_eval_eq {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) (hI : I.FG) (n : ℕ) :
    let P := MvPolynomial σ A
    let K := I.map (MvPolynomial.C : A →+* P)
    let C := AdicCompletion K P
    let J := I.map (algebraMap A C)
    ∀ x y : C, y ∈ (fun z ↦ x + z) '' ((J ^ n : Ideal C) : Set C) ↔
      AdicCompletion.evalₐ K n y = AdicCompletion.evalₐ K n x := by
  intro P K C J x y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [map_add, (mem_extendedIdeal_pow_iff_eval_eq_zero I σ hI n z).mp hz, add_zero]
  · intro hy
    refine ⟨y - x, ?_, by simp⟩
    apply (mem_extendedIdeal_pow_iff_eval_eq_zero I σ hI n (y - x)).mpr
    rw [map_sub, hy, sub_self]

private theorem continuous_adicCompletionEquiv {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) (hI : I.FG) :
    @Continuous (RestrictedPowerSeries I σ)
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A))
      (limitTopology I σ) (polynomialCompletionAdicTopology I σ)
      (adicCompletionEquiv I σ) := by
  let P := MvPolynomial σ A
  let K := I.map (MvPolynomial.C : A →+* P)
  let C := AdicCompletion K P
  let J := I.map (algebraMap A C)
  let f := adicCompletionEquiv I σ
  let : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
  let : TopologicalSpace C := polynomialCompletionAdicTopology I σ
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt]
  refine (J.hasBasis_nhds_adic (f x)).tendsto_right_iff.mpr ?_
  intro n hn
  let Q := P ⧸ K ^ n
  let q := polynomialQuotientProjection I σ n
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  have hproj : @Continuous (RestrictedPowerSeries I σ) Q
      (limitTopology I σ) ⊥ q := continuous_polynomialQuotientProjection I σ n
  have hfiber : f ⁻¹' ((fun y ↦ f x + y) '' ((J ^ n : Ideal C) : Set C)) = q ⁻¹' {q x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [mem_add_image_pow_iff_eval_eq I σ hI n (f x) (f y)]
    simp only [f, eval_adicCompletionEquiv]
    rfl
  have hopen : IsOpen (q ⁻¹' {q x}) := IsOpen.preimage hproj (isOpen_discrete {q x})
  exact mem_nhds_iff.mpr ⟨q ⁻¹' {q x}, hfiber.ge, hopen, by simp⟩

private theorem continuous_adicCompletionEquiv_symm {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) (hI : I.FG) :
    @Continuous
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)) (RestrictedPowerSeries I σ)
      (polynomialCompletionAdicTopology I σ) (limitTopology I σ)
      (fun x ↦ (adicCompletionEquiv I σ).symm x) := by
  let P := MvPolynomial σ A
  let K := I.map (MvPolynomial.C : A →+* P)
  let C := AdicCompletion K P
  let J := I.map (algebraMap A C)
  let : TopologicalSpace C := polynomialCompletionAdicTopology I σ
  let : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
  apply (continuous_idealSystem_iff (fun n : ℕ ↦ I ^ n)
    (fun _ _ h ↦ Ideal.pow_le_pow_right h) σ _).2
  intro n
  let Q := P ⧸ K ^ n
  let R := MvPolynomial σ (A ⧸ I ^ n)
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  have hEval : @Continuous C Q (polynomialCompletionAdicTopology I σ) ⊥
      (AdicCompletion.evalₐ K n) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, nhds_discrete Q, Filter.tendsto_pure]
    show (AdicCompletion.evalₐ K n) ⁻¹' {(AdicCompletion.evalₐ K n) x} ∈ nhds x
    have hfiber : (AdicCompletion.evalₐ K n) ⁻¹' {(AdicCompletion.evalₐ K n) x} =
        (fun y ↦ x + y) '' ((J ^ n : Ideal C) : Set C) := by
      ext y
      exact (mem_add_image_pow_iff_eval_eq I σ hI n x y).symm
    rw [hfiber]
    exact (J.hasBasis_nhds_adic x).mem_iff.mpr ⟨n, trivial, subset_rfl⟩
  have hquot : Continuous ((polynomialQuotientEquiv I σ n).symm : Q → R) :=
    continuous_of_discreteTopology
  exact hquot.comp hEval

/-- The canonical completion equivalence is an isomorphism of topological rings when the
coefficient ideal is finitely generated. -/
@[stacks 0AL0 "finite_generation_topology"]
public theorem isHomeomorph_adicCompletionEquiv {A : Type u} [CommRing A]
    (I : Ideal A) (σ : Type v) (hI : I.FG) :
    let _ : TopologicalSpace (RestrictedPowerSeries I σ) :=
      limitTopology I σ
    let _ : TopologicalSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)) := polynomialCompletionAdicTopology I σ
    IsHomeomorph (adicCompletionEquiv I σ) := by
  let : TopologicalSpace (RestrictedPowerSeries I σ) := limitTopology I σ
  let : TopologicalSpace
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)) := polynomialCompletionAdicTopology I σ
  exact (Equiv.isHomeomorph_iff (adicCompletionEquiv I σ).toEquiv).2
    ⟨continuous_adicCompletionEquiv I σ hI,
      continuous_adicCompletionEquiv_symm I σ hI⟩

end

end RestrictedPowerSeries

end
