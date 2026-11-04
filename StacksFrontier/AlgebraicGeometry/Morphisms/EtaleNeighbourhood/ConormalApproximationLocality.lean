module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximation
public import StacksFrontier.RingTheory.ArtinRees.SameDenominatorAway

/-!
# Locality of the identity-induced comparison of Stacks 0CAY

The chart-local datum that the basis-indexed assembly of Stacks 0CAY consumes is an
`AssociatedGraded.GradedAlgEquiv` between the two specialised cokernels which is induced by the
identity of the ambient polynomial ring. By
`Stacks.ArtinRees.sameDenominator_iff_exists_isInducedByIdentity` the existence of such a
comparison is the kernel equality `Stacks.ArtinRees.SameDenominator`, a condition on the two
ideals alone. This file moves that condition from one presented chart to another:

* between two presentations of the *same* chart ring, and
* from a chart to a *localization* of it — which is what shrinking an affine open of `Y` to a
  basic open does.

Both are instances of `Stacks.ArtinRees.SameDenominator.ofComp` and
`Stacks.ArtinRees.SameDenominator.ofAway`, whose hypothesis is a pair of comparison maps agreeing
modulo `m`. The pair is produced here: a generator of the new presentation is a `C`-rational
expression in the generators of the old one, and specialising that one expression along `σ` and
along `σ'` gives two maps differing by an element of `m`.

## Main definitions

* `Stacks.ConormalApproximation.presentationHom`: the structure map of a chart presentation, as a
  `D`-algebra surjection of `D[x_1, …, x_n]` onto the base change `B ⊗_{C,σ} D`, with kernel the
  module of relations of the specialised relation matrix.

## Main results

* `Stacks.ConormalApproximation.presentationHom_map`: **a `C`-rational polynomial is carried to
  `1 ⊗ (its value at the generators)`** — the computation that makes one `C`-rational expression
  serve both `σ` and `σ'`.
* `Stacks.ConormalApproximation.ker_presentationHom`: its kernel is the module of relations.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
* [Stacks Project, Tag 0CAZ](https://stacks.math.columbia.edu/tag/0CAZ)
-/

@[expose] public noncomputable section

open TensorProduct

universe u v w

namespace Stacks.ConormalApproximation

variable {C : Type u} {B : Type v} {D : Type w} [CommRing C] [CommRing B] [CommRing D]
  [Algebra C B] [Algebra C D] {n m : ℕ}

/-- **The structure map of a chart presentation**: the `D`-algebra map of `D[x_1, …, x_n]` onto
the base change `B ⊗_{C,σ} D` sending the variable `x_i` to `1 ⊗ x_i`. It is the quotient map by
the module of relations of the specialised relation matrix followed by Stacks 0CAZ's
identification `Stacks.ConormalApproximation.quotRangeEquivTensor`, so it is surjective with that
module of relations as kernel. -/
def presentationHom (D : Type w) [CommRing D] [Algebra C D]
    (P : Algebra.Presentation C B (Fin n) (Fin m)) :
    MvPolynomial (Fin n) D →ₐ[D] TensorProduct C D B :=
  (quotRangeEquivTensor D P).toAlgHom.comp
    (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) P.relation)))

/-- The structure map is the identification `quotRangeEquivTensor` of the quotient, read on
representatives. -/
private theorem quotRangeEquivTensor_mk_eq_presentationHom
    (P : Algebra.Presentation C B (Fin n) (Fin m)) (a : MvPolynomial (Fin n) D) :
    quotRangeEquivTensor D P (Ideal.Quotient.mk _ a) = presentationHom D P a := rfl

/-- The structure map `presentationHom D P` sends a polynomial `a` to its evaluation at the
elements `1 ⊗ x_i` of `B ⊗_C D`. -/
theorem presentationHom_apply (P : Algebra.Presentation C B (Fin n) (Fin m))
    (a : MvPolynomial (Fin n) D) :
    presentationHom D P a = MvPolynomial.aeval (R := D) (fun i => (1 : D) ⊗ₜ[C] P.val i) a :=
  quotRangeEquivTensor_mk D P a

/-- The structure map `presentationHom D P` sends the variable `x_i` to `1 ⊗ x_i`. -/
@[simp]
theorem presentationHom_X (P : Algebra.Presentation C B (Fin n) (Fin m)) (i : Fin n) :
    presentationHom D P (MvPolynomial.X i) = (1 : D) ⊗ₜ[C] P.val i := by
  rw [presentationHom_apply, MvPolynomial.aeval_X]

/-- **The structure map of a chart presentation is surjective.** -/
theorem surjective_presentationHom (P : Algebra.Presentation C B (Fin n) (Fin m)) :
    Function.Surjective (presentationHom D P) :=
  (quotRangeEquivTensor D P).surjective.comp Ideal.Quotient.mk_surjective

/-- **The kernel of the structure map of a chart presentation is the module of relations of the
specialised relation matrix** — the ideal the affine comparison of Stacks 0CAY is stated with. -/
theorem ker_presentationHom (P : Algebra.Presentation C B (Fin n) (Fin m)) :
    RingHom.ker (presentationHom D P : MvPolynomial (Fin n) D →+* TensorProduct C D B) =
      LinearMap.range (relationMapOfHom (algebraMap C D) P.relation) := by
  refine Ideal.ext fun a => ?_
  rw [RingHom.mem_ker]
  show presentationHom D P a = 0 ↔ _
  rw [← quotRangeEquivTensor_mk_eq_presentationHom,
    map_eq_zero_iff _ (quotRangeEquivTensor D P).injective, Ideal.Quotient.eq_zero_iff_mem]

/-- **A `C`-rational polynomial is carried to `1` tensor its value at the generators.** This is
the computation that lets one `C`-rational expression serve the two structure maps `σ` and `σ'` of
Stacks 0CAY at once: the image of `MvPolynomial.map σ F` under the structure map of the
presentation depends on `σ` only through the right-hand factor `1`, and the two specialisations
`MvPolynomial.map σ F` and `MvPolynomial.map σ' F` differ by a polynomial with coefficients in
`m` whenever `σ` and `σ'` are congruent modulo `m`. -/
theorem presentationHom_map (P : Algebra.Presentation C B (Fin n) (Fin m))
    (F : MvPolynomial (Fin n) C) :
    presentationHom D P (MvPolynomial.map (algebraMap C D) F) =
      (1 : D) ⊗ₜ[C] MvPolynomial.aeval P.val F := by
  rw [presentationHom_apply]
  induction F using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.algebraMap_eq_smul_one (R := C) (A := D) c,
        Algebra.algebraMap_eq_smul_one (R := C) (A := B) c, TensorProduct.smul_tmul]
  | add F₁ F₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, TensorProduct.tmul_add]
  | mul_X F i h =>
      rw [map_mul, map_mul, h, MvPolynomial.map_X, MvPolynomial.aeval_X, map_mul,
        MvPolynomial.aeval_X, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **Two specialisations of one `C`-rational polynomial differ by a polynomial with coefficients
in `m`.** -/
theorem map_sub_map_mem_map_C {C D : Type*} [CommRing C] [CommRing D] {n : ℕ}
    {σ σ' : C →+* D} (m : Ideal D) (hσ : ∀ c, σ c - σ' c ∈ m)
    (F : MvPolynomial (Fin n) C) :
    MvPolynomial.map σ F - MvPolynomial.map σ' F ∈
      m.map (MvPolynomial.C : D →+* MvPolynomial (Fin n) D) := by
  refine MvPolynomial.mem_map_C_iff.2 fun k => ?_
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  exact hσ _

/-! ### Comparing two presentations of one chart ring -/

/-- **The comparison map of two presentations of one `C`-algebra, specialised along `σ`.** Each
generator of the second presentation is the value at the generators of the first of a polynomial
`W j` over `C`; the comparison evaluates the variables of the second presentation at the
specialisations `MvPolynomial.map σ (W j)`.

The map is taken as data depending on `σ` as a plain ring homomorphism, because Stacks 0CAY needs
the comparison for `σ` and the one for `σ'` *at the same time*, and the two differ. -/
def presentationCompHom {C D : Type*} [CommRing C] [CommRing D] (σ : C →+* D) {n₁ n₂ : ℕ}
    (W : Fin n₂ → MvPolynomial (Fin n₁) C) :
    MvPolynomial (Fin n₂) D →ₐ[D] MvPolynomial (Fin n₁) D :=
  MvPolynomial.aeval fun j => MvPolynomial.map σ (W j)

/-- The comparison map `presentationCompHom σ W` sends the variable `x_j` to
`MvPolynomial.map σ (W j)`. -/
@[simp]
theorem presentationCompHom_X {C D : Type*} [CommRing C] [CommRing D] (σ : C →+* D) {n₁ n₂ : ℕ}
    (W : Fin n₂ → MvPolynomial (Fin n₁) C) (j : Fin n₂) :
    presentationCompHom σ W (MvPolynomial.X j) = MvPolynomial.map σ (W j) :=
  MvPolynomial.aeval_X _ _

/-- **The comparison map carries the structure map of one presentation to that of the other.**
This is `Stacks.ConormalApproximation.presentationHom_map` together with the hypothesis that `W j`
computes the `j`-th generator of the second presentation. -/
theorem presentationHom_presentationCompHom (P₁ : Algebra.Presentation C B (Fin n) (Fin m))
    {n₂ m₂ : ℕ} (P₂ : Algebra.Presentation C B (Fin n₂) (Fin m₂))
    (W : Fin n₂ → MvPolynomial (Fin n) C)
    (hW : ∀ j, MvPolynomial.aeval P₁.val (W j) = P₂.val j) (x : MvPolynomial (Fin n₂) D) :
    presentationHom D P₁ (presentationCompHom (algebraMap C D) W x) = presentationHom D P₂ x := by
  have key : (presentationHom D P₁).comp (presentationCompHom (algebraMap C D) W) =
      presentationHom D P₂ := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, presentationCompHom_X, presentationHom_map, hW, presentationHom_X]
  exact AlgHom.congr_fun key x

/-- **The quotient map of the first presentation, precomposed with the comparison, is
surjective.** -/
theorem surjective_mk_presentationCompHom (P₁ : Algebra.Presentation C B (Fin n) (Fin m))
    {n₂ m₂ : ℕ} (P₂ : Algebra.Presentation C B (Fin n₂) (Fin m₂))
    (W : Fin n₂ → MvPolynomial (Fin n) C)
    (hW : ∀ j, MvPolynomial.aeval P₁.val (W j) = P₂.val j) :
    Function.Surjective
      ((Ideal.Quotient.mkₐ D
          (LinearMap.range (relationMapOfHom (algebraMap C D) P₁.relation))).comp
        (presentationCompHom (algebraMap C D) W)) := by
  intro y
  obtain ⟨x, hx⟩ := surjective_presentationHom (D := D) P₂ (quotRangeEquivTensor D P₁ y)
  refine ⟨x, (quotRangeEquivTensor D P₁).injective ?_⟩
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, quotRangeEquivTensor_mk_eq_presentationHom,
    presentationHom_presentationCompHom P₁ P₂ W hW, hx]

/-- **Its kernel is the module of relations of the second presentation.** So the quotient of the
first presentation, read through the comparison, is a presentation of the chart ring with the
second presentation's relations — which is what makes the denominator criterion independent of the
presentation. -/
theorem ker_mk_presentationCompHom (P₁ : Algebra.Presentation C B (Fin n) (Fin m))
    {n₂ m₂ : ℕ} (P₂ : Algebra.Presentation C B (Fin n₂) (Fin m₂))
    (W : Fin n₂ → MvPolynomial (Fin n) C)
    (hW : ∀ j, MvPolynomial.aeval P₁.val (W j) = P₂.val j) :
    RingHom.ker
        ((Ideal.Quotient.mkₐ D
            (LinearMap.range (relationMapOfHom (algebraMap C D) P₁.relation))).comp
          (presentationCompHom (algebraMap C D) W)).toRingHom =
      LinearMap.range (relationMapOfHom (algebraMap C D) P₂.relation) := by
  rw [← ker_presentationHom (D := D) P₂]
  refine Ideal.ext fun x => ?_
  rw [RingHom.mem_ker, RingHom.mem_ker]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← presentationHom_presentationCompHom P₁ P₂ W hW x]
  exact (map_eq_zero_iff (quotRangeEquivTensor D P₁)
    (quotRangeEquivTensor D P₁).injective).symm

/-! ### The criterion does not depend on the presentation -/

section TwoSided

variable {C : Type u} {B : Type v} {D : Type w} [CommRing C] [CommRing B] [CommRing D]
  [Algebra C B]

/-- The constant-polynomial map `MvPolynomial.C` is the algebra map `D → D[x_1, …, x_k]`. -/
theorem algebraMap_mvPolynomial (k : ℕ) :
    (MvPolynomial.C : D →+* MvPolynomial (Fin k) D) =
      algebraMap D (MvPolynomial (Fin k) D) := rfl

/-- **The denominator criterion does not depend on the presentation of the chart ring.** Two
presentations of one `C`-algebra `B` are compared by expressing the generators of the second as
values `W j` of polynomials over `C` at the generators of the first; the comparison specialised
along `σ` and the comparison specialised along `σ'` are two different maps of ambient polynomial
rings, but they agree modulo `m` because they are the two specialisations of the one family `W`.
That is exactly the hypothesis of `Stacks.ArtinRees.SameDenominator.ofComp`.

This is what makes the condition, and hence the identity-induced comparison, a property of the
chart rather than of the chosen presentation. -/
theorem sameDenominator_of_presentations {σ σ' : C →+* D} {m : Ideal D}
    (hσ : ∀ c, σ c - σ' c ∈ m) {n₁ m₁ n₂ m₂ : ℕ}
    (P₁ : Algebra.Presentation C B (Fin n₁) (Fin m₁))
    (P₂ : Algebra.Presentation C B (Fin n₂) (Fin m₂))
    (W : Fin n₂ → MvPolynomial (Fin n₁) C)
    (hW : ∀ j, MvPolynomial.aeval P₁.val (W j) = P₂.val j)
    (hden : Stacks.ArtinRees.SameDenominator
      (m.map (MvPolynomial.C : D →+* MvPolynomial (Fin n₁) D))
      (LinearMap.range (relationMapOfHom σ P₁.relation))
      (LinearMap.range (relationMapOfHom σ' P₁.relation))) :
    Stacks.ArtinRees.SameDenominator
      (m.map (MvPolynomial.C : D →+* MvPolynomial (Fin n₂) D))
      (LinearMap.range (relationMapOfHom σ P₂.relation))
      (LinearMap.range (relationMapOfHom σ' P₂.relation)) := by
  have hcomp : ∀ τ : C →+* D, Function.Surjective ((Ideal.Quotient.mkₐ D
        (LinearMap.range (relationMapOfHom τ P₁.relation))).comp (presentationCompHom τ W)) ∧
      RingHom.ker ((Ideal.Quotient.mkₐ D
        (LinearMap.range (relationMapOfHom τ P₁.relation))).comp
          (presentationCompHom τ W)).toRingHom =
        LinearMap.range (relationMapOfHom τ P₂.relation) := fun τ => by
    let := τ.toAlgebra
    exact ⟨surjective_mk_presentationCompHom P₁ P₂ W hW, ker_mk_presentationCompHom P₁ P₂ W hW⟩
  obtain ⟨hsurj, hker⟩ := hcomp σ
  obtain ⟨hsurj', hker'⟩ := hcomp σ'
  have hcong : ∀ x : MvPolynomial (Fin n₂) D,
      presentationCompHom σ W x - presentationCompHom σ' W x ∈
        m.map (algebraMap D (MvPolynomial (Fin n₁) D)) :=
    fun x => Stacks.ArtinRees.aeval_sub_aeval_mem _ _ _
      (fun j => by
        rw [← algebraMap_mvPolynomial n₁]
        exact map_sub_map_mem_map_C m hσ (W j)) x
  have key := Stacks.ArtinRees.SameDenominator.ofComp (D := D) m
    (π₁ := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ P₁.relation)))
    (π₂ := (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ P₁.relation))).comp
      (presentationCompHom σ W))
    (ρ₁ := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ' P₁.relation)))
    (ρ₂ := (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ' P₁.relation))).comp
      (presentationCompHom σ' W))
    (h := presentationCompHom σ W) (h' := presentationCompHom σ' W)
    Ideal.Quotient.mk_surjective hsurj Ideal.Quotient.mk_surjective hsurj'
    (fun _ => rfl) (fun _ => rfl) hcong
    (by
      rw [Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ P₁.relation)),
        Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ' P₁.relation)),
        ← algebraMap_mvPolynomial n₁]
      exact hden)
  rw [algebraMap_mvPolynomial n₂, ← hker, ← hker', AlgHom.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe]
  exact key

end TwoSided

/-! ### The chart ring of a basic open as a localization of the chart ring

This section is one-sided: it works with a fixed `Algebra C D`, that is with one of the two
structure maps `σ`, `σ'` of Stacks 0CAY at a time. The two-sided statement
`Stacks.ConormalApproximation.sameDenominator_of_localization` installs `σ.toAlgebra` and
`σ'.toAlgebra` in turn, which is possible because every statement below has a type mentioning
`algebraMap C D` only inside `relationMapOfHom`, where it is a plain ring homomorphism. -/

section Away

variable {C : Type u} {Ba Bk : Type v} {D : Type w} [CommRing C] [CommRing Ba] [CommRing Bk]
  [CommRing D] [Algebra C Ba] [Algebra C Bk] [Algebra Ba Bk] [IsScalarTower C Ba Bk]
  [Algebra C D] {na ma nk mk : ℕ} (f : Ba) [IsLocalization.Away f Bk]
  (Pa : Algebra.Presentation C Ba (Fin na) (Fin ma))
  (Pk : Algebra.Presentation C Bk (Fin nk) (Fin mk))

/-- **The chart ring of a basic open, identified with a localization of the chart ring.**
Stacks 0CAZ identifies the quotient of `D[y_1, …, y_{n_k}]` by the specialised relations of a
presentation of `B_f` with `B_f ⊗_{C,σ} D`, and localization commutes with base change
(`IsLocalization.Away.tensorProductEquivTMulRight`), so that quotient is the localization of
`B ⊗_{C,σ} D` at `1 ⊗ f`. -/
def chartAwayEquiv :
    (MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation)) ≃ₐ[D]
      Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba) :=
  (quotRangeEquivTensor D Pk).trans (IsLocalization.Away.tensorProductEquivTMulRight C D f Bk)

/-- **The structure map making the chart ring of a basic open an algebra over the chart ring.**
It is Stacks 0CAZ's identification, followed by the localization map, followed by the inverse
identification; its characterising property is
`Stacks.ConormalApproximation.chartAwayEquiv_algebraMap`. -/
@[instance_reducible]
def chartAwayAlgebra :
    Algebra (MvPolynomial (Fin na) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
      (MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation)) :=
  ((chartAwayEquiv (D := D) f Pk).symm.toRingHom.comp
    ((algebraMap (TensorProduct C D Ba)
        (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))).comp
      (quotRangeEquivTensor D Pa).toRingHom)).toAlgebra

/-- **The structure map, read through the two identifications**: on the class of a polynomial it
is the localization map applied to the value of that polynomial in the base change. -/
theorem chartAwayEquiv_algebraMap (z : MvPolynomial (Fin na) D) :
    letI := chartAwayAlgebra (D := D) f Pa Pk
    chartAwayEquiv (D := D) f Pk
        (algebraMap
          (MvPolynomial (Fin na) D ⧸
            LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
          (MvPolynomial (Fin nk) D ⧸
            LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))
          (Ideal.Quotient.mk _ z)) =
      algebraMap (TensorProduct C D Ba)
        (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
        (presentationHom D Pa z) := by
  let := chartAwayAlgebra (D := D) f Pa Pk
  show chartAwayEquiv (D := D) f Pk ((chartAwayEquiv (D := D) f Pk).symm
      (algebraMap (TensorProduct C D Ba)
        (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
        (quotRangeEquivTensor D Pa (Ideal.Quotient.mk _ z)))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The chart ring of a basic open is a `D`-algebra through the chart ring. -/
theorem isScalarTower_chartAwayAlgebra :
    letI := chartAwayAlgebra (D := D) f Pa Pk
    IsScalarTower D
      (MvPolynomial (Fin na) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
      (MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation)) := by
  let := chartAwayAlgebra (D := D) f Pa Pk
  refine IsScalarTower.of_algebraMap_eq fun d => ?_
  refine (chartAwayEquiv (D := D) f Pk).injective ?_
  show chartAwayEquiv (D := D) f Pk (algebraMap D _ d) =
    chartAwayEquiv (D := D) f Pk
      ((chartAwayEquiv (D := D) f Pk).symm
        (algebraMap (TensorProduct C D Ba)
          (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
          (quotRangeEquivTensor D Pa (algebraMap D _ d))))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes,
    show quotRangeEquivTensor D Pa (algebraMap D _ d) =
      algebraMap D (TensorProduct C D Ba) d from AlgEquiv.commutes _ d,
    ← IsScalarTower.algebraMap_apply]

/-- **The chart ring of a basic open is the localization of the chart ring at the specialisation
of the `C`-rational function cutting the basic open out.** This is what lets
`Stacks.ArtinRees.SameDenominator.ofAway` be applied: the element inverted is
`MvPolynomial.map σ F₀` for one polynomial `F₀` over `C`, so on the `σ'` side the element inverted
is the specialisation of the *same* `F₀`, and the two are congruent modulo `m`. -/
theorem isLocalization_chartAwayAlgebra (F₀ : MvPolynomial (Fin na) C)
    (hF₀ : MvPolynomial.aeval Pa.val F₀ = f) :
    letI := chartAwayAlgebra (D := D) f Pa Pk
    IsLocalization.Away
      (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
        (MvPolynomial.map (algebraMap C D) F₀))
      (MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation)) := by
  let := chartAwayAlgebra (D := D) f Pa Pk
  have hG : (quotRangeEquivTensor D Pa).symm.toRingEquiv
        ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba) =
      Ideal.Quotient.mk (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
        (MvPolynomial.map (algebraMap C D) F₀) := by
    show (quotRangeEquivTensor D Pa).symm _ = _
    refine (AlgEquiv.symm_apply_eq _).2 ?_
    rw [quotRangeEquivTensor_mk_eq_presentationHom, presentationHom_map, hF₀]
  have key := Stacks.ArtinRees.isLocalization_of_ringEquiv
    (S := Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
    (Submonoid.powers ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
    (quotRangeEquivTensor D Pa).symm.toRingEquiv
    (chartAwayEquiv (D := D) f Pk).symm.toRingEquiv
    (fun x => by
      obtain ⟨y, rfl⟩ := (quotRangeEquivTensor D Pa).surjective x
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [show ((quotRangeEquivTensor D Pa).symm.toRingEquiv
            (quotRangeEquivTensor D Pa (Ideal.Quotient.mk _ z))) =
          Ideal.Quotient.mk _ z from (quotRangeEquivTensor D Pa).symm_apply_apply _]
      rfl)
  have hsub : (Submonoid.powers ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba)).map
        ((quotRangeEquivTensor D Pa).symm.toRingEquiv : TensorProduct C D Ba →+*
          (MvPolynomial (Fin na) D ⧸
            LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))) =
      Submonoid.powers (Ideal.Quotient.mkₐ D
        (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
        (MvPolynomial.map (algebraMap C D) F₀)) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers hG
  show IsLocalization (Submonoid.powers (Ideal.Quotient.mkₐ D
      (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
      (MvPolynomial.map (algebraMap C D) F₀)))
    (MvPolynomial (Fin nk) D ⧸
      LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))
  rw [← hsub]
  exact key

/-- **The comparison map of the given presentation of the localization with the one-variable
polynomial presentation.** A generator of a presentation of `B_f` is the value at the generators
of `B` of a polynomial `Y j` over `C`, divided by `f^(d j)`; the comparison sends its variable to
the specialisation of `Y j` times the `d j`-th power of the extra variable. The structure map
enters only through `MvPolynomial.map σ`, so the comparison for `σ` and the one for `σ'` are the
two specialisations of one family and agree modulo `m`. -/
def awayCompHom {C D : Type*} [CommRing C] [CommRing D] (σ : C →+* D) {na nk : ℕ}
    (Y : Fin nk → MvPolynomial (Fin na) C) (dd : Fin nk → ℕ) :
    MvPolynomial (Fin nk) D →ₐ[D] Polynomial (MvPolynomial (Fin na) D) :=
  MvPolynomial.aeval fun j => Polynomial.C (MvPolynomial.map σ (Y j)) * Polynomial.X ^ dd j

/-- The comparison map `awayCompHom σ Y dd` sends the variable `x_j` to the specialisation
`MvPolynomial.map σ (Y j)` times the `dd j`-th power of the extra variable. -/
@[simp]
theorem awayCompHom_X {C D : Type*} [CommRing C] [CommRing D] (σ : C →+* D) {na nk : ℕ}
    (Y : Fin nk → MvPolynomial (Fin na) C) (dd : Fin nk → ℕ) (j : Fin nk) :
    awayCompHom σ Y dd (MvPolynomial.X j) =
      Polynomial.C (MvPolynomial.map σ (Y j)) * Polynomial.X ^ dd j :=
  MvPolynomial.aeval_X _ _

/-- **The one-variable polynomial presentation of the localization, composed with the comparison,
is the given presentation of the localization.** This is the hypothesis `π₁ ∘ h = π₂` of
`Stacks.ArtinRees.SameDenominator.ofComp`, checked on the variables: both sides, multiplied by the
`d j`-th power of the inverted element and read in `B_f ⊗_{C,σ} D`, are `1 ⊗ (the numerator)`. -/
theorem awayPolyHom_comp_awayCompHom (F₀ : MvPolynomial (Fin na) C)
    (hF₀ : MvPolynomial.aeval Pa.val F₀ = f) (Y : Fin nk → MvPolynomial (Fin na) C)
    (dd : Fin nk → ℕ)
    (hY : ∀ j, algebraMap Ba Bk (MvPolynomial.aeval Pa.val (Y j)) =
      Pk.val j * algebraMap Ba Bk f ^ dd j) :
    letI := chartAwayAlgebra (D := D) f Pa Pk
    haveI := isScalarTower_chartAwayAlgebra (D := D) f Pa Pk
    haveI := isLocalization_chartAwayAlgebra (D := D) f Pa Pk F₀ hF₀
    (Stacks.ArtinRees.awayPolyHom
          (Ideal.Quotient.mkₐ D
            (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation)))
          (MvPolynomial.map (algebraMap C D) F₀)
          (MvPolynomial (Fin nk) D ⧸
            LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))).comp
        (awayCompHom (algebraMap C D) Y dd) =
      Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation)) := by
  let := chartAwayAlgebra (D := D) f Pa Pk
  have := isScalarTower_chartAwayAlgebra (D := D) f Pa Pk
  have := isLocalization_chartAwayAlgebra (D := D) f Pa Pk F₀ hF₀
  refine MvPolynomial.algHom_ext fun j => ?_
  have hunit : IsUnit (algebraMap
      (MvPolynomial (Fin na) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
      (MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))
      (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
        (MvPolynomial.map (algebraMap C D) F₀))) :=
    IsLocalization.map_units _
      (⟨Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
          (MvPolynomial.map (algebraMap C D) F₀), Submonoid.mem_powers _⟩ :
        Submonoid.powers (Ideal.Quotient.mkₐ D
          (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
          (MvPolynomial.map (algebraMap C D) F₀)))
  rw [AlgHom.comp_apply, awayCompHom_X, map_mul, map_pow, Stacks.ArtinRees.awayPolyHom_C,
    Stacks.ArtinRees.awayPolyHom_X]
  refine (hunit.pow (dd j)).mul_left_inj.1 ?_
  rw [mul_assoc, ← mul_pow,
    mul_comm (IsLocalization.Away.invSelf
      (S := MvPolynomial (Fin nk) D ⧸
        LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))
      (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom (algebraMap C D) Pa.relation))
        (MvPolynomial.map (algebraMap C D) F₀))) _,
    IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine (chartAwayEquiv (D := D) f Pk).injective ?_
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  have hEk : chartAwayEquiv (D := D) f Pk (Ideal.Quotient.mk
        (LinearMap.range (relationMapOfHom (algebraMap C D) Pk.relation))
        (MvPolynomial.X j)) =
      IsLocalization.Away.tensorProductEquivTMulRight C D f Bk
        ((1 : D) ⊗ₜ[C] Pk.val j : TensorProduct C D Bk) := by
    show IsLocalization.Away.tensorProductEquivTMulRight C D f Bk
      (quotRangeEquivTensor D Pk (Ideal.Quotient.mk _ (MvPolynomial.X j))) = _
    rw [quotRangeEquivTensor_mk_eq_presentationHom, presentationHom_X]
  rw [chartAwayEquiv_algebraMap (D := D) f Pa Pk, presentationHom_map, map_mul, map_pow, hEk,
    chartAwayEquiv_algebraMap (D := D) f Pa Pk, presentationHom_map, hF₀,
    show algebraMap (TensorProduct C D Ba)
        (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
        ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba) =
      IsLocalization.Away.tensorProductEquivTMulRight C D f Bk
        ((1 : D) ⊗ₜ[C] algebraMap Ba Bk f : TensorProduct C D Bk) from
      (IsLocalization.Away.tensorProductEquivTMulRight_tmul Ba f Bk (1 : D) f).symm,
    show algebraMap (TensorProduct C D Ba)
        (Localization.Away ((1 : D) ⊗ₜ[C] f : TensorProduct C D Ba))
        ((1 : D) ⊗ₜ[C] MvPolynomial.aeval Pa.val (Y j) : TensorProduct C D Ba) =
      IsLocalization.Away.tensorProductEquivTMulRight C D f Bk
        ((1 : D) ⊗ₜ[C] algebraMap Ba Bk (MvPolynomial.aeval Pa.val (Y j)) :
          TensorProduct C D Bk) from
      (IsLocalization.Away.tensorProductEquivTMulRight_tmul Ba f Bk (1 : D)
        (MvPolynomial.aeval Pa.val (Y j))).symm,
    ← map_pow, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, hY j]

end Away

/-! ### The criterion passes to a basic open -/

section AwayTwoSided

variable {C : Type u} {D : Type w} [CommRing C] [CommRing D]

/-- **The denominator criterion passes from a chart to a basic open of it.** Let `B_k = B[1/f]`
with `f` the value at the generators of `B` of a polynomial `F₀` over `C`, and let each generator
of the chosen presentation of `B_k` be the value of a polynomial `Y j` over `C` divided by
`f^(d j)`. Then the criterion for a presentation of `B` implies the criterion for the presentation
of `B_k`.

This is the locality of the identity-induced comparison of Stacks 0CAY. The affine core produces
an Artin-Rees bound depending on the presentation, so it can be invoked at only finitely many
charts; `Stacks.Conormal.CommonChartAssociatedGradedEquiv.isBasis` asks for the comparison at
charts arbitrarily small, and the charts arbitrarily small below a given one are its basic opens.
Both the inverted element and the numerators of the new generators are specialisations of
polynomials over `C`, so the `σ` data and the `σ'` data differ by elements of `m` — which is all
`Stacks.ArtinRees.SameDenominator.ofAway` and
`Stacks.ArtinRees.SameDenominator.ofComp` need. -/
theorem sameDenominator_of_localization {Ba Bk : Type v} [CommRing Ba] [CommRing Bk]
    [Algebra C Ba] [Algebra C Bk] [Algebra Ba Bk] [IsScalarTower C Ba Bk]
    {σ σ' : C →+* D} {m : Ideal D} (hσ : ∀ c, σ c - σ' c ∈ m)
    (f : Ba) [IsLocalization.Away f Bk] {na ma nk mk : ℕ}
    (Pa : Algebra.Presentation C Ba (Fin na) (Fin ma))
    (Pk : Algebra.Presentation C Bk (Fin nk) (Fin mk))
    (F₀ : MvPolynomial (Fin na) C) (hF₀ : MvPolynomial.aeval Pa.val F₀ = f)
    (Y : Fin nk → MvPolynomial (Fin na) C) (dd : Fin nk → ℕ)
    (hY : ∀ j, algebraMap Ba Bk (MvPolynomial.aeval Pa.val (Y j)) =
      Pk.val j * algebraMap Ba Bk f ^ dd j)
    (hden : Stacks.ArtinRees.SameDenominator
      (m.map (MvPolynomial.C : D →+* MvPolynomial (Fin na) D))
      (LinearMap.range (relationMapOfHom σ Pa.relation))
      (LinearMap.range (relationMapOfHom σ' Pa.relation))) :
    Stacks.ArtinRees.SameDenominator
      (m.map (MvPolynomial.C : D →+* MvPolynomial (Fin nk) D))
      (LinearMap.range (relationMapOfHom σ Pk.relation))
      (LinearMap.range (relationMapOfHom σ' Pk.relation)) := by
  have haway : ∀ τ : C →+* D, ∃ (_ : Algebra
        (MvPolynomial (Fin na) D ⧸ LinearMap.range (relationMapOfHom τ Pa.relation))
        (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom τ Pk.relation)))
      (_ : IsScalarTower D
        (MvPolynomial (Fin na) D ⧸ LinearMap.range (relationMapOfHom τ Pa.relation))
        (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom τ Pk.relation)))
      (_ : IsLocalization.Away
        (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom τ Pa.relation))
          (MvPolynomial.map τ F₀))
        (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom τ Pk.relation))),
      (Stacks.ArtinRees.awayPolyHom
        (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom τ Pa.relation)))
        (MvPolynomial.map τ F₀)
        (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom τ Pk.relation))).comp
      (awayCompHom τ Y dd) =
      Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom τ Pk.relation)) := fun τ => by
    let := τ.toAlgebra
    exact ⟨chartAwayAlgebra (D := D) f Pa Pk, isScalarTower_chartAwayAlgebra (D := D) f Pa Pk,
      isLocalization_chartAwayAlgebra (D := D) f Pa Pk F₀ hF₀,
      awayPolyHom_comp_awayCompHom (D := D) f Pa Pk F₀ hF₀ Y dd hY⟩
  obtain ⟨algσ, htσ, hlσ, hcompσ⟩ := haway σ
  obtain ⟨algσ', htσ', hlσ', hcompσ'⟩ := haway σ'
  -- the criterion for the one-variable polynomial ambient over the chart
  have hAway := Stacks.ArtinRees.SameDenominator.ofAway (D := D) m
    (π := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ Pa.relation)))
    (QL := MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom σ Pk.relation))
    Ideal.Quotient.mk_surjective
    (ρ := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ' Pa.relation)))
    (QL' := MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom σ' Pk.relation))
    Ideal.Quotient.mk_surjective (MvPolynomial.map σ F₀) (MvPolynomial.map σ' F₀)
    (by
      rw [← algebraMap_mvPolynomial na]
      exact map_sub_map_mem_map_C m hσ F₀)
    (by
      rw [Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ Pa.relation)),
        Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ' Pa.relation)),
        ← algebraMap_mvPolynomial na]
      exact hden)
  -- the coefficientwise bound for the two comparison maps
  have hPolyC : ∀ w : MvPolynomial (Fin na) D,
      w ∈ m.map (MvPolynomial.C : D →+* MvPolynomial (Fin na) D) →
      Polynomial.C w ∈ m.map (algebraMap D (Polynomial (MvPolynomial (Fin na) D))) := by
    intro w hw
    have hmem : Polynomial.C w ∈
        (m.map (MvPolynomial.C : D →+* MvPolynomial (Fin na) D)).map
          (Polynomial.C : MvPolynomial (Fin na) D →+*
            Polynomial (MvPolynomial (Fin na) D)) :=
      Ideal.mem_map_of_mem _ hw
    rwa [Ideal.map_map,
      show (Polynomial.C : MvPolynomial (Fin na) D →+* Polynomial (MvPolynomial (Fin na) D)).comp
          (MvPolynomial.C : D →+* MvPolynomial (Fin na) D) =
        algebraMap D (Polynomial (MvPolynomial (Fin na) D)) from rfl] at hmem
  have hcong : ∀ x : MvPolynomial (Fin nk) D,
      awayCompHom σ Y dd x - awayCompHom σ' Y dd x ∈
        m.map (algebraMap D (Polynomial (MvPolynomial (Fin na) D))) :=
    fun x => Stacks.ArtinRees.aeval_sub_aeval_mem _ _ _
      (fun j => by
        rw [show Polynomial.C (MvPolynomial.map σ (Y j)) * Polynomial.X ^ dd j -
            Polynomial.C (MvPolynomial.map σ' (Y j)) * Polynomial.X ^ dd j =
            Polynomial.C (MvPolynomial.map σ (Y j) - MvPolynomial.map σ' (Y j)) *
              Polynomial.X ^ dd j by
          rw [map_sub]; ring]
        exact Ideal.mul_mem_right _ _ (hPolyC _ (map_sub_map_mem_map_C m hσ (Y j)))) x
  have key := Stacks.ArtinRees.SameDenominator.ofComp (D := D) m
    (π₁ := Stacks.ArtinRees.awayPolyHom
      (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ Pa.relation)))
      (MvPolynomial.map σ F₀)
      (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom σ Pk.relation)))
    (π₂ := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ Pk.relation)))
    (ρ₁ := Stacks.ArtinRees.awayPolyHom
      (Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ' Pa.relation)))
      (MvPolynomial.map σ' F₀)
      (MvPolynomial (Fin nk) D ⧸ LinearMap.range (relationMapOfHom σ' Pk.relation)))
    (ρ₂ := Ideal.Quotient.mkₐ D (LinearMap.range (relationMapOfHom σ' Pk.relation)))
    (h := awayCompHom σ Y dd) (h' := awayCompHom σ' Y dd)
    (Stacks.ArtinRees.surjective_awayPolyHom Ideal.Quotient.mk_surjective _)
    Ideal.Quotient.mk_surjective
    (Stacks.ArtinRees.surjective_awayPolyHom Ideal.Quotient.mk_surjective _)
    Ideal.Quotient.mk_surjective
    (fun x => AlgHom.congr_fun hcompσ x) (fun x => AlgHom.congr_fun hcompσ' x) hcong hAway
  rw [algebraMap_mvPolynomial nk,
    ← Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ Pk.relation)),
    ← Ideal.Quotient.mkₐ_ker D (LinearMap.range (relationMapOfHom σ' Pk.relation))]
  exact key

end AwayTwoSided

end Stacks.ConormalApproximation

end
