module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorConditions
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorReesPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Blowup
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# The sections supported on the exceptional subscheme of the two-generator square

Let `f₁, f₂` be elements of a commutative ring `A`, let `I = (f₁,f₂)`, and let
`b : X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ X = Spec A` be the modification of the two-generator
square of `StacksFrontier/AlgebraicGeometry/TwoGeneratorSquare.lean`. The blowup of `Spec A` in `I`
is a closed subscheme of `X'` over `X` by
`Stacks.AlmostBlowUp.isClosedImmersion_blowUpSpecToModification`. This file proves that it is
*exactly* the closed subscheme cut out by the ideal of sections of `𝒪_{X'}` supported on the
exceptional subscheme `E = b^{-1}(Z)`, which is condition (4) in the definition of an almost
blowup square (Tag 0EV6), and concludes that the two-generator square is an almost blowup square
(Tag 0EVH).

## Main definitions

* `Stacks.AlmostBlowUp.chartElt` is the degree-one element `fᵢTᵢ` of `A[T₀,T₁]/(f₂T₀-f₁T₁)`.

## Main results

* `AlgebraicGeometry.Proj.isIso_map_restrict_basicOpen_of_bijective_awayMap`: `Proj` of a graded
  homomorphism is an isomorphism over a standard open on which the induced map of degree-zero
  localizations is bijective.
* `Stacks.AlmostBlowUp.C_pow_mul_eq_of_isHomogeneous`: for a homogeneous `p` of degree `n` the
  class of `fᵢⁿ p` in the modification ring is the class of `p(f₁,f₂) · Tᵢⁿ`.
* `Stacks.AlmostBlowUp.pow_chartElt_mul_eq_zero` and
  `Stacks.AlmostBlowUp.bijective_awayMap_chartElt`: the comparison of the chart rings at `fᵢTᵢ`
  is bijective.
* `Stacks.AlmostBlowUp.isIso_blowUpSpecToModification_restrict_compl_support`: the blowup is the
  modification away from the centre.
* `Stacks.AlmostBlowUp.supportedSectionsIdeal_eq_ker_blowUpSpecToModification`: **the ideal of
  sections supported on the exceptional subscheme is the ideal of the blowup**.
* `Stacks.AlmostBlowUp.nonempty_over_iso_supportedSectionsIdeal`: **condition (4)**, as an
  equality of closed subschemes over `Spec A`.
* `Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase`: the two-generator modification
  satisfies the conditions of an almost blowup square.
* `Stacks.AlmostBlowUp.isAlmostBlowUpSquare_twoGeneratorSquare`: **the displayed two-generator
  square is an almost blowup square** (Tag 0EVH).

## Implementation notes

Only one inclusion of condition (4) is cheap. That the blowup contains no sections supported on
its exceptional subscheme is
`AlgebraicGeometry.supportedSectionsIdeal_eq_bot_of_isEffectiveCartierDivisor` applied to the
exceptional Cartier divisor of the blowup; the substance is the reverse
inclusion, which by `AlgebraicGeometry.supportedSectionsIdeal_map_of_restrict_isIso` is exactly
that the closed immersion of the blowup into the modification is an isomorphism away from the
exceptional subscheme.

That isomorphism is proved on two standard affine charts. The complement of the exceptional
subscheme is covered by the standard opens `D₊(f₁T₀)` and `D₊(f₂T₁)`: at a point where `f₁T₀` and
`f₂T₁` both vanish the relation `f₂T₀ = f₁T₁` of the square forces both `f₁` and `f₂` to vanish,
because one of the two homogeneous coordinates does not. On each of those charts the comparison
of the degree-zero localizations is bijective. Surjectivity is
`AlgebraicGeometry.Proj.away_map_surjective_of_surjective`. Injectivity is the only computation:
a homogeneous element of degree `n` killed after inverting `fᵢTᵢ` is the class of a homogeneous
polynomial `p` with `fᵢ^{2k} p(f₁,f₂) = 0`, and `Stacks.AlmostBlowUp.C_pow_mul_eq_of_isHomogeneous`
turns that into `(fᵢTᵢ)^{n+2k} p = 0` in the modification ring. That identity — the class of
`fᵢⁿ p` is the class of `p(f₁,f₂)Tᵢⁿ` — is checked monomial by monomial, where it is the `k`-th
power of the relation of the square.

The identification of the blowup `Proj` of the Rees algebra of `(f₁,f₂)` with the blowup of the
ideal sheaf of the centre, which is the form condition (4) is stated in, is
`Stacks.Blowup.nonempty_over_iso_blowUpToBase`.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 0EV8](https://stacks.math.columbia.edu/tag/0EV8)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Blowup

universe u

namespace AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **`Proj` of a graded homomorphism is an isomorphism over a standard open on which the
comparison of chart rings is bijective.** Over `D₊(s)` the morphism `Proj.map f` is, up to the
two chart identifications, `Spec` of the induced map `A_(s) ⟶ B_(f s)` of degree-zero
localizations. -/
theorem isIso_map_restrict_basicOpen_of_bijective_awayMap (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) {i : ℕ}
    (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i)
    (hbij : Function.Bijective (HomogeneousLocalization.Away.map f s)) :
    IsIso (Proj.map f hf ∣_ Proj.basicOpen 𝒜 s) := by
  have h2 : IsIso (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have h3 : IsIso (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))) :=
    inferInstance
  have hsq : IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)) ≫
        (Proj.basicOpenIsoSpec 𝒜 s hs hi).inv)
      (Proj.awayι ℬ (f s) (GradedRingHom.map_mem f hs) hi)
      (Proj.basicOpen 𝒜 s).ι (Proj.map f hf) := by
    refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · rw [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
      exact Proj.awayι_comp_map f hf hi s hs
    · rw [Proj.opensRange_awayι, Scheme.Opens.opensRange_ι, Proj.map_preimage_basicOpen]
  rw [← hsq.isoIsPullback_inv_fst _ _
    (isPullback_morphismRestrict (Proj.map f hf) (Proj.basicOpen 𝒜 s))]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso' h3 (Iso.isIso_inv _))

end AlgebraicGeometry.Proj

namespace Stacks.AlmostBlowUp

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-! ### The dehomogenizing relation in the modification ring -/

/-- In the modification ring, the classes of the variables satisfy `f₂T₀ = f₁T₁`. -/
theorem mk_C_mul_mk_X :
    Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (0 : Fin 2)) =
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (1 : Fin 2)) := by
  rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- **The key identity of the two-generator modification ring.** For a homogeneous polynomial
`p` of degree `n`, the relation `f₂T₀ = f₁T₁` lets one trade all occurrences of the variables
for the single variable `Tᵢ`, at the cost of multiplying by `fᵢⁿ`: the class of `fᵢⁿ p` is the
class of `p(f₁,f₂) · Tᵢⁿ`. -/
theorem C_pow_mul_eq_of_isHomogeneous (i : Fin 2) {n : ℕ} {p : MvPolynomial (Fin 2) A}
    (hp : p.IsHomogeneous n) :
    Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C (centerGens A f₁ f₂ i)) ^ n *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) p =
      Ideal.Quotient.mk (relationIdeal A f₁ f₂)
          (MvPolynomial.C (MvPolynomial.eval (centerGens A f₁ f₂) p)) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ n := by
  classical
  have hrel := mk_C_mul_mk_X A f₁ f₂
  have h1 : Ideal.Quotient.mk (relationIdeal A f₁ f₂) p =
      ∑ d ∈ p.support, Ideal.Quotient.mk (relationIdeal A f₁ f₂)
        (MvPolynomial.monomial d (p.coeff d)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  have h2 : MvPolynomial.eval (centerGens A f₁ f₂) p =
      ∑ d ∈ p.support, p.coeff d * ∏ j, centerGens A f₁ f₂ j ^ d j :=
    MvPolynomial.eval_eq' _ p
  rw [h1, h2, Finset.mul_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d 0 + d 1 = n := by
    have := hp.coeff_eq_zero (d := d)
    have hd' : d.degree = n := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hd) (this h)
    rw [← hd', Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hmon : MvPolynomial.monomial d (p.coeff d) =
      MvPolynomial.C (p.coeff d) *
        (MvPolynomial.X (0 : Fin 2) ^ d 0 * MvPolynomial.X (1 : Fin 2) ^ d 1) := by
    rw [MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rw [hmon, ← hdeg]
  simp only [map_mul, map_pow, Fin.prod_univ_two, centerGens_zero, centerGens_one]
  fin_cases i
  · simp only [Fin.zero_eta, centerGens_zero]
    have hb : (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (1 : Fin 2))) ^ d 1 =
        (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (0 : Fin 2))) ^ d 1 := by
      rw [hrel]
    linear_combination (Ideal.Quotient.mk (relationIdeal A f₁ f₂)
          (MvPolynomial.C (p.coeff d)) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (0 : Fin 2)) ^ d 0 *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) ^ d 0) * hb
  · simp only [Fin.mk_one, centerGens_one]
    have ha : (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (0 : Fin 2))) ^ d 0 =
        (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (1 : Fin 2))) ^ d 0 := by
      rw [hrel]
    linear_combination (Ideal.Quotient.mk (relationIdeal A f₁ f₂)
          (MvPolynomial.C (p.coeff d)) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X (1 : Fin 2)) ^ d 1 *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) ^ d 1) * ha

/-! ### The two distinguished degree-one elements -/

/-- The degree-one element `fᵢTᵢ` of the modification ring. The two standard affine charts of
the modification at `f₁T₀` and at `f₂T₁` cover the part of the modification away from the
exceptional subscheme. -/
def chartElt (i : Fin 2) : modificationRing A f₁ f₂ :=
  Ideal.Quotient.mk (relationIdeal A f₁ f₂)
    (MvPolynomial.C (centerGens A f₁ f₂ i) * MvPolynomial.X i)

/-- The polynomial `fᵢTᵢ` is homogeneous of degree one. -/
theorem isHomogeneous_C_mul_X (i : Fin 2) :
    (MvPolynomial.C (centerGens A f₁ f₂ i) * MvPolynomial.X i).IsHomogeneous 1 := by
  simpa using (MvPolynomial.isHomogeneous_C _ (centerGens A f₁ f₂ i)).mul
    (MvPolynomial.isHomogeneous_X _ i)

/-- The element `fᵢTᵢ` lies in the degree-one part of the modification ring. -/
theorem chartElt_mem (i : Fin 2) : chartElt A f₁ f₂ i ∈ modificationGrading A f₁ f₂ 1 := by
  refine AddSubgroup.mem_map.mpr
    ⟨MvPolynomial.C (centerGens A f₁ f₂ i) * MvPolynomial.X i, ?_, rfl⟩
  exact (Submodule.mem_toAddSubgroup _).mpr
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_C_mul_X A f₁ f₂ i))

/-- The class of a homogeneous polynomial `q` of degree `m` is sent into the Rees algebra, viewed
inside `A[X]`, to the monomial `q(f₁,f₂) Xᵐ`. -/
theorem coe_reesQuotPresentation_mk {m : ℕ} {q : MvPolynomial (Fin 2) A}
    (hq : q.IsHomogeneous m) :
    ((reesQuotPresentation A f₁ f₂ (Ideal.Quotient.mk (relationIdeal A f₁ f₂) q) :
        reesAlgebra (centerIdeal A f₁ f₂)) : Polynomial A) =
      Polynomial.monomial m (MvPolynomial.eval (centerGens A f₁ f₂) q) := by
  rw [reesQuotPresentation_mk, show (centerReesPresentation A f₁ f₂).toRingHom q =
    centerReesPresentation A f₁ f₂ q from rfl]
  exact coe_reesPresentation_apply (centerIdeal A f₁ f₂) (centerGens A f₁ f₂)
    (centerGens_mem A f₁ f₂) hq

/-- **The comparison with the Rees algebra kills nothing new after inverting `fᵢTᵢ`.** A
homogeneous element of the modification ring whose image in the Rees algebra is killed by a
power of the image of `fᵢTᵢ` is already killed by a power of `fᵢTᵢ`. -/
theorem pow_chartElt_mul_eq_zero (i : Fin 2) {n : ℕ} {a : modificationRing A f₁ f₂}
    (ha : a ∈ modificationGrading A f₁ f₂ n) {k : ℕ}
    (hk : reesQuotPresentation A f₁ f₂ (chartElt A f₁ f₂ i) ^ k *
      reesQuotPresentation A f₁ f₂ a = 0) :
    chartElt A f₁ f₂ i ^ (n + 2 * k) * a = 0 := by
  obtain ⟨p, hp, hpa⟩ := AddSubgroup.mem_map.mp ha
  have hpa' : Ideal.Quotient.mk (relationIdeal A f₁ f₂) p = a := hpa
  subst hpa'
  have hp' : p.IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule n p).mp ((Submodule.mem_toAddSubgroup _).mp hp)
  set c := MvPolynomial.eval (centerGens A f₁ f₂) p with hcdef
  have h0 : ((reesQuotPresentation A f₁ f₂ (chartElt A f₁ f₂ i) ^ k *
      reesQuotPresentation A f₁ f₂ (Ideal.Quotient.mk (relationIdeal A f₁ f₂) p) :
        reesAlgebra (centerIdeal A f₁ f₂)) : Polynomial A) = 0 := by
    rw [hk]; simp
  rw [Subalgebra.coe_mul, SubmonoidClass.coe_pow, chartElt,
    coe_reesQuotPresentation_mk A f₁ f₂ (isHomogeneous_C_mul_X A f₁ f₂ i),
    coe_reesQuotPresentation_mk A f₁ f₂ hp', Polynomial.monomial_pow,
    Polynomial.monomial_mul_monomial, Polynomial.monomial_eq_zero_iff] at h0
  have hc : centerGens A f₁ f₂ i ^ (2 * k) * c = 0 := by
    rw [← h0]
    simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  calc chartElt A f₁ f₂ i ^ (n + 2 * k) *
        Ideal.Quotient.mk (relationIdeal A f₁ f₂) p
      = Ideal.Quotient.mk (relationIdeal A f₁ f₂)
            (MvPolynomial.C (centerGens A f₁ f₂ i)) ^ (2 * k) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ (n + 2 * k) *
          (Ideal.Quotient.mk (relationIdeal A f₁ f₂)
              (MvPolynomial.C (centerGens A f₁ f₂ i)) ^ n *
            Ideal.Quotient.mk (relationIdeal A f₁ f₂) p) := by
        simp only [chartElt, map_mul, mul_pow]
        ring
    _ = Ideal.Quotient.mk (relationIdeal A f₁ f₂)
            (MvPolynomial.C (centerGens A f₁ f₂ i)) ^ (2 * k) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ (n + 2 * k) *
          (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C c) *
            Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ n) := by
        rw [C_pow_mul_eq_of_isHomogeneous A f₁ f₂ i hp']
    _ = Ideal.Quotient.mk (relationIdeal A f₁ f₂)
            (MvPolynomial.C (centerGens A f₁ f₂ i ^ (2 * k) * c)) *
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.X i) ^ (n + 2 * k + n) := by
        simp only [map_mul, map_pow]
        ring
    _ = 0 := by rw [hc]; simp

/-! ### The comparison is an isomorphism on the two charts -/

section Graded

variable [GradedRing (modificationGrading A f₁ f₂)]

/-- **The comparison of chart rings at `fᵢTᵢ` is injective.** -/
theorem injective_awayMap_chartElt (i : Fin 2) :
    Function.Injective (HomogeneousLocalization.Away.map (reesQuotPresentation A f₁ f₂)
      (chartElt A f₁ f₂ i)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (modificationGrading A f₁ f₂)
      (chartElt_mem A f₁ f₂ i) x
  have ha' : a ∈ modificationGrading A f₁ f₂ n := by simpa using ha
  rw [HomogeneousLocalization.Away.map_mk] at hx
  have hval := congrArg HomogeneousLocalization.val hx
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    ← Localization.mk_zero 1, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
  obtain ⟨⟨u, k, hu⟩, hu'⟩ := hval
  have hu2 : reesQuotPresentation A f₁ f₂ (chartElt A f₁ f₂ i) ^ k = u := hu
  have hk : reesQuotPresentation A f₁ f₂ (chartElt A f₁ f₂ i) ^ k *
      reesQuotPresentation A f₁ f₂ a = 0 := by
    rw [hu2]
    simpa using hu'
  have hzero := pow_chartElt_mul_eq_zero A f₁ f₂ i ha' hk
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
    ← Localization.mk_zero 1, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨⟨chartElt A f₁ f₂ i ^ (n + 2 * k), n + 2 * k, rfl⟩, by simpa using hzero⟩

/-- **The comparison of chart rings at `fᵢTᵢ` is bijective.** Surjectivity is surjectivity of
the presentation of the Rees algebra by the modification ring, and injectivity is
`Stacks.AlmostBlowUp.injective_awayMap_chartElt`. -/
theorem bijective_awayMap_chartElt (i : Fin 2) :
    Function.Bijective (HomogeneousLocalization.Away.map (reesQuotPresentation A f₁ f₂)
      (chartElt A f₁ f₂ i)) :=
  ⟨injective_awayMap_chartElt A f₁ f₂ i,
    Proj.away_map_surjective_of_surjective _ (surjective_reesQuotPresentation A f₁ f₂)
      (chartElt_mem A f₁ f₂ i)⟩

end Graded

/-- **The blowup is the modification over the standard open `D₊(fᵢTᵢ)`.** The chart of the
modification at the degree-one element `fᵢTᵢ` is the chart of the blowup at the image element,
because the comparison of the two chart rings is bijective. -/
theorem isIso_blowUpSpecToModification_restrict_basicOpen (i : Fin 2) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsIso (blowUpSpecToModification A f₁ f₂ ∣_
      Proj.basicOpen (modificationGrading A f₁ f₂) (chartElt A f₁ f₂ i)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact Proj.isIso_map_restrict_basicOpen_of_bijective_awayMap (reesQuotPresentation A f₁ f₂) _
    Nat.one_pos _ (chartElt_mem A f₁ f₂ i) (bijective_awayMap_chartElt A f₁ f₂ i)

/-! ### The two charts cover the complement of the exceptional subscheme -/

/-- **If both `f₁T₀` and `f₂T₁` vanish at a point of the modification, then so do `f₁` and
`f₂`.** One of the two homogeneous coordinates is nonzero at the point, and the relation
`f₂T₀ = f₁T₁` then transports the vanishing from one coefficient to the other. -/
theorem mem_asHomogeneousIdeal_of_chartElt_mem :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ x : ProjectiveSpectrum (modificationGrading A f₁ f₂),
      chartElt A f₁ f₂ 0 ∈ x.asHomogeneousIdeal.toIdeal →
        chartElt A f₁ f₂ 1 ∈ x.asHomogeneousIdeal.toIdeal →
          Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) ∈
              x.asHomogeneousIdeal.toIdeal ∧
            Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) ∈
              x.asHomogeneousIdeal.toIdeal := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro x h0 h1
  have hprime : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have he0 : chartElt A f₁ f₂ 0 =
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₁) *
        modificationCoord A f₁ f₂ 0 := by
    rw [chartElt, modificationCoord, ← map_mul, centerGens_zero]
  have he1 : chartElt A f₁ f₂ 1 =
      Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C f₂) *
        modificationCoord A f₁ f₂ 1 := by
    rw [chartElt, modificationCoord, ← map_mul, centerGens_one]
  have key : ∀ u v t s : modificationRing A f₁ f₂, v * t = u * s →
      u * t ∈ x.asHomogeneousIdeal.toIdeal → t ∉ x.asHomogeneousIdeal.toIdeal →
      u ∈ x.asHomogeneousIdeal.toIdeal ∧ v ∈ x.asHomogeneousIdeal.toIdeal := by
    intro u v t s hvt hut ht
    have hu := (hprime.mem_or_mem hut).resolve_right ht
    refine ⟨hu, (hprime.mem_or_mem ?_).resolve_right ht⟩
    rw [hvt]
    exact Ideal.mul_mem_right _ _ hu
  have hrel := C_mul_coord_eq A f₁ f₂
  have ht : modificationCoord A f₁ f₂ 0 ∉ x.asHomogeneousIdeal.toIdeal ∨
      modificationCoord A f₁ f₂ 1 ∉ x.asHomogeneousIdeal.toIdeal := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have hspan : Ideal.span (Set.range (modificationCoord A f₁ f₂)) ≤
        x.asHomogeneousIdeal.toIdeal := by
      refine Ideal.span_le.mpr ?_
      rintro z ⟨j, rfl⟩
      fin_cases j
      · exact hcon.1
      · exact hcon.2
    exact x.not_irrelevant_le ((irrelevant_le_span_modificationCoord A f₁ f₂).trans hspan)
  rcases ht with ht0 | ht1
  · exact key _ _ _ _ hrel (he0 ▸ h0) ht0
  · exact (key _ _ _ _ hrel.symm (he1 ▸ h1) ht1).symm

/-- The part of the modification over a standard open `D(a)` of the base is the standard open of
the class of the constant `a`. -/
theorem modificationToBase_preimage_basicOpen (a : A) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    modificationToBase A f₁ f₂ ⁻¹ᵁ PrimeSpectrum.basicOpen a =
      Proj.basicOpen (modificationGrading A f₁ f₂)
        (Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hcomp : modificationToBase A f₁ f₂ ⁻¹ᵁ PrimeSpectrum.basicOpen a =
      Proj.toSpecZero (modificationGrading A f₁ f₂) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (twoGeneratorSquare A f₁ f₂).baseMap) ⁻¹ᵁ
          PrimeSpectrum.basicOpen a) := rfl
  rw [hcomp, SpecMap_preimage_basicOpen, Proj.toSpecZero_preimage_basicOpen]
  exact congrArg _ ((twoGeneratorSquare A f₁ f₂).baseMap_apply a)

/-- The support of the ideal sheaf of the centre is the zero locus of `(f₁,f₂)`. -/
theorem coe_support_centerIdealSheaf :
    ((centerIdealSheaf A f₁ f₂).support : Set (Spec (CommRingCat.of A))) =
      PrimeSpectrum.zeroLocus (centerIdeal A f₁ f₂ : Set A) := by
  rw [centerIdealSheaf, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  have hmap : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (centerIdeal A f₁ f₂)) =
      centerIdeal A f₁ f₂ := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp,
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id, CommRingCat.hom_id, Ideal.map_id]
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe]
  refine ⟨fun hy => ?_, fun hy => Ideal.mem_map_of_mem _ hy⟩
  have h2 := Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom hy
  rw [hmap] at h2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) = y :=
    congr($((Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id).hom y)
  rwa [h3] at h2

/-! ### The comparison is an isomorphism away from the centre -/

/-- Being an isomorphism over an open passes to smaller opens. -/
theorem isIso_morphismRestrict_of_le {Y Z : Scheme.{u}} (g : Y ⟶ Z) {W W' : Z.Opens}
    (hle : W' ≤ W) (h : IsIso (g ∣_ W)) : IsIso (g ∣_ W') := by
  have h1 : MorphismProperty.isomorphisms Scheme ((g ∣_ W) ∣_ (W.ι ⁻¹ᵁ W')) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) h _
  have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict g W (W.ι ⁻¹ᵁ W'))).mp h1
  have h3 : W.ι ''ᵁ (W.ι ⁻¹ᵁ W') = W' := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  rwa [h3] at h2

/-- Being an isomorphism over two opens gives it over any open they cover. -/
theorem isIso_morphismRestrict_of_le_sup {Y Z : Scheme.{u}} (g : Y ⟶ Z) {W W₀ W₁ : Z.Opens}
    (hle : (W : Set Z) ⊆ (W₀ : Set Z) ∪ (W₁ : Set Z)) (h0 : IsIso (g ∣_ W₀))
    (h1 : IsIso (g ∣_ W₁)) : IsIso (g ∣_ W) := by
  refine isIso_morphismRestrict_of_iSup g W
    (fun j : ULift.{u} (Fin 2) => W.ι ⁻¹ᵁ ![W₀, W₁] j.down) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    rcases hle y.2 with hy | hy
    · exact ⟨⟨0⟩, hy⟩
    · exact ⟨⟨1⟩, hy⟩
  · rintro ⟨j⟩
    fin_cases j
    · exact isIso_morphismRestrict_of_le g (W.ι.image_preimage_le W₀) h0
    · exact isIso_morphismRestrict_of_le g (W.ι.image_preimage_le W₁) h1

/-- **The two standard opens `D₊(f₁T₀)` and `D₊(f₂T₁)` cover the complement of the exceptional
subscheme.** -/
theorem compl_support_subset_union_basicOpen_chartElt :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ x : AlgebraicGeometry.Proj (modificationGrading A f₁ f₂),
      x ∉ (((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support :
          Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) →
        x ∈ (Proj.basicOpen (modificationGrading A f₁ f₂) (chartElt A f₁ f₂ 0) :
            Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) ∪
          (Proj.basicOpen (modificationGrading A f₁ f₂) (chartElt A f₁ f₂ 1) :
            Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  have hchart : ∀ i, x ∉ (Proj.basicOpen (modificationGrading A f₁ f₂) (chartElt A f₁ f₂ i) :
      Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) →
      chartElt A f₁ f₂ i ∈ x.asHomogeneousIdeal.toIdeal := fun i hi => by
    by_contra hm
    exact hi ((ProjectiveSpectrum.mem_coe_basicOpen _ _ _).mpr hm)
  have h0 := hchart 0 hcon.1
  have h1 := hchart 1 hcon.2
  obtain ⟨hu, hv⟩ := mem_asHomogeneousIdeal_of_chartElt_mem A f₁ f₂ x h0 h1
  have hmem : ∀ a : A, Ideal.Quotient.mk (relationIdeal A f₁ f₂) (MvPolynomial.C a) ∈
      x.asHomogeneousIdeal.toIdeal →
      a ∈ ((modificationToBase A f₁ f₂).base x).asIdeal := by
    intro a ha
    by_contra hna
    have hb : x ∈ modificationToBase A f₁ f₂ ⁻¹ᵁ PrimeSpectrum.basicOpen a :=
      (PrimeSpectrum.mem_basicOpen a _).mpr hna
    rw [modificationToBase_preimage_basicOpen] at hb
    exact (ProjectiveSpectrum.mem_basicOpen _ _ _).mp hb ha
  refine hx ?_
  have hz : (modificationToBase A f₁ f₂).base x ∈
      ((centerIdealSheaf A f₁ f₂).support : Set (Spec (CommRingCat.of A))) := by
    rw [coe_support_centerIdealSheaf]
    refine (PrimeSpectrum.mem_zeroLocus _ _).mpr ?_
    rw [SetLike.coe_subset_coe]
    refine Ideal.span_le.mpr ?_
    intro z hzm
    rcases hzm with hzm | hzm
    · rw [hzm]
      exact hmem f₁ hu
    · rw [Set.mem_singleton_iff] at hzm
      rw [hzm]
      exact hmem f₂ hv
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage]
  exact hz

/-- **The blowup of `Spec A` in `(f₁,f₂)` is the modification away from the centre.** -/
theorem isIso_blowUpSpecToModification_restrict_compl_support :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsIso (blowUpSpecToModification A f₁ f₂ ∣_
      (⟨(((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support :
            Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)))ᶜ,
          ((centerIdealSheaf A f₁ f₂).comap
            (modificationToBase A f₁ f₂)).support.isClosed.isOpen_compl⟩ :
        (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Opens)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine isIso_morphismRestrict_of_le_sup _ ?_
    (isIso_blowUpSpecToModification_restrict_basicOpen A f₁ f₂ 0)
    (isIso_blowUpSpecToModification_restrict_basicOpen A f₁ f₂ 1)
  intro x hx
  exact compl_support_subset_union_basicOpen_chartElt A f₁ f₂ x hx

/-! ### Condition (4): the supported sections cut out the blowup -/

/-- **The ideal of sections of `𝒪_{X'}` supported on the exceptional subscheme is the ideal of
the blowup.** The blowup is a closed subscheme of the modification which is an isomorphism away
from the exceptional subscheme, so the ideal of supported sections of the modification is the
pushforward of that of the blowup; and the blowup has no sections supported on its exceptional
subscheme, that being an effective Cartier divisor. -/
theorem supportedSectionsIdeal_eq_ker_blowUpSpecToModification :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    supportedSectionsIdeal
        (((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support :
          Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) =
      (blowUpSpecToModification A f₁ f₂).ker := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hcomap : ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).comap
      (blowUpSpecToModification A f₁ f₂) =
      (centerIdealSheaf A f₁ f₂).comap (Stacks.Blowup.toSpec (centerIdeal A f₁ f₂)) := by
    rw [← Scheme.IdealSheafData.comap_comp,
      blowUpSpecToModification_comp_modificationToBase A f₁ f₂]
  have hEff : Stacks.Divisors.IsEffectiveCartierDivisor
      ((centerIdealSheaf A f₁ f₂).comap (Stacks.Blowup.toSpec (centerIdeal A f₁ f₂))) :=
    Stacks.Blowup.isEffectiveCartierDivisor_comap_toSpec (centerIdeal A f₁ f₂)
      (centerIdealSheaf A f₁ f₂) (map_ideal_centerIdealSheaf_top A f₁ f₂)
  have hpre : (blowUpSpecToModification A f₁ f₂).base ⁻¹'
      (((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support :
        Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂))) =
      (((centerIdealSheaf A f₁ f₂).comap
          (Stacks.Blowup.toSpec (centerIdeal A f₁ f₂))).support :
        Set (Stacks.Blowup.blowUpSpec (centerIdeal A f₁ f₂))) := by
    conv_rhs => rw [← hcomap, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage]
  rw [← supportedSectionsIdeal_map_of_restrict_isIso (blowUpSpecToModification A f₁ f₂) _
      ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support.isClosed
      (isIso_blowUpSpecToModification_restrict_compl_support A f₁ f₂),
    hpre, supportedSectionsIdeal_eq_bot_of_isEffectiveCartierDivisor _ hEff,
    Scheme.IdealSheafData.map_bot]

/-- **Condition (4) in the definition of an almost blowup square, for the two-generator square.**
Removing from the modification `X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))` the sections of `𝒪_{X'}`
supported on the exceptional subscheme leaves the blowup of `Spec A` in `(f₁,f₂)`, as a scheme
over `Spec A`. -/
theorem nonempty_over_iso_supportedSectionsIdeal :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    Nonempty (Over.mk ((supportedSectionsIdeal
          (((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).support :
            Set (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)))).subschemeι ≫
        modificationToBase A f₁ f₂) ≅
      Over.mk (Stacks.Blowup.toSpec (centerIdeal A f₁ f₂))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  rw [supportedSectionsIdeal_eq_ker_blowUpSpecToModification A f₁ f₂]
  refine ⟨Over.isoMk (asIso (blowUpSpecToModification A f₁ f₂).toImage).symm ?_⟩
  change inv (blowUpSpecToModification A f₁ f₂).toImage ≫
      Stacks.Blowup.toSpec (centerIdeal A f₁ f₂) =
    (blowUpSpecToModification A f₁ f₂).ker.subschemeι ≫ modificationToBase A f₁ f₂
  rw [IsIso.inv_comp_eq, ← blowUpSpecToModification_comp_modificationToBase A f₁ f₂,
    ← Category.assoc, Scheme.Hom.toImage_imageι]

/-! ### The two-generator square is an almost blowup square -/

/-- **The two-generator modification is an almost blowup.** For elements `f₁, f₂` of a commutative
ring `A` the morphism `Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ Spec A`, with centre the closed subscheme cut
out by `(f₁,f₂)`, is the modification of an almost blowup square. Tag 0EVH in full, with the
corners of the displayed square, is `Stacks.AlmostBlowUp.isAlmostBlowUpSquare_twoGeneratorSquare`.

The first four conditions are the finite presentation of the centre, the local principality of
the exceptional subscheme, properness and finite presentation of the modification; the fifth is
`Stacks.AlmostBlowUp.nonempty_over_iso_supportedSectionsIdeal`, the identification of the closed
subscheme cut out by the sections supported on the exceptional subscheme with the blowup. -/
theorem isAlmostBlowUpSquare_modificationToBase :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    AlgebraicGeometry.IsAlmostBlowUpSquare (centerIdealSheaf A f₁ f₂)
      (modificationToBase A f₁ f₂) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine ⟨finitePresentation_centerIdealSheaf_subschemeι A f₁ f₂,
    isLocallyPrincipal_comap_centerIdealSheaf A f₁ f₂,
    isProper_modificationToBase A f₁ f₂,
    finitePresentation_modificationToBase A f₁ f₂, ?_⟩
  obtain ⟨e1⟩ := nonempty_over_iso_supportedSectionsIdeal A f₁ f₂
  obtain ⟨e2⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase A (centerIdeal A f₁ f₂)
  exact ⟨e1 ≪≫ e2⟩


/-- **Stacks Project, Tag 0EVH.** Let `A` be a ring and `f₁, f₂ ∈ A`. The square
```
E = Proj ((A/(f₁,f₂))[T₀,T₁]) ⟶ Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) = X'
            ↓                                ↓
     Z = Spec (A/(f₁,f₂))      ⟶       Spec A = X
```
is an almost blowup square: it is cartesian, so that `E = b⁻¹(Z)`; its lower arrow is, over
`Spec A`, the closed subscheme cut out by `(f₁,f₂)`; and the right-hand arrow `b` with that centre
satisfies the conditions of an almost blowup square. -/
@[stacks 0EVH]
theorem isAlmostBlowUpSquare_twoGeneratorSquare :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsPullback (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂) ∧
      Nonempty (Over.mk (centerToBase A f₁ f₂) ≅
        Over.mk (centerIdealSheaf A f₁ f₂).subschemeι) ∧
      AlgebraicGeometry.IsAlmostBlowUpSquare (centerIdealSheaf A f₁ f₂)
        (modificationToBase A f₁ f₂) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine ⟨twoGenerator_isPullback A f₁ f₂, ?_, isAlmostBlowUpSquare_modificationToBase A f₁ f₂⟩
  have : IsClosedImmersion (centerToBase A f₁ f₂) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hker : (centerToBase A f₁ f₂).ker = centerIdealSheaf A f₁ f₂ :=
    ker_Spec_map_quotient_mk (centerIdeal A f₁ f₂)
  rw [← hker]
  exact ⟨Over.isoMk (asIso (centerToBase A f₁ f₂).toImage) (by simp)⟩

end Stacks.AlmostBlowUp

end
