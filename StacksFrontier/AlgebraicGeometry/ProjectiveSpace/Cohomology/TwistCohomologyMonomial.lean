module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistWeights
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the twists of the structure sheaf on projective space

Let `R` be a commutative ring, let `n ≥ 0` be an integer and let `d` be an integer. Then, as
`R`-modules,

$$ H^q(\mathbf{P}^n_R, \mathcal{O}(d)) =
  \begin{cases} (R[T_0, \ldots, T_n])_d & q = 0 \text{ and } d \geq 0 \\
    \bigl(\tfrac{1}{T_0 \cdots T_n} R[\tfrac{1}{T_0}, \ldots, \tfrac{1}{T_n}]\bigr)_d
      & q = n \text{ and } d < 0 \\
    0 & \text{otherwise,} \end{cases} $$

which is [Stacks, Tag 01XT]. The degree-`d` part of `(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]` is the free
`R`-module `Stacks.ProjectiveSpace.Cohomology.negativeTwistPart` on the exponent vectors of total
degree `d` all of whose entries are negative. Both non-vanishing modules are finite free over
`R`, so `H^q(ℙⁿ_R, 𝒪(d))` is a finite `R`-module in every degree.

The two non-vanishing rows overlap at `n = 0`, where they are the two sign ranges of
`H⁰(ℙ⁰_R, 𝒪(d)) = R`; the side conditions `d ≥ 0` and `d < 0` are what makes the displayed
equation well formed there. For `n ≥ 1` they are the equation of [Stacks, Tag 01XU], formalized as
`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology`, with the top row dualised back along
the residue pairing `Stacks.ProjectiveSpace.Cohomology.topDualEquiv`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.TwistCohomologyMonomial`: the three rows, bundled.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous`: **`H⁰(ℙⁿ_R, 𝒪(d))` is the
  module of degree-`d` homogeneous polynomials in `T₀, …, Tₙ` for `d ≥ 0`.**
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative`: **`Hⁿ(ℙⁿ_R, 𝒪(d))` is the free
  module on the degree-`d` Laurent monomials with every exponent negative, for `d < 0`.**
* `Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology`: **`H^q(ℙⁿ_R, 𝒪(d))` vanishes in
  every other case.**
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyMonomial`: the three together.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistCohomology`: **`H^q(ℙⁿ_R, 𝒪(d))` is a
  finite `R`-module**, for every `q`, `n` and `d`.

## Implementation notes

For `n = 0` the standard cover of `ℙ⁰_R = D₊(T₀)` has a single member, so the Čech complex of
`Stacks.ProjectiveSpace.Cohomology.laurentCechComplex` is concentrated in degree `0` and its
degree-zero homology is the whole module of degree-zero cochains, which is the chart inverting
every variable. That chart coincides with the polynomial chart for `d ≥ 0` and with the negative
Laurent part for `d < 0`, because in one variable the total degree is the only exponent.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### Finiteness of the two monomial index sets -/

/-- The degree-`d` Laurent monomials with every exponent negative are finite in number: every
exponent lies between `d` and `-1`. -/
instance instFiniteNegativeLaurentMonomials (n : ℕ) (d : ℤ) :
    Finite (negativeLaurentMonomials n d) :=
  Set.Finite.to_subtype (Stacks.ProjectiveCohomology.finite_neg_weights (n := n) d)

/-- The degree-`d` part of `R[T₀, …, Tₙ]` is a finite `R`-module. -/
instance instModuleFiniteTwistChartEmpty (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Finite R (twistChart R n d (∅ : Set (Fin (n + 1)))) :=
  Module.Finite.of_basis (twistChartBasis R n d (∅ : Set (Fin (n + 1))))

/-- The degree-`d` part of `(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]` is a finite `R`-module. -/
instance instModuleFiniteNegativeTwistPart (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Finite R (negativeTwistPart R n d) :=
  Module.Finite.of_basis (negativeTwistPartBasis R n d)

/-! ### Projective space of dimension zero -/

section ZeroDim

variable {R : Type u} [CommRing R] {d : ℤ}

/-- In one variable the total degree of a Laurent monomial is its only exponent. -/
private theorem sum_eq_apply_zeroDim (e : Fin (0 + 1) → ℤ) (i : Fin (0 + 1)) :
    (∑ j, e j) = e i := by
  have h : ∀ j : Fin (0 + 1), j = i := by
    intro j
    refine Fin.ext ?_
    have hj := j.isLt
    have hi := i.isLt
    omega
  exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hj => absurd (h j) hj

/-- For `d ≥ 0` the degree-`d` Laurent monomials in one variable are the polynomial ones. -/
theorem laurentMonomials_univ_eq_empty_zeroDim (hd : 0 ≤ d) :
    laurentMonomials 0 d (Set.univ : Set (Fin (0 + 1)))
      = laurentMonomials 0 d (∅ : Set (Fin (0 + 1))) := by
  ext e
  refine ⟨fun he => ⟨he.1, fun i _ => ?_⟩, fun he => ⟨he.1, fun i hi => absurd (Set.mem_univ i) hi⟩⟩
  have h := (sum_eq_apply_zeroDim e i).symm.trans he.1
  omega

/-- For `d < 0` the degree-`d` Laurent monomials in one variable all have negative exponent. -/
theorem laurentMonomials_univ_eq_negative_zeroDim (hd : d < 0) :
    laurentMonomials 0 d (Set.univ : Set (Fin (0 + 1))) = negativeLaurentMonomials 0 d := by
  ext e
  refine ⟨fun he => ⟨he.1, fun i => ?_⟩, fun he => ⟨he.1, fun i hi => absurd (Set.mem_univ i) hi⟩⟩
  have h := (sum_eq_apply_zeroDim e i).symm.trans he.1
  omega

/-- For `d ≥ 0` the chart of `ℙ⁰_R` inverting `T₀` is the degree-`d` part of `R[T₀]`. -/
theorem twistChart_univ_eq_empty_zeroDim (R : Type u) [CommRing R] (hd : 0 ≤ d) :
    twistChart R 0 d (Set.univ : Set (Fin (0 + 1)))
      = twistChart R 0 d (∅ : Set (Fin (0 + 1))) :=
  congrArg (Finsupp.supported R R) (laurentMonomials_univ_eq_empty_zeroDim hd)

/-- For `d < 0` the chart of `ℙ⁰_R` inverting `T₀` is the degree-`d` part of `T₀⁻¹ R[T₀⁻¹]`. -/
theorem twistChart_univ_eq_negativeTwistPart_zeroDim (R : Type u) [CommRing R] (hd : d < 0) :
    twistChart R 0 d (Set.univ : Set (Fin (0 + 1))) = negativeTwistPart R 0 d :=
  congrArg (Finsupp.supported R R) (laurentMonomials_univ_eq_negative_zeroDim hd)

/-- The degree-`d` Laurent monomials in one variable are finite in number. -/
private theorem finite_laurentMonomials_univ_zeroDim (d : ℤ) :
    (laurentMonomials 0 d (Set.univ : Set (Fin (0 + 1)))).Finite := by
  rcases le_or_gt 0 d with hd | hd
  · rw [laurentMonomials_univ_eq_empty_zeroDim hd]
    exact finite_laurentMonomials_empty 0 d
  · rw [laurentMonomials_univ_eq_negative_zeroDim hd]
    exact Stacks.ProjectiveCohomology.finite_neg_weights (n := 0) d

/-- The chart of `ℙ⁰_R` inverting `T₀` is a finite `R`-module. -/
instance instModuleFiniteTwistChartUnivZeroDim (R : Type u) [CommRing R] (d : ℤ) :
    Module.Finite R (twistChart R 0 d (Set.univ : Set (Fin (0 + 1)))) :=
  haveI : Finite (laurentMonomials 0 d (Set.univ : Set (Fin (0 + 1)))) :=
    Set.Finite.to_subtype (finite_laurentMonomials_univ_zeroDim d)
  Module.Finite.of_basis (twistChartBasis R 0 d (Set.univ : Set (Fin (0 + 1))))

/-- A degree-zero Čech cochain of the one-member cover of `ℙ⁰_R` read at the total index set. -/
def zeroDimCochainMap (R : Type u) [CommRing R] (d : ℤ) :
    laurentCechCochains R 0 d 0 →ₗ[R] twistChart R 0 d (Set.univ : Set (Fin (0 + 1))) where
  toFun c := ⟨(c : LaurentCochain R 0) Finset.univ, by
    have h := (mem_laurentCechCochains.1 c.2).1 Finset.univ
    rwa [Finset.coe_univ] at h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The degree-zero Čech cochains of the standard cover of `ℙ⁰_R` are the degree-`d` Laurent
sections on `D₊(T₀)`. This is the case `n = 0` of
`Stacks.ProjectiveSpace.Cohomology.topCochainEquiv`, which is stated for `n = m + 1`. -/
def zeroDimCochainEquiv (R : Type u) [CommRing R] (d : ℤ) :
    laurentCechCochains R 0 d 0 ≃ₗ[R] twistChart R 0 d (Set.univ : Set (Fin (0 + 1))) := by
  classical
  refine LinearEquiv.ofBijective (zeroDimCochainMap R d) ⟨fun c₁ c₂ h => ?_, fun x => ?_⟩
  · refine Subtype.ext (funext fun S => ?_)
    by_cases hS : S.card = 0 + 1
    · rw [eq_univ_of_card_eq S hS]
      exact congrArg (fun y : twistChart R 0 d (Set.univ : Set (Fin (0 + 1))) =>
        (y : (Fin (0 + 1) → ℤ) →₀ R)) h
    · rw [(mem_laurentCechCochains.1 c₁.2).2 S hS, (mem_laurentCechCochains.1 c₂.2).2 S hS]
  · refine ⟨⟨fun S => if S = Finset.univ then (x : (Fin (0 + 1) → ℤ) →₀ R) else 0,
      ⟨fun S => ?_, fun S hS => ?_⟩⟩, ?_⟩
    · change (if S = Finset.univ then (x : (Fin (0 + 1) → ℤ) →₀ R) else 0)
        ∈ twistChart R 0 d (S : Set (Fin (0 + 1)))
      by_cases hS : S = Finset.univ
      · rw [ite_eq_left hS, hS, Finset.coe_univ]
        exact x.2
      · rw [ite_eq_right hS]
        exact zero_mem _
    · change (if S = Finset.univ then (x : (Fin (0 + 1) → ℤ) →₀ R) else 0) = 0
      refine ite_eq_right fun hSu => hS ?_
      rw [hSu, Finset.card_univ, Fintype.card_fin]
    · exact Subtype.ext (by simp [zeroDimCochainMap])

attribute [local implicit_reducible] laurentCechComplex

/-- The degree-zero homology of the Čech complex of the standard cover of `ℙ⁰_R` for `𝒪(d)` is
the whole module of degree-zero cochains, i.e. the chart inverting `T₀`: there is no differential
into or out of degree zero. -/
def zeroDimHomologyIso (R : Type u) [CommRing R] (d : ℤ) :
    (laurentCechComplex R 0 d).homology 0 ≅
      ModuleCat.of R (twistChart R 0 d (Set.univ : Set (Fin (0 + 1)))) :=
  ((laurentCechComplex R 0 d).isoHomologyπ 0 0 (by simp)
        ((laurentCechComplex R 0 d).shape 0 0 (by simp))).symm ≪≫
    (laurentCechComplex R 0 d).cyclesIsoSc' 0 0 (0 + 1) (by simp) (by simp) ≪≫
    ShortComplex.moduleCatCyclesIso _ ≪≫
    LinearEquiv.toModuleIso
      ((LinearEquiv.ofEq _ (LinearMap.ker (laurentCechDiffRestrict R 0 d 0)) (by
            simp only [HomologicalComplex.shortComplexFunctor'_obj_g, laurentCechComplex_d]
            rfl)).trans
        ((LinearEquiv.ofEq (LinearMap.ker (laurentCechDiffRestrict R 0 d 0)) ⊤ (by
              rw [show laurentCechDiffRestrict R 0 d 0 = 0 from
                laurentCechDiffRestrict_eq_zero_of_lt (by omega), LinearMap.ker_zero])).trans
          (Submodule.topEquiv.trans (zeroDimCochainEquiv R d))))

/-- **`H⁰(ℙ⁰_R, 𝒪(d))` is the degree-`d` part of `R[T₀][1/T₀]`**, an `R`-module free of rank one.
-/
def twistCohomologyIsoChartUnivZeroDim (R : Type u) [CommRing R] (d : ℤ) :
    twistCohomology R 0 d 0 ≅
      ModuleCat.of R (twistChart R 0 d (Set.univ : Set (Fin (0 + 1)))) :=
  twistCohomologyIsoLaurentHomology R 0 d 0 ≪≫ zeroDimHomologyIso R d

end ZeroDim

/-! ### The top degree, in the monomial form -/

/-- **`Hⁿ(ℙⁿ_R, 𝒪(d))` is the degree-`d` part of `(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]`** for
`n = m + 1 ≥ 1` and every integer `d`: the top row of [Stacks, Tag 01XU] read back through the
residue pairing. -/
def twistCohomologyIsoNegativeSucc (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) :
    twistCohomology R (m + 1) d (m + 1) ≅ ModuleCat.of R (negativeTwistPart R (m + 1) d) :=
  (serreTwistCohomology R m d).degreeTop ≪≫
    (LinearEquiv.toModuleIso (topDualEquiv R (m + 1) d)).symm

/-! ### The three rows of Tag 01XT -/

/-- **[Stacks, Tag 01XT], the degree-zero row.** For `d ≥ 0` the module `H⁰(ℙⁿ_R, 𝒪(d))` is the
module of degree-`d` homogeneous polynomials in `T₀, …, Tₙ`, for every `n ≥ 0`. -/
@[stacks 01XT "degree zero, nonnegative twist"]
def twistCohomologyIsoHomogeneous (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : 0 ≤ d) :
    twistCohomology R n d 0 ≅
      ModuleCat.of R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat) :=
  match n with
  | 0 => twistCohomologyIsoChartUnivZeroDim R d ≪≫
      LinearEquiv.toModuleIso
        ((LinearEquiv.ofEq _ _ (twistChart_univ_eq_empty_zeroDim R hd)).trans
          (twistChartEmptyLinearEquiv (R := R) 0 hd))
  | m + 1 => (serreTwistCohomology R m d).degreeZeroPolynomial hd

/-- **[Stacks, Tag 01XT], the top-degree row.** For `d < 0` the module `Hⁿ(ℙⁿ_R, 𝒪(d))` is the
degree-`d` part of `(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]`, the free `R`-module on the degree-`d` Laurent
monomials with every exponent negative, for every `n ≥ 0`. -/
@[stacks 01XT "top degree, negative twist"]
def twistCohomologyIsoNegative (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (hd : d < 0) :
    twistCohomology R n d n ≅ ModuleCat.of R (negativeTwistPart R n d) :=
  match n with
  | 0 => twistCohomologyIsoChartUnivZeroDim R d ≪≫
      LinearEquiv.toModuleIso
        (LinearEquiv.ofEq _ _ (twistChart_univ_eq_negativeTwistPart_zeroDim R hd))
  | m + 1 => twistCohomologyIsoNegativeSucc R m d

/-- **[Stacks, Tag 01XT], the vanishing row.** Outside the two cases `q = 0, d ≥ 0` and
`q = n, d < 0` the module `H^q(ℙⁿ_R, 𝒪(d))` is zero, for every `n ≥ 0`. -/
@[stacks 01XT "all other cases"]
theorem isZero_twistCohomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ)
    (hq : ¬ ((q = 0 ∧ 0 ≤ d) ∨ (q = n ∧ d < 0))) :
    IsZero (twistCohomology R n d q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have hdneg : d < 0 := by
      by_contra h
      exact hq (Or.inl ⟨rfl, not_lt.1 h⟩)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd (Or.inr ⟨rfl, hdneg⟩) hq
      · omega⟩
    refine ((serreTwistCohomology R m d).degreeZero).isZero_iff.2 ?_
    have : Subsingleton (twistChart R (m + 1) d (∅ : Set (Fin (m + 1 + 1)))) := by
      rw [twistChart_eq_bot_of_neg (R := R) (m + 1) hdneg]
      infer_instance
    exact ModuleCat.isZero_of_subsingleton _
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    by_cases hpn : p + 1 = n
    · subst hpn
      have hdnn : 0 ≤ d := by
        by_contra h
        exact hq (Or.inr ⟨rfl, not_le.1 h⟩)
      refine (twistCohomologyIsoNegativeSucc R p d).isZero_iff.2 ?_
      have : Subsingleton (negativeTwistPart R (p + 1) d) := by
        rw [negativeTwistPart_eq_bot_of_nonneg R (p + 1) d hdnn]
        infer_instance
      exact ModuleCat.isZero_of_subsingleton _
    · exact (twistCohomologyIsoLaurentHomology R n d (p + 1)).isZero_iff.2
        (isZero_homology_laurentCechComplex hpn)

/-- The three rows of the displayed equation of [Stacks, Tag 01XT] for `ℙⁿ_R`, `n ≥ 0`: the
degree-zero cohomology of a nonnegative twist, the top-degree cohomology of a negative twist, and
the vanishing of everything else. -/
structure TwistCohomologyMonomial (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) where
  /-- `H⁰(ℙⁿ_R, 𝒪(d))` is `(R[T₀, …, Tₙ])_d` for `d ≥ 0`. -/
  degreeZero : 0 ≤ d → (twistCohomology R n d 0 ≅
    ModuleCat.of R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat))
  /-- `Hⁿ(ℙⁿ_R, 𝒪(d))` is `((T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹])_d` for `d < 0`. -/
  degreeTop : d < 0 → (twistCohomology R n d n ≅ ModuleCat.of R (negativeTwistPart R n d))
  /-- `H^q(ℙⁿ_R, 𝒪(d)) = 0` in every other case. -/
  vanishing : ∀ q : ℕ, ¬ ((q = 0 ∧ 0 ≤ d) ∨ (q = n ∧ d < 0)) →
    IsZero (twistCohomology R n d q)

/-- **The cohomology of the twists of the structure sheaf on projective space.** For every
commutative ring `R`, every `n ≥ 0` and every integer `d`, `H^q(ℙⁿ_R, 𝒪(d))` is the degree-`d`
part of `R[T₀, …, Tₙ]` when `q = 0` and `d ≥ 0`, is the degree-`d` part of
`(T₀ ⋯ Tₙ)⁻¹ R[T₀⁻¹, …, Tₙ⁻¹]` when `q = n` and `d < 0`, and is zero otherwise, as
`R`-modules. -/
@[stacks 01XT,
  ega "III 2.1.13" "more general",
  ega "III 2.1.14" "more general",
  sga "7 XIX 1.2" "special case"]
def twistCohomologyMonomial (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    TwistCohomologyMonomial R n d where
  degreeZero hd := twistCohomologyIsoHomogeneous R n d hd
  degreeTop hd := twistCohomologyIsoNegative R n d hd
  vanishing q hq := isZero_twistCohomology R n d q hq

/-! ### Finiteness -/

/-- **The cohomology of a twist on projective space is a finite module.** For every commutative
ring `R`, every `n ≥ 0`, every integer `d` and every `q`, the `R`-module `H^q(ℙⁿ_R, 𝒪(d))` is
finite: it is free on a finite set of monomials in the two non-vanishing cases of
[Stacks, Tag 01XT] and zero in the others. -/
@[ega "III 2.1.14" "partial"]
theorem moduleFinite_twistCohomology (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (q : ℕ) :
    Module.Finite R (twistCohomology R n d q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · cases n with
    | zero => exact Module.Finite.equiv (twistCohomologyIsoChartUnivZeroDim R d).symm.toLinearEquiv
    | succ m =>
      exact Module.Finite.equiv ((serreTwistCohomology R m d).degreeZero).symm.toLinearEquiv
  · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    by_cases hpn : p + 1 = n
    · subst hpn
      exact Module.Finite.equiv (twistCohomologyIsoNegativeSucc R p d).symm.toLinearEquiv
    · exact moduleFinite_of_isZero (isZero_twistCohomology R n d (p + 1) (by omega))

end Stacks.ProjectiveSpace.Cohomology

end
