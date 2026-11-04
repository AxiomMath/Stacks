module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriple
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksCore.Tactic.StacksAttribute

/-!
# The SGA2 injectivity of `Pic(U) → Pic(U₀)` for a quotient of a regular ring

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪`. Assume `A` is a quotient of a regular ring,
that `f` is a nonzerodivisor, and that

* (a) `depth(A_𝔭) ≥ 2` for every prime `𝔭` with `dim(A/𝔭) = 1`, and
* (b) `depth(A/fA) ≥ 3`, equivalently `depth(A) ≥ 4`.

Let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. Then `Pic(U) → Pic(U₀)`
is injective. This is [Stacks, Tag 0FIX].

The remark Tag 0FIX deduces this from Kollár's proposition [Stacks, Tag 0F2B], because

1. a quotient of a regular ring has a dualizing complex ([Stacks, Tag 0AWX] and
   [Stacks, Tag 0A7K]), and
2. if `depth(A) ≥ 4` then `depth(A_𝔭) ≥ 2` for every prime `𝔭` with `dim(A/𝔭) = 2`
   ([Stacks, Tag 0FCC]).

This file proves these two items, the equivalence of the two forms of hypothesis (b), the
footnote that (a) follows from (b), and the deduction of the lemma from [Stacks, Tag 0F2B].

## Main definitions

* `Stacks.Algebraization.puncturedClosedFibreRestriction`: the morphism `U₀ ⟶ U`.
* `Stacks.Algebraization.PicRestrictionInjective`: injectivity of `Pic(U) → Pic(U₀)`, the
  conclusion shared by Tag 0F2B and Tag 0FIX.
* `Stacks.Algebraization.TwoLeDepthLocalization`: `depth(A_𝔭) ≥ 2`.
* `Stacks.Algebraization.HasDualizingComplexOfRegularQuotient`: the statement of item (1).
* `Stacks.Algebraization.IsKollarPicardInjectivity`: the statement of [Stacks, Tag 0F2B].

## Main results

* `Stacks.Algebraization.hasDualizingComplexOfRegularQuotient`: item (1) -- a Noetherian local
  ring that is a quotient of a regular ring has a dualizing complex.
* `Stacks.Algebraization.twoLeDepthLocalization_of_four_le_depth`: item (2) -- from
  `depth(A) ≥ 4`, every prime with `dim(A/𝔭) ≤ 2` has `depth(A_𝔭) ≥ 2`.
* `Stacks.Algebraization.three_le_depth_quotient_iff_four_le_depth`: the equivalence recorded in
  hypothesis (b).
* `Stacks.Algebraization.twoLeDepthLocalization_of_dim_eq_one`: the footnote -- hypothesis (a)
  follows from hypothesis (b).
* `Stacks.Algebraization.kollarHypotheses_of_regularQuotient`: the hypotheses of the SGA2 lemma
  give the four hypotheses of [Stacks, Tag 0F2B].
* `Stacks.Algebraization.picRestrictionInjective_of_regularQuotient`: the SGA2 lemma from the
  statement of [Stacks, Tag 0F2B].

## Implementation notes

`U` is `Stacks.Divisors.puncturedSpectrum A`, the complement of the closed point, and `U₀` is
`Stacks.Algebraization.puncturedClosedFibre A f`, the part of `Spec(A/fA)` lying over `U`; when
`f ∈ 𝔪` it is the punctured spectrum of `A/fA`. The morphism `U₀ ⟶ U` is
`AlgebraicGeometry.morphismRestrict` of the closed immersion, and injectivity on Picard groups is
`Function.Injective (Stacks.Picard.schemePullbackClass _)`.

`depth(A_𝔭)` is read, as in [Stacks, Tag 0FCC], over an arbitrary ring presenting the
localization rather than over the model `Localization.AtPrime 𝔭`.

## References

* [Stacks Project, Tag 0FIX](https://stacks.math.columbia.edu/tag/0FIX)
* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0FCC](https://stacks.math.columbia.edu/tag/0FCC)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- The morphism `U₀ ⟶ U` from the punctured closed fibre to the punctured spectrum: the
restriction of the closed immersion `Spec(A/fA) ⟶ Spec A` over the punctured spectrum. -/
abbrev puncturedClosedFibreRestriction (A : Type u) [CommRing A] [IsLocalRing A] (f : A) :
    (puncturedClosedFibre A f).toScheme ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)

/-- **`Pic(U) → Pic(U₀)` is injective**, the conclusion shared by [Stacks, Tag 0F2B] and
[Stacks, Tag 0FIX]: the map is pullback of invertible modules along the restriction `U₀ ⟶ U` of
the closed immersion `Spec(A/fA) ⟶ Spec A`. -/
def PicRestrictionInjective (A : Type u) [CommRing A] [IsLocalRing A] (f : A) : Prop :=
  Function.Injective (Stacks.Picard.schemePullbackClass (puncturedClosedFibreRestriction A f))

/-- **`depth(A_𝔭) ≥ 2`.** As in [Stacks, Tag 0FCC], the localization is presented abstractly: the
condition is asked of every ring presenting `A_𝔭`, each of which is uniquely isomorphic to
`Localization.AtPrime 𝔭`, so this is the same condition. -/
def TwoLeDepthLocalization (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime] : Prop :=
  ∀ (Aₚ : Type u) [CommRing Aₚ] [Algebra A Aₚ] [IsLocalization.AtPrime Aₚ p] [IsLocalRing Aₚ],
    2 ≤ Module.depth Aₚ (IsLocalRing.maximalIdeal Aₚ) Aₚ

/-- **A quotient of a regular ring has a dualizing complex**: for every regular ring `R` and
surjection `R →+* A`, the ring `A` has a dualizing complex. -/
def HasDualizingComplexOfRegularQuotient (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularRing R] (π : R →+* A), Function.Surjective π →
    ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K

/-- A Noetherian local ring that is a quotient of a regular ring has a dualizing complex. -/
@[stacks 0FIX "item (1): a Noetherian local ring that is a quotient of a regular ring has a \
dualizing complex"]
theorem hasDualizingComplexOfRegularQuotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : HasDualizingComplexOfRegularQuotient A := by
  intro R _ _ π hπ
  set 𝔭 : Ideal R := Ideal.comap π (IsLocalRing.maximalIdeal A) with hp_def
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (π (y : R)) := by
    rintro ⟨y, hy⟩
    refine IsLocalRing.notMem_maximalIdeal.1 ?_
    simpa [hp_def, Ideal.mem_comap] using hy
  let g : Localization.AtPrime 𝔭 →+* A := IsLocalization.lift hunit
  have hcomp : g.comp (algebraMap R (Localization.AtPrime 𝔭)) = π := IsLocalization.lift_comp hunit
  have hgsurj : Function.Surjective g := by
    intro a
    obtain ⟨r, hr⟩ := hπ a
    exact ⟨algebraMap R (Localization.AtPrime 𝔭) r, by rw [← RingHom.comp_apply, hcomp, hr]⟩
  let _ : Algebra (Localization.AtPrime 𝔭) A := g.toAlgebra
  have hRegLoc : IsRegularLocalRing (Localization.AtPrime 𝔭) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization 𝔭 (Localization.AtPrime 𝔭)
  obtain ⟨K0, hK0⟩ : ∃ K : DerivedCategory (ModuleCat.{u} (Localization.AtPrime 𝔭)),
      Dualizing.IsDualizingComplex K :=
    ⟨_, Dualizing.IsRegularLocalRing.isGorensteinLocalRing (Localization.AtPrime 𝔭)⟩
  have hEss : IsEssentiallyOfFiniteType (Localization.AtPrime 𝔭) A
      (algebraMap (Localization.AtPrime 𝔭) A) :=
    ⟨A, inferInstance, inferInstance,
      Algebra.FiniteType.of_surjective (Algebra.ofId (Localization.AtPrime 𝔭) A) hgsurj,
      IsUnit.submonoid A, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨_hNoeth, L, hL⟩ :=
    Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType hEss K0 hK0
  exact ⟨L, hL⟩

/-- **The statement of [Stacks, Tag 0F2B]** (Kollár). Let `(A, 𝔪)` be a Noetherian local ring
with a dualizing complex and let `f ∈ 𝔪` be a nonzerodivisor with `depth(A/fA) ≥ 2`. Assume every
prime `𝔭` containing `f` with `dim(A/𝔭) = 2` has `depth(A_𝔭) ≥ 2`. Then `Pic(U) → Pic(U₀)` is
injective. -/
def IsKollarPicardInjectivity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (f : A),
    f ∈ IsLocalRing.maximalIdeal A →
    (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
    IsSMulRegular A f →
    2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) →
    (∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
      TwoLeDepthLocalization A p) →
    PicRestrictionInjective A f

/-- Let `A` be a Noetherian local ring. If `depth(A) ≥ 4` and `𝔭` is a prime with
`dim(A/𝔭) ≤ 2` then `depth(A_𝔭) ≥ 2`. -/
@[stacks 0FIX "item (2): for a Noetherian local ring with `depth(A) ≥ 4`, every prime `𝔭` with \
`dim(A/𝔭) = 2` (indeed `≤ 2`) has `depth(A_𝔭) ≥ 2`"]
theorem twoLeDepthLocalization_of_four_le_depth (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hA : 4 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A) (p : Ideal A)
    [p.IsPrime] (hdim : ringKrullDim (A ⧸ p) ≤ 2) :
    TwoLeDepthLocalization A p := by
  intro Aₚ _ _ _ _
  have h0FCC := Module.depth_le_depth_localized_add_ringKrullDim_quotient
    (R := A) A p Aₚ Aₚ (Algebra.linearMap A Aₚ)
  refine (ENat.add_le_add_iff_right (k := 2) (by simp)).1 ?_
  rw [show (2 : ℕ∞) + 2 = 4 by norm_num]
  have hstep : ((4 : ℕ∞) : WithBot ℕ∞) ≤
      ((Module.depth Aₚ (IsLocalRing.maximalIdeal Aₚ) Aₚ + 2 : ℕ∞) : WithBot ℕ∞) := by
    refine le_trans (by exact_mod_cast hA) (le_trans h0FCC ?_)
    rw [WithBot.coe_add]
    exact add_le_add le_rfl (by exact_mod_cast hdim)
  exact_mod_cast hstep

/-- Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor. Then
`n ≤ depth(A/fA)` if and only if `n + 1 ≤ depth(A)`, the depth of `A/fA` being taken over `A`. -/
theorem le_depth_quotient_span_singleton_iff (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A)
    (hf : IsSMulRegular A f) (n : ℕ∞) :
    n ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) ↔
      n + 1 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A := by
  have hspan : (f • (⊤ : Submodule A A)) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  have hbridge : Module.depth A (IsLocalRing.maximalIdeal A) (QuotSMulTop f A) =
      Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) :=
    Module.depth_eq_depth_of_linearEquiv _ (Submodule.quotEquivOfEq _ _ hspan)
  have h090R := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal A) A).1 f hfm hf
  rw [← h090R, hbridge]
  exact (ENat.add_le_add_iff_right (show (1 : ℕ∞) ≠ ⊤ by simp)).symm

/-- Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor. Then
`depth(A/fA) ≥ 3` if and only if `depth(A) ≥ 4`. -/
@[stacks 0FIX "hypothesis (b): for `f ∈ 𝔪` a nonzerodivisor of a Noetherian local ring, \
`depth(A/fA) ≥ 3` is equivalent to `depth(A) ≥ 4`"]
theorem three_le_depth_quotient_iff_four_le_depth (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A)
    (hf : IsSMulRegular A f) :
    3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) ↔
      4 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A :=
  le_depth_quotient_span_singleton_iff A f hfm hf 3

/-- For `f ∈ 𝔪` a nonzerodivisor of a Noetherian local ring, `depth(A/fA) ≥ 3` gives
`depth(A) ≥ 4`. -/
theorem four_le_depth_of_three_le_depth_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) (hf : IsSMulRegular A f)
    (hb : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f})) :
    4 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A :=
  (three_le_depth_quotient_iff_four_le_depth A f hfm hf).1 hb

/-- Let `(A, 𝔪)` be a Noetherian local ring. If `f ∈ 𝔪` is a nonzerodivisor with
`depth(A/fA) ≥ 3`, then every prime `𝔭` with `dim(A/𝔭) = 1` has `depth(A_𝔭) ≥ 2`. -/
@[stacks 0FIX "footnote: (b) implies (a) -- for `f ∈ 𝔪` a nonzerodivisor of a Noetherian local \
ring with `depth(A/fA) ≥ 3`, every prime `𝔭` with `dim(A/𝔭) = 1` has `depth(A_𝔭) ≥ 2`"]
theorem twoLeDepthLocalization_of_dim_eq_one (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) (hf : IsSMulRegular A f)
    (hb : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f})) (p : Ideal A)
    [p.IsPrime] (hdim : ringKrullDim (A ⧸ p) = 1) :
    TwoLeDepthLocalization A p :=
  twoLeDepthLocalization_of_four_le_depth A
    (four_le_depth_of_three_le_depth_quotient A f hfm hf hb) p (by rw [hdim]; norm_num)

/-- The hypotheses of the SGA2 lemma give the four hypotheses of Kollár's proposition
[Stacks, Tag 0F2B]. Let `(A, 𝔪)` be a Noetherian local ring, `f ∈ 𝔪`, and assume `A` is a
quotient of a regular ring `R`, that `f` is a nonzerodivisor and that `depth(A/fA) ≥ 3`. Then

1. `A` has a dualizing complex,
2. `f` is a nonzerodivisor,
3. `depth(A/fA) ≥ 2`, and
4. every prime `𝔭 ∋ f` with `dim(A/𝔭) = 2` has `depth(A_𝔭) ≥ 2`. -/
@[stacks 0FIX "the deduction from 0F2B: the hypotheses of the SGA2 lemma (a Noetherian local \
ring that is a quotient of a regular ring, `f ∈ 𝔪` a nonzerodivisor, `depth(A/fA) ≥ 3`) give \
the four hypotheses of 0F2B -- a dualizing complex by item (1), `f` a nonzerodivisor, \
`depth(A/fA) ≥ 2`, and `depth(A_𝔭) ≥ 2` for every prime `𝔭 ∋ f` with `dim(A/𝔭) = 2` by item (2)"]
theorem kollarHypotheses_of_regularQuotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) (R : Type u) [CommRing R]
    [IsRegularRing R] (π : R →+* A) (hπ : Function.Surjective π) (hf : IsSMulRegular A f)
    (hb : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f})) :
    (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) ∧
      IsSMulRegular A f ∧
      2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}) ∧
      ∀ p : Ideal A, ∀ _ : p.IsPrime, f ∈ p → ringKrullDim (A ⧸ p) = 2 →
        TwoLeDepthLocalization A p := by
  exact ⟨hasDualizingComplexOfRegularQuotient A R π hπ, hf, le_trans (by norm_num) hb,
    fun p _ _ hdim => twoLeDepthLocalization_of_four_le_depth A
      (four_le_depth_of_three_le_depth_quotient A f hfm hf hb) p hdim.le⟩

/-- **The SGA2 lemma from Kollár's proposition.** For `A`, `f`, `R`, `π` as in
[Stacks, Tag 0FIX], the statement `IsKollarPicardInjectivity` of [Stacks, Tag 0F2B] yields the
injectivity of `Pic(U) → Pic(U₀)`. -/
theorem picRestrictionInjective_of_regularQuotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (f : A) (hfm : f ∈ IsLocalRing.maximalIdeal A) (R : Type u) [CommRing R]
    [IsRegularRing R] (π : R →+* A) (hπ : Function.Surjective π) (hf : IsSMulRegular A f)
    (_ha : ∀ p : Ideal A, ∀ _ : p.IsPrime, ringKrullDim (A ⧸ p) = 1 → TwoLeDepthLocalization A p)
    (hb : 3 ≤ Module.depth A (IsLocalRing.maximalIdeal A) (A ⧸ Ideal.span {f}))
    (hKollar : IsKollarPicardInjectivity.{u}) :
    PicRestrictionInjective A f := by
  obtain ⟨hK, hf', h2, h4⟩ := kollarHypotheses_of_regularQuotient A f hfm R π hπ hf hb
  exact hKollar A f hfm hK hf' h2 h4

end Stacks.Algebraization

end
