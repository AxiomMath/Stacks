module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Basic opens of affine space

Let `R` be a commutative ring, let `σ` be a finite index type and let `h` be an element of the
polynomial ring `R[σ]`. A localization of `R[σ]` away from `h` — that is, the basic open
`D(h)` of affine `σ`-space over `R` — is a smooth `R`-algebra: the polynomial ring is formally
smooth and of finite presentation over `R`, inverting one element is again both, and smoothness
of algebras is stable under composition. Consequently the spectrum of such a localization is a
smooth scheme over `Spec R`.

Over a field `k`, when the localization is moreover a domain, its spectrum is a variety over `k`;
and when `k` is infinite the `k`-rational points of `D(h)` are dense.

## Main results

* `AlgebraicGeometry.smooth_mvPolynomial`: the polynomial ring on a finite index type is a
  smooth algebra.
* `AlgebraicGeometry.smooth_of_isLocalization_away_mvPolynomial`: a localization of it away
  from one element is a smooth algebra.
* `AlgebraicGeometry.smooth_Spec_map_algebraMap`: the spectrum of a smooth algebra is smooth
  over the spectrum of the base ring.
* `AlgebraicGeometry.smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial`: the two
  previous results combined — a basic open of affine space is smooth over the base.
* `AlgebraicGeometry.isVariety_Spec_map_algebraMap`: the spectrum of a smooth algebra over a
  field which is a domain is a variety.
* `AlgebraicGeometry.dense_rationalPoints_of_isLocalization_away_mvPolynomial` and
  `AlgebraicGeometry.dense_rationalPoints_Spec_of_isLocalization_away_mvPolynomial`: over an
  infinite field the `k`-rational points of a basic open of affine space are dense, in the
  prime spectrum and in the scheme respectively.

## Implementation notes

The localization is an abstract algebra `A` satisfying `IsLocalization.Away h A`, with the
`R`-algebra structure required to be compatible with the one of the polynomial ring. The index
type `σ` and the localization live in universes independent of that of the base ring for the
algebra-level statements; for the scheme-level ones the base ring and the localization share a
universe, as `AlgebraicGeometry.Spec` requires.

Smoothness of a morphism of schemes is transported from smoothness of the ring map by
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`, the ring-homomorphism property attached to
`AlgebraicGeometry.Smooth` being `RingHom.Smooth`.

A `k`-rational point of the spectrum of a `k`-algebra `A` is recorded as a `k`-algebra
homomorphism `A →ₐ[k] k`; the point of the prime spectrum it names is the kernel, and the
morphism of schemes it names is `Spec` of it, which is a section of the structure morphism.

## References

* [Stacks Project, Tag 00T2](https://stacks.math.columbia.edu/tag/00T2)
* [Stacks Project, Tag 01V4](https://stacks.math.columbia.edu/tag/01V4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry

/-! ### Smoothness of a basic open of affine space -/

/-- **The polynomial ring on a finite index type is a smooth algebra.** -/
@[ega "0 19.10.3" "finitely many variables", ega "0 19.3.3" "Finitely many variables"]
theorem smooth_mvPolynomial (R : Type u) [CommRing R] (σ : Type v) [Finite σ] :
    Algebra.Smooth R (MvPolynomial σ R) :=
  ⟨inferInstance, inferInstance⟩

/-- **A basic open of affine space over `R` is a smooth `R`-algebra**: a localization of the
polynomial ring on a finite index type away from one element is smooth over `R`. -/
theorem smooth_of_isLocalization_away_mvPolynomial (R : Type u) [CommRing R] {σ : Type v}
    [Finite σ] (h : MvPolynomial σ R) (A : Type w) [CommRing A]
    [Algebra (MvPolynomial σ R) A] [IsLocalization.Away h A] [Algebra R A]
    [IsScalarTower R (MvPolynomial σ R) A] :
    Algebra.Smooth R A :=
  have : Algebra.Smooth R (MvPolynomial σ R) := smooth_mvPolynomial R σ
  have : Algebra.Smooth (MvPolynomial σ R) A := .of_isLocalization_Away h
  .comp R (MvPolynomial σ R) A

/-- **The spectrum of a smooth algebra is smooth over the spectrum of the base ring.** -/
theorem smooth_Spec_map_algebraMap (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] [Algebra.Smooth R A] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 ‹_›

/-- **A basic open of affine space over `R` is smooth over `Spec R`.** -/
@[sga "3 XVII 6.4" "partial"]
theorem smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial (R : Type u) [CommRing R]
    {σ : Type v} [Finite σ] (h : MvPolynomial σ R) (A : Type u) [CommRing A]
    [Algebra (MvPolynomial σ R) A] [IsLocalization.Away h A] [Algebra R A]
    [IsScalarTower R (MvPolynomial σ R) A] :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  have : Algebra.Smooth R A := smooth_of_isLocalization_away_mvPolynomial R h A
  smooth_Spec_map_algebraMap R A

/-! ### Basic opens of affine space over a field -/

/-- **The spectrum of a smooth algebra over a field which is a domain is a variety.** -/
theorem isVariety_Spec_map_algebraMap (k : Type u) [Field k] (A : Type u) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.Smooth k A] :
    IsVariety k (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    smooth_Spec_map_algebraMap k A
  { }

/-- **The `k`-rational points of a basic open of affine space over an infinite field are dense
in its prime spectrum.** A `k`-rational point is recorded as a `k`-algebra homomorphism to `k`,
and the point of the prime spectrum it names is its kernel. -/
theorem dense_rationalPoints_of_isLocalization_away_mvPolynomial (k : Type u) [Field k]
    [Infinite k] {σ : Type v} [Finite σ] {h : MvPolynomial σ k} (hh : h ≠ 0) (A : Type w)
    [CommRing A] [Algebra (MvPolynomial σ k) A] [IsLocalization.Away h A] [Algebra k A]
    [IsScalarTower k (MvPolynomial σ k) A] :
    Dense {x : PrimeSpectrum A | ∃ φ : A →ₐ[k] k, RingHom.ker (φ : A →+* k) = x.asIdeal} := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨y, hy⟩
  obtain ⟨_, ⟨a, rfl⟩, hyV, hVO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy hO
  have hay : a ∉ y.asIdeal := hyV
  have ha : a ≠ 0 := fun hz ↦ hay (hz ▸ Submodule.zero_mem _)
  obtain ⟨⟨p, s⟩, hps⟩ := IsLocalization.surj (Submonoid.powers h) a
  have hps' : a * algebraMap (MvPolynomial σ k) A (s : MvPolynomial σ k) =
      algebraMap (MvPolynomial σ k) A p := hps
  have hsunit : IsUnit (algebraMap (MvPolynomial σ k) A (s : MvPolynomial σ k)) := by
    obtain ⟨n, hn⟩ := s.2
    rw [← hn, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit h).pow n
  have hp : p ≠ 0 := by
    intro hz
    refine ha (hsunit.mul_left_eq_zero.mp ?_)
    rw [hps', hz, map_zero]
  obtain ⟨x, hx⟩ : ∃ x : σ → k, MvPolynomial.eval x (p * h) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact mul_ne_zero hp hh (MvPolynomial.funext fun x ↦ by rw [hcon x, map_zero])
  rw [map_mul] at hx
  have hxp : MvPolynomial.eval x p ≠ 0 := fun hz ↦ hx (by rw [hz, zero_mul])
  have hxh : IsUnit ((MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] k) h) :=
    isUnit_iff_ne_zero.2 fun hz ↦ hx (by rw [show MvPolynomial.eval x h = 0 from hz, mul_zero])
  set φ : A →ₐ[k] k := IsLocalization.Away.liftAlgHom h hxh
  have hφalg : ∀ q : MvPolynomial σ k,
      φ (algebraMap (MvPolynomial σ k) A q) = MvPolynomial.eval x q := fun q ↦
    IsLocalization.Away.lift_eq h hxh q
  have hφa : φ a ≠ 0 := fun hz ↦ hxp <| by
    have hcongr := congrArg φ hps'
    rwa [map_mul, hz, zero_mul, hφalg, eq_comm] at hcongr
  exact ⟨⟨RingHom.ker (φ : A →+* k), RingHom.ker_isPrime _⟩, hVO fun hmem ↦ hφa hmem, φ, rfl⟩

/-- **The `k`-rational points of a basic open of affine space over an infinite field are dense
in it as a scheme.** A `k`-rational point is a section of the structure morphism. -/
theorem dense_rationalPoints_Spec_of_isLocalization_away_mvPolynomial (k : Type u) [Field k]
    [Infinite k] {σ : Type v} [Finite σ] {h : MvPolynomial σ k} (hh : h ≠ 0) (A : Type u)
    [CommRing A] [Algebra (MvPolynomial σ k) A] [IsLocalization.Away h A] [Algebra k A]
    [IsScalarTower k (MvPolynomial σ k) A] :
    Dense {x : Spec (CommRingCat.of A) |
      ∃ s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        s ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ ∧ x ∈ Set.range s.base} := by
  refine (dense_rationalPoints_of_isLocalization_away_mvPolynomial k hh A).mono ?_
  rintro x ⟨φ, hφ⟩
  refine ⟨Spec.map (CommRingCat.ofHom (φ : A →+* k)), ?_, (⊥ : PrimeSpectrum k), ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ.comp_algebraMap, CommRingCat.ofHom_id,
      Spec.map_id]
  · exact PrimeSpectrum.ext hφ

end AlgebraicGeometry

end
