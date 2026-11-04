module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeWeakNormalizationAway.Criterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RelativeWeakNormalization

/-!
# Localizing the base preserves universal homeomorphy of a subalgebra

Let `A → B` be an algebra, `r` an element of `A`, and let `Af` and `Bf` be the localizations of
`A` and of `B` away from `r`. If a subalgebra `C` of `B` has universally homeomorphic spectrum
over `A`, then the subalgebra of `Bf` generated over `Af` by the image of `C` has universally
homeomorphic spectrum over `Af`. Applied to the relative weak normalization of
[Stacks, Tag 0H3J](https://stacks.math.columbia.edu/tag/0H3J), this is one of the two inclusions
of [Stacks, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K): the image of `B'` in `Bf` lies
in the relative weak normalization of `Af` in `Bf`.

The argument is not the base change of spectra that the source suggests. Each of the three
ring-theoretic properties of
`AlgebraicGeometry.universalHomeomorphism_specMap_of_isIntegral` passes to the generated
subalgebra by itself: integrality because the generators are integral, nilpotency of the kernel
by clearing one denominator, and uniqueness of field-valued extensions because a field-valued
map on the generated subalgebra restricts to one on `C`.

## Main definitions

* `AlgebraicGeometry.subalgebraToAdjoinImage` is the map from a subalgebra of `B` to the
  subalgebra of `Bf` generated over `Af` by its image.

## Main results

* `AlgebraicGeometry.ker_algebraMap_localization_le_nilradical`: nilpotency of the kernel of a
  structure map passes to localizations of the base and of the target.
* `AlgebraicGeometry.universalHomeomorphism_specMap_adjoin_image`: universal homeomorphy of the
  spectrum of a subalgebra passes to the generated subalgebra of the localization.
* `AlgebraicGeometry.algebraMap_mem_relativeWeakNormalization`: the image of the relative weak
  normalization lies in the relative weak normalization over the localized base.

## Implementation notes

No abbreviation is introduced for the generated subalgebra. It is written out as an
`Algebra.adjoin` at every occurrence, because an opaque definition wrapping it would hide the
`Algebra.adjoin` from `Algebra.IsIntegral.adjoin` and from `Algebra.adjoin_induction`, which are
the two tools the proofs run on.

## References

* [Stacks Project, Tag 0H3K](https://stacks.math.columbia.edu/tag/0H3K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A B Af Bf : Type u} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bf]
  [Algebra A B] [Algebra A Af] [Algebra Af Bf] [Algebra A Bf] [Algebra B Bf]
  [IsScalarTower A B Bf] [IsScalarTower A Af Bf]

/-- The two ways of mapping `A` into `Bf`, through `B` and through `Af`, agree. -/
private theorem algebraMap_algebraMap_eq (a : A) :
    algebraMap B Bf (algebraMap A B a) = algebraMap Af Bf (algebraMap A Af a) :=
  (IsScalarTower.algebraMap_apply A B Bf a).symm.trans (IsScalarTower.algebraMap_apply A Af Bf a)

/-- If the kernel of a structure map consists of nilpotents, then so does the kernel of the
structure map obtained by localizing the base and the target away from an element of the
base. -/
theorem ker_algebraMap_localization_le_nilradical (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hker : RingHom.ker (algebraMap A B) ≤ nilradical A) :
    RingHom.ker (algebraMap Af Bf) ≤ nilradical Af := by
  intro x hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) x
  obtain ⟨m, hm⟩ := s.2
  have hsm : (s : A) = r ^ m := hm.symm
  have hs' : x * algebraMap A Af r ^ m = algebraMap A Af a := by
    rw [← map_pow, ← hsm]
    exact hs
  have ha : algebraMap B Bf (algebraMap A B a) = 0 := by
    rw [algebraMap_algebraMap_eq (Af := Af), ← hs', map_mul, RingHom.mem_ker.mp hx, zero_mul]
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A B r)) Bf (algebraMap A B a)).mp ha
  obtain ⟨k, hk⟩ := t.2
  have hnil : algebraMap A B (r ^ k * a) = 0 := by
    rw [map_mul, map_pow, show algebraMap A B r ^ k = (t : B) from hk]
    exact ht
  obtain ⟨j, hj⟩ := hker (RingHom.mem_ker.mpr hnil)
  have hj0 : (r ^ k * a) ^ j = 0 := by simpa using hj
  have hunit : IsUnit (algebraMap A Af r) :=
    IsLocalization.map_units Af (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)
  have h1 : x ^ j * algebraMap A Af r ^ (m * j) = algebraMap A Af (a ^ j) := by
    rw [pow_mul, ← mul_pow, hs', ← map_pow]
  have key : x ^ j * algebraMap A Af r ^ (m * j + k * j) = 0 :=
    calc x ^ j * algebraMap A Af r ^ (m * j + k * j)
        = x ^ j * algebraMap A Af r ^ (m * j) * algebraMap A Af r ^ (k * j) := by
          rw [pow_add, mul_assoc]
      _ = algebraMap A Af ((r ^ k * a) ^ j) := by
          rw [h1, ← map_pow, ← map_mul]
          congr 1
          ring
      _ = 0 := by rw [hj0, map_zero]
  exact ⟨j, (IsUnit.mul_left_eq_zero (hunit.pow (m * j + k * j))).mp key⟩

variable (Af Bf) in
/-- The map from a subalgebra of `B` into the subalgebra of a localization `Bf` of `B` generated
over the corresponding localization `Af` of the base by its image. -/
def subalgebraToAdjoinImage (C : Subalgebra A B) :
    C →+* Algebra.adjoin Af (algebraMap B Bf '' (C : Set B)) where
  toFun c := ⟨algebraMap B Bf (c : B), Algebra.subset_adjoin ⟨(c : B), c.2, rfl⟩⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

omit [Algebra A Af] [Algebra A Bf] [IsScalarTower A B Bf] [IsScalarTower A Af Bf] in
/-- The image of `c` under `subalgebraToAdjoinImage`, viewed in `Bf`, is the image of `c` under
`algebraMap B Bf`. -/
@[simp]
theorem coe_subalgebraToAdjoinImage (C : Subalgebra A B) (c : C) :
    (subalgebraToAdjoinImage Af Bf C c : Bf) = algebraMap B Bf (c : B) :=
  rfl

/-- The map into the generated subalgebra is a map of algebras over the base. -/
theorem subalgebraToAdjoinImage_algebraMap (C : Subalgebra A B) (a : A) :
    subalgebraToAdjoinImage Af Bf C (algebraMap A C a) =
      algebraMap Af (Algebra.adjoin Af (algebraMap B Bf '' (C : Set B)))
        (algebraMap A Af a) := by
  apply Subtype.ext
  rw [coe_subalgebraToAdjoinImage, show ((algebraMap A C a : C) : B) = algebraMap A B a from rfl,
    algebraMap_algebraMap_eq (Af := Af)]
  rfl

/-- Universal homeomorphy of the spectrum of a subalgebra over the base passes to the subalgebra
generated by its image over a localization of the base. -/
theorem universalHomeomorphism_specMap_adjoin_image (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hker : RingHom.ker (algebraMap A B) ≤ nilradical A) (C : Subalgebra A B)
    (hC : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Af
      (Algebra.adjoin Af (algebraMap B Bf '' (C : Set B))))).op) := by
  have hintC : Algebra.IsIntegral A C :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.SpecMap_iff.mp
      ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp hC).1)
  have hint : Algebra.IsIntegral Af
      (Algebra.adjoin Af (algebraMap B Bf '' (C : Set B))) := by
    apply Algebra.IsIntegral.adjoin
    rintro x ⟨y, hy, rfl⟩
    have h1 : _root_.IsIntegral A y := (hintC.isIntegral (⟨y, hy⟩ : C)).map C.val
    exact (h1.map (IsScalarTower.toAlgHom A B Bf)).tower_top
  refine universalHomeomorphism_specMap_of_isIntegral
    (ker_algebraMap_subalgebra_le_nilradical _
      (ker_algebraMap_localization_le_nilradical (B := B) r hker)) ?_
  intro K _ φ ψ hcomp
  have hbase : ∀ a : Af,
      φ (algebraMap Af (Algebra.adjoin Af (algebraMap B Bf '' (C : Set B))) a) =
        ψ (algebraMap Af (Algebra.adjoin Af (algebraMap B Bf '' (C : Set B))) a) :=
    fun a => congrArg (fun q : Af →+* K => q a) hcomp
  have hΦΨ : φ.comp (subalgebraToAdjoinImage Af Bf C) =
      ψ.comp (subalgebraToAdjoinImage Af Bf C) := by
    refine ringHom_eq_of_universalHomeomorphism (algebraMap A C) hC _ _ fun a => ?_
    simpa only [RingHom.comp_apply, subalgebraToAdjoinImage_algebraMap] using
      hbase (algebraMap A Af a)
  apply RingHom.ext
  rintro ⟨w, hw⟩
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg (fun q : C →+* K => q ⟨y, hy⟩) hΦΨ
  | algebraMap a => exact hbase a
  | add x y hx hy ihx ihy =>
    change φ (⟨x, hx⟩ + ⟨y, hy⟩) = ψ (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
    change φ (⟨x, hx⟩ * ⟨y, hy⟩) = ψ (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

/-- The image of the relative weak normalization of `A` in `B` under a localization away from an
element of `A` lies in the relative weak normalization of the localized base in the localized
target. This is one of the two inclusions of Stacks 0H3K. -/
theorem algebraMap_mem_relativeWeakNormalization (r : A) [IsLocalization.Away r Af]
    [IsLocalization.Away (algebraMap A B r) Bf]
    (hdom : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op))
    (b : relativeWeakNormalization A B) :
    algebraMap B Bf (b : B) ∈ relativeWeakNormalization Af Bf := by
  have hker := isDominant_specMap_iff_ker_le_nilradical.mp hdom
  have hdomf : IsDominant (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Af Bf)).op) :=
    isDominant_specMap_iff_ker_le_nilradical.mpr
      (ker_algebraMap_localization_le_nilradical (B := B) r hker)
  have hUH := universalHomeomorphism_specMap_adjoin_image (Af := Af) (Bf := Bf) r hker
    (relativeWeakNormalization A B) (relativeWeakNormalization_isUniversalHomeomorphism A B hdom)
  have hle := range_le_relativeWeakNormalization Af Bf
    (Algebra.adjoin Af (algebraMap B Bf '' (relativeWeakNormalization A B : Set B)))
    (Algebra.adjoin Af (algebraMap B Bf '' (relativeWeakNormalization A B : Set B))).val
    hdomf hUH
  rw [Subalgebra.range_val] at hle
  exact hle (Algebra.subset_adjoin ⟨(b : B), b.2, rfl⟩)

end AlgebraicGeometry

end
