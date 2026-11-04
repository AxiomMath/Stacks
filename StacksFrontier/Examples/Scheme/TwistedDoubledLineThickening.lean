module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.SpanOverBase
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardTorsionGeneral
public import StacksFrontier.Examples.Scheme.TwistedDoubledLineUnits

/-!
# The twisted doubled line, as a thickening of schemes

This file assembles the rings and the gluing twist of
`StacksFrontier/Examples/Scheme/TwistedDoubledLineUnits.lean` into an actual thickening of schemes,
and deduces from them that [Stacks, Tag 0C6S] is false as stated.

Work over `ℚ` and write `R = ℚ[t, t⁻¹]`, `A = R[x]`, `B = R[x, x⁻¹]`, `A' = A[ε]`, `B' = B[ε]`
with `ε² = 0`.  The scheme `X` is the affine line over `R` with its origin doubled: two copies of
`Spec A` glued along `Spec B` by the identity.  The scheme `X'` is glued from two copies of
`Spec A'` along `Spec B'`, but by the twist `b₀ + ε b₁ ↦ b₀ + ε (b₁ + x⁻¹ (t ∂/∂t) b₀)` rather
than by the identity.  Reduction modulo `ε` glues to a morphism `i : X ⟶ X'`, which is a
thickening because over each of the two charts of `X'` it is the closed immersion
`Spec A ⟶ Spec A'`, which is surjective.  Two is invertible on `X`, coming from the unit `2`
of `R`.

The invertible global function `t` on `X` is not a square times the restriction of an invertible
global function on `X'`.  That is the arithmetic already proved in
`Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_fst_of_twist_eq`; what this file adds is
the identification of its hypothesis `twist c₀ = c₁` with the gluing condition satisfied by the
two chart restrictions of a global function on `X'`.  So
`Stacks.Thickenings.GlobalUnitsPowerLift i 2` fails, and by
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff` — which proves that condition
equivalent to the tag's conclusion — the bijection `Pic(X')[2] → Pic(X)[2]` the tag asserts
fails as well.

## Main definitions

* `Stacks.Examples.TwistedDoubledLine.doubledLine`: **the scheme `X`**, the affine line over
  `ℚ[t, t⁻¹]` with its origin doubled.
* `Stacks.Examples.TwistedDoubledLine.twistedThickening`: **the scheme `X'`**, glued from two
  copies of `Spec A'` along `Spec B'` by the twist.
* `Stacks.Examples.TwistedDoubledLine.thickeningHom`: **the morphism `i : X ⟶ X'`**, glued from
  reduction modulo `ε` on the two charts.
* `Stacks.Examples.TwistedDoubledLine.toBaseHom`: the structure morphism `X ⟶ Spec R`, which is
  where the invertible global function `t` on `X` comes from.
* `Stacks.Examples.TwistedDoubledLine.resChart`, `Stacks.Examples.TwistedDoubledLine.resDual₁`
  and `Stacks.Examples.TwistedDoubledLine.resDual₂`: restriction of a global function to a
  chart, read in the chart ring.

## Main results

* `Stacks.Examples.TwistedDoubledLine.isLocalization_dualOverlap`: `B'` is the localisation of
  `A'` away from `x`, so that `Spec B' ⟶ Spec A'` is an open immersion and the gluing of the
  thickening makes sense.
* `Stacks.Examples.TwistedDoubledLine.isThickening_thickeningHom`: `i` is a thickening.
* `Stacks.Examples.TwistedDoubledLine.isUnit_two_doubledLine`: two is invertible on `X`.
* `Stacks.Examples.TwistedDoubledLine.twist_dualToOverlap_resDual₁`: the gluing condition on a
  global function of `X'`, in the form the arithmetic of the previous file consumes.
* `Stacks.Examples.TwistedDoubledLine.not_globalUnitsPowerLift`:
  `Stacks.Thickenings.GlobalUnitsPowerLift i 2` fails.
* `Stacks.Examples.TwistedDoubledLine.not_bijOn_schemePullbackClass_zsmulTorsion`: restriction
  is not a bijection `Pic(X')[2] → Pic(X)[2]`.
* `Stacks.Examples.TwistedDoubledLine.not_forall_bijOn_schemePullbackClass_zsmulTorsion`:
  **the refutation of [Stacks, Tag 0C6S] as stated**, the negation of the tag's own universally
  quantified assertion.  The source has not been corrected, so nothing here carries the tag.

## Implementation notes

The two gluings are `AlgebraicGeometry.SpanGlue.glued`, the colimit of a span of open immersions,
rather than `AlgebraicGeometry.Scheme.GlueData`: with that presentation the compatibility of the
two charts is functoriality of the colimit cocone, and — which is what matters here —
`AlgebraicGeometry.SpanGlue.isPullback_ι₁_desc` says that each chart of the glued source is
exactly the part of it lying over the corresponding chart of the glued target.  That is the
input `AlgebraicGeometry.IsZariskiLocalAtTarget` needs, for
`AlgebraicGeometry.IsClosedImmersion` and for `AlgebraicGeometry.Surjective`, to conclude that
`i` is a thickening from the single affine statement that `Spec A ⟶ Spec A'` is one; it is
packaged as `Stacks.Examples.TwistedDoubledLine.property_thickeningHom_of_chartRed`.

The twist enters only through the first chart: the span presenting `X'` is
`Spec A' ⟵ Spec B' ⟶ Spec A'` whose first leg is the localisation precomposed with the
automorphism of `Spec B'` given by the twist, and whose second leg is the localisation itself.
Which leg carries it is immaterial, but with this choice the gluing condition on a global
section of `X'` reads `twist c₀ = c₁` in the orientation of
`Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_fst_of_twist_eq`.

That `Spec B' ⟶ Spec A'` is an open immersion is the statement that `B'` is the localisation of
`A'` away from `x`, proved here from scratch: a single power of `x` clears the poles of both
components of an element of `B'`, and `A' ⟶ B'` is injective because `A ⟶ B` is.  Mathlib has
localisations of `TrivSqZeroExt` in neither direction.

Surjectivity of `Spec A ⟶ Spec A'` is
`Stacks.Examples.TwistedDoubledLine.isNilpotent_of_fst_eq_zero` together with
`Stacks.Examples.TwistedDoubledLine.surjective_comap_of_ker_isNilpotent`: the image of the
spectrum of a surjective ring map is the zero locus of its kernel, which is everything when that
kernel is nil.

Everything lives in `Scheme.{0}`, the counterexample being over `ℚ`; the tag's assertion is
therefore already false for schemes whose rings are in `Type`.

## References

* [Stacks Project, Tag 0C6S](https://stacks.math.columbia.edu/tag/0C6S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Polynomial LaurentPolynomial TopologicalSpace
open Stacks.Thickenings (IsThickening GlobalUnitsPowerLift)
open Stacks.Picard (zsmulTorsion ofScheme schemePullbackClass)

universe u

namespace Stacks.Examples.TwistedDoubledLine

/-! ### General statements -/

/-- Reduction modulo `ε`, as a ring homomorphism `R[ε] →+* R`. -/
def dualFst (R : Type*) [CommRing R] : DualNumber R →+* R where
  toFun := TrivSqZeroExt.fst
  map_one' := TrivSqZeroExt.fst_one
  map_mul' := TrivSqZeroExt.fst_mul
  map_zero' := TrivSqZeroExt.fst_zero
  map_add' := TrivSqZeroExt.fst_add

/-- Reduction modulo `ε` is the constant term. -/
@[simp] theorem dualFst_apply {R : Type*} [CommRing R] (z : DualNumber R) :
    dualFst R z = z.fst := rfl

/-- The dual number with given constant and `ε`-component. -/
def dualMk {R : Type*} [CommRing R] (a b : R) : DualNumber R := (a, b)

/-- The constant term of a dual number built from its two components. -/
@[simp] theorem dualMk_fst {R : Type*} [CommRing R] (a b : R) :
    TrivSqZeroExt.fst (dualMk a b) = a := rfl

/-- The `ε`-component of a dual number built from its two components. -/
@[simp] theorem dualMk_snd {R : Type*} [CommRing R] (a b : R) :
    TrivSqZeroExt.snd (dualMk a b) = b := rfl

/-- A dual number with vanishing constant term is nilpotent: it squares to zero. -/
theorem isNilpotent_of_fst_eq_zero {R : Type*} [CommRing R] {z : DualNumber R}
    (hz : z.fst = 0) : IsNilpotent z := by
  refine ⟨2, ?_⟩
  rw [pow_two]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, hz, mul_zero, TrivSqZeroExt.fst_zero]
  · rw [DualNumber.snd_mul, hz, zero_mul, mul_zero, add_zero, TrivSqZeroExt.snd_zero]

/-- The spectrum of a surjective ring map whose kernel consists of nilpotents is surjective:
its image is the zero locus of the kernel, which is everything. -/
theorem surjective_comap_of_ker_isNilpotent {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : ∀ x, φ x = 0 → IsNilpotent x) :
    Function.Surjective (PrimeSpectrum.comap φ) := by
  rw [← Set.range_eq_univ, range_comap_of_surjective _ φ hφ,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  exact hker x hx

/-- The preimage of a basic open under `Spec` of a ring map is the basic open of the image. -/
theorem preimage_basicOpen_specMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (r : R) :
    Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen r =
      PrimeSpectrum.basicOpen (φ r) :=
  rfl

/-- `Stacks.Thickenings.GlobalUnitsPowerLift` for `n = 2`, read on elements: every invertible
global function on `X` is a square times the restriction of an invertible global function on
`X'`. -/
theorem exists_sq_mul_appTop_of_globalUnitsPowerLift {X X' : Scheme.{u}} (i : X ⟶ X')
    (h : GlobalUnitsPowerLift i 2) (u : Γ(X, ⊤)ˣ) :
    ∃ (a : Γ(X, ⊤)) (b : Γ(X', ⊤)), (u : Γ(X, ⊤)) = a ^ 2 * i.appTop b := by
  obtain ⟨v, w, hvw⟩ := h u
  refine ⟨v.val, w.val, ?_⟩
  have hval := congrArg Units.val hvw
  rw [zpow_two, Units.val_mul, Units.val_mul, Units.coe_map, ← pow_two] at hval
  exact hval

/-! ### The chart ring of the thickening and its localisation -/

/-- The chart ring `A' = A[ε]` of the thickening: both charts of `X'` are `Spec A'`. -/
abbrev DualChart : Type := DualNumber Chart

/-- The coordinate `x`, as an element of the chart ring `A'` of the thickening. -/
def dualX : DualChart := TrivSqZeroExt.inl (Polynomial.X : Chart)

/-- `B'` as an `A'`-algebra, through the inclusion
`Stacks.Examples.TwistedDoubledLine.dualToOverlap`. -/
instance : Algebra DualChart DualOverlap := dualToOverlap.toAlgebra

/-- The `A'`-algebra structure of `B'` is the inclusion `A' ⟶ B'`. -/
theorem algebraMap_dualChart (c : DualChart) :
    algebraMap DualChart DualOverlap c = dualToOverlap c := rfl

/-- Powers of `x` in `A'` stay in the constant component. -/
theorem dualX_pow (n : ℕ) : dualX ^ n = TrivSqZeroExt.inl ((Polynomial.X : Chart) ^ n) :=
  (map_pow (TrivSqZeroExt.inlHom Chart Chart) Polynomial.X n).symm

/-- In `B'` the `n`-th power of `x` is the monomial `xⁿ` of the constant component. -/
theorem algebraMap_dualX_pow (n : ℕ) :
    algebraMap DualChart DualOverlap (dualX ^ n) =
      TrivSqZeroExt.inl (T (n : ℤ) : Overlap) := by
  rw [dualX_pow]
  refine TrivSqZeroExt.ext ?_ ?_ <;>
    simp [algebraMap_dualChart, Polynomial.toLaurent_X_pow]

/-- **`B'` is the localisation of `A'` away from `x`.** -/
instance isLocalization_dualOverlap : IsLocalization.Away dualX DualOverlap := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [show algebraMap DualChart DualOverlap dualX =
      TrivSqZeroExt.inl (T ((1 : ℕ) : ℤ) : Overlap) by simpa using algebraMap_dualX_pow 1]
    exact (LaurentPolynomial.isUnit_T (R := Coeff) _).map
      (TrivSqZeroExt.inlHom Overlap Overlap)
  · intro s
    obtain ⟨n₀, f₀, hf₀⟩ := LaurentPolynomial.exists_T_pow (TrivSqZeroExt.fst s)
    obtain ⟨n₁, f₁, hf₁⟩ := LaurentPolynomial.exists_T_pow (TrivSqZeroExt.snd s)
    refine ⟨n₀ + n₁, dualMk (f₀ * Polynomial.X ^ n₁) (f₁ * Polynomial.X ^ n₀), ?_⟩
    rw [← map_pow, algebraMap_dualX_pow]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, algebraMap_dualChart,
        dualToOverlap_apply, dualToOverlapFun_fst, dualMk_fst,
        show ((n₀ + n₁ : ℕ) : ℤ) = (n₀ : ℤ) + (n₁ : ℤ) by push_cast; ring,
        T_add, map_mul, Polynomial.toLaurent_X_pow, hf₀, ← mul_assoc]
    · rw [DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, mul_zero, zero_add,
        algebraMap_dualChart, dualToOverlap_apply, dualToOverlapFun_snd, dualMk_snd,
        show ((n₀ + n₁ : ℕ) : ℤ) = (n₁ : ℤ) + (n₀ : ℤ) by push_cast; ring,
        T_add, map_mul, Polynomial.toLaurent_X_pow, hf₁, ← mul_assoc]
  · intro a b hab
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul, one_mul]
    rw [algebraMap_dualChart, algebraMap_dualChart] at hab
    refine TrivSqZeroExt.ext (Polynomial.toLaurent_injective ?_)
      (Polynomial.toLaurent_injective ?_)
    · simpa using congrArg TrivSqZeroExt.fst hab
    · simpa using congrArg TrivSqZeroExt.snd hab

/-! ### The two gluings -/

/-- The overlap of the two charts of the doubled line: `Spec B ⟶ Spec A`. -/
abbrev chartOverlap : Spec (CommRingCat.of Overlap) ⟶ Spec (CommRingCat.of Chart) :=
  Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Chart →+* Overlap))

/-- `Spec B ⟶ Spec A` is an open immersion, `B` being the localisation of `A` at `x`. -/
instance : IsOpenImmersion chartOverlap :=
  IsOpenImmersion.of_isLocalization (S := Overlap) (Polynomial.X : Chart)

/-- The overlap of the two charts of the thickening: `Spec B' ⟶ Spec A'`. -/
abbrev dualOverlapIncl :
    Spec (CommRingCat.of DualOverlap) ⟶ Spec (CommRingCat.of DualChart) :=
  Spec.map (CommRingCat.ofHom dualToOverlap)

/-- `Spec B' ⟶ Spec A'` is an open immersion, `B'` being the localisation of `A'` at `x`. -/
instance : IsOpenImmersion dualOverlapIncl :=
  IsOpenImmersion.of_isLocalization (S := DualOverlap) dualX

/-- The gluing twist is an isomorphism of rings, so it induces an automorphism of `Spec B'`. -/
instance isIso_ofHom_twist : IsIso (CommRingCat.ofHom twist) :=
  inferInstanceAs (IsIso (RingEquiv.ofBijective twist twist_bijective).toCommRingCatIso.hom)

/-- **The twisted leg of the span presenting `X'`.** -/
abbrev dualOverlapTwisted :
    Spec (CommRingCat.of DualOverlap) ⟶ Spec (CommRingCat.of DualChart) :=
  Spec.map (CommRingCat.ofHom twist) ≫ dualOverlapIncl

/-- **The scheme `X`**: the affine line over `ℚ[t, t⁻¹]` with its origin doubled. -/
abbrev doubledLine : Scheme.{0} := SpanGlue.glued chartOverlap chartOverlap

/-- **The scheme `X'`**: two copies of `Spec A'` glued along `Spec B'` by the twist. -/
abbrev twistedThickening : Scheme.{0} :=
  SpanGlue.glued dualOverlapTwisted dualOverlapIncl

/-- Reduction modulo `ε` on a chart: the closed immersion `Spec A ⟶ Spec A'`. -/
abbrev chartRed : Spec (CommRingCat.of Chart) ⟶ Spec (CommRingCat.of DualChart) :=
  Spec.map (CommRingCat.ofHom (dualFst Chart))

/-- Reduction modulo `ε` on the overlap: the closed immersion `Spec B ⟶ Spec B'`. -/
abbrev overlapRed :
    Spec (CommRingCat.of Overlap) ⟶ Spec (CommRingCat.of DualOverlap) :=
  Spec.map (CommRingCat.ofHom (dualFst Overlap))

/-- Reduction modulo `ε` commutes with the twisted inclusion of the overlap: the twist is the
identity modulo `ε`. -/
theorem chartOverlap_chartRed_eq_twisted :
    chartOverlap ≫ chartRed = overlapRed ≫ dualOverlapTwisted := by
  simp only [← Spec.map_comp]
  congr 1

/-- Reduction modulo `ε` commutes with the inclusion of the overlap. -/
theorem chartOverlap_chartRed_eq_plain :
    chartOverlap ≫ chartRed = overlapRed ≫ dualOverlapIncl := by
  simp only [← Spec.map_comp]
  congr 1

/-- The two chart maps `Spec A ⟶ X'` agree on the overlap, so they glue. -/
theorem thickeningHom_cond :
    chartOverlap ≫ (chartRed ≫ SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl) =
      chartOverlap ≫ (chartRed ≫ SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl) :=
  by rw [← Category.assoc, chartOverlap_chartRed_eq_twisted, Category.assoc,
    SpanGlue.glue_condition dualOverlapTwisted dualOverlapIncl, ← Category.assoc,
    ← chartOverlap_chartRed_eq_plain, Category.assoc]

/-- **The morphism `i : X ⟶ X'`**, glued from reduction modulo `ε` on the two charts. -/
abbrev thickeningHom : doubledLine ⟶ twistedThickening :=
  SpanGlue.desc chartOverlap chartOverlap
    (chartRed ≫ SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl)
    (chartRed ≫ SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl) thickeningHom_cond

/-! ### `i` is a thickening -/

/-- The overlap of the two charts of `X'` is the basic open of `x` in either chart. -/
theorem opensRange_dualOverlapIncl :
    dualOverlapIncl.opensRange = PrimeSpectrum.basicOpen dualX :=
  Opens.ext (PrimeSpectrum.localization_away_comap_range DualOverlap dualX)

/-- The twisted leg has the same image as the untwisted one, the twist being an
isomorphism. -/
theorem opensRange_dualOverlapTwisted :
    dualOverlapTwisted.opensRange = PrimeSpectrum.basicOpen dualX := by
  rw [← opensRange_dualOverlapIncl]
  exact Opens.ext (range_eq_range_of_surjective dualOverlapTwisted dualOverlapIncl
    (Spec.map (CommRingCat.ofHom twist)) rfl)

/-- The overlap of the two charts of `X` is the basic open of `x` in either chart. -/
theorem opensRange_chartOverlap :
    chartOverlap.opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Chart) :=
  Opens.ext (PrimeSpectrum.localization_away_comap_range Overlap (Polynomial.X : Chart))

/-- The overlap of the two charts of `X` lies over the overlap of the two charts of `X'`, and is
the whole of what lies over it. -/
theorem preimage_opensRange_dualOverlapIncl :
    chartRed ⁻¹ᵁ dualOverlapIncl.opensRange = chartOverlap.opensRange := by
  rw [opensRange_dualOverlapIncl, opensRange_chartOverlap]
  exact preimage_basicOpen_specMap (dualFst Chart) dualX

/-- The same for the twisted leg of the span presenting `X'`. -/
theorem preimage_opensRange_dualOverlapTwisted :
    chartRed ⁻¹ᵁ dualOverlapTwisted.opensRange = chartOverlap.opensRange := by
  rw [opensRange_dualOverlapTwisted, opensRange_chartOverlap]
  exact preimage_basicOpen_specMap (dualFst Chart) dualX

/-- The first chart of `X` is exactly the part of `X` lying over the first chart of `X'`. -/
theorem isPullback_chart₁ :
    IsPullback (SpanGlue.ι₁ chartOverlap chartOverlap) chartRed thickeningHom
      (SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl) :=
  SpanGlue.isPullback_ι₁_desc dualOverlapTwisted dualOverlapIncl chartOverlap chartOverlap
    chartRed chartRed thickeningHom_cond preimage_opensRange_dualOverlapIncl

/-- The second chart of `X` is exactly the part of `X` lying over the second chart of `X'`. -/
theorem isPullback_chart₂ :
    IsPullback (SpanGlue.ι₂ chartOverlap chartOverlap) chartRed thickeningHom
      (SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl) :=
  SpanGlue.isPullback_ι₂_desc dualOverlapTwisted dualOverlapIncl chartOverlap chartOverlap
    chartRed chartRed thickeningHom_cond preimage_opensRange_dualOverlapTwisted

/-- Reduction modulo `ε` is surjective on the chart ring, split by the constant inclusion. -/
theorem surjective_dualFst_chart : Function.Surjective (dualFst Chart) :=
  fun p => ⟨TrivSqZeroExt.inl p, rfl⟩

/-- A property of morphisms which is Zariski-local at the target and holds for the affine
reduction `Spec A ⟶ Spec A'` holds for `i`. -/
theorem property_thickeningHom_of_chartRed {P : MorphismProperty Scheme.{0}}
    [IsZariskiLocalAtTarget P] (hP : P chartRed) : P thickeningHom := by
  have key : ∀ {U : Scheme.{0}} (g : U ⟶ twistedThickening), ∀ _ : IsOpenImmersion g,
      ∀ {V : Scheme.{0}} {a : V ⟶ doubledLine} {c : V ⟶ U},
      IsPullback a c thickeningHom g → P c → P (thickeningHom ∣_ g.opensRange) := by
    intro U g _ V a c h hc
    refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange thickeningHom g)).mpr ?_
    rw [← h.isoPullback_hom_snd] at hc
    exact (P.cancel_left_of_respectsIso _ _).mp hc
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun b : Bool => cond b (SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl).opensRange
      (SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl).opensRange) ?_ ?_
  · rw [iSup_bool_eq]
    change (SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl).opensRange ⊔
      (SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl).opensRange = ⊤
    rw [sup_comm]
    exact SpanGlue.opensRange_ι₁_sup_opensRange_ι₂ _ _
  · intro b
    cases b
    · exact key _ inferInstance isPullback_chart₁ hP
    · exact key _ inferInstance isPullback_chart₂ hP

/-- `Spec A ⟶ Spec A'` is a closed immersion, being `Spec` of a surjective ring map. -/
instance isClosedImmersion_chartRed : IsClosedImmersion chartRed :=
  IsClosedImmersion.spec_of_surjective _ surjective_dualFst_chart

/-- `Spec A ⟶ Spec A'` is surjective: the kernel of `A' ⟶ A` is square-zero, so it lies in
every prime. -/
instance surjective_chartRed : Surjective chartRed :=
  ⟨surjective_comap_of_ker_isNilpotent (dualFst Chart) surjective_dualFst_chart
    fun _ hz => isNilpotent_of_fst_eq_zero hz⟩

/-- `i : X ⟶ X'` is a closed immersion, being one over each chart of `X'`. -/
instance isClosedImmersion_thickeningHom : IsClosedImmersion thickeningHom :=
  property_thickeningHom_of_chartRed (P := @IsClosedImmersion) inferInstance

/-- `i : X ⟶ X'` is surjective, being surjective over each chart of `X'`. -/
instance surjective_thickeningHom : Surjective thickeningHom :=
  property_thickeningHom_of_chartRed (P := @Surjective) inferInstance

/-- **`i : X ⟶ X'` is a thickening.** -/
theorem isThickening_thickeningHom : IsThickening thickeningHom :=
  ⟨inferInstance, thickeningHom.surjective⟩

/-! ### The invertible global function `t` on `X` -/

/-- The structure morphism `X ⟶ Spec ℚ[t, t⁻¹]`. -/
abbrev toBaseHom : doubledLine ⟶ Spec (CommRingCat.of Coeff) :=
  SpanGlue.desc chartOverlap chartOverlap
    (Spec.map (CommRingCat.ofHom (Polynomial.C : Coeff →+* Chart)))
    (Spec.map (CommRingCat.ofHom (Polynomial.C : Coeff →+* Chart))) rfl

/-- Restriction of a global function of `X` to the first chart, read in `A`. -/
def resChart : Γ(doubledLine, ⊤) ⟶ CommRingCat.of Chart :=
  (SpanGlue.ι₁ chartOverlap chartOverlap).appTop ≫ (Scheme.ΓSpecIso _).hom

/-- Restriction of a global function of `X'` to the first — twisted — chart, read in `A'`. -/
def resDual₁ : Γ(twistedThickening, ⊤) ⟶ CommRingCat.of DualChart :=
  (SpanGlue.ι₁ dualOverlapTwisted dualOverlapIncl).appTop ≫ (Scheme.ΓSpecIso _).hom

/-- Restriction of a global function of `X'` to the second chart, read in `A'`. -/
def resDual₂ : Γ(twistedThickening, ⊤) ⟶ CommRingCat.of DualChart :=
  (SpanGlue.ι₂ dualOverlapTwisted dualOverlapIncl).appTop ≫ (Scheme.ΓSpecIso _).hom

/-- Pulling a function back from the base and restricting it to the first chart of `X` is its
image in `A`. -/
theorem toBaseHom_appTop_resChart :
    toBaseHom.appTop ≫ resChart =
      (Scheme.ΓSpecIso (CommRingCat.of Coeff)).hom ≫
        CommRingCat.ofHom (Polynomial.C : Coeff →+* Chart) := by
  rw [resChart, ← Category.assoc, ← Scheme.Hom.comp_appTop,
    SpanGlue.ι₁_desc chartOverlap chartOverlap _ _ rfl, Scheme.ΓSpecIso_naturality]

/-- Restricting a global function of `X'` to `X` and then to the first chart is reduction modulo
`ε` of its restriction to the first chart of `X'`. -/
theorem thickeningHom_appTop_resChart :
    thickeningHom.appTop ≫ resChart = resDual₁ ≫ CommRingCat.ofHom (dualFst Chart) := by
  rw [resChart, ← Category.assoc, ← Scheme.Hom.comp_appTop,
    SpanGlue.ι₁_desc chartOverlap chartOverlap _ _ thickeningHom_cond,
    Scheme.Hom.comp_appTop, Category.assoc, resDual₁, Category.assoc,
    Scheme.ΓSpecIso_naturality]

/-- **The gluing condition on a global function of `X'`**, as an equality of ring maps out of
`Γ(X', ⊤)`: the two chart restrictions are identified over `B'` by the twist. -/
theorem resDual_glue :
    resDual₁ ≫ (CommRingCat.ofHom dualToOverlap ≫ CommRingCat.ofHom twist) =
      resDual₂ ≫ CommRingCat.ofHom dualToOverlap := by
  have h₁ : dualOverlapTwisted.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of DualOverlap)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of DualChart)).hom ≫
        (CommRingCat.ofHom dualToOverlap ≫ CommRingCat.ofHom twist) := by
    rw [show dualOverlapTwisted =
      Spec.map (CommRingCat.ofHom dualToOverlap ≫ CommRingCat.ofHom twist) by
        rw [Spec.map_comp], Scheme.ΓSpecIso_naturality]
  have h₂ : dualOverlapIncl.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of DualOverlap)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of DualChart)).hom ≫ CommRingCat.ofHom dualToOverlap :=
    Scheme.ΓSpecIso_naturality _
  rw [resDual₁, resDual₂, Category.assoc, Category.assoc, ← h₁, ← h₂,
    ← Category.assoc, ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    SpanGlue.glue_condition dualOverlapTwisted dualOverlapIncl]

/-- **The gluing condition on a global function of `X'`, on elements.**  Its two chart
restrictions `c₀` and `c₁` satisfy `twist c₀ = c₁` in `B'`, which is the hypothesis of
`Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_fst_of_twist_eq`. -/
theorem twist_dualToOverlap_resDual₁ (w : Γ(twistedThickening, ⊤)) :
    twist (dualToOverlap (resDual₁ w)) = dualToOverlap (resDual₂ w) := by
  simpa using ConcreteCategory.congr_hom resDual_glue w

/-! ### The counterexample -/

/-- The unit `t` of `ℚ[t, t⁻¹]`, pulled back to an invertible global function on `X`. -/
theorem isUnit_tGlobal :
    IsUnit (toBaseHom.appTop ((Scheme.ΓSpecIso (CommRingCat.of Coeff)).inv (T 1))) :=
  (LaurentPolynomial.isUnit_T (R := ℚ) 1).map
    ((Scheme.ΓSpecIso (CommRingCat.of Coeff)).inv ≫ toBaseHom.appTop).hom

/-- The restriction of `t` to the first chart of `X` is `t` itself, as an element of `A`. -/
theorem resChart_tGlobal :
    resChart (toBaseHom.appTop ((Scheme.ΓSpecIso (CommRingCat.of Coeff)).inv (T 1))) =
      Polynomial.C (T 1 : Coeff) := by
  simpa using ConcreteCategory.congr_hom toBaseHom_appTop_resChart
    ((Scheme.ΓSpecIso (CommRingCat.of Coeff)).inv (T 1))

/-- Two is invertible in `ℚ[t, t⁻¹]`. -/
theorem isUnit_two_coeff : IsUnit ((2 : ℤ) : Coeff) := by
  rw [← map_intCast (algebraMap ℚ Coeff)]
  exact (isUnit_iff_ne_zero.mpr (by norm_num)).map _

/-- **Two is invertible on `X`.** -/
theorem isUnit_two_doubledLine : IsUnit ((2 : ℤ) : Γ(doubledLine, ⊤)) := by
  rw [← map_intCast ((Scheme.ΓSpecIso (CommRingCat.of Coeff)).inv ≫ toBaseHom.appTop).hom]
  exact isUnit_two_coeff.map _

/-- **The failure of `Stacks.Thickenings.GlobalUnitsPowerLift` for this thickening and
`n = 2`.**  The invertible global function `t` on `X` is not a square times the restriction of
an invertible global function on `X'`: restricting such an identity to the first chart turns it
into `a² c₀ = t` in `A`, where `c₀` is the first chart restriction of the global function on
`X'` and is therefore subject to the gluing condition `twist c₀ = c₁`, and
`Stacks.Examples.TwistedDoubledLine.not_exists_sq_mul_fst_of_twist_eq` says there is no such
pair. -/
theorem not_globalUnitsPowerLift : ¬ GlobalUnitsPowerLift thickeningHom 2 := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_sq_mul_appTop_of_globalUnitsPowerLift thickeningHom h
    isUnit_tGlobal.unit
  refine not_exists_sq_mul_fst_of_twist_eq
    ⟨resChart a, resDual₁ b, resDual₂ b, twist_dualToOverlap_resDual₁ b, ?_⟩
  have h₁ : resChart (thickeningHom.appTop b) = (resDual₁ b).fst := by
    simpa using ConcreteCategory.congr_hom thickeningHom_appTop_resChart b
  have h₂ := congrArg (CommRingCat.Hom.hom resChart) hab
  rw [map_mul, map_pow, h₁] at h₂
  rw [← h₂]
  exact resChart_tGlobal

/-- **The bijection asserted by [Stacks, Tag 0C6S] fails for this thickening.**  Two is
invertible on `X` and `i` is a thickening, yet restriction of invertible modules is not a
bijection from the `2`-torsion of `Pic(X')` onto the `2`-torsion of `Pic(X)`: by
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff` that bijection is equivalent to
`Stacks.Thickenings.GlobalUnitsPowerLift i 2`, which fails here. -/
theorem not_bijOn_schemePullbackClass_zsmulTorsion :
    ¬ Set.BijOn (schemePullbackClass thickeningHom)
      (zsmulTorsion (ofScheme twistedThickening) 2)
      (zsmulTorsion (ofScheme doubledLine) 2) := fun h =>
  not_globalUnitsPowerLift
    ((Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff thickeningHom
      isThickening_thickeningHom isUnit_two_doubledLine).mp h)

/-- **[Stacks, Tag 0C6S] is false as stated, and this is the negation of what it asserts.**
The tag says that for a thickening `i : X ⟶ X'` of schemes and an integer `n` invertible in
`𝒪_X`, restriction of invertible modules is a bijection from the `n`-torsion of `Pic(X')` onto
the `n`-torsion of `Pic(X)`, with no further hypothesis.

The witness is `n = 2`, `X = Stacks.Examples.TwistedDoubledLine.doubledLine` the affine line over
`ℚ[t, t⁻¹]` with its origin doubled, `X' =
Stacks.Examples.TwistedDoubledLine.twistedThickening` the first-order thickening of `X` glued by
`b₀ + ε b₁ ↦ b₀ + ε (b₁ + x⁻¹ (t ∂/∂t) b₀)`, and
`i = Stacks.Examples.TwistedDoubledLine.thickeningHom`.  Two is invertible on `X` and `i` is a
thickening; but the invertible global function `t` on `X` is not a square times the restriction
of an invertible global function on `X'`, and
`Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff` proves that condition equivalent
to the tag's conclusion.

What the source's own argument gives is surjectivity, which holds with no extra hypothesis and
is what carries the tag, in
`Stacks.Thickenings.surjOn_schemePullbackClass_zsmulTorsion_of_isThickening`; the corrected
biconditional is `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_iff`.  **The tag is
refuted here, but the source has not been corrected**, so
neither this theorem nor the corrected statement is registered against the tag. -/
theorem not_forall_bijOn_schemePullbackClass_zsmulTorsion :
    ¬ ∀ (X X' : Scheme.{0}) (i : X ⟶ X') (n : ℤ), IsThickening i →
        IsUnit ((n : ℤ) : Γ(X, ⊤)) →
          Set.BijOn (schemePullbackClass i) (zsmulTorsion (ofScheme X') n)
            (zsmulTorsion (ofScheme X) n) := by
  intro h
  exact not_bijOn_schemePullbackClass_zsmulTorsion
    (h doubledLine twistedThickening thickeningHom 2 isThickening_thickeningHom
      isUnit_two_doubledLine)

end Stacks.Examples.TwistedDoubledLine

end
