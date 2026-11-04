module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksFrontier.RingTheory.Serre.Reduced

/-!
# Serre's conditions for schemes

A scheme is regular in codimension `k`, property `(R_k)`, when every local ring of dimension at
most `k` is regular. A locally Noetherian scheme has Serre's property `(S_k)` when the depth of
every local ring is at least the minimum of `k` and its Krull dimension. Serre's criteria
identify the reduced locally Noetherian schemes as those satisfying `(S₁)` and `(R₀)`, and the
normal ones as those satisfying `(S₂)` and `(R₁)`.

## Main definitions

* `AlgebraicGeometry.IsRegularInCodimension` expresses property `(R_k)` for a scheme.
* `AlgebraicGeometry.HasPropertySk` is Serre's property `(S_k)` for a locally Noetherian scheme.

## Main results

* `AlgebraicGeometry.hasPropertySk_iff` is the pointwise characterization of `(S_k)`.
* `AlgebraicGeometry.hasPropertySk_zero` says that every locally Noetherian scheme has property
  `(S₀)`.
* `AlgebraicGeometry.isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero` characterizes
  reduced locally Noetherian schemes by conditions `(S₁)` and `(R₀)`.
* `AlgebraicGeometry.isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one` is Serre's
  criterion for normality: `(S₂)` together with `(R₁)`.

## Implementation notes

The predicate `IsRegularInCodimension` is meaningful without a local Noetherian hypothesis, so
that hypothesis is left to the results which use it, and the dimension is written directly as the
Krull dimension of the stalk.

Both sides of the defining inequality for `(S_k)` are compared in `WithBot ℕ∞`, the codomain of
`ringKrullDim`. The depth is the depth along the maximal ideal of the local ring, as in the
source definition of depth. Clients can use `hasPropertySk_iff` to pass between the named
predicate and its pointwise inequality, while `simp` discharges property `(S₀)` directly.

Serre's criterion for normality is deduced from its affine form
`isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth` by
comparing the local rings of the scheme at the points of an affine open with the localizations
of its ring of sections at the corresponding primes; the characterization of normality by the
rings of sections of all affine opens is `isNormal_tfae`.

## References

* [Stacks Project, Tag 033Q](https://stacks.math.columbia.edu/tag/033Q)
* [Stacks Project, Tag 0344](https://stacks.math.columbia.edu/tag/0344)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public section

open CategoryTheory RingTheory.Sequence

universe u

namespace AlgebraicGeometry

/-- A scheme is regular in codimension `k` (has property `(R_k)`) if each of its local rings of
Krull dimension at most `k` is regular. -/
@[stacks 033Q "property_rk",
  ega "IV 5.8.2"]
public abbrev IsRegularInCodimension (X : Scheme) (k : ℕ) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ (k : WithBot ℕ∞) →
    IsRegularLocalRing (X.presheaf.stalk x)

/-- Serre's property `(Sₖ)` for a locally Noetherian scheme: at every point, the depth of the
local ring is at least the minimum of `k` and the dimension of that local ring. -/
@[stacks 033Q "property_sk"]
def HasPropertySk (X : Scheme.{u}) [IsLocallyNoetherian X] (k : ℕ) : Prop :=
  ∀ x : X,
    min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) : WithBot ℕ∞)

/-- The pointwise characterization of Serre's property `(Sₖ)`. -/
public theorem hasPropertySk_iff (X : Scheme.{u}) [IsLocallyNoetherian X] (k : ℕ) :
    HasPropertySk X k ↔
      ∀ x : X,
        min (k : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
          (Module.depth (X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x) : WithBot ℕ∞) :=
  Iff.rfl

/-- Every locally Noetherian scheme has Serre's property `(S₀)`. -/
@[simp]
public theorem hasPropertySk_zero (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasPropertySk X 0 := by simp [HasPropertySk]

/-- For a local ring, depth along the maximal ideal is the corresponding depth supremum. -/
public lemma depth_eq_depthSup_of_isLocalRing (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.depth A (IsLocalRing.maximalIdeal A) A =
      Module.depthSup A (IsLocalRing.maximalIdeal A) A := by
  rw [Module.depth, ite_eq_right (by simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top),
    Module.depthSup_eq_iSup]

/-- The dimension of a stalk of an affine scheme is the height of the corresponding prime. -/
private lemma spec_dimension_eq_height (R : CommRingCat.{u}) (p : PrimeSpectrum R) :
    ringKrullDim ((Spec R).presheaf.stalk p) = (p.asIdeal.height : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso R p).commRingCatIsoToRingEquiv,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]

/-- The depth of a stalk of an affine scheme, as a depth supremum of the localization. -/
private lemma spec_depth_eq_depthSup (R : CommRingCat.{u}) (p : PrimeSpectrum R)
    [IsLocalRing ((Spec R).presheaf.stalk p)] :
    (Module.depth ((Spec R).presheaf.stalk p)
        (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk p))
        ((Spec R).presheaf.stalk p) : WithBot ℕ∞) =
      (Module.depthSup (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal) : WithBot ℕ∞) := by
  rw [Module.depth_self_eq_of_ringEquiv (Spec.stalkIso R p).commRingCatIsoToRingEquiv,
    depth_eq_depthSup_of_isLocalRing]

/-- On an affine scheme, `(S₁)` and `(R₀)` are the ring-theoretic conditions `HasS1` and
`HasR0`. -/
private lemma spec_hasPropertyS1_and_R0_iff (R : CommRingCat.{u})
    [IsNoetherianRing R] :
    (HasPropertySk (Spec R) 1 ∧
      IsRegularInCodimension (Spec R) 0) ↔
      HasR0 R ∧ HasS1 R := by
  rw [hasPropertySk_iff]
  constructor
  · rintro ⟨hs, hr⟩
    constructor
    · intro p hp hheight
      let e := (Spec.stalkIso R ⟨p, hp⟩).commRingCatIsoToRingEquiv
      let : p.IsPrime := hp
      let : IsLocalRing ((Spec R).presheaf.stalk ⟨p, hp⟩) := e.symm.isLocalRing
      have hbound : ringKrullDim ((Spec R).presheaf.stalk ⟨p, hp⟩) ≤
          (0 : WithBot ℕ∞) := by
        rw [spec_dimension_eq_height R ⟨p, hp⟩]
        exact_mod_cast hheight.le
      have : IsRegularLocalRing ((Spec R).presheaf.stalk ⟨p, hp⟩) := hr ⟨p, hp⟩ hbound
      exact IsRegularLocalRing.of_ringEquiv e
    · intro p hp
      let e := (Spec.stalkIso R ⟨p, hp⟩).commRingCatIsoToRingEquiv
      let : IsLocalRing ((Spec R).presheaf.stalk ⟨p, hp⟩) := e.symm.isLocalRing
      have hs' := hs (⟨p, hp⟩ : Spec R)
      rw [spec_dimension_eq_height R ⟨p, hp⟩, spec_depth_eq_depthSup R ⟨p, hp⟩] at hs'
      exact_mod_cast hs'
  · rintro ⟨hR0, hS1⟩
    constructor
    · intro x
      let e := (Spec.stalkIso R x).commRingCatIsoToRingEquiv
      let : IsLocalRing ((Spec R).presheaf.stalk x) := e.symm.isLocalRing
      have : x.asIdeal.IsPrime := x.2
      rw [spec_dimension_eq_height R x, spec_depth_eq_depthSup R x]
      exact_mod_cast hS1 x.asIdeal
    · intro x hdim
      rw [spec_dimension_eq_height R x] at hdim
      have : x.asIdeal.IsPrime := x.2
      have : IsRegularLocalRing (Localization.AtPrime x.asIdeal) :=
        hR0 x.asIdeal (le_antisymm (by exact_mod_cast hdim) bot_le)
      exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso R x).commRingCatIsoToRingEquiv.symm

/-- Property `(S₁)` at a single point. -/
private def hasPropertyS1At (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Prop :=
  min (1 : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
    (Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) : WithBot ℕ∞)

/-- Property `(R₀)` at a single point. -/
private def isRegularInCodimensionZeroAt (X : Scheme.{u}) (x : X) : Prop :=
  ringKrullDim (X.presheaf.stalk x) ≤ (0 : WithBot ℕ∞) →
    IsRegularLocalRing (X.presheaf.stalk x)

/-- The inequality defining Serre's property `(Sₖ)` at a point is invariant under isomorphism of
the local ring. -/
private lemma min_le_depth_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (k : WithBot ℕ∞) :
    (min k (ringKrullDim A) ≤
        (Module.depth A (IsLocalRing.maximalIdeal A) A : WithBot ℕ∞)) ↔
      (min k (ringKrullDim B) ≤
        (Module.depth B (IsLocalRing.maximalIdeal B) B : WithBot ℕ∞)) := by
  rw [ringKrullDim_eq_of_ringEquiv e, Module.depth_self_eq_of_ringEquiv e]

/-- Regularity of a local ring is invariant under isomorphism. -/
private lemma isRegularLocalRing_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsRegularLocalRing A ↔ IsRegularLocalRing B :=
  ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

/-- The implication defining property `(Rₖ)` at a point is invariant under isomorphism of the
local ring. -/
private lemma isRegularLocalRing_of_le_iff_of_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (k : WithBot ℕ∞) :
    (ringKrullDim A ≤ k → IsRegularLocalRing A) ↔
      (ringKrullDim B ≤ k → IsRegularLocalRing B) := by
  rw [ringKrullDim_eq_of_ringEquiv e, isRegularLocalRing_iff_of_ringEquiv e]

/-- Property `(S₁)` transfers along a morphism inducing an isomorphism on a stalk. -/
private lemma hasPropertyS1At_iff_of_stalkMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : hasPropertyS1At X x ↔ hasPropertyS1At Y (f x) :=
  min_le_depth_iff_of_ringEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm 1

/-- Property `(R₀)` transfers along a morphism inducing an isomorphism on a stalk. -/
private lemma isRegularInCodimensionZeroAt_iff_of_stalkMap {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] :
    isRegularInCodimensionZeroAt X x ↔ isRegularInCodimensionZeroAt Y (f x) :=
  isRegularLocalRing_of_le_iff_of_ringEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm 0

/-- The pair of conditions `(S₁)` and `(R₀)` is local on an open cover. -/
private lemma schemePredicates_iff_of_openCover (X : Scheme.{u})
    [IsLocallyNoetherian X] (𝒰 : X.OpenCover) :
    (HasPropertySk X 1 ∧ IsRegularInCodimension X 0) ↔
      ∀ i, HasPropertySk (𝒰.X i) 1 ∧ IsRegularInCodimension (𝒰.X i) 0 := by
  show ((∀ x, hasPropertyS1At X x) ∧ ∀ x, isRegularInCodimensionZeroAt X x) ↔
    ∀ i, (∀ x, hasPropertyS1At (𝒰.X i) x) ∧ ∀ x, isRegularInCodimensionZeroAt (𝒰.X i) x
  refine ⟨fun ⟨hs, hr⟩ i ↦ ⟨fun x ↦ (hasPropertyS1At_iff_of_stalkMap (𝒰.f i) x).mpr (hs _),
      fun x ↦ (isRegularInCodimensionZeroAt_iff_of_stalkMap (𝒰.f i) x).mpr (hr _)⟩,
    fun h ↦ ⟨fun x ↦ ?_, fun x ↦ ?_⟩⟩
  · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact (hasPropertyS1At_iff_of_stalkMap (𝒰.f i) y).mp ((h i).1 y)
  · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    exact (isRegularInCodimensionZeroAt_iff_of_stalkMap (𝒰.f i) y).mp ((h i).2 y)

/-- The pair of conditions `(S₁)` and `(R₀)` is invariant under isomorphism of schemes. -/
private lemma schemePredicates_iff_of_iso {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) :
    (HasPropertySk X 1 ∧ IsRegularInCodimension X 0) ↔
      (HasPropertySk Y 1 ∧ IsRegularInCodimension Y 0) := by
  show ((∀ x, hasPropertyS1At X x) ∧ IsRegularInCodimension X 0) ↔
    ((∀ y, hasPropertyS1At Y y) ∧ IsRegularInCodimension Y 0)
  constructor
  · rintro ⟨hs, hr⟩
    constructor
    · intro y
      have hx := hs (e.inv y)
      simpa using (hasPropertyS1At_iff_of_stalkMap e.hom (e.inv y)).mp hx
    · intro y hy
      have hx := hr (e.inv y)
      have heq : e.hom (e.inv y) = y := by
        simp
      have hy' : ringKrullDim (Y.presheaf.stalk (e.hom (e.inv y))) ≤
          (0 : WithBot ℕ∞) := by rw [heq]; exact hy
      have hreg := (isRegularInCodimensionZeroAt_iff_of_stalkMap e.hom (e.inv y)).mp hx hy'
      rw [← heq]
      exact hreg
  · rintro ⟨hs, hr⟩
    constructor
    · intro x
      have hy := hs (e.hom x)
      simpa using (hasPropertyS1At_iff_of_stalkMap e.hom x).mpr hy
    · intro x hx
      have hy := hr (e.hom x)
      simpa using (isRegularInCodimensionZeroAt_iff_of_stalkMap e.hom x).mpr hy hx

/-- Serre's criterion on an affine locally Noetherian scheme. -/
private lemma affine_isReduced_iff_hasPropertyS1_and_R0 (Y : Scheme.{u})
    [IsAffine Y] [IsLocallyNoetherian Y] :
    IsReduced Y ↔ HasPropertySk Y 1 ∧ IsRegularInCodimension Y 0 := by
  let R : CommRingCat := CommRingCat.of Γ(Y, ⊤)
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  exact (ObjectProperty.prop_iff_of_iso (IsReduced ·) Y.isoSpec).trans <|
    (affine_isReduced_iff R).trans <| (isReduced_iff_hasR0_and_hasS1 R).trans <|
      (spec_hasPropertyS1_and_R0_iff R).symm.trans (schemePredicates_iff_of_iso Y.isoSpec).symm

/-- A locally Noetherian scheme is reduced if and only if it satisfies Serre's conditions `(S₁)`
and `(R₀)`. -/
@[stacks 0344, ega "IV 5.8.5", ega "IV 7.3.9"]
public theorem isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsReduced X ↔
      HasPropertySk X 1 ∧ IsRegularInCodimension X 0 :=
  (IsReduced.iff_of_openCover X X.affineCover).trans
    ((forall_congr' fun i =>
      affine_isReduced_iff_hasPropertyS1_and_R0 (X.affineCover.X i)).trans
      (schemePredicates_iff_of_openCover X X.affineCover).symm)

section Normality

/-- The local ring at a point of an affine open is the localization of the ring of sections of
that open at the corresponding prime. -/
private lemma nonempty_ringEquiv_stalk_localization {X : Scheme.{u}} (U : X.affineOpens)
    {x : X} (hx : x ∈ U.val) :
    Nonempty (X.presheaf.stalk x ≃+*
      Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  exact ⟨((IsLocalization.algEquiv (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (U.2.primeIdealOf ⟨x, hx⟩).asIdeal)
    (X.presheaf.stalk x)).toRingEquiv).symm⟩

/-- Every prime of the ring of sections of an affine open is the prime of a point of that open,
whose local ring is therefore the localization at that prime. -/
private lemma exists_nonempty_ringEquiv_localization {X : Scheme.{u}} (U : X.affineOpens)
    (z : PrimeSpectrum Γ(X, U)) :
    ∃ x : X, Nonempty (X.presheaf.stalk x ≃+* Localization.AtPrime z.asIdeal) := by
  have hx : U.2.fromSpec z ∈ U.val := by
    have hz : z ∈ U.2.fromSpec ⁻¹ᵁ (U : X.Opens) := by
      rw [U.2.fromSpec_preimage_self]; trivial
    exact hz
  refine ⟨U.2.fromSpec z, ⟨?_⟩⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk (U.2.fromSpec z)) :=
    X.presheaf.algebra_section_stalk ⟨U.2.fromSpec z, hx⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec z)) z.asIdeal :=
    U.2.isLocalization_stalk' z hx
  exact ((IsLocalization.algEquiv z.asIdeal.primeCompl (Localization.AtPrime z.asIdeal)
    (X.presheaf.stalk (U.2.fromSpec z))).toRingEquiv).symm

/-- Normality of the ring of sections on every affine open gives Serre's conditions `(S₂)` and
`(R₁)` for the scheme. -/
private lemma serreConditions_of_forall_affineOpen_isNormalRing (X : Scheme.{u})
    [IsLocallyNoetherian X] (h : ∀ U : X.affineOpens, IsNormalRing Γ(X, U)) :
    HasPropertySk X 2 ∧ IsRegularInCodimension X 1 := by
  have key : ∀ x : X,
      (min ((2 : ℕ) : WithBot ℕ∞) (ringKrullDim (X.presheaf.stalk x)) ≤
          (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) : WithBot ℕ∞)) ∧
        (ringKrullDim (X.presheaf.stalk x) ≤ ((1 : ℕ) : WithBot ℕ∞) →
          IsRegularLocalRing (X.presheaf.stalk x)) := by
    intro x
    obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.val := by
      rw [← TopologicalSpace.Opens.mem_iSup, iSup_affineOpens_eq_top]; trivial
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨e⟩ := nonempty_ringEquiv_stalk_localization U hxU
    obtain ⟨hR, hS⟩ :=
      isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp
        (isNormalRing_iff.mp (h U))
    constructor
    · refine (min_le_depth_iff_of_ringEquiv e ((2 : ℕ) : WithBot ℕ∞)).mpr ?_
      simpa only [Nat.cast_ofNat] using hS (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
    · refine (isRegularLocalRing_of_le_iff_of_ringEquiv e ((1 : ℕ) : WithBot ℕ∞)).mpr ?_
      intro hdim
      refine hR (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal ?_
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
        (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)] at hdim
      exact_mod_cast hdim
  exact ⟨(hasPropertySk_iff X 2).mpr fun x ↦ (key x).1, fun x ↦ (key x).2⟩

/-- Serre's conditions `(S₂)` and `(R₁)` for a scheme give normality of the ring of sections on
every affine open. -/
private lemma forall_affineOpen_isNormalRing_of_serreConditions (X : Scheme.{u})
    [IsLocallyNoetherian X] (hS : HasPropertySk X 2) (hR : IsRegularInCodimension X 1) :
    ∀ U : X.affineOpens, IsNormalRing Γ(X, U) := by
  intro U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  refine isNormalRing_iff.mpr
    (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mpr
      ⟨?_, ?_⟩)
  · intro p hp hheight
    let : p.IsPrime := hp
    obtain ⟨x, ⟨e⟩⟩ := exists_nonempty_ringEquiv_localization U ⟨p, hp⟩
    refine (isRegularLocalRing_of_le_iff_of_ringEquiv e ((1 : ℕ) : WithBot ℕ∞)).mp (hR x) ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
    exact_mod_cast hheight
  · intro p hp
    let : p.IsPrime := hp
    obtain ⟨x, ⟨e⟩⟩ := exists_nonempty_ringEquiv_localization U ⟨p, hp⟩
    simpa only [Nat.cast_ofNat] using
      (min_le_depth_iff_of_ringEquiv e ((2 : ℕ) : WithBot ℕ∞)).mp ((hasPropertySk_iff X 2).mp hS x)

/-- **Serre's criterion for normality, Stacks Project, Tag 0345.** A locally Noetherian scheme is
normal if and only if it satisfies Serre's condition `(S₂)` and is regular in codimension one. -/
@[stacks 0345, ega "II 7.3.7" "partial", ega "IV 5.8.6", ega "IV 7.3.9"]
public theorem isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one (X : Scheme.{u})
    [IsLocallyNoetherian X] :
    IsNormal X ↔ HasPropertySk X 2 ∧ IsRegularInCodimension X 1 := by
  rw [(isNormal_tfae X).out 1 2 rfl rfl]
  exact ⟨serreConditions_of_forall_affineOpen_isNormalRing X,
    fun h ↦ forall_affineOpen_isNormalRing_of_serreConditions X h.1 h.2⟩

end Normality

end AlgebraicGeometry

end
