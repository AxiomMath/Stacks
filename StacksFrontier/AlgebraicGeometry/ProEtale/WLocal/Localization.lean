module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.SpectralComap

/-!
# Localization along a locally closed affine subscheme

For a locally closed subset `D(f) ∩ V(I)` of an affine spectrum, we localize at the elements
that become units on its coordinate ring. The resulting affine scheme contains the locally
closed subscheme as a closed subscheme, and the localization is canonical under maps
preserving the locally closed subsets.

## Main definitions

* `AlgebraicGeometry.ProEtale.locallyClosedPoints` is the subset `D(f) ∩ V(I)`.
* `AlgebraicGeometry.ProEtale.localizationSubmonoid` consists of the elements of `A`
  invertible in `(A ⧸ I)₍f₎`.
* `AlgebraicGeometry.ProEtale.localizationRing` is the localization of `A` at this submonoid.
* `AlgebraicGeometry.ProEtale.localizationToCoordinateRing` and
  `AlgebraicGeometry.ProEtale.localizationMap` are the canonical maps to the coordinate ring
  and under change of base.

## Main results

* `AlgebraicGeometry.ProEtale.locallyClosedCoordinateMap_range` identifies the image of the
  spectrum of the coordinate ring with `D(f) ∩ V(I)`.
* `AlgebraicGeometry.ProEtale.localization_comap_range` describes the points of the
  localization.
* `AlgebraicGeometry.ProEtale.localizationSubmonoid_eq_of_locallyClosedPoints_eq` proves
  dependence only on the underlying locally closed subset.
* `AlgebraicGeometry.ProEtale.localizationToCoordinateRing_isClosedImmersion` places the
  original subscheme as a closed subscheme of the localization.
* `AlgebraicGeometry.ProEtale.localizationMap_unique` is the canonical and unique map under
  base change.

## Implementation notes

The coordinate ring of `D(f) ∩ V(I)` is `Localization.Away (Ideal.Quotient.mk I f)`. The
selected submonoid is the inverse image of its units. In part (1), the homeomorphism is
expressed by the standard embedding of a localization's prime spectrum together with its
specified range. Equality of selected submonoids in part (2) is stronger than, and gives a
canonical form of, dependence of the localized algebra only on the underlying subset. Part (3)
is expressed as the closed immersion of affine schemes induced by the canonical ring map. The
last part is the universal property characterizing the map of localizations.

Specialization of points is Mathlib's `Specializes`, which is membership in the closure of a
singleton by `specializes_iff_mem_closure`.

## References

* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

universe u

variable {A : Type u} [CommRing A]

/-- The underlying points of the locally closed subscheme `D(f) ∩ V(I)`. -/
def locallyClosedPoints (I : Ideal A) (f : A) : Set (PrimeSpectrum A) :=
  {p | I ≤ p.asIdeal ∧ f ∉ p.asIdeal}

/-- The coordinate ring of `D(f) ∩ V(I)`. -/
abbrev locallyClosedCoordinateRing (I : Ideal A) (f : A) : Type u :=
  Localization.Away (Ideal.Quotient.mk I f)

/-- The canonical map from `A` to the coordinate ring of `D(f) ∩ V(I)`. -/
def locallyClosedCoordinateMap (I : Ideal A) (f : A) :
    A →+* locallyClosedCoordinateRing I f :=
  (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f)).comp (Ideal.Quotient.mk I)

/-- The multiplicative set of elements invertible on `D(f) ∩ V(I)`. -/
def localizationSubmonoid (I : Ideal A) (f : A) : Submonoid A :=
  (IsUnit.submonoid (locallyClosedCoordinateRing I f)).comap
    (locallyClosedCoordinateMap I f)

/-- The canonical ring localized along `D(f) ∩ V(I)`. -/
abbrev localizationRing (I : Ideal A) (f : A) : Type u :=
  Localization (localizationSubmonoid I f)

/-- The canonical map from the localized ring to the coordinate ring of the locally closed
subscheme. -/
def localizationToCoordinateRing (I : Ideal A) (f : A) :
    localizationRing I f →+* locallyClosedCoordinateRing I f :=
  IsLocalization.lift (M := localizationSubmonoid I f)
    (g := locallyClosedCoordinateMap I f) (fun s => s.property)

/-- An element of a commutative ring is a unit exactly when it avoids every prime ideal. -/
private theorem isUnit_iff_forall_prime_not_mem {R : Type*} [CommRing R] (x : R) :
    IsUnit x ↔ ∀ p : PrimeSpectrum R, x ∉ p.asIdeal := by
  constructor
  · intro hx p hxp
    exact p.2.ne_top (p.asIdeal.eq_top_of_isUnit_mem hxp hx)
  · intro hx
    apply PrimeSpectrum.basicOpen_eq_top_iff_isUnit.mp
    apply SetLike.coe_injective
    ext p
    simp [hx p]

/-- A prime of the coordinate ring of `D(f) ∩ V(I)` contracts to a point of `D(f) ∩ V(I)`. -/
private theorem locallyClosedCoordinateMap_comap_mem (I : Ideal A) (f : A)
    (q : PrimeSpectrum (locallyClosedCoordinateRing I f)) :
    PrimeSpectrum.comap (locallyClosedCoordinateMap I f) q ∈ locallyClosedPoints I f := by
  constructor
  · intro x hx
    show locallyClosedCoordinateMap I f x ∈ q.asIdeal
    simp [locallyClosedCoordinateMap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  · exact (isUnit_iff_forall_prime_not_mem _).mp
      (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I f)) q

/-- The spectrum of the coordinate ring of `D(f) ∩ V(I)` has image exactly `D(f) ∩ V(I)`. -/
theorem locallyClosedCoordinateMap_range (I : Ideal A) (f : A) :
    Set.range (PrimeSpectrum.comap (locallyClosedCoordinateMap I f)) =
      locallyClosedPoints I f := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact locallyClosedCoordinateMap_comap_mem I f q
  · intro hp
    let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
    have hp' : p ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
      simpa [PrimeSpectrum.mem_zeroLocus] using hp.1
    let q₀ : PrimeSpectrum (A ⧸ I) := e.symm ⟨p, hp'⟩
    have hback : PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀ = p :=
      congrArg Subtype.val (e.apply_symm_apply ⟨p, hp'⟩)
    have hq₀ : q₀ ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f) := by
      show Ideal.Quotient.mk I f ∉ q₀.asIdeal
      intro hfq
      have hf' : f ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk I) q₀).asIdeal := hfq
      exact hp.2 (by simpa [hback] using hf')
    let : IsLocalization.Away (Ideal.Quotient.mk I f) (locallyClosedCoordinateRing I f) :=
      inferInstance
    have hq₀range : q₀ ∈ Set.range
        (PrimeSpectrum.comap
          (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f))) := by
      rwa [PrimeSpectrum.localization_away_comap_range
        (locallyClosedCoordinateRing I f) (Ideal.Quotient.mk I f)]
    obtain ⟨q, hq⟩ := hq₀range
    refine ⟨q, ?_⟩
    show PrimeSpectrum.comap
      ((algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f)).comp
        (Ideal.Quotient.mk I)) q = p
    rw [PrimeSpectrum.comap_comp_apply, hq, hback]

/-- The selected multiplicative set consists of the elements vanishing at no point of
`D(f) ∩ V(I)`. -/
private theorem localizationSubmonoid_mem_iff (I : Ideal A) (f a : A) :
    a ∈ localizationSubmonoid I f ↔
      ∀ p ∈ locallyClosedPoints I f, a ∉ p.asIdeal := by
  show IsUnit (locallyClosedCoordinateMap I f a) ↔ _
  rw [isUnit_iff_forall_prime_not_mem]
  constructor
  · intro ha p hp
    rw [← locallyClosedCoordinateMap_range] at hp
    obtain ⟨q, rfl⟩ := hp
    exact ha q
  · intro ha q
    exact ha _ (locallyClosedCoordinateMap_comap_mem I f q)

-- The spectrum of the selected localization is embedded in `Spec A`.
add_to_stacks 096V "part (1): embedding" PrimeSpectrum.localization_comap_isEmbedding
add_to_ega "I 1.2.4" "localization R → M⁻¹R" PrimeSpectrum.localization_comap_isEmbedding
add_to_ega "I 1.6.2" "partial" PrimeSpectrum.localization_comap_isEmbedding
add_to_ega "I 2.4.2" "topological embedding" PrimeSpectrum.localization_comap_isEmbedding
add_to_ega "IV 10.7.3" "partial" PrimeSpectrum.localization_comap_isEmbedding

/-- The points of the localization are precisely those specializing to
`D(f) ∩ V(I)`. -/
@[stacks 096V "part (1): image"]
theorem localization_comap_range (I : Ideal A) (f : A) :
    Set.range (PrimeSpectrum.comap (algebraMap A (localizationRing I f))) =
      {p | ∃ q ∈ locallyClosedPoints I f, p ⤳ q} := by
  rw [PrimeSpectrum.localization_comap_range (localizationRing I f)
    (localizationSubmonoid I f)]
  ext p
  constructor
  · intro hdisj
    let : IsLocalization.Away (Ideal.Quotient.mk I f) (locallyClosedCoordinateRing I f) :=
      inferInstance
    let pbar : Ideal (A ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
    let P : Ideal (locallyClosedCoordinateRing I f) :=
      pbar.map (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f))
    have hP : P ≠ ⊤ := by
      intro htop
      have hone : (1 : locallyClosedCoordinateRing I f) ∈ P := by
        rw [htop]
        simp
      obtain ⟨w, hs⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (locallyClosedCoordinateRing I f)
          (M := Submonoid.powers (Ideal.Quotient.mk I f))).mp hone
      obtain ⟨y, hyp, hyx⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
          Ideal.Quotient.mk_surjective).mp w.1.2
      have hyS : y ∈ localizationSubmonoid I f := by
        show IsUnit (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f)
          (Ideal.Quotient.mk I y))
        rw [hyx, ← hs]
        simpa using IsLocalization.map_units (locallyClosedCoordinateRing I f) w.2
      exact (Set.disjoint_left.mp hdisj) hyS hyp
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP
    let r : PrimeSpectrum (locallyClosedCoordinateRing I f) := ⟨M, hM.isPrime⟩
    let q : PrimeSpectrum A := PrimeSpectrum.comap (locallyClosedCoordinateMap I f) r
    have hq : q ∈ locallyClosedPoints I f := locallyClosedCoordinateMap_comap_mem I f r
    have hpbar : pbar ≤ r.asIdeal.comap
        (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f)) :=
      (Ideal.map_le_iff_le_comap).mp hPM
    have hpq : p.asIdeal ≤
        (r.asIdeal.comap (algebraMap (A ⧸ I) (locallyClosedCoordinateRing I f))).comap
          (Ideal.Quotient.mk I) :=
      (Ideal.map_le_iff_le_comap).mp hpbar
    exact ⟨q, hq, (PrimeSpectrum.le_iff_specializes p q).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal p q).mp hpq)⟩
  · rintro ⟨q, hq, hspec⟩
    apply Set.disjoint_left.mpr
    intro x hxS hxp
    have hpq : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.asIdeal_le_asIdeal p q).mpr
      ((PrimeSpectrum.le_iff_specializes p q).mpr hspec)
    exact (localizationSubmonoid_mem_iff I f x).mp hxS q hq (hpq hxp)

/-- The selected multiplicative subset, hence the localized `A`-algebra, depends only on the
underlying locally closed subset. -/
@[stacks 096V "part (2)"]
theorem localizationSubmonoid_eq_of_locallyClosedPoints_eq
    (I J : Ideal A) (f g : A) (h : locallyClosedPoints I f = locallyClosedPoints J g) :
    localizationSubmonoid I f = localizationSubmonoid J g := by
  ext a
  rw [localizationSubmonoid_mem_iff, localizationSubmonoid_mem_iff]
  simp [h]

/-- The locally closed subscheme is closed in the selected localization. -/
@[stacks 096V "part (3)"]
instance localizationToCoordinateRing_isClosedImmersion
    (I : Ideal A) (f : A) :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (localizationToCoordinateRing I f))) := by
  apply IsClosedImmersion.spec_of_surjective _
  intro z
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk I f) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  let : IsLocalization.Away (Ideal.Quotient.mk I f) (locallyClosedCoordinateRing I f) :=
    inferInstance
  have hfS : f ^ n ∈ localizationSubmonoid I f := by
    change IsUnit (locallyClosedCoordinateMap I f (f ^ n))
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I f)).pow n
  refine ⟨IsLocalization.mk' (localizationRing I f) a ⟨f ^ n, hfS⟩, ?_⟩
  exact (IsLocalization.lift_mk'_spec (fun s => s.property) a z ⟨f ^ n, hfS⟩).2
    (by simpa [locallyClosedCoordinateMap, mul_comm] using hb.symm)

variable {A' : Type u} [CommRing A']

/-- A map taking `D(g) ∩ V(J)` into `D(f) ∩ V(I)` preserves the selected multiplicative
sets. -/
@[stacks 096V "naturality: selected multiplicative sets"]
theorem localizationSubmonoid_le_comap
    (h : A →+* A') (I : Ideal A) (f : A) (J : Ideal A') (g : A')
    (hZ : ∀ q ∈ locallyClosedPoints J g,
      PrimeSpectrum.comap h q ∈ locallyClosedPoints I f) :
    localizationSubmonoid I f ≤ (localizationSubmonoid J g).comap h := by
  intro a ha
  show h a ∈ localizationSubmonoid J g
  rw [localizationSubmonoid_mem_iff]
  intro q hq hqa
  exact (localizationSubmonoid_mem_iff I f a).mp ha _ (hZ q hq) hqa

/-- The canonical map between the localizations under a map preserving the locally closed
subsets. -/
def localizationMap
    (h : A →+* A') (I : Ideal A) (f : A) (J : Ideal A') (g : A')
    (hZ : ∀ q ∈ locallyClosedPoints J g,
      PrimeSpectrum.comap h q ∈ locallyClosedPoints I f) :
    localizationRing I f →+* localizationRing J g :=
  IsLocalization.map (localizationRing J g) h
    (localizationSubmonoid_le_comap h I f J g hZ)

/-- The canonical map is the unique map of `A`-algebras extending `h`. -/
@[stacks 096V "naturality and uniqueness"]
theorem localizationMap_unique
    (h : A →+* A') (I : Ideal A) (f : A) (J : Ideal A') (g : A')
    (hZ : ∀ q ∈ locallyClosedPoints J g,
      PrimeSpectrum.comap h q ∈ locallyClosedPoints I f) :
    ∃! k : localizationRing I f →+* localizationRing J g,
      k.comp (algebraMap A (localizationRing I f)) =
        (algebraMap A' (localizationRing J g)).comp h := by
  refine ⟨localizationMap h I f J g hZ, ?_, ?_⟩
  · simp [localizationMap]
  · intro k hk
    apply IsLocalization.ringHom_ext (localizationSubmonoid I f)
    rw [hk]
    simp [localizationMap]

end AlgebraicGeometry.ProEtale

end
