module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs

/-!
# Formal smoothness against a class of test objects

A transformation of set-valued functors on the big fppf site of a scheme is formally smooth when
it lifts across every square-zero closed immersion `T ⟶ T'` of affine test objects
(`AlgebraicGeometry.Space.FormallySmooth`). This file records the same lifting condition when
the larger test object `T'` is only required to lie in a prescribed class, and the class of
spectra of local rings with nilpotent maximal ideal — the spectra of Artinian local rings among
them — which is the class deformation theory tests against.

## Main definitions

* `AlgebraicGeometry.Space.FormallySmoothOn` is the lifting condition of
  `AlgebraicGeometry.Space.FormallySmooth` for those lifting problems whose larger test object
  satisfies a given predicate.
* `AlgebraicGeometry.Space.HasLocalNilpotentSections` is the predicate on an object of the big
  fppf site that its ring of global sections is a local ring with nilpotent maximal ideal.
* `AlgebraicGeometry.Space.HasFiniteLocalNilpotentSections` is the predicate that its ring of
  global sections is finite over a local ring with nilpotent maximal ideal.

## Main results

* `AlgebraicGeometry.Space.FormallySmooth.formallySmoothOn`: formal smoothness gives the lifting
  condition against every class of test objects.
* `AlgebraicGeometry.Space.formallySmoothOn_true_iff`: against the class of all objects the
  lifting condition is formal smoothness.
* `AlgebraicGeometry.Space.hasLocalNilpotentSections_of_iso_spec_isArtinianRing`: the spectrum of
  an Artinian local ring lies in the class of test objects with local nilpotent sections.

## References

* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The lifting condition of `AlgebraicGeometry.Space.FormallySmooth` for the lifting problems
along a square-zero closed immersion `T ⟶ T'` of affine objects whose larger object `T'`
satisfies `P`. -/
abbrev FormallySmoothOn (P : BigFppfOver B S hS → Prop)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) : Prop :=
  ∀ (T T' : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj T') → P T' → ∀ (i : T ⟶ T'),
      IsSquareZeroClosedImmersion B S hS i → ∀ (x : F.obj (op T)) (y : G.obj (op T')),
        a.app (op T) x = G.map i.op y → ∃ z : F.obj (op T'), IsLift a i x y z

/-- A formally smooth transformation satisfies the lifting condition against every class of test
objects. -/
theorem FormallySmooth.formallySmoothOn {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {a : F ⟶ G}
    (h : FormallySmooth a) (P : BigFppfOver B S hS → Prop) : FormallySmoothOn P a :=
  fun T T' hT hT' _ i hi x y hxy => h T T' hT hT' i hi x y hxy

/-- Against the class of all objects the lifting condition is formal smoothness. -/
theorem formallySmoothOn_true_iff {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) :
    FormallySmoothOn (fun _ => True) a ↔ FormallySmooth a :=
  ⟨fun h T T' hT hT' i hi x y hxy => h T T' hT hT' trivial i hi x y hxy,
    fun h => h.formallySmoothOn _⟩

variable (B S hS) in
/-- The ring of global sections of an object of the big fppf site over `S` is a local ring with
nilpotent maximal ideal. For an affine object this says it is the spectrum of such a ring, the
spectrum of an Artinian local ring for instance. -/
abbrev HasLocalNilpotentSections (T : BigFppfOver B S hS) : Prop :=
  ∃ _ : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤),
    IsNilpotent (IsLocalRing.maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))

variable (B S hS) in
/-- An object of the site whose underlying scheme is the spectrum of a local ring with nilpotent
maximal ideal has local global sections with nilpotent maximal ideal. -/
theorem hasLocalNilpotentSections_of_iso (T : BigFppfOver B S hS) {R : Type u} [CommRing R]
    [IsLocalRing R] (hnil : IsNilpotent (IsLocalRing.maximalIdeal R))
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of R)) :
    HasLocalNilpotentSections B S hS T := by
  let φ : R ≃+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).symm ≪≫ Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := φ.symm.surjective.nontrivial
  have hloc : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    IsLocalRing.of_surjective' φ.toRingHom φ.surjective
  refine ⟨hloc, ?_⟩
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  have hle : IsLocalRing.maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ≤
      (IsLocalRing.maximalIdeal R).map φ := fun a ha => by
    have hmem : φ.symm a ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (by simpa using hu.map φ)
    simpa using Ideal.mem_map_of_mem φ hmem
  calc IsLocalRing.maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) ^ n
      ≤ ((IsLocalRing.maximalIdeal R).map φ) ^ n := Ideal.pow_right_mono hle n
    _ = ((IsLocalRing.maximalIdeal R) ^ n).map φ := (Ideal.map_pow _ _ _).symm
    _ ≤ ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

variable (B S hS) in
/-- An object of the site whose underlying scheme is the spectrum of an Artinian local ring has
local global sections with nilpotent maximal ideal. -/
theorem hasLocalNilpotentSections_of_iso_spec_isArtinianRing (T : BigFppfOver B S hS)
    {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of R)) :
    HasLocalNilpotentSections B S hS T :=
  hasLocalNilpotentSections_of_iso B S hS T
    (by simpa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] using
      IsArtinianRing.isNilpotent_jacobson_bot (R := R)) e

/-- Shrinking the class of test objects preserves the lifting condition. -/
theorem FormallySmoothOn.mono {P Q : BigFppfOver B S hS → Prop} (hPQ : ∀ T, P T → Q T)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} {a : F ⟶ G} (h : FormallySmoothOn Q a) :
    FormallySmoothOn P a :=
  fun T T' hT hT' hP i hi x y hxy => h T T' hT hT' (hPQ T' hP) i hi x y hxy

variable (B S hS) in
/-- The predicate on an object of the big fppf site that its ring of global sections is a finite
algebra over a local ring with nilpotent maximal ideal: for an affine object, that it is the
spectrum of a finite algebra over an Artinian local ring, for instance. Such an object need not
be local; this is the class of test objects of the Rim–Schlessinger condition for algebraic
stacks, where pushouts of spectra of Artinian local rings are taken along finite maps. -/
abbrev HasFiniteLocalNilpotentSections (T : BigFppfOver B S hS) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
    (_ : Algebra R Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
    IsNilpotent (IsLocalRing.maximalIdeal R) ∧
      Module.Finite R Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)

/-- Local global sections with nilpotent maximal ideal are finite over themselves. -/
theorem HasLocalNilpotentSections.hasFiniteLocalNilpotentSections {T : BigFppfOver B S hS}
    (h : HasLocalNilpotentSections B S hS T) : HasFiniteLocalNilpotentSections B S hS T := by
  obtain ⟨hloc, hnil⟩ := h
  exact ⟨_, inferInstance, hloc, inferInstance, hnil, inferInstance⟩

end AlgebraicGeometry.Space

end
