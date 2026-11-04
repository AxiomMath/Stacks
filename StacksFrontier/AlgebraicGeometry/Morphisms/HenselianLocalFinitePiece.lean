module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.QuasiFiniteLocalPiece
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite piece of a quasi-finite morphism over a henselian local scheme

Let `R` be a henselian local ring and `f : X ⟶ Spec R` a morphism of schemes which is locally
of finite type and locally quasi-finite, and let `x` be a point of `X` over the closed point.
Then `x` has an open neighbourhood `U` such that `U ⟶ Spec R` is finite and `x` is the only
point of `U` over the closed point. This is the step of the proof of Stacks 0CVB which applies
Stacks 02LK over the strictly henselian base `Spec 𝒪_{Y, ȳ}`: over a henselian local base no
étale base change is needed.

## Main results

* `AlgebraicGeometry.exists_isFinite_forall_eq_of_locallyQuasiFinite`: the neighbourhood, for a
  morphism locally of finite type and locally quasi-finite.
* `AlgebraicGeometry.exists_isFinite_forall_eq_of_opens`: the same, when only the restriction to
  an open neighbourhood of `x` is locally of finite type and locally quasi-finite.

## Implementation notes

The neighbourhood is `D(h)` inside an affine open `Spec Γ(X, V)` around `x`, for the idempotent
`h` of `exists_isIdempotentElem_finite_forall_eq_of_quasiFiniteAt`; it is the open range of
`Spec Γ(X, V)_h ⟶ X`, whose composite to `Spec R` is the spectrum of the finite ring map
`R → Γ(X, V)_h`.

## References

* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

/-- Quasi-finiteness of a ring map at a prime is quasi-finiteness of its composite with the
localization at that prime. -/
theorem RingHom.quasiFiniteAt_iff_quasiFinite_comp {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : Ideal B) [p.IsPrime] :
    φ.QuasiFiniteAt p ↔ ((algebraMap B (Localization.AtPrime p)).comp φ).QuasiFinite := by
  let := φ.toAlgebra
  show Algebra.QuasiFinite A (Localization.AtPrime p) ↔ _
  rw [← RingHom.quasiFinite_algebraMap,
    IsScalarTower.algebraMap_eq A B (Localization.AtPrime p), RingHom.algebraMap_toAlgebra]

/-- Quasi-finiteness of a ring map at a prime is unchanged by precomposition with a ring
isomorphism. -/
theorem RingHom.QuasiFiniteAt.comp_ringEquiv {A A' B : Type*} [CommRing A] [CommRing A']
    [CommRing B] {φ : A →+* B} {p : Ideal B} [p.IsPrime] (hφ : φ.QuasiFiniteAt p)
    (e : A' ≃+* A) : (φ.comp (e : A' →+* A)).QuasiFiniteAt p := by
  rw [RingHom.quasiFiniteAt_iff_quasiFinite_comp] at hφ ⊢
  rw [← RingHom.comp_assoc]
  exact hφ.comp (RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ e.surjective))

namespace AlgebraicGeometry

/-- Evaluating a composite of morphisms of schemes at a point, from an equation of morphisms. -/
theorem Scheme.Hom.apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (h : a ≫ b = c) (x : X) : b (a x) = c x := by
  rw [← h, Scheme.Hom.comp_apply]

/-- A point lies in the open range of `Spec Γ(X, V)_h ⟶ X` iff it comes from a prime of
`Γ(X, V)` not containing `h`. -/
private theorem IsAffineOpen.mem_opensRange_specAway_fromSpec_iff {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (h : Γ(X, V)) (u : X) :
    u ∈ (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) (Localization.Away h))) ≫
        hV.fromSpec).opensRange ↔
      ∃ p : Spec Γ(X, V), h ∉ p.asIdeal ∧ hV.fromSpec p = u := by
  rw [Scheme.Hom.mem_opensRange]
  have key := PrimeSpectrum.localization_away_comap_range (Localization.Away h) h
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) (Localization.Away h))) z,
      key.subset ⟨z, rfl⟩, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ := key.symm.subset hp
    exact ⟨z, (Scheme.Hom.comp_apply _ _ _).trans (congrArg hV.fromSpec hz)⟩

/-- Precomposing with an isomorphism does not change whether a morphism is finite. -/
private theorem isFinite_iso_hom_comp_iff {X Y Z : Scheme.{u}} (e : X ≅ Y) (g : Y ⟶ Z) :
    IsFinite (e.hom ≫ g) ↔ IsFinite g := by
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact MorphismProperty.cancel_left_of_respectsIso @IsFinite e.hom g

/-- **A finite piece of a quasi-finite morphism over a henselian local scheme.** Let `R` be a
henselian local ring and `f : X ⟶ Spec R` locally of finite type and locally quasi-finite. A point
`x` of `X` over the closed point has an open neighbourhood `U` finite over `Spec R` in which `x`
is the only point over the closed point. -/
@[ega "IV 18.5.11" "a ⇒ c, a ⇒ c′"]
theorem exists_isFinite_forall_eq_of_locallyQuasiFinite {R : CommRingCat.{u}}
    [HenselianLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (x : X) (hx : f x = closedPoint R) :
    ∃ U : X.Opens, x ∈ U ∧ IsFinite (U.ι ≫ f) ∧
      ∀ u : X, u ∈ U → f u = closedPoint R → u = x := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV : IsAffineOpen V := hV
  set ψ : R ⟶ Γ(X, V) := (Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ V le_top with hψ
  have hSpec : Spec.map ψ = hV.fromSpec ≫ f := by
    rw [hψ, Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV
      le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  let : Algebra R Γ(X, V) := ψ.hom.toAlgebra
  -- `Γ(X, V)` is of finite type over `R`.
  have hft : Algebra.FiniteType R Γ(X, V) :=
    (f.finiteType_appLE (isAffineOpen_top _) hV (le_top : V ≤ f ⁻¹ᵁ ⊤)).comp
      (_root_.RingHom.FiniteType.of_surjective ((Scheme.ΓSpecIso R).inv.hom)
        (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.surjective)
  -- The prime of `x` lies over the maximal ideal.
  have hliesOver : ∀ p : Spec Γ(X, V), f (hV.fromSpec p) = closedPoint R →
      p.asIdeal.LiesOver (maximalIdeal R) := fun p hp =>
    ⟨(congrArg PrimeSpectrum.asIdeal (show Spec.map ψ p = closedPoint R from
      (Scheme.Hom.apply_eq_of_comp_eq hSpec.symm p).symm.trans hp)).symm⟩
  set q := hV.primeIdealOf ⟨x, hxV⟩
  have hqx : hV.fromSpec q = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have : q.asIdeal.LiesOver (maximalIdeal R) := hliesOver q (by rw [hqx, hx])
  have : Algebra.QuasiFiniteAt R q.asIdeal := by
    have h : (f.appLE ⊤ V le_top).hom.QuasiFiniteAt q.asIdeal :=
      (f.quasiFiniteAt x).quasiFiniteAt hV (isAffineOpen_top _) le_top hxV
    exact _root_.RingHom.QuasiFiniteAt.comp_ringEquiv h
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  obtain ⟨h, -, hhq, hfin, huniq⟩ :=
    exists_isIdempotentElem_finite_forall_eq_of_quasiFiniteAt R Γ(X, V) q.asIdeal
  -- The open piece `D(h)`, as the open range of `Spec Γ(X, V)_h ⟶ X`.
  set ι : Spec (CommRingCat.of (Localization.Away h)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) (Localization.Away h))) ≫ hV.fromSpec
    with hι
  refine ⟨ι.opensRange, (hV.mem_opensRange_specAway_fromSpec_iff h x).2 ⟨q, hhq, hqx⟩, ?_, ?_⟩
  · -- finiteness
    rw [← isFinite_iso_hom_comp_iff (Scheme.Hom.isoOpensRange ι),
      ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hι, Category.assoc, ← hSpec,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
    exact _root_.RingHom.finite_algebraMap.mpr hfin
  · -- uniqueness
    intro u hu hfu
    obtain ⟨p, hp, rfl⟩ := (hV.mem_opensRange_specAway_fromSpec_iff h u).1 hu
    rw [PrimeSpectrum.ext (huniq p.asIdeal p.isPrime (hliesOver p hfu) hp), hqx]

/-- **A finite piece of a morphism over a henselian local scheme, quasi-finite near a point.** Let
`R` be a henselian local ring, `f : X ⟶ Spec R` a morphism of schemes and `x` a point of `X` over
the closed point having an open neighbourhood `W` on which `f` is locally of finite type and
locally quasi-finite. Then `x` has an open neighbourhood `U ≤ W` finite over `Spec R` in which `x`
is the only point over the closed point. -/
@[ega "IV 18.5.11" "a ⇒ c, a ⇒ c′"]
theorem exists_isFinite_forall_eq_of_opens {R : CommRingCat.{u}} [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) (x : X) (hx : f x = closedPoint R) (W : X.Opens)
    (hxW : x ∈ W) [LocallyOfFiniteType (W.ι ≫ f)] [LocallyQuasiFinite (W.ι ≫ f)] :
    ∃ U : X.Opens, x ∈ U ∧ IsFinite (U.ι ≫ f) ∧
      ∀ u : X, u ∈ U → f u = closedPoint R → u = x := by
  obtain ⟨U', hxU', hfin, huniq⟩ :=
    exists_isFinite_forall_eq_of_locallyQuasiFinite (W.ι ≫ f) ⟨x, hxW⟩ hx
  refine ⟨W.ι ''ᵁ U', ⟨⟨x, hxW⟩, hxU', rfl⟩, ?_, ?_⟩
  · rwa [← isFinite_iso_hom_comp_iff (Scheme.Hom.isoImage W.ι U'),
      ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
  · rintro u ⟨u', hu', rfl⟩ hfu
    rw [huniq u' hu' (by rwa [Scheme.Hom.comp_apply])]
    rfl

end AlgebraicGeometry

end
