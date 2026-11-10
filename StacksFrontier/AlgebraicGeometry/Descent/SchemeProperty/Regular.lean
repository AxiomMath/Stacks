module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# Regularity of schemes read on stalks and on global sections

Regularity of a scheme is the conjunction of local Noetherianity with regularity of every
stalk, a condition that can be transported along open immersions and, on an affine scheme,
read off the ring of global sections.

## Main results

* `AlgebraicGeometry.isRegular_iff_regular_stalks`: a scheme is regular exactly when it is
  locally Noetherian with regular local rings at every point.
* `AlgebraicGeometry.isRegular_iff_isRegularRing_appTop`: an affine scheme is regular exactly
  when its ring of global sections is a regular ring.
* `AlgebraicGeometry.isRegular_spec_iff`: the spectrum of a ring is regular exactly when the
  ring is.
* `AlgebraicGeometry.isRegular_isLocal_zariski`: regularity is a Zariski local condition.

## References

* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- A scheme is regular exactly when it is locally Noetherian with regular local rings at every
point. -/
public theorem isRegular_iff_regular_stalks (X : Scheme.{u}) :
    IsRegular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  (isRegular_tfae X).out 1 2

/-- Regularity of a stalk is unchanged by passing along an open immersion. -/
public theorem isRegularLocalRing_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) ↔ IsRegularLocalRing (Y.presheaf.stalk (j x)) :=
  ⟨fun h => @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm,
    fun h => @IsRegularLocalRing.of_ringEquiv _ _ h _ _
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv⟩

/-- An affine scheme is regular exactly when its ring of global sections is a regular ring. -/
public theorem isRegular_iff_isRegularRing_appTop (X : Scheme.{u}) [IsAffine X] :
    IsRegular X ↔ IsRegularRing Γ(X, ⊤) := by
  refine ⟨fun h => ?_, fun h => fun x => ⟨⟨⊤, isAffineOpen_top X⟩, trivial, h⟩⟩
  obtain ⟨hN, hstalk⟩ := (isRegular_iff_regular_stalks X).mp h
  have _ : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  rw [isRegularRing_iff]
  intro p hp
  let x : X := (isAffineOpen_top X).fromSpec ⟨p, hp⟩
  have hx : x ∈ (⊤ : X.Opens) := trivial
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    (isAffineOpen_top X).isLocalization_stalk' ⟨p, hp⟩ hx
  have _ := hstalk x
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv).symm

/-- Regularity of schemes is invariant under isomorphism. -/
public instance isRegular_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => IsRegular X) :=
  ⟨fun e hX => by
    obtain ⟨hN, hstalk⟩ := (isRegular_iff_regular_stalks _).mp hX
    exact (isRegular_iff_regular_stalks _).mpr
      ⟨isLocallyNoetherian_of_isOpenImmersion e.inv, fun y =>
        (isRegularLocalRing_stalk_iff_of_isOpenImmersion e.inv y).mpr (hstalk (e.inv y))⟩⟩

/-- Regularity of schemes is a Zariski local condition. -/
public instance isRegular_isLocal_zariski :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsRegular X) Scheme.zariskiPrecoverage := by
  refine ObjectProperty.IsLocal.mk_of_zeroHypercover fun X 𝒰 => ?_
  have hdata : (∀ x : X, ∃ i, x ∈ Set.range (𝒰.f i).base) ∧
      ∀ i, IsOpenImmersion (𝒰.f i) := by
    simpa [Scheme.zariskiPrecoverage] using 𝒰.mem₀
  have hN := isLocallyNoetherian_iff_openCover (X := X) 𝒰
  refine ⟨fun hX i => ?_, fun h => ?_⟩
  · obtain ⟨hNX, hstalk⟩ := (isRegular_iff_regular_stalks X).mp hX
    have _ : IsOpenImmersion (𝒰.f i) := hdata.2 i
    exact (isRegular_iff_regular_stalks (𝒰.X i)).mpr ⟨hN.mp hNX i, fun z =>
      (isRegularLocalRing_stalk_iff_of_isOpenImmersion (𝒰.f i) z).mpr (hstalk (𝒰.f i z))⟩
  · refine (isRegular_iff_regular_stalks X).mpr
      ⟨hN.mpr fun i => ((isRegular_iff_regular_stalks (𝒰.X i)).mp (h i)).1, fun x => ?_⟩
    obtain ⟨i, z, hz⟩ := hdata.1 x
    have _ : IsOpenImmersion (𝒰.f i) := hdata.2 i
    rw [← hz]
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (𝒰.f i) z).mp
      (((isRegular_iff_regular_stalks (𝒰.X i)).mp (h i)).2 z)

/-- The spectrum of a ring is a regular scheme exactly when the ring is a regular ring. -/
public theorem isRegular_spec_iff (R : Type u) [CommRing R] :
    IsRegular (Spec (.of R)) ↔ IsRegularRing R := by
  refine (isRegular_iff_isRegularRing_appTop (Spec (.of R))).trans ?_
  exact ⟨fun h => IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv,
    fun h => IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm⟩

end AlgebraicGeometry
