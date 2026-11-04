module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.Topology.Jacobson.OpenCover

/-!
# Jacobson schemes

A scheme is Jacobson when its underlying topological space is, that is, when the closed points
of every closed subset are dense in it. This file proves that this is a condition that can be
read off from the rings of sections over affine opens: being a Jacobson ring is a *local*
property of rings, so the five conditions of Tag 01P4 agree, and the property passes to open
subschemes.

## Main results

* `CommRing.isJacobsonRing_propertyIsLocal`: being a Jacobson ring is a local property of
  commutative rings.
* `AlgebraicGeometry.IsAffineOpen.jacobsonSpace_iff`: an affine open of a scheme is a Jacobson
  space precisely when its ring of sections is a Jacobson ring. This is Tag 01P3 for an affine
  open rather than for an affine scheme.
* `AlgebraicGeometry.jacobsonSpace_tfae`: the five equivalent conditions of Tag 01P4.
* `AlgebraicGeometry.jacobsonSpace_open`: every open subscheme of a Jacobson scheme is Jacobson,
  the final assertion of Tag 01P4.

## Implementation notes

"Locally Jacobson" in the sense of Definition 01OQ is `AlgebraicGeometry.IsLocally` applied to
`IsJacobsonRing`, and conditions (2), (3) and (4) of Tag 01P4 are the corresponding conditions
of Tag 01OR for that property.

## References

* [Stacks Project, Tag 01P3](https://stacks.math.columbia.edu/tag/01P3)
* [Stacks Project, Tag 01P4](https://stacks.math.columbia.edu/tag/01P4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace CommRing

/-- Being a Jacobson ring is a local property of commutative rings: it passes to the localization
away from an element, and a ring is Jacobson as soon as its localizations away from a family of
elements generating the unit ideal are. -/
theorem isJacobsonRing_propertyIsLocal :
    PropertyIsLocal (fun (R : Type u) [CommRing R] => IsJacobsonRing R) where
  localizationAwayPreserves {R} _ f S _ _ _ hR :=
    have : IsJacobsonRing R := hR
    isJacobsonRing_localization f
  ofLocalizationSpan {R} _ ι _ f hspan hloc := by
    rw [PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace]
    have hcover : IsOpenCover fun i ↦ PrimeSpectrum.basicOpen (f i) :=
      PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan
    refine (jacobsonSpace_iff_of_isOpenCover hcover).mpr fun i ↦ ?_
    have : IsJacobsonRing (Localization.Away (f i)) := hloc i
    have hemb : Topology.IsOpenEmbedding
        (PrimeSpectrum.comap (algebraMap R (Localization.Away (f i)))) :=
      PrimeSpectrum.localization_away_isOpenEmbedding _ (f i)
    exact JacobsonSpace.of_isOpenEmbedding
      (hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr
        (PrimeSpectrum.localization_away_comap_range _ (f i)))).symm.isOpenEmbedding

end CommRing

namespace AlgebraicGeometry

/-- An affine open `U` of a scheme is a Jacobson topological space if and only if the ring
`Γ(X, U)` is a Jacobson ring. -/
@[ega "IV 10.4.1" "more general", ega "IV 10.4.2" "special case"]
theorem IsAffineOpen.jacobsonSpace_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    JacobsonSpace U.toScheme ↔ IsJacobsonRing Γ(X, U) := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have : JacobsonSpace (Spec Γ(X, U)) :=
      JacobsonSpace.of_isOpenEmbedding (Scheme.homeoOfIso hU.isoSpec).symm.isOpenEmbedding
    exact PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr this
  · have : JacobsonSpace (Spec Γ(X, U)) := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp h
    exact JacobsonSpace.of_isOpenEmbedding (Scheme.homeoOfIso hU.isoSpec).isOpenEmbedding

/-- An open subscheme of a Jacobson scheme is Jacobson. -/
private theorem jacobsonSpace_toScheme_of_jacobsonSpace {X : Scheme.{u}} [JacobsonSpace X]
    (U : X.Opens) : JacobsonSpace U.toScheme :=
  JacobsonSpace.of_isOpenEmbedding (X := U.toScheme) U.ι.isOpenEmbedding

/-- For a scheme `X` the following are equivalent: `X` is a Jacobson space; `X` is locally
Jacobson in the sense of Definition 01OQ; the ring of sections over every affine open of `X` is
Jacobson; there is an affine open covering of `X` whose rings of sections are Jacobson; there is
an open covering of `X` by Jacobson open subschemes. -/
@[stacks 01P4 "the equivalence of the five conditions (1)–(5)",
  ega "IV 10.3.3" "sufficiency",
  ega "IV 10.4.2"]
theorem jacobsonSpace_tfae (X : Scheme.{u}) :
    List.TFAE [
      JacobsonSpace X,
      IsLocally (fun (R : Type u) [CommRing R] => IsJacobsonRing R) X,
      ∀ U : X.affineOpens, IsJacobsonRing Γ(X, (U : X.Opens)),
      ∃ (I : Type u) (U : I → X.affineOpens),
        IsOpenCover (fun i ↦ (U i : X.Opens)) ∧
          ∀ i, IsJacobsonRing Γ(X, (U i : X.Opens)),
      ∃ (I : Type u) (U : I → X.Opens),
        IsOpenCover U ∧ ∀ i, JacobsonSpace (U i).toScheme] := by
  tfae_have 2 ↔ 3 := isLocally_iff_forall_affineOpens CommRing.isJacobsonRing_propertyIsLocal X
  tfae_have 2 ↔ 4 :=
    isLocally_iff_exists_affineOpenCover (fun (R : Type u) [CommRing R] => IsJacobsonRing R) X
  tfae_have 1 → 3 := by
    intro h U
    exact U.2.jacobsonSpace_iff.mp (jacobsonSpace_toScheme_of_jacobsonSpace (U : X.Opens))
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hcover, hU⟩
    exact (jacobsonSpace_iff_of_isOpenCover hcover).mpr fun i ↦ (U i).2.jacobsonSpace_iff.mpr (hU i)
  tfae_have 1 → 5 := by
    intro h
    exact ⟨PUnit, fun _ ↦ ⊤, by simp [IsOpenCover],
      fun _ ↦ jacobsonSpace_toScheme_of_jacobsonSpace _⟩
  tfae_have 5 → 1 := by
    rintro ⟨I, U, hcover, hU⟩
    exact (jacobsonSpace_iff_of_isOpenCover hcover).mpr hU
  tfae_finish

/-- Every open subscheme of a Jacobson scheme is Jacobson. -/
@[stacks 01P4 "the final assertion: every open subscheme of a Jacobson scheme is Jacobson",
  ega "IV 10.4.3" "Open subpreschemes"]
theorem jacobsonSpace_open {X : Scheme.{u}} (hX : JacobsonSpace X) (U : X.Opens) :
    JacobsonSpace U.toScheme :=
  have : JacobsonSpace X := hX
  jacobsonSpace_toScheme_of_jacobsonSpace U

end AlgebraicGeometry

add_to_stacks 01P4 "jacobson_open_subscheme" JacobsonSpace.of_isOpenEmbedding
add_to_ega "IV 10.3.2" "special case" JacobsonSpace.of_isOpenEmbedding
add_to_ega "IV 10.3.3" "necessity" JacobsonSpace.of_isOpenEmbedding
add_to_ega "IV 10.4.3" "Open subpreschemes" JacobsonSpace.of_isOpenEmbedding
add_to_ega "IV 10.4.7" "open immersions" JacobsonSpace.of_isOpenEmbedding

end
