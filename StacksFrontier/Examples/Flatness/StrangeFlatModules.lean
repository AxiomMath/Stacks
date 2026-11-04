module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.Pure
public import StacksFrontier.RingTheory.Module.LocallyFree.Basic

/-!
# Strange flat modules

Over a general commutative ring, flatness is much weaker than projectivity, and a flat
closed immersion of schemes need not be an open map.

Both phenomena are exhibited by one example: the ring `R = C^∞(ℝ)` of smooth real functions
and its ideal `I` of functions vanishing on a neighbourhood of the origin. The quotient
`R ⧸ I` is a finite flat `R`-module which is not projective, because `I` is pure but not
finitely generated. Geometrically, `Spec (R ⧸ I) → Spec R` is then a flat closed immersion
whose image `V(I)` is not open: if it were, purity together with openness of the vanishing
locus would make `R ⧸ I` projective.

## Main definitions

* `Stacks.Examples.vanishNearZeroLift`: the ideal `I`, transported to an arbitrary
  universe.

## Main results

* `Stacks.Examples.vanishNearZeroLift_pure`: the transported ideal is pure.
* `Stacks.Examples.exists_flat_closedImmersion_not_isOpenMap`: there is a flat closed
  immersion of schemes whose underlying continuous map is not open.

The module half of the example is Mathlib's instance `Module.Finite.quotient` (finiteness),
`Stacks.FiniteFlatNotProjective.quotientModule_flat` and
`Stacks.FiniteFlatNotProjective.quotientModule_not_projective`.

## References

* [Stacks Project, Tag 05FY](https://stacks.math.columbia.edu/tag/05FY)
-/

@[expose] public section

namespace Stacks.Examples

open AlgebraicGeometry CategoryTheory

universe u

add_to_stacks 05FY "part (1): finite" Module.Finite.quotient
add_to_stacks 05FY "part (1): flat" Stacks.FiniteFlatNotProjective.quotientModule_flat
add_to_stacks 05FY "part (1): not projective"
  Stacks.FiniteFlatNotProjective.quotientModule_not_projective

/-- The vanishing locus of the ideal of smooth functions vanishing near the origin is not
open: purity together with openness of that locus would force the quotient to be
projective. -/
private theorem zeroLocus_vanishNearZero_not_isOpen :
    ¬ IsOpen
      (PrimeSpectrum.zeroLocus
        (Stacks.FiniteFlatNotProjective.vanishNearZero : Set
          Stacks.FiniteFlatNotProjective.SmoothFunReal)) := by
  intro hopen
  exact Stacks.FiniteFlatNotProjective.quotientModule_not_projective
    (((pure_fg_tfae Stacks.FiniteFlatNotProjective.SmoothFunReal
      Stacks.FiniteFlatNotProjective.vanishNearZero).out 3 4).mp
      (And.intro Stacks.FiniteFlatNotProjective.vanishNearZero_pure hopen))

/-- The ideal of smooth functions vanishing on a neighbourhood of the origin, transported
to an arbitrary universe along `ULift.ringEquiv`. -/
def vanishNearZeroLift : Ideal (ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal) :=
  Stacks.FiniteFlatNotProjective.vanishNearZero.comap
    (ULift.ringEquiv : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
      Stacks.FiniteFlatNotProjective.SmoothFunReal).toRingHom

/-- The transported ideal is pure. -/
theorem vanishNearZeroLift_pure : (vanishNearZeroLift.{u}).Pure := by
  let e : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
    Stacks.FiniteFlatNotProjective.SmoothFunReal := ULift.ringEquiv
  refine Ideal.Pure.of_inf_eq_mul vanishNearZeroLift (fun {K} hK => ?_)
  apply le_antisymm
  · rintro x ⟨hxJ, hxK⟩
    change e x ∈ Stacks.FiniteFlatNotProjective.vanishNearZero at hxJ
    obtain ⟨g, hg, hxg⟩ := Stacks.FiniteFlatNotProjective.exists_mem_vanishNearZero_eq_mul hxJ
    have hmul : x = x * e.symm g :=
      e.injective (by simpa only [map_mul, e.apply_symm_apply] using hxg)
    have hgJ : e.symm g ∈ vanishNearZeroLift.{u} := hg
    rw [hmul, mul_comm x]
    exact Ideal.mul_mem_mul hgJ hxK
  · exact Ideal.mul_le_inf

/-- The vanishing locus of the transported ideal is not open either, since the spectra of
the two isomorphic rings are homeomorphic. -/
private theorem zeroLocus_vanishNearZeroLift_not_isOpen :
    ¬ IsOpen (PrimeSpectrum.zeroLocus
      (vanishNearZeroLift.{u} : Set (ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal))) := by
  let e : ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal ≃+*
    Stacks.FiniteFlatNotProjective.SmoothFunReal := ULift.ringEquiv
  have hset : (PrimeSpectrum.homeomorphOfRingEquiv e) ''
      PrimeSpectrum.zeroLocus (vanishNearZeroLift.{u} :
        Set (ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal)) =
      PrimeSpectrum.zeroLocus
        (Stacks.FiniteFlatNotProjective.vanishNearZero : Set
          Stacks.FiniteFlatNotProjective.SmoothFunReal) := by
    show PrimeSpectrum.comap e.symm.toRingHom '' _ = _
    rw [image_comap_zeroLocus_eq_zeroLocus_comap _ e.symm.toRingHom e.symm.surjective
      vanishNearZeroLift]
    congr 1
  intro hopen
  apply zeroLocus_vanishNearZero_not_isOpen
  rw [← hset]
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).isOpenMap _ hopen

/-- A flat closed immersion of schemes need not be an open map. -/
@[stacks 05FY "part (2)"]
theorem exists_flat_closedImmersion_not_isOpenMap :
    ∃ (X Y : Scheme.{u}) (f : X ⟶ Y),
      IsClosedImmersion f ∧ Flat f ∧ ¬ IsOpenMap f := by
  let R : Type u := ULift.{u} Stacks.FiniteFlatNotProjective.SmoothFunReal
  let I : Ideal R := vanishNearZeroLift
  let q : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  refine ⟨Spec (.of (R ⧸ I)), Spec (.of R), Spec.map q, ?_, ?_, ?_⟩
  · exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective q Ideal.Quotient.mk_surjective
  · rw [AlgebraicGeometry.Flat.SpecMap_iff]
    show (algebraMap R (R ⧸ I)).Flat
    exact RingHom.flat_algebraMap_iff.mpr vanishNearZeroLift_pure
  · intro hopen
    have hopenV : IsOpen (PrimeSpectrum.zeroLocus (I : Set R)) := by
      have hrange := hopen.isOpen_range
      change IsOpen (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))) at hrange
      rwa [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at hrange
    exact zeroLocus_vanishNearZeroLift_not_isOpen hopenV

end Stacks.Examples
