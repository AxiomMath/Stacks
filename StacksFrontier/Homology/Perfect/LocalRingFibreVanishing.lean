module

public import StacksFrontier.Homology.Perfect.Local
import Mathlib

/-!
# Cohomology of a pseudo-coherent complex over a local ring from its derived fibre

Let `R` be a local ring with residue field `κ` and let `K` be a pseudo-coherent object of `D(R)`.
If the derived fibre `K ⊗_R^L κ` has no cohomology in degree `i`, then neither has `K`.

## Main results

* `StacksDraft.Perfect.isZero_homology_of_fibreCohomologyVanishes_maximalIdeal`: the derived fibre
  at the maximal ideal detects the cohomology of a pseudo-coherent complex, degree by degree.

## Implementation notes

[Stacks, Tag 068U] produces an element `g` outside the prime at which the fibre is taken on whose
principal open the degree-`i` cohomology dies, the two summands of the decomposition it supplies
being concentrated above and below degree `i`. Over a local ring the prime is the maximal ideal,
so `g` is a unit and localizing at it changes nothing: the degree-`i` cohomology of the
localization is the localization of the degree-`i` cohomology, by
`StacksDraft.PseudoCoherence.localizationAwayHomologyIso`, and a module whose localization at a
submonoid of units vanishes already vanishes.

## References

* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- A module whose localization at a submonoid consisting of units is zero is itself zero. -/
public theorem subsingleton_of_subsingleton_localizedModule_of_forall_isUnit {R : Type u}
    [CommRing R] (S : Submonoid R) (hS : ∀ s ∈ S, IsUnit s) (M : Type w) [AddCommGroup M]
    [Module R M] [Subsingleton (LocalizedModule S M)] : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun m => ?_
  obtain ⟨s, hs⟩ :=
    (IsLocalizedModule.eq_zero_iff S (LocalizedModule.mkLinearMap S M)).1 (Subsingleton.elim _ _)
  rw [Submonoid.smul_def] at hs
  exact (hS s s.property).smul_eq_zero.1 hs

/-- **Over a local ring the derived fibre detects cohomology, degree by degree.** If `K` is a
pseudo-coherent object of `D(R)` whose derived fibre `K ⊗_R^L κ` at the maximal ideal has
vanishing degree-`i` cohomology, then `H^i(K) = 0`.

This is [Stacks, Tag 068U] at the maximal ideal of a local ring, where the element it produces
outside the ideal is a unit. -/
public theorem isZero_homology_of_fibreCohomologyVanishes_maximalIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hfibre : FibreCohomologyVanishes.{u, v} (IsLocalRing.maximalIdeal R) K i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  obtain ⟨g, hg, hrest⟩ :=
    exists_localization_iso_biprod_truncGE_truncLE.{u, v} (IsLocalRing.maximalIdeal R) K hK i
      hfibre
  dsimp only at hrest
  obtain ⟨-, -, e, -⟩ := hrest
  -- The two summands of the decomposition of [stacks 068U] miss degree `i`, so the degree-`i`
  -- cohomology of the localization vanishes.
  set Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K
  set upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
  set lower := (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Kf
  set H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} (Localization.Away g)) i
  have hzSum : IsZero (H.obj (upper ⊞ lower)) := by
    let c := H.biprodComparison upper lower
    let c' := H.biprodComparison' upper lower
    have : IsSplitMono c := IsSplitMono.mk' ⟨c', by
      dsimp [c, c', Functor.biprodComparison, Functor.biprodComparison']
      rw [biprod.lift_desc, ← H.map_comp, ← H.map_comp, ← H.map_add]
      simp⟩
    rw [IsZero.iff_id_eq_zero, ← cancel_mono c]
    exact biprod.hom_ext _ _
      ((DerivedCategory.isZero_of_isGE upper (i + 1) i (by omega)).eq_of_tgt _ _)
      ((DerivedCategory.isZero_of_isLE lower (i - 1) i (by omega)).eq_of_tgt _ _)
  have hz : IsZero (H.obj Kf) := hzSum.of_iso (H.mapIso e)
  -- `g` lies outside the maximal ideal, hence is a unit, and localizing at a unit changes nothing.
  have hunit : IsUnit g := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hg
  have hsub : Subsingleton (LocalizedModule (Submonoid.powers g)
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K : Type (max u v))) :=
    ModuleCat.isZero_iff_subsingleton.1
      (hz.of_iso (PseudoCoherence.localizationAwayHomologyIso.{u, v} g K i).symm)
  exact ModuleCat.isZero_iff_subsingleton.2
    (subsingleton_of_subsingleton_localizedModule_of_forall_isUnit (Submonoid.powers g)
      (fun _ ⟨n, hn⟩ => hn ▸ hunit.pow n) _)

end StacksDraft.Perfect

end
