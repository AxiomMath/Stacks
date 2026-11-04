module

public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.PuncturedFreeSurjectivity
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.RingTheory.LocalCohomology.FiniteLocallyFreeFiniteness
public import StacksFrontier.RingTheory.Module.LocallyFree.LocalizationAwayRestrict

/-!
# Finiteness of the local cohomology of sections finite locally free on the punctured spectrum

Let `A` be a Noetherian local ring of depth at least three and let `F` be a quasi-coherent module
on `Spec A` with finite global sections `M = Γ(Spec A, F)` whose restriction to the punctured
spectrum is finite locally free. Then `H^i_𝔪(M)` is a finite `A`-module for `i ≤ 2`.

This is [Stacks, Tag 0BPY] with both of its hypotheses discharged:

* the hypothesis on the ring itself, that `H^i_𝔪(A)` be finite for `i ≤ 2`, holds because those
  modules vanish once `depth(A) ≥ 3`;
* the hypothesis on the module, that `M_g` be a finite locally free `A_g`-module for every
  `g ∈ 𝔪`, is read off the sheaf by
  `Module.isFiniteLocallyFree_localization_away_of_isFiniteLocallyFree_restrict`, the standard
  open of an element of `𝔪` being contained in the punctured spectrum, and `F` being the tilde of
  its global sections because it is quasi-coherent.

## Main results

* `Stacks.Algebraization.finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict`

## Implementation notes

`Scheme.Modules` carries its own category instance whose morphisms are only definitionally those
of `SheafOfModules`, so `IsIso F.fromTildeΓ` is not found by instance resolution and the witness
has to be supplied explicitly to `asIso`. The same workaround is used in
`StacksFrontier/AlgebraicGeometry/Properties/ExtendFiniteType/FiniteModule.lean` and in
`StacksFrontier/AlgebraicGeometry/PicardUFD/Affine.lean`.

The containment of the standard open of `g ∈ 𝔪` in the punctured spectrum is proved here rather
than taken from `Stacks.PuncturedSpectrum.specBasicOpen_le_puncturedSpectrum`, which is stated
for the spelling `Stacks.LocalCohomology.puncturedSpectrum` of that open; the spelling used by
the coherent triples, and so by this file, is `Stacks.Divisors.puncturedSpectrum`.

## References

* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- A module with at most one element is finite: the empty family generates it. -/
private theorem finite_of_subsingleton (R : Type*) [Ring R] (X : Type*) [AddCommGroup X]
    [Module R X] [Subsingleton X] : Module.Finite R X := by
  refine Module.finite_def.mpr ⟨∅, ?_⟩
  rw [Finset.coe_empty, Submodule.span_empty]
  exact le_antisymm bot_le fun x _ ↦ by
    rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _

/-- **The standard open of an element of the maximal ideal lies in the punctured spectrum.** A
prime avoiding `g` is not the closed point, which contains `g`. -/
theorem specBasicOpen_le_divisorsPuncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    {g : A} (hg : g ∈ maximalIdeal A) :
    specBasicOpen A g ≤ Stacks.Divisors.puncturedSpectrum A := by
  intro p hp
  have hp' : g ∉ p.asIdeal := hp
  refine fun (hcp : p ∈ ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A))) ↦ hp' ?_
  rw [show p = IsLocalRing.closedPoint A from hcp]
  exact hg

/-- **[Stacks, Tag 0BPY] for the global sections of a quasi-coherent module finite locally free
on the punctured spectrum.** Let `A` be a Noetherian local ring with `depth(A) ≥ 3` and let `F` be
a quasi-coherent module on `Spec A` whose global sections `M` form a finite `A`-module and whose
restriction to the punctured spectrum is finite locally free. Then `H^i_𝔪(M)` is a finite
`A`-module for every `i ≤ 2`.

`depth(A) ≥ 3` makes `H^i_𝔪(A)` vanish for `i ≤ 2`, hence finite, which is the hypothesis Tag
0BPY asks of the ring. For the hypothesis it asks of the module, `F` is the tilde of `M` because
it is quasi-coherent, so the restriction of that tilde to the punctured spectrum is finite
locally free, and the standard open of any `g ∈ 𝔪` is contained in the punctured spectrum. -/
theorem finite_localCohomology_globalSections_of_isFiniteLocallyFree_restrict (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (F : (Spec (CommRingCat.of A)).Modules) [F.IsQuasicoherent]
    (hMfin : Module.Finite A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj F))
    (hdepth : 3 ≤ Module.depth A (maximalIdeal A) A)
    (hFL : Scheme.Modules.IsFiniteLocallyFree
      (F.restrict (Stacks.Divisors.puncturedSpectrum A).ι))
    (i : ℕ) (hi : i ≤ 2) :
    Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, 0} A
      (PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj F)) (i : ℤ)) := by
  set M := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj F with hMdef
  -- the hypothesis Tag 0BPY asks of the ring: `H^i_𝔪(A)` is finite for `i ≤ 2`
  have hA : ∀ j : ℕ, j ≤ 2 → Module.Finite A
      (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, 0} A
        (PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
        (j : ℤ)) := by
    intro j hj
    have hz := Stacks.LocalCohomology.isZero_localCohomology_maximalIdeal_of_lt_depth A
      (ModuleCat.of A A) 3 hdepth (j : ℤ) (by exact_mod_cast Nat.lt_succ_of_le hj)
    have hs := ModuleCat.isZero_iff_subsingleton.mp hz
    exact finite_of_subsingleton A _
  -- `F` is the tilde of its global sections, so that tilde is finite locally free on `U`
  have hiso : IsIso F.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  have hU : Scheme.Modules.IsFiniteLocallyFree
      ((tilde M).restrict (Stacks.Divisors.puncturedSpectrum A).ι) :=
    Scheme.Modules.IsFiniteLocallyFree.of_iso
      ((Scheme.Modules.restrictFunctor (Stacks.Divisors.puncturedSpectrum A).ι).mapIso
        (@asIso _ _ _ _ F.fromTildeΓ hiso).symm) hFL
  -- the hypothesis Tag 0BPY asks of the module
  have hM : ∀ g ∈ (maximalIdeal A : Ideal A), Module.IsFiniteLocallyFree (Localization.Away g)
      (LocalizedModule.Away g (M : Type u)) := fun g hg ↦
    Module.isFiniteLocallyFree_localization_away_of_isFiniteLocallyFree_restrict
      (Stacks.Divisors.puncturedSpectrum A) M hU g
      (specBasicOpen_le_divisorsPuncturedSpectrum A hg)
  have hMfin' : Module.Finite A (M : Type u) := hMfin
  exact Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away
    A (maximalIdeal A) 2 hA M hM i hi

end Stacks.Algebraization

end
