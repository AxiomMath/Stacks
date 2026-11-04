module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorCoefficientBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackTransport
public import StacksFrontier.Topology.Sheaves.Modules.CommonTrivialisingCover
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A cover of an affine scheme by basic opens trivialising two modules at once

The trivialising-cover step of [Stacks, Tag 0EXD] runs the free case of full faithfulness over
each member of a cover of `Spec A` and glues. For that to be possible the members of the cover
cannot be arbitrary opens: over an arbitrary open the almost blowup square of
[Stacks, Example 0EVH] restricts to no square this development can say anything about, whereas
over a *basic* open `D(g)` the restricted square is the two-generator square over the
localisation `A_g`, so that `AlgebraicGeometry.isPullback_frobeniusColimitSections_twoGenerator`
and `AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator` both apply
there verbatim.

This file supplies the refinement: a pair of finite locally free `colim_F 𝒪_{Spec A}`-modules is
free over the members of a cover of `Spec A` **by basic opens**.

## Main results

* `AlgebraicGeometry.exists_basicOpen_cover_commonFree_frobeniusColimit`: **two finite locally
  free `colim_F 𝒪_{Spec A}`-modules are both carried to free modules by the transition functor of
  each member of a cover of `Spec A` by basic opens**, with the members written as the images of
  the morphisms `Spec (A_g) ⟶ Spec A`.
* `AlgebraicGeometry.exists_cover_free_localizationAway_frobeniusColimit`: the same with the
  transition functors taken along the morphisms `Spec (A_g) ⟶ Spec A` **themselves** rather than
  along the inclusions of their images. This is the form the two-generator square over `A_g`
  consumes, since the corner of that square is `Spec (A_g)` and not the open subscheme `D(g)`.
* `AlgebraicGeometry.isInCharacteristic_spec_localizationAway`: a localisation of a ring in which
  `p` vanishes is a ring in which `p` vanishes, read on spectra.

## Implementation notes

The cover is produced by `Stacks.SheafOfModules.exists_cover_commonFree_of_isBasis`, which takes
the basis as a parameter, and the basis taken is the basic opens of `Spec A`. The members are
written as `(Spec.map (algebraMap A (A_g))).opensRange` rather than as
`PrimeSpectrum.basicOpen g`, which is the same open by
`Stacks.AlmostBlowUp.opensRange_specMap_algebraMap_localizationAway`, for two reasons. It is
the spelling the three corner identifications
`Stacks.AlmostBlowUp.centerAwayIsoPreimage`, `…exceptionalAwayIsoPreimage` and
`…modificationAwayIsoPreimage` are stated against. And `PrimeSpectrum.basicOpen g` has type
`TopologicalSpace.Opens (PrimeSpectrum A)`, which is `(Spec (.of A)).Opens` only after unfolding
`Spec`: a type ascription does not survive a field projection, so `(PrimeSpectrum.basicOpen g :
(Spec (.of A)).Opens).ι` does not elaborate, and instance search does not find the induced
category structure on the slice over it either. `Scheme.Hom.opensRange` is at the
`(Spec (.of A)).Opens` spelling to begin with and has neither problem.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CommRingCat
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- **The images of the morphisms `Spec (A_g) ⟶ Spec A` form a basis of the topology of
`Spec A`.**

This is `PrimeSpectrum.isBasis_basic_opens` read at the `(Spec (.of A)).Opens` spelling through
`Stacks.AlmostBlowUp.opensRange_specMap_algebraMap_localizationAway`. -/
@[ega "IV 8.1.2" "The principal opens D(f)"]
theorem isBasis_opensRange_specMap_localizationAway (A : Type u) [CommRing A] :
    Opens.IsBasis (Set.range fun g : A =>
      (Spec.map (ofHom (algebraMap A (Localization.Away g)))).opensRange) := by
  rw [show (fun g : A => (Spec.map (ofHom (algebraMap A (Localization.Away g)))).opensRange)
      = fun g : A => (PrimeSpectrum.basicOpen g : (Spec (CommRingCat.of A)).Opens) from
    funext fun g => opensRange_specMap_algebraMap_localizationAway A g]
  exact PrimeSpectrum.isBasis_basic_opens

/-- **Two finite locally free `colim_F 𝒪_{Spec A}`-modules are both carried to free modules by the
transition functor of each member of a cover of `Spec A` by basic opens.**

This is the refinement the trivialising-cover step of [Stacks, Tag 0EXD] needs: over a basic open
`D(g)` the almost blowup square of [Stacks, Example 0EVH] is the two-generator square over the
localisation `A_g`, so the free case of full faithfulness is available there, whereas over an
arbitrary open it is not.

It is `Stacks.SheafOfModules.exists_cover_commonFree_of_isBasis` at the basis of basic opens,
with the trivialisations moved into the transition-functor spelling of [Stacks, Tag 0EXE] by
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso`. -/
theorem exists_basicOpen_cover_commonFree_frobeniusColimit (A : Type u) [CommRing A]
    (hX : IsInCharacteristic (Spec (CommRingCat.of A)) p)
    (M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf (Spec (.of A)) p hX))
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ (σ : Type u) (g : σ → A) (K L : σ → Type u),
      (⨆ s, (Spec.map (ofHom (algebraMap A (Localization.Away (g s))))).opensRange) = ⊤ ∧
      (∀ s, Finite (K s)) ∧ (∀ s, Finite (L s)) ∧
      (∀ s, Nonempty ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p
            (Spec.map (ofHom (algebraMap A (Localization.Away (g s))))).opensRange.ι
            (isInCharacteristic_toScheme hX _) hX)).obj M ≅
        _root_.SheafOfModules.free (K s))) ∧
      (∀ s, Nonempty ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p
            (Spec.map (ofHom (algebraMap A (Localization.Away (g s))))).opensRange.ι
            (isInCharacteristic_toScheme hX _) hX)).obj N ≅
        _root_.SheafOfModules.free (L s))) := by
  obtain ⟨σ, a, K, L, hcov, hKfin, hLfin, hMfree, hNfree⟩ :=
    Stacks.SheafOfModules.exists_cover_commonFree_of_isBasis
      (frobeniusColimitRingSheaf (Spec (CommRingCat.of A)) p hX) M N hM hN _
      (isBasis_opensRange_specMap_localizationAway A)
  exact ⟨σ, a, K, L, hcov, hKfin, hLfin,
    fun s => (hMfree s).map (frobeniusColimitPullbackObjFreeOfIso _ p hX _
      (isInCharacteristic_toScheme hX _) M (K s)),
    fun s => (hNfree s).map (frobeniusColimitPullbackObjFreeOfIso _ p hX _
      (isInCharacteristic_toScheme hX _) N (L s))⟩

omit [Fact p.Prime] in
/-- **A prime vanishing in `A` vanishes in every localisation of `A`**, read on spectra.

This is what makes the two-generator square over `A_g` a square of schemes in characteristic `p`,
so that the comparison functor of [Stacks, Tag 0EXD] exists over `A_g` at all. -/
theorem isInCharacteristic_spec_localizationAway (A : Type u) [CommRing A]
    (hpA : (p : A) = 0) (g : A) :
    IsInCharacteristic (Spec (CommRingCat.of (Localization.Away g))) p :=
  isInCharacteristic_spec _ p (by
    rw [← map_natCast (algebraMap A (Localization.Away g)) p, hpA, map_zero])

/-- **Two finite locally free `colim_F 𝒪_{Spec A}`-modules are both carried to free modules by
the transition functor of `Spec (A_g) ⟶ Spec A`, for the members `D(g)` of a cover of
`Spec A`.**

This is `AlgebraicGeometry.exists_basicOpen_cover_commonFree_frobeniusColimit` with the
transition taken along the localisation morphism itself rather than along the inclusion of its
image, which is what the two-generator square over `A_g` consumes: the corner of that square is
`Spec (A_g)`, and the open subscheme `D(g)` is only isomorphic to it. The crossing is
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfOpenImmersion`, which needs no equivalence
because the transition of a free module is free. -/
theorem exists_cover_free_localizationAway_frobeniusColimit (A : Type u) [CommRing A]
    (hpA : (p : A) = 0)
    (M N : _root_.SheafOfModules.{u}
      (frobeniusColimitRingSheaf (Spec (.of A)) p (isInCharacteristic_spec A p hpA)))
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ (σ : Type u) (g : σ → A) (K L : σ → Type u),
      (⨆ s, (Spec.map (ofHom (algebraMap A (Localization.Away (g s))))).opensRange) = ⊤ ∧
      (∀ s, Finite (K s)) ∧ (∀ s, Finite (L s)) ∧
      (∀ s, Nonempty ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p
            (Spec.map (ofHom (algebraMap A (Localization.Away (g s)))))
            (isInCharacteristic_spec_localizationAway p A hpA (g s))
            (isInCharacteristic_spec A p hpA))).obj M ≅
        _root_.SheafOfModules.free (K s))) ∧
      (∀ s, Nonempty ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p
            (Spec.map (ofHom (algebraMap A (Localization.Away (g s)))))
            (isInCharacteristic_spec_localizationAway p A hpA (g s))
            (isInCharacteristic_spec A p hpA))).obj N ≅
        _root_.SheafOfModules.free (L s))) := by
  obtain ⟨σ, a, K, L, hcov, hKfin, hLfin, hMfree, hNfree⟩ :=
    Stacks.SheafOfModules.exists_cover_commonFree_of_isBasis
      (frobeniusColimitRingSheaf (Spec (CommRingCat.of A)) p (isInCharacteristic_spec A p hpA))
      M N hM hN _ (isBasis_opensRange_specMap_localizationAway A)
  exact ⟨σ, a, K, L, hcov, hKfin, hLfin,
    fun s => (hMfree s).map (frobeniusColimitPullbackObjFreeOfOpenImmersion p _ _ _
      (isInCharacteristic_spec_localizationAway p A hpA (a s)) M (K s)),
    fun s => (hNfree s).map (frobeniusColimitPullbackObjFreeOfOpenImmersion p _ _ _
      (isInCharacteristic_spec_localizationAway p A hpA (a s)) N (L s))⟩

end AlgebraicGeometry

end
