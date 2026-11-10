module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent

/-!
# Coherence of the higher direct images of a module with proper support, over a Noetherian base

The form of Stacks 08GC of `isCoherent_rightDerived_modulePushforward_of_hasProperSupport` in
which the vanishing half of Stacks 07UH is applied to the quasi-coherent module produced by
Stacks 0CZI, so that the étale-affine case of Stacks 03DW is not carried, and Stacks 08AR over a
locally Noetherian target, `coherentHigherDirectImageOfProper_of_isLocallyNoetherian`.

## Main results

* `coherentHigherDirectImageOfProper_of_isLocallyNoetherian`: the input `h08AR` holds over an
  étale-locally Noetherian target.
* `isCoherent_rightDerived_modulePushforward_of_hasProperSupport_of_isQuasicoherent`: Stacks 08GC
  granted `h08AR` and `h0734`.

## References

* [Stacks Project, Tag 08GC](https://stacks.math.columbia.edu/tag/08GC)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08AR as a property of a locally Noetherian target.**  Every algebraic space which is
étale-locally Noetherian has coherent higher direct images from proper morphisms: this is
`AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_isProper`. -/
theorem coherentHigherDirectImageOfProper_of_isLocallyNoetherian (Y : AlgebraicSpaces B S hS)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    CoherentHigherDirectImageOfProper B S hS Y :=
  fun _ g hg G hG p => isCoherent_higherDirectImage_of_isProper B S hS
    (ObjectProperty.homMk g.hom) hg hY G hG p

/-! ### Stacks 08GC -/

/-- **Stacks 08GC, without the input of Stacks 03DW.**  Let `S` be a scheme, let `f : X ⟶ Y` be
a morphism of algebraic spaces over `S` which is locally of finite type with `Y` locally
Noetherian, and let `𝓕` be a coherent `𝒪_X`-module whose support is proper over `Y`.  Then
`R^p f_*𝓕` is a coherent `𝒪_Y`-module for every `p`, granted `h08AR`, Stacks 08AR, and `h0734`,
the degeneration of the relative Leray spectral sequence. -/
theorem isCoherent_rightDerived_modulePushforward_of_hasProperSupport_of_isQuasicoherent
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F))
    (h08AR : CoherentHigherDirectImageOfProper B S hS Y)
    (h0734 : HigherDirectImageCompOfAcyclic B S hS f) (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F) := by
  have _hFc := hF
  have _hFcs := hF.toIsCoherentOnSite
  have _hinjX := hasInjectiveResolutions_modules B S hS X.1 X.2
  change IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived p).obj F)
  obtain ⟨Z, G, hGqc, -, hZp, ⟨e⟩⟩ :=
    ((hasProperSupport_tfae B S hS X Y f.hom hf F hF.toIsQuasicoherentOnSite
      (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F)
      hF.toIsCoherentOnSite.isFiniteType).out 1 3).1 hsupp
  have hXn := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hf hY
  have hGcoh := isCoherent_of_modulePushforward_closedSubspace B S hS X hXn F Z G hGqc e
  have hfin : IsFinite B S hS (closedSubspaceInclusion B S hS X Z).hom :=
    isFinite_of_isClosedImmersion B S hS _ Z.2.2
  have hiso := (h0734 (closedSubspaceToSpace B S hS X Z)
    (closedSubspaceInclusion B S hS X Z) Z.2.2 G
    (fun q hq => isZero_rightDerived_modulePushforward_of_isFinite_of_isQuasicoherent B S hS
      (closedSubspaceInclusion B S hS X Z) hfin G hGqc q hq) p).some
  have hcoh := h08AR (closedSubspaceToSpace B S hS X Z)
    (closedSubspaceInclusion B S hS X Z ≫ f) hZp G hGcoh p
  exact (isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso
    (((modulePushforward B S hS f).rightDerived p).mapIso e)
    ((isCoherent.{u, u} B S hS Y.1 Y.2).prop_of_iso hiso.symm hcoh)

end AlgebraicGeometry.Space

end
