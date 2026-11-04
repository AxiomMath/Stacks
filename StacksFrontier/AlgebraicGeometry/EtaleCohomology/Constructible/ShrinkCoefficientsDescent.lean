module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage

/-!
# Surjective descent and finite étale direct image for a small coefficient ring

Stacks 095Q for sheaves of modules
(`AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective`) and Stacks 095H for
sheaves of modules (`AlgebraicGeometry.isConstructibleModuleSheaf_pushforward`) are stated for a
Noetherian coefficient ring in `Type (u + 1)`, the universe of the modules. This file reads them
at a Noetherian ring `R` that is only small in that universe (for instance `ℤ` or `ZMod n` in
`Type 0`), through the equivalence `AlgebraicGeometry.SmallEtale.sheafShrinkEquivalence` of
sheaves of `R`-modules with sheaves of `Shrink R`-modules: it commutes with inverse image
(`Sheaf.sheafPullbackCoefficientIso`) and, on the nose, with direct image.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback'` —
  **Stacks 095Q** (the descent half) for a small Noetherian coefficient ring.
* `AlgebraicGeometry.isConstructibleModuleSheaf_pushforward'` — **Stacks 095H** for a small
  Noetherian coefficient ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (R : Type r) [CommRing R] [IsNoetherianRing R] [Small.{u + 1} R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]

attribute [local instance 2000] isRightAdjoint_sheafPushforwardContinuous_shrink
  hasWeakSheafify_over_shrink

/-- **Stacks 095Q, descent half, for a small Noetherian coefficient ring.** Let `f : X ⟶ Y` be a
surjective morphism of quasi-compact and quasi-separated schemes of `B`, and `ℱ` a sheaf of
`R`-modules on `Y_étale`. If `f⁻¹ℱ` is constructible, so is `ℱ`. -/
theorem isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback' {X Y : B.Scheme}
    (f : X ⟶ Y) (hYc : CompactSpace Y.1) (hYq : QuasiSeparatedSpace Y.1)
    (hXc : CompactSpace X.1) (hXq : QuasiSeparatedSpace X.1)
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} R)
        (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)).obj F)) :
    IsConstructibleModuleSheaf B Y R F := by
  refine isConstructibleModuleSheaf_of_shrink B R Y F ?_
  refine (isConstructibleModuleSheaf_pullback_iff_of_surjective B (Shrink.{u + 1} R) f
    hYc hYq hXc hXq hf _).2 ?_
  exact isConstructibleModuleSheaf_congr B (Shrink.{u + 1} R) X
    ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f) _ _
      (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)).app F)
    (isConstructibleModuleSheaf_shrink B R X _ hF)

/-- **Stacks 095H for a small Noetherian coefficient ring.** The direct image along a finite
étale morphism of `B` of a constructible sheaf of `R`-modules is constructible. -/
theorem isConstructibleModuleSheaf_pushforward' {S T : B.Scheme} (p : T ⟶ S)
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B T R F) :
    IsConstructibleModuleSheaf B S R ((B.smallPushforward p (ModuleCat.{u + 1} R)).obj F) :=
  isConstructibleModuleSheaf_of_shrink B R S _
    (isConstructibleModuleSheaf_pushforward B p (Shrink.{u + 1} R) _
      (isConstructibleModuleSheaf_shrink B R T F hF))

end AlgebraicGeometry

end
