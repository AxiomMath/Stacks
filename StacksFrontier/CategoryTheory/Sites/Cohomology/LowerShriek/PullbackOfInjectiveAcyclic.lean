module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.StacksAttribute

/-! # Acyclicity on objects of the inverse image of a module, reduced to Čech vanishing

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g` be the corresponding
morphism of topoi, let `O` be a sheaf of rings on `D` and let `I` be an `O`-module. Stacks 0D6X
asserts that `H^p(U, g^{-1} I) = 0` for `p > 0` and every object `U` of `C`, provided `I` is
injective.

The source proves it in two steps: the Čech cohomology of `g^{-1} I` on a covering of `U`
agrees with the Čech cohomology of `I` on the image covering of `u(U)`, where it vanishes
because `I` is injective (Stacks 03FC); and Čech vanishing on a cofinal system of coverings
implies vanishing of sheaf cohomology (Stacks 03F9). The second step is proved as
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero`, and this file carries it
out: it supplies that criterion's covering system, its iterated fibre products and its
cofinality from `Stacks.Sites.PreservesCoveringPullbacks`, and so reduces Stacks 0D6X to the
first step alone, which is taken here as the single hypothesis `hCech`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.subsingleton_ext_inverseImage_of_cechCohomology_isZero`:
  Stacks 0D6X with the Čech vanishing of `g^{-1} I` as its only hypothesis.

## Relation to the tag

This file is the reduction only, and carries no `@[stacks 0D6X]` attribute: it leaves the Čech
vanishing as the hypothesis `hCech`. Stacks 0D6X itself, with that hypothesis discharged from
the covering-pullback clause of continuity, at general universes and on sites that need not be
small, is `Stacks.CechSite.injective_module_subsingleton_ext_of_continuous`; the two ingredients
it uses are the Čech comparison along the functor of sites,
`Stacks.CechSite.isIso_cechProductMapOfFunctor_of_continuityCovering`, and Stacks 03FC in
positive degrees, `Stacks.CechSite.injective_moduleCechCohomology_isZero`. Its small-site form
is `Stacks.Cohomology.DerivedLowerShriek.subsingleton_ext_freeAbelianSheaf_restriction`.

## Implementation notes

Cocontinuity of `u` is not used by this reduction; it is kept because it is a hypothesis of
Stacks 0D6X, and it is what makes restriction along `u` the inverse image `g^{-1}` of a
morphism of topoi. Restriction itself is `SheafOfModules.pushforward` for the identity of
`g^{-1} O`, and needs only continuity.

The universes are narrowed relative to Stacks 0D6X: both sites are small and their objects,
morphisms, the sheaf of rings, the module sections and the `Ext`-groups all lie in one
universe `w`. Two ingredients force this. The criterion of Stacks 03F9 is stated with
the coefficient universe containing the morphism universe and with `Small` on the site, and
`Presieve.preZeroHypercover` indexes a covering by its own arrows, so a cofinal system of
coverings extracted from a Grothendieck topology has index type in `max u₁ v₁`; the two
together collapse the site's object and morphism universes into the coefficient universe.
At those universes `P` is forced to be isomorphic to `yoneda.obj U`, which is how the
conclusion below is phrased for an arbitrary representable `P`, as in Stacks 0D6X.

## References

* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FC](https://stacks.math.columbia.edu/tag/03FC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J u]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

omit [u.IsCocontinuous J K] in
/-- **Stacks 0D6X, reduced to Čech vanishing.** If the positive-degree Čech cohomology of the
inverse image `g^{-1} I` of a module along a functor of sites vanishes on every covering whose
arrows admit covering pullbacks preserved by the functor, then `H^p(U, g^{-1} I) = 0` for every
`p > 0` and every object `U` of the source site, cohomology over `U` being `Ext` from the
sheafification of the free abelian presheaf on a presheaf representing `U`.

This is Stacks 0D6X with its hypothesis that `I` be injective replaced by the Čech vanishing
that the source deduces from it. The covering system, its iterated fibre products and its
cofinality in the topology are supplied from
`Stacks.Sites.PreservesCoveringPullbacks`; what remains open is the hypothesis `hCech`. -/
theorem subsingleton_ext_inverseImage_of_cechCohomology_isZero
    (O : Sheaf K RingCat.{w}) (I : SheafOfModules.{w} O)
    (hCech : ∀ (V : C) (E : PreZeroHypercover.{w} V), E.sieve₀ ∈ J V →
      ∀ (hpb : ∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.f j) g),
      (∀ (j : E.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.f j) g) u) →
      ∀ (p : ℕ), 0 < p →
      letI := Stacks.Sites.hasProduct_fibreProducts E hpb
      IsZero (Stacks.CechSite.cechCohomology E
        ((SheafOfModules.toSheaf _).obj
          ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J K).obj O))).obj I)).obj p))
    (U : C) (P : Cᵒᵖ ⥤ Type w) (hP : P.RepresentableBy U)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton
      (Abelian.Ext ((presheafToSheaf J AddCommGrpCat.{w}).obj (P ⋙ AddCommGrpCat.free))
        ((SheafOfModules.toSheaf _).obj
          ((SheafOfModules.pushforward
            (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J K).obj O))).obj I)) p) := by
  set F : Sheaf J AddCommGrpCat.{w} := (SheafOfModules.toSheaf _).obj
    ((SheafOfModules.pushforward
      (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J K).obj O))).obj I) with hF
  have hzero : IsZero (Sheaf.H'.{w, w, w} F p U) := by
    refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero.{w, w, w, w}
      J Set.univ
      (fun V => { E | (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), HasPullback (E.1.f j) g) ∧
        (∀ (j : E.1.I₀) ⦃W : C⦄ (g : W ⟶ V), PreservesLimit (cospan (E.1.f j) g) u) })
      (fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i)
      (fun E hE => ⟨Set.mem_univ _, fun i => Set.mem_univ _, fun q i => Set.mem_univ _⟩)
      ?_ F ?_ U (Set.mem_univ U) p hp
    · intro V _ S hS
      obtain ⟨E, hJ, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u S hS
      exact ⟨⟨E, hJ⟩, ⟨hpb, hpr⟩, hle⟩
    · intro V E hE q hq
      exact hCech V E.1 E.2 hE.1 hE.2 q hq
  have hsub : Subsingleton (Abelian.Ext
      ((presheafToSheaf J AddCommGrpCat.{w}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F p) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  let iso : (presheafToSheaf J AddCommGrpCat.{w}).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (presheafToSheaf J AddCommGrpCat.{w}).obj (P ⋙ AddCommGrpCat.free) :=
    (presheafToSheaf J AddCommGrpCat.{w}).mapIso
      (Functor.isoWhiskerRight hP.toIso AddCommGrpCat.free)
  exact (((Abelian.extFunctor p).mapIso iso.op).app F).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr.mpr hsub

end Stacks.Cohomology.DerivedLowerShriek

end
