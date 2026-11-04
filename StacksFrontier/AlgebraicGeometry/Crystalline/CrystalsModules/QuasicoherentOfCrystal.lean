module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCriterion
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverPresentationLift
public import StacksFrontier.CategoryTheory.Limits.CokernelOfBijectiveFamily

/-!
# A locally quasi-coherent crystal in modules is quasi-coherent

This file proves the direction (2) ⇒ (1) of [Stacks, Tag 07IT] on the big crystalline site
`CRIS(X/S)` of a global crystalline situation: a sheaf of `𝒪_{X/S}`-modules all of whose
restrictions `F_T` are quasi-coherent `𝒪_T`-modules and which is a crystal in `𝒪_{X/S}`-modules is
quasi-coherent on the site.

The source's argument is

> Assume (a) and (b).  Let `(U, T, δ)` be an object of `𝒞`.  We have to show that `F` restricted to
> `𝒞/(U, T, δ)` has a global presentation.  ...  we may assume `T` is affine.  Then `F_T` is a
> quasi-coherent `𝒪_T`-module, so it has a presentation `⊕_J 𝒪_T → ⊕_I 𝒪_T → F_T → 0`.  Then by the
> crystal property of `F` we see that this pulls back to a presentation of `F_{T'}` for any
> morphism `f : (U', T', δ') → (U, T, δ)` of `𝒞`.

and that is the shape of the proof below.  The reduction to affine ambient scheme is
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine`; the presentation
of `F_T` on the affine ambient scheme, placed on the localised site `CRIS(X/S)/(U, T, δ)`, is
`Crystalline.GlobalCrystallineSituation.exists_crystallineCoproduct_cokernelCofork_restrictOver`;
and "this pulls back to a presentation of `F_{T'}`" is the content of
`Crystalline.GlobalCrystallineSituation.Thickening`
`.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal` below.

## How the crystal property is used

The crystal property enters without the pullback functor, through the criterion
`Crystalline.GlobalCrystallineSituation.Thickening`
`.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`:
the comparison map of a morphism `f` is invertible exactly when composition with the `f`-map is
bijective on morphisms out of the restriction `F_T`.  That criterion survives the universe lift of
the module sections, so it is available at the module universe `u + 1` at which a global
presentation on a localised crystalline site is read.

Writing `ρ_Y` for the restriction `F ↦ F_T` over an object `Y` of `CRIS(X/S)/B` and `Φ_N` for
composition with the `f`-map of the structure morphism `Y ⟶ B`, naturality of `Φ` in the module
gives for each morphism `ψ` of `CRIS(X/S)/B` a commuting square relating precomposition with
`ρ_Y(ψ)` upstairs and with `ρ_B(ψ)` downstairs.  Composition with the `f`-map is bijective at the
structure sheaf, hence at a coproduct of copies of it, and it is bijective at the universe lift of
`F` precisely because `F` is a crystal; so the two outer columns of the two squares attached to the
presenting morphisms are bijections, and the universal property of the cokernel transfers from
`ρ_B` to `ρ_Y`.  That is
`CategoryTheory.Limits.existsUnique_comp_of_bijective`.

The bijections are available only at test objects which are universe lifts of sheaves of modules
at the module universe `u`, so the transfer gives the universal property of the cokernel only
against those.  That is enough: the index types of the presentation are universe lifts of types in
`Type u`, so the whole restricted cofork is the universe lift of a cofork at the module universe
`u`, and the universe lift of the sections is fully faithful and preserves finite colimits.  The
cofork at the module universe `u` is a cokernel because the transfer applies to exactly the test
objects its universal property quantifies over, and its universe lift — the restricted cofork — is
then a cokernel against *every* test object.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal`
  — **the presentation of the affine ambient scheme of `B` restricts to a presentation over every
  object of `CRIS(X/S)/B`.**
* `Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_over_of_isAffine` — **a locally
  quasi-coherent crystal in `𝒪_{X/S}`-modules has a global presentation on the localisation of
  `CRIS(X/S)` at an object with affine ambient scheme.**
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_isLocallyQuasiCoherent` —
  **the implication (2) ⇒ (1) of [Stacks, Tag 07IT] on `CRIS(X/S)`.**
* `Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_iff` — **the equivalence of
  [Stacks, Tag 07IT] on `CRIS(X/S)`**, read with the sheaf-level crystal condition.

## The reading of the tag

[Stacks, Tag 07IT] is false as literally stated against this library, because the library's
`Crystalline.GlobalCrystallineSituation.IsCrystal` reads the crystal condition of
[Stacks, Tag 07IS] with the comparison maps of *presheaves* of modules whereas the source reads it
with the comparison maps of sheaves of modules; the correction is set out in the module
documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCriterion`.  Everything
below is stated with the sheaf-level condition
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, which is the reading under which the tag
holds.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

/-- Sheaves of modules on the Zariski site of the ambient scheme of an object have coproducts
indexed by any type of the universe `u` of their sections. -/
theorem hasColimitsOfShape_discrete_ambient (A : Thickening S) (I : Type u) :
    HasColimitsOfShape (Discrete I) (SheafOfModules.{u} A.ringRestrictionSheaf) := by
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      AddCommGrpCat.{u} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} _
  infer_instance

section

attribute [local instance] hasColimitsOfShape_discrete_ambient

/-- **The coproduct of `I` copies of the structure sheaf of the Zariski site of the ambient scheme
of an object**, at the module universe `u`. -/
noncomputable def ambientCoproduct (A : Thickening S) (I : Type u) :
    SheafOfModules.{u} A.ringRestrictionSheaf :=
  ∐ fun _ : I ↦ SheafOfModules.unit A.ringRestrictionSheaf

/-- The inclusion of the `i`-th summand of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientCoproduct`. -/
noncomputable def ambientCoproductι (A : Thickening S) (I : Type u) (i : I) :
    SheafOfModules.unit A.ringRestrictionSheaf ⟶ ambientCoproduct A I :=
  Sigma.ι (fun _ : I ↦ SheafOfModules.unit A.ringRestrictionSheaf) i

/-- The cofan of the inclusions of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientCoproduct` is a colimit. -/
noncomputable def isColimitAmbientCoproductCofan (A : Thickening S) (I : Type u) :
    IsColimit (Cofan.mk (ambientCoproduct A I) (ambientCoproductι A I)) :=
  coproductIsCoproduct fun _ : I ↦ SheafOfModules.unit A.ringRestrictionSheaf

end

variable (B : Thickening S)

/-- The pushforward of sheaves of modules along the ring map `ringRestrictionSheafFMap g` of a
morphism `g` of thickenings preserves zero morphisms. -/
instance preservesZeroMorphisms_pushforward_ringRestrictionSheafFMap {A : Thickening S}
    (g : A ⟶ B) :
    (SheafOfModules.pushforward.{u + 1} (ringRestrictionSheafFMap g)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Composition with the `f`-map of the structure morphism of an object of a localised crystalline
site carries the zero morphism to the zero morphism, the pushforward of sheaves of modules
preserving zero morphisms. -/
theorem fmapCompOver_toTerminalOver_zero (X : Over B)
    (N : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
    (Z : SheafOfModules.{u + 1} X.left.ringRestrictionSheaf) :
    fmapCompOver.{u + 1} N (toTerminalOver B X) Z 0 = 0 := by
  show moduleFMapSheafOver N (toTerminalOver B X) ≫
    (SheafOfModules.pushforward.{u + 1}
      (ringRestrictionSheafFMap (toTerminalOver B X).left)).map 0 = 0
  rw [Functor.map_zero, comp_zero]

/-- **Composition with the `f`-map of the structure morphism of an object of a localised
crystalline site is bijective at the universe lift of the structure sheaf**, when the test module
is a universe lift.  This is the comparison map of `𝒪_{X/S}` being an isomorphism. -/
theorem bijective_fmapCompOver_toTerminalOver_uliftUnit (X : Over B)
    (Z : SheafOfModules.{u} X.left.ringRestrictionSheaf) :
    Function.Bijective (fmapCompOver.{u + 1} (uliftUnitOver B) (toTerminalOver B X)
      ((ambientUliftFunctor X.left).obj Z)) :=
  (bijective_fmapCompOver_uliftForPresentation_iff
      (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) (toTerminalOver B X) Z).2
    ((bijective_fmapCompOverLift_iff _ (toTerminalOver B X) Z).2
      (bijective_fmapCompOver_unit (toTerminalOver B X) Z))

/-- **Composition with the `f`-map of the structure morphism of an object of a localised
crystalline site is bijective at the universe lift of a module restricted from `CRIS(X/S)` exactly
when the comparison map of that structure morphism is invertible**, when the test module is a
universe lift.  For a crystal in `𝒪_{X/S}`-modules the right-hand side holds. -/
theorem bijective_fmapCompOver_toTerminalOver_uliftOver
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (X : Over B)
    (hX : IsIso (moduleComparisonSheaf M X.hom))
    (Z : SheafOfModules.{u} X.left.ringRestrictionSheaf) :
    Function.Bijective
      (fmapCompOver.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (M.over B)) (toTerminalOver B X) ((ambientUliftFunctor X.left).obj Z)) :=
  (bijective_fmapCompOver_uliftForPresentation_iff (M.over B) (toTerminalOver B X) Z).2
    ((bijective_fmapCompOverLift_iff (M.over B) (toTerminalOver B X) Z).2
      ((bijective_fmapCompOver_over_iff M (toTerminalOver B X) Z).2
        ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp M X.hom).1 hX Z)))

/-- **The restriction of a crystalline coproduct over a universe-lifted index type to the ambient
scheme of an object over the base is the universe lift of a coproduct at the module universe
`u`.**  Both sides are coproducts of the universe lift of the structure sheaf of that ambient
scheme over the same index type: on the left by
`Crystalline.GlobalCrystallineSituation.Thickening.isColimitRestrictOverCrystallineCoproductCofan`,
on the right because the universe lift of the sections preserves coproducts of size `u` and the
index type is reindexed by `CategoryTheory.Limits.isColimit_cofan_ulift`. -/
noncomputable def restrictOverCrystallineCoproductUliftIso (I₀ : Type u) {A : Thickening S}
    (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{u + 1} h).obj
        (crystallineCoproduct B (ULift.{u + 1} I₀)) ≅
      (ambientUliftFunctor A).obj (ambientCoproduct A I₀) := by
  have := preservesColimitsOfSize_ambientUliftFunctor A
  have hT : IsColimit (Cofan.mk ((ambientUliftFunctor A).obj (ambientCoproduct A I₀))
      (fun j : ULift.{u + 1} I₀ ↦ (ambientUliftFunctor A).map (ambientCoproductι A I₀ j.down)) :
        Cofan fun _ : ULift.{u + 1} I₀ ↦ (ambientUliftFunctor A).obj
          (SheafOfModules.unit A.ringRestrictionSheaf)) :=
    isColimit_cofan_ulift _ (isColimitCofanMkObjOfIsColimit (ambientUliftFunctor A) _
      (ambientCoproductι A I₀) (isColimitAmbientCoproductCofan A I₀))
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) h) hT

/-- **The universal property of the cokernel transfers from the ambient scheme of `B` to the
ambient scheme of an arbitrary object of `CRIS(X/S)/B`, against test modules which are universe
lifts.**  This is where the crystal property of `F` is used: composition with the `f`-map of the
structure morphism of the object is bijective at the two crystalline coproducts because it is
bijective at the structure sheaf, and at the universe lift of `F` because the comparison map of
that structure morphism is invertible. -/
theorem existsUnique_comp_moduleRestrictionSheafOver_of_isSheafCrystal
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hcrys : IsSheafCrystal M)
    {I₀ K₀ : Type u}
    {a : crystallineCoproduct B (ULift.{u + 1} K₀) ⟶ crystallineCoproduct B (ULift.{u + 1} I₀)}
    {b : crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)}
    (hab : a ≫ b = 0)
    (h₂ : IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab)))
    (X : Over B) (Z : SheafOfModules.{u} X.left.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).obj
      (crystallineCoproduct B (ULift.{u + 1} I₀)) ⟶ (ambientUliftFunctor X.left).obj Z)
    (hk : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map a ≫ k = 0) :
    ∃! m : (ambientUliftFunctor X.left).obj
        ((moduleRestrictionSheafOverFunctor.{u} X.hom).obj (M.over B)) ⟶
      (ambientUliftFunctor X.left).obj Z,
      (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map b ≫ m = k := by
  have hθ : ∀ {N₁ N₂ : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
      (ψ : N₁ ⟶ N₂) (kk : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).obj N₂ ⟶
        (ambientUliftFunctor X.left).obj Z),
      fmapCompOver.{u + 1} N₁ (toTerminalOver B X) ((ambientUliftFunctor X.left).obj Z)
          ((moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map ψ ≫ kk) =
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map ψ ≫
          fmapCompOver.{u + 1} N₂ (toTerminalOver B X)
            ((ambientUliftFunctor X.left).obj Z) kk :=
    fun ψ kk ↦ fmapCompOver_naturality ψ (toTerminalOver B X) _ kk
  have hP : Function.Bijective (fmapCompOver.{u + 1}
      (crystallineCoproduct B (ULift.{u + 1} I₀)) (toTerminalOver B X)
      ((ambientUliftFunctor X.left).obj Z)) :=
    Stacks.PresentedBijectivity.bijective_of_cofan hθ
      (crystallineCoproductι B (ULift.{u + 1} I₀))
      (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) X.hom)
      (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) (𝟙 B))
      (bijective_fmapCompOver_toTerminalOver_uliftUnit B X Z)
  exact existsUnique_comp_of_bijective hθ h₂ (fmapCompOver_toTerminalOver_zero B X _ _) hP
    (bijective_fmapCompOver_toTerminalOver_uliftOver B M X (hcrys X.left B X.hom) Z) k hk

/-- **The presentation of the affine ambient scheme of `B`, restricted to the ambient scheme of an
arbitrary object of `CRIS(X/S)/B`, is still a presentation.**  This is the step of the direction
(2) ⇒ (1) of [Stacks, Tag 07IT] at which the crystal property is used: the restriction `F_{T'}`
over an object of the localised site is the pullback of `F_T`, so the presentation base-changes.

The universal property of the cokernel is transferred from `B` to the object against test modules
which are universe lifts
(`Crystalline.GlobalCrystallineSituation.Thickening`
`.existsUnique_comp_moduleRestrictionSheafOver_of_isSheafCrystal`);
the restricted cofork is then recognised as the universe lift of a cofork at the module universe
`u`, which that transfer shows to be a cokernel, and the universe lift of the sections preserves
it. -/
noncomputable def isColimitCokernelCoforkRestrictOverOfIsSheafCrystal
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hcrys : IsSheafCrystal M)
    {I₀ K₀ : Type u}
    {a : crystallineCoproduct B (ULift.{u + 1} K₀) ⟶ crystallineCoproduct B (ULift.{u + 1} I₀)}
    {b : crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)}
    (hab : a ≫ b = 0)
    (h₂ : IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab)))
    (X : Over B) :
    IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B X.hom hab)) :=
  have := preservesFiniteColimits_ambientUliftFunctor X.left
  isColimitCokernelCoforkOfDescent (ambientUliftFunctor X.left)
    (Q₀ := ambientCoproduct X.left K₀) (P₀ := ambientCoproduct X.left I₀)
    (N₀ := (moduleRestrictionSheafOverFunctor.{u} X.hom).obj (M.over B))
    (restrictOverCrystallineCoproductUliftIso B K₀ X.hom)
    (restrictOverCrystallineCoproductUliftIso B I₀ X.hom) (Iso.refl _)
    (moduleRestrictionSheafOver_map_comp_eq_zero B X.hom hab)
    ((ambientUliftFunctor X.left).map_preimage _) ((ambientUliftFunctor X.left).map_preimage _)
    (fun Z k hk ↦ existsUnique_comp_moduleRestrictionSheafOver_of_isSheafCrystal
      B hcrys hab h₂ X Z k hk)

/-- Sheaves of `𝒪_{X/S}`-modules on a localised crystalline site have cokernels at the module
universe `u + 1`, the sheafification of `AddCommGrpCat.{u + 1}`-valued presheaves on that site
existing and its equivalences being the local bijections. -/
theorem hasCokernels_sheafOfModules_over :
    HasCokernels (SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) := by
  have := hasSheafify_over_addCommGrpCat_succ B
  have := wEqualsLocallyBijective_over_addCommGrpCat_succ B
  infer_instance

end Thickening

/-- **A locally quasi-coherent crystal in `𝒪_{X/S}`-modules has a global presentation on the
localisation of `CRIS(X/S)` at an object with affine ambient scheme.**

The presentation of the restriction `F_{T'}` to the affine ambient scheme is placed on the
localised site by
`Crystalline.GlobalCrystallineSituation.exists_crystallineCoproduct_cokernelCofork_restrictOver`;
the crystal property makes it a presentation after restricting to the ambient scheme of *every*
object of that site
(`Crystalline.GlobalCrystallineSituation.Thickening`
`.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal`),
and those restrictions detect a cokernel
(`Crystalline.GlobalCrystallineSituation.Thickening`
`.isColimitCokernelCoforkOfForallRestrictOver`). -/
theorem hasGlobalPresentation_over_of_isAffine
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : Thickening S) [IsAffine B.thickening.target.scheme] :
    (M.over B).HasGlobalPresentation := by
  obtain ⟨I₀, K₀, a, b, hab, ⟨h₂⟩⟩ :=
    exists_crystallineCoproduct_cokernelCofork_restrictOver hlqc B
  have := Thickening.hasCokernels_sheafOfModules_over B
  refine ⟨ULift.{u + 1} I₀, ULift.{u + 1} K₀,
    Thickening.crystallineCoproduct B (ULift.{u + 1} I₀),
    Thickening.crystallineCoproduct B (ULift.{u + 1} K₀),
    Thickening.crystallineCoproductι B (ULift.{u + 1} I₀),
    Thickening.crystallineCoproductι B (ULift.{u + 1} K₀),
    ⟨Thickening.isColimitCrystallineCoproductCofan B (ULift.{u + 1} I₀)⟩,
    ⟨Thickening.isColimitCrystallineCoproductCofan B (ULift.{u + 1} K₀)⟩, a, b, hab, ⟨?_⟩⟩
  exact Thickening.isColimitCokernelCoforkOfForallRestrictOver B hab
    (fun Y ↦ Thickening.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal B hcrys hab h₂ Y)

/-- **The implication (2) ⇒ (1) of [Stacks, Tag 07IT] on the big crystalline site `CRIS(X/S)`: a
locally quasi-coherent sheaf of `𝒪_{X/S}`-modules which is a crystal in `𝒪_{X/S}`-modules is
quasi-coherent on the site.**

Quasi-coherence is Zariski-local on the ambient scheme of each object
(`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine`), so it is
enough to present `F` globally on the localisation of `CRIS(X/S)` at an object whose ambient scheme
is affine, which is
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_over_of_isAffine`.

The crystal condition is read at sheaf level, as
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`; that is the reading under which the tag
holds, and the two hypotheses are exactly the source's conditions (a) and (b). -/
@[stacks 07IT "the implication (2) ⇒ (1) on the big site CRIS(X/S): a sheaf of 𝒪_{X/S}-modules
  whose restrictions F_T are all quasi-coherent and which is a crystal in 𝒪_{X/S}-modules is
  quasi-coherent on the site"]
theorem isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_forall_isAffine M fun B hB ↦
    have := hB
    hasGlobalPresentation_over_of_isAffine hlqc hcrys B

/-- **[Stacks, Tag 07IT] on the big crystalline site `CRIS(X/S)`:** a sheaf of
`𝒪_{X/S}`-modules is quasi-coherent on the site if and only if all its restrictions `F_T` are
quasi-coherent `𝒪_T`-modules and it is a crystal in `𝒪_{X/S}`-modules.

The two halves of the forward implication are
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` and
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite`; the converse is
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_isLocallyQuasiCoherent`.  The
crystal condition is read at sheaf level, which is the reading under which the tag holds; see the
module documentation. -/
@[stacks 07IT "the equivalence on the big site CRIS(X/S), with the crystal condition read with the
  comparison maps of sheaves of modules"]
theorem isQuasicoherentOnSite_iff (M : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    M.IsQuasicoherentOnSite ↔ IsLocallyQuasiCoherent M ∧ IsSheafCrystal M :=
  ⟨fun hM ↦ ⟨isLocallyQuasiCoherent_of_isQuasicoherentOnSite M hM,
      isSheafCrystal_of_isQuasicoherentOnSite M hM⟩,
    fun h ↦ isQuasicoherentOnSite_of_isLocallyQuasiCoherent h.1 h.2⟩

end Crystalline.GlobalCrystallineSituation

end
