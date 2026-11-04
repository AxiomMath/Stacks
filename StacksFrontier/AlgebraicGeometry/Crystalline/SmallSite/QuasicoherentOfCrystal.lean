module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverPresentationLift
public import StacksFrontier.CategoryTheory.Limits.CokernelOfBijectiveFamily

/-!
# A locally quasi-coherent crystal in modules on the small crystalline site is quasi-coherent

This file proves the direction (2) ⇒ (1) of [Stacks, Tag 07IT] on the small crystalline site
`Cris(X/S)` of a global crystalline situation: a sheaf of `𝒪_{X/S}`-modules all of whose
restrictions `F_T` are quasi-coherent `𝒪_T`-modules and which is a crystal in `𝒪_{X/S}`-modules is
quasi-coherent on the site.  The tag is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike,
and a sheaf of modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`, so
the argument is repeated here; it is the big site's, carried out in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentOfCrystal`, whose module
documentation explains how the crystal property is used.

The two ingredients that are new on this site are the Zariski-local reduction to an object with
affine ambient scheme — the big site's is
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine`, and the
restrictions of an object of `Cris(X/S)` to a family of opens covering its ambient scheme form a
covering family of the small site just as they do of the big one — and the recognition of a
cokernel on a localised site from the restrictions to the ambient schemes, which is
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverConservative`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_of_forall_isAffine` — it
  suffices to present a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` globally on the objects whose
  ambient scheme is affine.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal`
  — **the presentation of the affine ambient scheme of `B` restricts to a presentation over every
  object of `Cris(X/S)/B`.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.hasGlobalPresentation_over_of_isAffine` — **a
  locally quasi-coherent crystal in `𝒪_{X/S}`-modules has a global presentation on the localisation
  of `Cris(X/S)` at an object with affine ambient scheme.**
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.isQuasicoherentOnSite_of_isLocallyQuasiCoherent` — **the implication (2) ⇒ (1) of [Stacks, Tag
  07IT] on `Cris(X/S)`.**
* `Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_iff` — **the equivalence
  of [Stacks, Tag 07IT] on `Cris(X/S)`**, read with the sheaf-level crystal condition.

## The reading of the tag

As on the big site, the crystal condition is read at sheaf level, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal`: the reading with the comparison
maps of presheaves of modules makes the tag false against this library, and the correction is set
out in the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCriterion`.

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

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **Global presentations on the restrictions to a Zariski-local family of opens of each ambient
scheme make a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` quasi-coherent.**  The restrictions of an
object to a family of opens covering its ambient scheme form a Zariski covering family of the
small crystalline site, so the opens carrying a global presentation generate a covering sieve. -/
theorem isQuasicoherentOnSite_of_forall_exists_restrictOpen
    (M : SheafOfModules.{u} (structureSheaf S))
    (h : ∀ (A : CrystallineThickening S) (x : A.obj.thickening.target.scheme),
      ∃ V : A.obj.thickening.target.scheme.Opens,
        x ∈ V ∧ (M.over (A.restrictOpen V)).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite := by
  choose V hxV hV using h
  refine ⟨fun A ↦ ?_⟩
  refine ⟨ULift.{u + 1} ↥A.obj.thickening.target.scheme,
    fun i : ULift.{u + 1} ↥A.obj.thickening.target.scheme ↦ A.restrictOpen (V A i.down),
    fun i ↦ A.restrictOpenHom (V A i.down), ?_, fun i ↦ hV A i.down⟩
  exact smallZariskiCovering_mem_smallTopology S
    (A.restrictOpenCover (ι := ULift.{u + 1} ↥A.obj.thickening.target.scheme)
      fun i ↦ V A i.down)
    (CrystallineThickening.isZariskiCovering_restrictOpenCover A _
      fun y ↦ ⟨ULift.up y, hxV A y⟩)

/-- **It suffices to present a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` globally on the objects
whose ambient scheme is affine.**  This is the shape in which the direction (2) ⇒ (1) of
[Stacks, Tag 07IT] uses the Zariski-local reduction: every object is covered by its restrictions
to the affine opens of its ambient scheme, and the ambient scheme of such a restriction is the
affine open subscheme. -/
theorem isQuasicoherentOnSite_of_forall_isAffine (M : SheafOfModules.{u} (structureSheaf S))
    (h : ∀ B : CrystallineThickening S, IsAffine B.obj.thickening.target.scheme →
      (M.over B).HasGlobalPresentation) :
    M.IsQuasicoherentOnSite := by
  refine isQuasicoherentOnSite_of_forall_exists_restrictOpen M fun A x ↦ ?_
  obtain ⟨W, hWaff, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  exact ⟨W, hxW, h (A.restrictOpen W) hWaff⟩

namespace CohomologyRestriction

/-- Sheaves of modules on the Zariski site of the ambient scheme of an object have coproducts
indexed by any type of the universe `u` of their sections. -/
theorem hasColimitsOfShape_discrete_ambient (A : CrystallineThickening S) (I : Type u) :
    HasColimitsOfShape (Discrete I)
      (SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) := by
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      AddCommGrpCat.{u} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} _
  infer_instance

section

attribute [local instance] hasColimitsOfShape_discrete_ambient

/-- **The coproduct of `I` copies of the structure sheaf of the Zariski site of the ambient scheme
of an object**, at the module universe `u`. -/
noncomputable def ambientCoproduct (A : CrystallineThickening S) (I : Type u) :
    SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj) :=
  ∐ fun _ : I ↦ SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj)

/-- The inclusion of the `i`-th summand of
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.ambientCoproduct`. -/
noncomputable def ambientCoproductι (A : CrystallineThickening S) (I : Type u) (i : I) :
    SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj) ⟶ ambientCoproduct A I :=
  Sigma.ι (fun _ : I ↦ SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj)) i

/-- The cofan of the inclusions of
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.ambientCoproduct` is a
colimit. -/
noncomputable def isColimitAmbientCoproductCofan (A : CrystallineThickening S) (I : Type u) :
    IsColimit (Cofan.mk (ambientCoproduct A I) (ambientCoproductι A I)) :=
  coproductIsCoproduct fun _ : I ↦ SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj)

end

variable (B : CrystallineThickening S)

/-- Pushforward of sheaves of modules along the morphism of ambient structure sheaves induced by
a morphism `g : A ⟶ B` of the small crystalline site preserves zero morphisms. -/
instance preservesZeroMorphisms_pushforward_ringRestrictionSheafFMap
    {A : CrystallineThickening S} (g : A ⟶ B) :
    (SheafOfModules.pushforward.{u + 1}
      (Thickening.ringRestrictionSheafFMap g.hom)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Composition with the `f`-map of the structure morphism of an object of a localised small
crystalline site carries the zero morphism to the zero morphism. -/
theorem fmapCompOver_toTerminalOver_zero (X : Over B)
    (N : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (Z : SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf X.left.obj)) :
    fmapCompOver.{u + 1} N (toTerminalOver B X) Z 0 = 0 := by
  change moduleFMapSheafOver N (toTerminalOver B X) ≫
    (SheafOfModules.pushforward.{u + 1}
      (Thickening.ringRestrictionSheafFMap (toTerminalOver B X).left.hom)).map 0 = 0
  rw [Functor.map_zero, comp_zero]

/-- **Composition with the `f`-map of the structure morphism of an object of a localised small
crystalline site is bijective at the universe lift of the structure sheaf**, when the test module
is a universe lift. -/
theorem bijective_fmapCompOver_toTerminalOver_uliftUnit (X : Over B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)) :
    Function.Bijective (fmapCompOver.{u + 1} (CrystallineThickening.uliftUnitOver B)
      (toTerminalOver B X) ((ambientUliftFunctor X.left).obj Z)) :=
  (bijective_fmapCompOver_uliftForPresentation_iff
      (SheafOfModules.unit ((structureSheaf S).over B)) (toTerminalOver B X) Z).2
    ((bijective_fmapCompOverLift_iff _ (toTerminalOver B X) Z).2
      (bijective_fmapCompOver_unit (toTerminalOver B X) Z))

/-- **Composition with the `f`-map of the structure morphism of an object of a localised small
crystalline site is bijective at the universe lift of a module exactly when the comparison map of
that structure morphism is invertible**, when the test module is a universe lift.  For a crystal in
`𝒪_{X/S}`-modules the right-hand side holds. -/
theorem bijective_fmapCompOver_toTerminalOver_uliftOver
    (M : SheafOfModules.{u} (structureSheaf S)) (X : Over B)
    (hX : IsIso (moduleComparisonSheaf M X.hom))
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj)) :
    Function.Bijective
      (fmapCompOver.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (M.over B)) (toTerminalOver B X) ((ambientUliftFunctor X.left).obj Z)) :=
  (bijective_fmapCompOver_uliftForPresentation_iff (M.over B) (toTerminalOver B X) Z).2
    ((bijective_fmapCompOverLift_iff (M.over B) (toTerminalOver B X) Z).2
      ((bijective_fmapCompOver_over_iff M (toTerminalOver B X) Z).2
        ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp M X.hom).1 hX Z)))

/-- **The restriction of a crystalline coproduct over a universe-lifted index type to the ambient
scheme of an object over the base is the universe lift of a coproduct at the module universe
`u`.** -/
noncomputable def restrictOverCrystallineCoproductUliftIso (I₀ : Type u)
    {A : CrystallineThickening S} (h : A ⟶ B) :
    (moduleRestrictionSheafOverFunctor.{u + 1} h).obj
        (CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀)) ≅
      (ambientUliftFunctor A).obj (ambientCoproduct A I₀) := by
  haveI := preservesColimitsOfSize_ambientUliftFunctor A
  have hT : IsColimit (Cofan.mk ((ambientUliftFunctor A).obj (ambientCoproduct A I₀))
      (fun j : ULift.{u + 1} I₀ ↦ (ambientUliftFunctor A).map (ambientCoproductι A I₀ j.down)) :
        Cofan fun _ : ULift.{u + 1} I₀ ↦ (ambientUliftFunctor A).obj
          (SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj))) :=
    isColimit_cofan_ulift _ (isColimitCofanMkObjOfIsColimit (ambientUliftFunctor A) _
      (ambientCoproductι A I₀) (isColimitAmbientCoproductCofan A I₀))
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) h) hT

/-- **The universal property of the cokernel transfers from the ambient scheme of `B` to the
ambient scheme of an arbitrary object of `Cris(X/S)/B`, against test modules which are universe
lifts.**  This is where the crystal property of `F` is used. -/
theorem existsUnique_comp_moduleRestrictionSheafOver_of_isSheafCrystal
    {M : SheafOfModules.{u} (structureSheaf S)} (hcrys : IsSheafCrystal M) {I₀ K₀ : Type u}
    {a : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} K₀) ⟶
      CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀)}
    {b : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)}
    (hab : a ≫ b = 0)
    (h₂ : IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab)))
    (X : Over B) (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf X.left.obj))
    (k : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).obj
      (CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀)) ⟶
      (ambientUliftFunctor X.left).obj Z)
    (hk : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map a ≫ k = 0) :
    ∃! m : (ambientUliftFunctor X.left).obj
        ((moduleRestrictionSheafOverFunctor.{u} X.hom).obj (M.over B)) ⟶
      (ambientUliftFunctor X.left).obj Z,
      (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map b ≫ m = k := by
  have hθ : ∀ {N₁ N₂ : SheafOfModules.{u + 1} ((structureSheaf S).over B)} (ψ : N₁ ⟶ N₂)
      (kk : (moduleRestrictionSheafOverFunctor.{u + 1} X.hom).obj N₂ ⟶
        (ambientUliftFunctor X.left).obj Z),
      fmapCompOver.{u + 1} N₁ (toTerminalOver B X) ((ambientUliftFunctor X.left).obj Z)
          ((moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map ψ ≫ kk) =
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map ψ ≫
          fmapCompOver.{u + 1} N₂ (toTerminalOver B X)
            ((ambientUliftFunctor X.left).obj Z) kk :=
    fun ψ kk ↦ fmapCompOver_naturality ψ (toTerminalOver B X) _ kk
  have hP : Function.Bijective (fmapCompOver.{u + 1}
      (CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀)) (toTerminalOver B X)
      ((ambientUliftFunctor X.left).obj Z)) :=
    Stacks.PresentedBijectivity.bijective_of_cofan hθ
      (CrystallineThickening.crystallineCoproductι B (ULift.{u + 1} I₀))
      (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) X.hom)
      (isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} I₀) (𝟙 B))
      (bijective_fmapCompOver_toTerminalOver_uliftUnit B X Z)
  exact existsUnique_comp_of_bijective hθ h₂ (fmapCompOver_toTerminalOver_zero B X _ _) hP
    (bijective_fmapCompOver_toTerminalOver_uliftOver B M X (hcrys X.left B X.hom) Z) k hk

/-- **The presentation of the affine ambient scheme of `B`, restricted to the ambient scheme of an
arbitrary object of `Cris(X/S)/B`, is still a presentation.**  This is the step of the direction
(2) ⇒ (1) of [Stacks, Tag 07IT] at which the crystal property is used: the restriction `F_{T'}`
over an object of the localised site is the pullback of `F_T`, so the presentation
base-changes. -/
noncomputable def isColimitCokernelCoforkRestrictOverOfIsSheafCrystal
    {M : SheafOfModules.{u} (structureSheaf S)} (hcrys : IsSheafCrystal M) {I₀ K₀ : Type u}
    {a : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} K₀) ⟶
      CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀)}
    {b : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
      SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)}
    (hab : a ≫ b = 0)
    (h₂ : IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab)))
    (X : Over B) :
    IsColimit (CokernelCofork.ofπ
      ((moduleRestrictionSheafOverFunctor.{u + 1} X.hom).map b)
      (moduleRestrictionSheafOver_map_comp_eq_zero B X.hom hab)) :=
  haveI := preservesFiniteColimits_ambientUliftFunctor X.left
  isColimitCokernelCoforkOfDescent (ambientUliftFunctor X.left)
    (Q₀ := ambientCoproduct X.left K₀) (P₀ := ambientCoproduct X.left I₀)
    (N₀ := (moduleRestrictionSheafOverFunctor.{u} X.hom).obj (M.over B))
    (restrictOverCrystallineCoproductUliftIso B K₀ X.hom)
    (restrictOverCrystallineCoproductUliftIso B I₀ X.hom) (Iso.refl _)
    (moduleRestrictionSheafOver_map_comp_eq_zero B X.hom hab)
    ((ambientUliftFunctor X.left).map_preimage _) ((ambientUliftFunctor X.left).map_preimage _)
    (fun Z k hk ↦ existsUnique_comp_moduleRestrictionSheafOver_of_isSheafCrystal
      B hcrys hab h₂ X Z k hk)

/-- Sheaves of `𝒪_{X/S}`-modules on a localised small crystalline site have cokernels at the
module universe `u + 1`. -/
theorem hasCokernels_sheafOfModules_over :
    HasCokernels (SheafOfModules.{u + 1} ((structureSheaf S).over B)) := by
  have := CrystallineThickening.hasSheafify_over_addCommGrpCat_succ B
  have := CrystallineThickening.wEqualsLocallyBijective_over_addCommGrpCat_succ B
  infer_instance

end CohomologyRestriction

/-- **A locally quasi-coherent crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` has a global
presentation on the localisation of `Cris(X/S)` at an object with affine ambient scheme.** -/
theorem hasGlobalPresentation_over_of_isAffine
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.target.scheme] :
    (M.over B).HasGlobalPresentation := by
  obtain ⟨I₀, K₀, a, b, hab, ⟨h₂⟩⟩ :=
    exists_crystallineCoproduct_cokernelCofork_restrictOver hlqc B
  have := CohomologyRestriction.hasCokernels_sheafOfModules_over B
  refine ⟨ULift.{u + 1} I₀, ULift.{u + 1} K₀,
    CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀),
    CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} K₀),
    CrystallineThickening.crystallineCoproductι B (ULift.{u + 1} I₀),
    CrystallineThickening.crystallineCoproductι B (ULift.{u + 1} K₀),
    ⟨CrystallineThickening.isColimitCrystallineCoproductCofan B (ULift.{u + 1} I₀)⟩,
    ⟨CrystallineThickening.isColimitCrystallineCoproductCofan B (ULift.{u + 1} K₀)⟩,
    a, b, hab, ⟨?_⟩⟩
  exact CohomologyRestriction.isColimitCokernelCoforkOfForallRestrictOver B hab
    (fun Y ↦ CohomologyRestriction.isColimitCokernelCoforkRestrictOverOfIsSheafCrystal
      B hcrys hab h₂ Y)

/-- **The implication (2) ⇒ (1) of [Stacks, Tag 07IT] on the small crystalline site `Cris(X/S)`: a
locally quasi-coherent sheaf of `𝒪_{X/S}`-modules which is a crystal in `𝒪_{X/S}`-modules is
quasi-coherent on the site.**

Quasi-coherence is Zariski-local on the ambient scheme of each object
(`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_of_forall_isAffine`), so
it is enough to present `F` globally on the localisation of `Cris(X/S)` at an object whose ambient
scheme is affine, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.hasGlobalPresentation_over_of_isAffine`.

The crystal condition is read at sheaf level, as
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal`; that is the reading under which
the tag holds, and the two hypotheses are exactly the source's conditions (a) and (b). -/
@[stacks 07IT "the implication (2) ⇒ (1) on the small site Cris(X/S): a sheaf of 𝒪_{X/S}-modules
  whose restrictions F_T are all quasi-coherent and which is a crystal in 𝒪_{X/S}-modules is
  quasi-coherent on the site"]
theorem isQuasicoherentOnSite_of_isLocallyQuasiCoherent
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_forall_isAffine M fun B hB ↦
    have := hB
    hasGlobalPresentation_over_of_isAffine hlqc hcrys B

/-- **[Stacks, Tag 07IT] on the small crystalline site `Cris(X/S)`:** a sheaf of
`𝒪_{X/S}`-modules is quasi-coherent on the site if and only if all its restrictions `F_T` are
quasi-coherent `𝒪_T`-modules and it is a crystal in `𝒪_{X/S}`-modules.

The two halves of the forward implication are
`Crystalline.GlobalCrystallineSituation.SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`
and `Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`; the
converse is
`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_of_isLocallyQuasiCoherent`.
The crystal condition is read at sheaf level, which is the reading under which the tag holds; see
the module documentation. -/
@[stacks 07IT "the equivalence on the small site Cris(X/S), with the crystal condition read with
  the comparison maps of sheaves of modules"]
theorem isQuasicoherentOnSite_iff (M : SheafOfModules.{u} (structureSheaf S)) :
    M.IsQuasicoherentOnSite ↔ IsLocallyQuasiCoherent M ∧ IsSheafCrystal M :=
  ⟨fun hM ↦ ⟨isLocallyQuasiCoherent_of_isQuasicoherentOnSite M hM,
      isSheafCrystal_of_isQuasicoherentOnSite M hM⟩,
    fun h ↦ isQuasicoherentOnSite_of_isLocallyQuasiCoherent h.1 h.2⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
