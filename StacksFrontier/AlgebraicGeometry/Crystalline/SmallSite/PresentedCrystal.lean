module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalFirstOrderComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal

/-!
# A globally presented sheaf of modules on the small crystalline site is a crystal

This is the small-site form of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal`:
**a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` with a global presentation is a crystal in
`𝒪_{X/S}`-modules.**  [Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)`
alike, and the argument is the big site's; it is repeated here because a sheaf of modules on
`Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`.  Everything about why the
module universe of a global presentation is not an obstruction to this implication is set out in
the big site's module documentation, and the two abstract steps,
`Stacks.PresentedBijectivity.bijective_of_cofan` and
`Stacks.PresentedBijectivity.bijective_of_cofork`, are reused from there.

## Main results

* `...SmallSite.CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp` — the
  crystal condition at a morphism of `Cris(X/S)`, tested without the pullback.
* `...SmallSite.isSheafCrystal_of_hasGlobalPresentation` — **a sheaf of `𝒪_{X/S}`-modules on
  `Cris(X/S)` with a global presentation is a crystal in `𝒪_{X/S}`-modules.**

## What this file proves, and where the tag is delivered

No `@[stacks]` attribute is placed here, because the hypothesis is stronger than quasi-coherence:
a global presentation on all of `Cris(X/S)`, whereas quasi-coherence gives one on the members of a
covering of each object.  The source's reduction "since it suffices to prove (a) and (b) Zariski
locally" bridges the two, in
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverCrystal`, which redoes this
computation on a localised site, and in
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal`, which glues over a
Zariski cover and proves the implication (1) ⇒ (2)(b) itself as
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`.  The
same two files for the big site are named in the big site's module documentation.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe m u u₁ v₁

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

attribute [local instance] CrystallineThickening.restrictOpenFunctor_isContinuous
  CrystallineThickening.restrictOpenFunctor_isCocontinuous

variable {S : GlobalCrystallineSituation.{u}} {A B : CrystallineThickening S}

/-- The comparison of structure sheaves for the restriction to the ambient scheme of an object of
`Cris(X/S)` is the identity: the restriction of `𝒪_{X/S}` to the opens of the ambient scheme *is*
its restriction along the restriction functor. -/
noncomputable def restrictOpenStructureHom (A : CrystallineThickening S) :
    Thickening.ringRestrictionSheaf A.obj ⟶
      ((CrystallineThickening.restrictOpenFunctor A).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology A.obj.thickening.target.scheme) (smallTopology S)).obj
          (structureSheaf S) :=
  𝟙 _

/-- **The restriction `F ↦ F_T` of [Stacks, Tag 07IQ] on `Cris(X/S)` as a functor, at an arbitrary
module universe.** -/
noncomputable def moduleRestrictionSheafFunctor (A : CrystallineThickening S) :
    SheafOfModules.{m} (structureSheaf S) ⥤
      SheafOfModules.{m} (Thickening.ringRestrictionSheaf A.obj) :=
  SheafOfModules.pushforward.{m} (restrictOpenStructureHom A)

/-- At the universe `u`, the functor `moduleRestrictionSheafFunctor A` sends `M` to
`moduleRestrictionSheaf M A`. -/
@[simp]
theorem moduleRestrictionSheafFunctor_obj (M : SheafOfModules.{u} (structureSheaf S))
    (A : CrystallineThickening S) :
    (moduleRestrictionSheafFunctor.{u} A).obj M = moduleRestrictionSheaf M A := rfl

/-- **Restriction to the ambient scheme preserves colimits of size `u + 1`**, the size in which a
global presentation on the small crystalline site is indexed. -/
theorem preservesColimitsOfSize_moduleRestrictionSheafFunctor (A : CrystallineThickening S) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} (structureSheaf S) ⥤
          SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A.obj) from
        moduleRestrictionSheafFunctor.{u + 1} A) := by
  have _ : HasSheafify (smallTopology S) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : (smallTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (CrystallineThickening.restrictOpenFunctor A) (restrictOpenStructureHom A)

/-- **The `f`-map of [Stacks, Tag 07IQ] on `Cris(X/S)` at an arbitrary module universe.** -/
noncomputable def moduleFMapSheafOfUniv (M : SheafOfModules.{m} (structureSheaf S)) (g : A ⟶ B) :
    (moduleRestrictionSheafFunctor.{m} B).obj M ⟶
      (SheafOfModules.pushforward.{m} (Thickening.ringRestrictionSheafFMap g.hom)).obj
        ((moduleRestrictionSheafFunctor.{m} A).obj M) :=
  ⟨PresheafOfModules.pushforwardOfNatTrans (CrystallineThickening.restrictOpenFunctorMap g)
    (crisRing S) M.val⟩

/-- At the universe `u`, the map `moduleFMapSheafOfUniv M g` is `moduleFMapSheaf M g`. -/
theorem moduleFMapSheafOfUniv_eq (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B) :
    moduleFMapSheafOfUniv.{u} M g = moduleFMapSheaf M g := rfl

/-- **Composition with the `f`-map on `Cris(X/S)`**, the transpose of postcomposition with the
comparison map of sheaves of modules.  It is defined at an arbitrary module universe, and it
mentions no pullback. -/
noncomputable def fmapComp (M : SheafOfModules.{m} (structureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A.obj)) :
    ((moduleRestrictionSheafFunctor.{m} A).obj M ⟶ Z) →
      ((moduleRestrictionSheafFunctor.{m} B).obj M ⟶
        (SheafOfModules.pushforward.{m} (Thickening.ringRestrictionSheafFMap g.hom)).obj Z) :=
  fun k ↦ moduleFMapSheafOfUniv M g ≫
    (SheafOfModules.pushforward.{m} (Thickening.ringRestrictionSheafFMap g.hom)).map k

/-- **Composition with the `f`-map is natural in the module**, contravariantly. -/
theorem fmapComp_naturality {M N : SheafOfModules.{m} (structureSheaf S)} (ψ : M ⟶ N)
    (g : A ⟶ B) (Z : SheafOfModules.{m} (Thickening.ringRestrictionSheaf A.obj))
    (k : (moduleRestrictionSheafFunctor.{m} A).obj N ⟶ Z) :
    fmapComp M g Z ((moduleRestrictionSheafFunctor.{m} A).map ψ ≫ k) =
      (moduleRestrictionSheafFunctor.{m} B).map ψ ≫ fmapComp N g Z k := by
  have h : (moduleRestrictionSheafFunctor.{m} B).map ψ ≫ moduleFMapSheafOfUniv N g =
      moduleFMapSheafOfUniv M g ≫
        (SheafOfModules.pushforward.{m} (Thickening.ringRestrictionSheafFMap g.hom)).map
          ((moduleRestrictionSheafFunctor.{m} A).map ψ) := by
    apply SheafOfModules.Hom.ext
    ext W x
    exact (PresheafOfModules.naturality_apply ψ.val
      (CrystallineThickening.restrictOpenMap g W.unop).op x).symm
  simp only [fmapComp, Functor.map_comp]
  rw [← Category.assoc, ← h, Category.assoc]

/-- The transposition identity: composing with the `f`-map is the transpose of composing with the
comparison map of sheaves of modules. -/
theorem homEquiv_moduleComparisonSheaf_comp (M : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (k : moduleRestrictionSheaf M A ⟶ Z) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
        (moduleRestrictionSheaf M B) Z (moduleComparisonSheaf M g ≫ k) =
      fmapComp.{u} M g Z k := by
  rw [Adjunction.homEquiv_naturality_right, moduleComparisonSheaf, Equiv.apply_symm_apply]
  rfl

/-- **The crystal condition at a morphism of `Cris(X/S)`, tested without the pullback.** -/
theorem isIso_moduleComparisonSheaf_iff_bijective_fmapComp
    (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B) :
    IsIso (moduleComparisonSheaf M g) ↔
      ∀ Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj),
        Function.Bijective (fmapComp.{u} M g Z) := by
  rw [isIso_iff_coyoneda_map_bijective]
  refine forall_congr' fun Z ↦ ?_
  have hfun : (fun k : moduleRestrictionSheaf M A ⟶ Z ↦
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv (moduleRestrictionSheaf M B) Z
            (moduleComparisonSheaf M g ≫ k)) = fmapComp.{u} M g Z :=
    funext (homEquiv_moduleComparisonSheaf_comp M g Z)
  rw [← hfun]
  exact ((Equiv.bijective ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
      (moduleRestrictionSheaf M B) Z)).of_comp_iff' _).symm

/-- **Composition with the `f`-map at the raised module universe, read on the universe lifts of
the modules at the module universe `u`.** -/
noncomputable def fmapCompLift (N : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafFunctor.{u} A).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) →
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((moduleRestrictionSheafFunctor.{u} B).obj N) ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
          ((SheafOfModules.pushforward.{u}
            (Thickening.ringRestrictionSheafFMap g.hom)).obj Z)) :=
  fmapComp.{u + 1} (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
    (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)

/-- **Composition with the `f`-map commutes with a universe lift of the module sections**, all
three of the restriction, the pushforward and the `f`-map being computed on sections. -/
theorem fmapCompLift_uliftForPresentationMap (N : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (k : (moduleRestrictionSheafFunctor.{u} A).obj N ⟶ Z) :
    fmapCompLift N g Z (SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} (fmapComp.{u} N g Z k) := by
  apply SheafOfModules.Hom.ext
  ext W x
  rfl

/-- **Composition with the `f`-map is bijective exactly when its universe lift is.** -/
theorem bijective_fmapCompLift_iff (N : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Bijective (fmapCompLift N g Z) ↔ Function.Bijective (fmapComp.{u} N g Z) := by
  have h₁ := Thickening.bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafFunctor.{u} A).obj N) Z
  have h₂ := Thickening.bijective_uliftForPresentationMap.{u, u, u}
    ((moduleRestrictionSheafFunctor.{u} B).obj N)
    ((SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g.hom)).obj Z)
  have hsq : (fmapCompLift N g Z) ∘
        (fun k : (moduleRestrictionSheafFunctor.{u} A).obj N ⟶ Z ↦
          SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) =
      (fun k ↦ SheafOfModules.uliftForPresentationMap.{u, u, u, u, u + 1} k) ∘
        (fmapComp.{u} N g Z) :=
    funext (fmapCompLift_uliftForPresentationMap N g Z)
  refine ⟨fun h ↦ (h₂.of_comp_iff' _).1 ?_, fun h ↦ (Function.Bijective.of_comp_iff _ h₁).1 ?_⟩
  · rw [← hsq]
    exact h.comp h₁
  · rw [hsq]
    exact h₂.comp h

/-- **Composition with the `f`-map is bijective at the structure sheaf**, at the raised module
universe: the comparison map of `𝒪_{X/S}` on `Cris(X/S)` is an isomorphism, the structure sheaf
being the restriction of that of `CRIS(X/S)`, which is a crystal. -/
theorem bijective_fmapCompLift_unit (g : A ⟶ B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Bijective (fmapCompLift (SheafOfModules.unit (structureSheaf S)) g Z) :=
  (bijective_fmapCompLift_iff _ g Z).2
    ((isIso_moduleComparisonSheaf_iff_bijective_fmapComp _ g).1
      (isSheafCrystal_restrictUnit S A B g) Z)

/-- Composition with the `f`-map at the raised universe, in its own spelling and in the spelling
`...SmallSite.CohomologyRestriction.fmapCompLift` gives it, are the same map. -/
theorem bijective_fmapComp_uliftForPresentation_iff (N : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Bijective (fmapComp.{u + 1}
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} N) g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) ↔
      Function.Bijective (fmapCompLift N g Z) :=
  Iff.rfl

/-- **A globally presented sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` has bijective `f`-map
composition**, by the computation the source of [Stacks, Tag 07IT] performs for the implication
(1) ⇒ (2)(b). -/
theorem bijective_fmapCompLift_of_hasGlobalPresentation
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : M.HasGlobalPresentation) (g : A ⟶ B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Bijective (fmapCompLift M g Z) := by
  have hA := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} A
  have hB := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} B
  have hpres : ∀ C : CrystallineThickening S, PreservesColimitsOfSize.{0, 0}
      (show SheafOfModules.{u + 1} (structureSheaf S) ⥤
        SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf C.obj) from
          moduleRestrictionSheafFunctor.{u + 1} C) := fun C ↦ by
    have := preservesColimitsOfSize_moduleRestrictionSheafFunctor.{u} C
    exact preservesColimitsOfSize_shrink _
  have hA' := hpres A
  have hB' := hpres B
  refine (bijective_fmapComp_uliftForPresentation_iff M g Z).1 ?_
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hcoker⟩⟩ := hM
  have hθ : ∀ {M' N' : SheafOfModules.{u + 1} (structureSheaf S)} (ψ : M' ⟶ N')
      (k : (moduleRestrictionSheafFunctor.{u + 1} A).obj N' ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z),
      fmapComp.{u + 1} M' g (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)
          ((moduleRestrictionSheafFunctor.{u + 1} A).map ψ ≫ k) =
        (moduleRestrictionSheafFunctor.{u + 1} B).map ψ ≫
          fmapComp.{u + 1} N' g (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z) k :=
    fun ψ k ↦ fmapComp_naturality ψ g _ k
  have hunit : Function.Bijective (fmapComp.{u + 1}
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit (structureSheaf S))) g
      (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    (bijective_fmapComp_uliftForPresentation_iff _ g Z).2 (bijective_fmapCompLift_unit g Z)
  have hcofan : ∀ {J : Type (u + 1)} {X : SheafOfModules.{u + 1} (structureSheaf S)}
      (ε : J → (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit (structureSheaf S)) ⟶ X)), IsColimit (Cofan.mk X ε) →
      Function.Bijective (fmapComp.{u + 1} X g
        (SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1} Z)) :=
    fun ε hX ↦ Stacks.PresentedBijectivity.bijective_of_cofan hθ ε
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafFunctor.{u + 1} A) _ _)
        (isColimitOfPreserves _ hX))
      ((Cofan.isColimitMapCoconeEquiv (moduleRestrictionSheafFunctor.{u + 1} B) _ _)
        (isColimitOfPreserves _ hX)) hunit
  have hab' : a ≫ b = 0 ≫ b := by rw [hab, zero_comp]
  exact Stacks.PresentedBijectivity.bijective_of_cofork hθ
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafFunctor.{u + 1} A) hab'
      (isColimitOfPreserves _ hcoker))
    (isColimitMapCoconeCoforkEquiv (moduleRestrictionSheafFunctor.{u + 1} B) hab'
      (isColimitOfPreserves _ hcoker)) (hcofan ι hP) (hcofan κ hQ).1

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- **Stacks Project, Tag 07IT, the implication (1) ⇒ (2)(b) for a globally presented module on
`Cris(X/S)`:** a sheaf of `𝒪_{X/S}`-modules on the small crystalline site with a global
presentation is a crystal in `𝒪_{X/S}`-modules. -/
theorem isSheafCrystal_of_hasGlobalPresentation {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : M.HasGlobalPresentation) :
    IsSheafCrystal M := fun _ _ g ↦
  (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M g).2 fun Z ↦
    (CohomologyRestriction.bijective_fmapCompLift_iff M g Z).1
      (CohomologyRestriction.bijective_fmapCompLift_of_hasGlobalPresentation M hM g Z)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
