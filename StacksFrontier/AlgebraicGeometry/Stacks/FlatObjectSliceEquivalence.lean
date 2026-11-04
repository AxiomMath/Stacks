module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfModuleLowerShriekLocalization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCokernelLocallyNoetherian

/-!
# The slice of an algebraic stack at an object is the big site of the scheme below it

Let `𝒳` be an algebraic stack and `y` an object of `𝒳` lying over the scheme `T`. The
1-morphism `V ⟶ 𝒳` named by `y` (`AlgebraicGeometry.Stack.ambientSliceMorphism`) is the functor
`(a : W ⟶ T) ↦ a^*y` out of `(Sch/T)_{fppf}`, and the chosen cartesian lifts `a^*y ⟶ y` lift it
to a functor `(Sch/T)_{fppf} ⥤ 𝒳/y`. That lift is an equivalence of sites
`(Sch/T)_{fppf} ≌ 𝒳_{fppf}/y` (Stacks 06WI), strictly over the base, and restriction along it
carries the restriction `M|_{𝒳/y}` of a sheaf of modules to the inverse image `y^{-1}M` of `M`
along the 1-morphism named by `y`. So `M|_{𝒳/y}` has a global presentation exactly when `y^{-1}M`
does.

## References

* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} {Q : ObjectProperty 𝒳.val.val.obj}
  (y : Q.FullSubcategory)

/-- **The lift of the slice 1-morphism of `y` to the slice `𝒳/y`**: `(a : W ⟶ T) ↦ (a^*y ⟶ y)`,
the chosen cartesian lift. Composed with the forgetful functor of `𝒳/y` it is the slice
1-morphism on the nose. -/
def sliceLift : Over (𝒳.val.val.p.obj y.obj) ⥤ Over y.obj :=
  Over.lift (ambientSliceMorphism B S hS y).hom.hom.toFunctor
    ({ app := fun a ↦ (ambientChoiceOfPullbacks B S hS 𝒳).map a.hom ⟨y.obj, rfl⟩
       naturality := fun _ _ h ↦
        (Functor.ChoiceOfPullbacks.sliceFunctor_map_fac _ _ h).trans (Category.comp_id _).symm } :
      (ambientSliceMorphism B S hS y).hom.hom.toFunctor ⟶
        (Functor.const (Over (𝒳.val.val.p.obj y.obj))).obj y.obj)

/-- The lift of the slice 1-morphism followed by the forgetful functor `𝒳/y ⥤ 𝒳` is the slice
1-morphism of `y`. -/
lemma sliceLift_comp_forget :
    sliceLift B S hS y ⋙ Over.forget y.obj = (ambientSliceMorphism B S hS y).hom.hom.toFunctor :=
  rfl

/-- The lift of the slice 1-morphism is strictly over the base. -/
lemma sliceLift_comp_forget_comp_p :
    sliceLift B S hS y ⋙ (Over.forget y.obj ⋙ 𝒳.val.val.p) =
      Over.forget (𝒳.val.val.p.obj y.obj) :=
  Functor.ChoiceOfPullbacks.sliceFunctor_comp _ _

private lemma eqToHom_comp_comp_eqToHom_comp_eqToHom {C : Type*} [Category C] {A A' B B' : C}
    (p : A' = A) (f : A ⟶ B) (q : B = B') (r : B' = B) :
    (eqToHom p ≫ f ≫ eqToHom q) ≫ eqToHom r = eqToHom p ≫ f := by
  subst q
  simp

/-- For `a : W ⟶ T`, the image of the chosen lift `a^*y ⟶ y` under the projection to `(Sch/T)`
is `a`, up to the identification of `p(a^*y)` with `W`. -/
lemma sliceLift_comp_overPost_obj_hom (a : Over (𝒳.val.val.p.obj y.obj)) :
    ((sliceLift B S hS y ⋙ Over.post 𝒳.val.val.p).obj a).hom =
      eqToHom ((ambientChoiceOfPullbacks B S hS 𝒳).obj a.hom ⟨y.obj, rfl⟩).2 ≫ a.hom := by
  have := ((ambientChoiceOfPullbacks B S hS 𝒳).isStronglyCartesian a.hom ⟨y.obj, rfl⟩).toIsHomLift
  exact (IsHomLift.fac' 𝒳.val.val.p a.hom
    ((ambientChoiceOfPullbacks B S hS 𝒳).map a.hom ⟨y.obj, rfl⟩)).trans (by simp)

/-- For a morphism `h : a ⟶ b` over `T`, the image under the projection `𝒳 ⥤ (Sch/T)` of the
induced morphism `a^*y ⟶ b^*y` is `h`, up to the identifications of `p(a^*y)` and `p(b^*y)` with
the sources of `a` and `b`. -/
lemma sliceLift_comp_overPost_map_left {a b : Over (𝒳.val.val.p.obj y.obj)} (h : a ⟶ b) :
    ((sliceLift B S hS y ⋙ Over.post 𝒳.val.val.p).map h).left ≫
        eqToHom ((ambientChoiceOfPullbacks B S hS 𝒳).obj b.hom ⟨y.obj, rfl⟩).2 =
      eqToHom ((ambientChoiceOfPullbacks B S hS 𝒳).obj a.hom ⟨y.obj, rfl⟩).2 ≫ h.left := by
  have := Functor.ChoiceOfPullbacks.sliceFunctor_map_isHomLift
    (ambientChoiceOfPullbacks B S hS 𝒳) ⟨y.obj, rfl⟩ h
  have hh := IsHomLift.fac' 𝒳.val.val.p h.left
    (((ambientChoiceOfPullbacks B S hS 𝒳).sliceFunctor ⟨y.obj, rfl⟩).map h)
  exact (congrArg (· ≫ _) hh).trans (eqToHom_comp_comp_eqToHom_comp_eqToHom _ _ _ _)

/-- The lift of the slice 1-morphism followed by the projection `𝒳/y ⥤ (Sch/T)` is isomorphic to
the identity: the chosen pullback `a^*y` lies over the source of `a`, and its chosen lift to `y`
lies over `a`. -/
def sliceLiftCompOverPostIso :
    sliceLift B S hS y ⋙ Over.post 𝒳.val.val.p ≅ 𝟭 (Over (𝒳.val.val.p.obj y.obj)) :=
  NatIso.ofComponents
    (fun a ↦ Over.isoMk (eqToIso ((ambientChoiceOfPullbacks B S hS 𝒳).obj a.hom ⟨y.obj, rfl⟩).2)
      (sliceLift_comp_overPost_obj_hom B S hS y a).symm)
    (fun h ↦ Over.OverMorphism.ext (sliceLift_comp_overPost_map_left B S hS y h))

/-- **The lift of the slice 1-morphism is an equivalence** `(Sch/T)_{fppf} ≌ 𝒳/y`: composed with
the equivalence `𝒳/y ≌ (Sch/T)` of a category fibred in groupoids it is isomorphic to the
identity. -/
theorem isEquivalence_sliceLift : (sliceLift B S hS y).IsEquivalence := by
  have := 𝒳.val.isFiberedInGroupoids.isEquivalence_overPost y.obj
  have : (sliceLift B S hS y ⋙ Over.post 𝒳.val.val.p).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso (sliceLiftCompOverPostIso B S hS y)).mpr inferInstance
  exact Functor.isEquivalence_of_comp_right _ (Over.post 𝒳.val.val.p)

/-- Global presentations are unchanged by reading the scalars through an equality of sheaves of
rings. -/
theorem _root_.Stacks.SheafOfModules.hasGlobalPresentation_of_iso_pushforward_eqToHom
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R₀ R₁ : Sheaf J RingCat.{u}}
    (h : R₀ = R₁) (P : _root_.SheafOfModules.{u} R₀) (Y : _root_.SheafOfModules.{u} R₁)
    (i : Y ≅ (_root_.SheafOfModules.pushforward.{u} (F := 𝟭 C) (eqToHom h.symm)).obj P)
    (hY : Y.HasGlobalPresentation) : P.HasGlobalPresentation := by
  subst h
  exact SheafOfModules.HasGlobalPresentation.of_iso
    (i ≪≫ (_root_.SheafOfModules.pushforwardId _).app P) hY

/-- A global presentation at the universe of the sections travels along an isomorphism. -/
theorem _root_.Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) (h : M.IsPresentedByGlobalSections) :
    N.IsPresentedByGlobalSections :=
  Stacks.Sheaves.LocalizedPullback.isPresentedByGlobalSections_map (𝟭 _) (Iso.refl _) e h

/-- A finite global presentation at the universe of the sections travels along an
isomorphism. -/
theorem _root_.Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N)
    (h : M.IsFinitelyPresentedByGlobalSections) : N.IsFinitelyPresentedByGlobalSections := by
  obtain ⟨n, k, P, Q, ι, κ, hP, hQ, a, b, hab, ⟨hc⟩⟩ := h
  exact ⟨n, k, P, Q, ι, κ, hP, hQ, a, b ≫ e.hom, by rw [← Category.assoc, hab, zero_comp],
    ⟨hc.ofIsoColimit (Cofork.ext e rfl)⟩⟩

section Transport

variable {C' : Type*} [Category C'] {C : Type*} [Category C] {D : Type*} [Category D]
  {J' : GrothendieckTopology C'} {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (G : C ⥤ D) [G.IsContinuous J K] (F : C' ⥤ D) [F.IsContinuous J' K]
  {R : Sheaf K RingCat.{u}} {R₁ : Sheaf J' RingCat.{u}}

/-- The direct image along `G` followed by the reindexing along `e` is the direct image along
`F = e.functor ⋙ G`, read through an equality of sheaves of rings. -/
def pushforwardReindexIso (hF : e.functor ⋙ G = F)
    (h : (F.sheafPushforwardContinuous RingCat.{u} J' K).obj R = R₁)
    (M : _root_.SheafOfModules.{u} R) :
    (_root_.SheafOfModules.pushforward.{u} (F := 𝟭 C') (eqToHom (by subst hF h; rfl) :
        reindexRing J' e ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R) ⟶ _)).obj
      ((_root_.SheafOfModules.pushforward.{u} (F := F) (eqToHom h.symm)).obj M) ≅
      (_root_.SheafOfModules.pushforward.{u}
        (𝟙 (reindexRing J' e ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R)))).obj
        ((_root_.SheafOfModules.pushforward.{u} (F := G) (𝟙 _)).obj M) := by
  subst hF h
  exact (_root_.SheafOfModules.pushforwardCongr rfl).app M ≪≫
    ((_root_.SheafOfModules.pushforwardComp (𝟙 _) (𝟙 _)).app M).symm

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

include e in
/-- **Finite global presentations are unchanged by restriction along an equivalence `e`
followed by `G`.** -/
theorem isFinitelyPresentedByGlobalSections_pushforward_iff (hF : e.functor ⋙ G = F)
    (h : (F.sheafPushforwardContinuous RingCat.{u} J' K).obj R = R₁)
    (M : _root_.SheafOfModules.{u} R) :
    ((_root_.SheafOfModules.pushforward.{u} (F := G)
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R))).obj
        M).IsFinitelyPresentedByGlobalSections ↔
      ((_root_.SheafOfModules.pushforward.{u} (F := F) (eqToHom h.symm)).obj
        M).IsFinitelyPresentedByGlobalSections := by
  rw [Stacks.Sheaves.GlobalTypeComparison.isFinitelyPresentedByGlobalSections_iff
    (reindexEquivalence.{u} (J := J) (J' := J') e
      ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R)).functor (Iso.refl _)]
  have i := pushforwardReindexIso (J := J) e G F hF h M
  subst hF h
  exact ⟨Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso i.symm,
    Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso i⟩

variable [HasWeakSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

include e in
/-- **Global presentations at the universe of the sections are unchanged by restriction along an
equivalence `e` followed by `G`.** -/
theorem isPresentedByGlobalSections_pushforward_iff (hF : e.functor ⋙ G = F)
    (h : (F.sheafPushforwardContinuous RingCat.{u} J' K).obj R = R₁)
    (M : _root_.SheafOfModules.{u} R) :
    ((_root_.SheafOfModules.pushforward.{u} (F := G)
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R))).obj
        M).IsPresentedByGlobalSections ↔
      ((_root_.SheafOfModules.pushforward.{u} (F := F) (eqToHom h.symm)).obj
        M).IsPresentedByGlobalSections := by
  rw [Stacks.Sheaves.GlobalTypeComparison.isPresentedByGlobalSections_iff
    (reindexEquivalence.{u} (J := J) (J' := J') e
      ((G.sheafPushforwardContinuous RingCat.{u} J K).obj R)).functor (Iso.refl _)]
  have i := pushforwardReindexIso (J := J) e G F hF h M
  subst hF h
  exact ⟨Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso i.symm,
    Stacks.SheafOfModules.isPresentedByGlobalSections_of_iso i⟩

end Transport

/-- **The equivalence of sites `(Sch/T)_{fppf} ≌ 𝒳_{fppf}/y`** (Stacks 06WI) whose functor is the
lift of the slice 1-morphism of `y`, with an inverse strictly over the base; both functors are
continuous for the fppf topology of the scheme stack of `T` and the localization at `y` of the
fppf topology of `𝒳`. -/
theorem exists_sliceLiftEquivalence :
    ∃ e : Over (𝒳.val.val.p.obj y.obj) ≌ Over y.obj, e.functor = sliceLift B S hS y ∧
      e.functor.IsContinuous
        (associatedTopology B S hS (Over.forget (𝒳.val.val.p.obj y.obj)) B.topology)
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over y.obj) ∧
      e.inverse.IsContinuous
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over y.obj)
        (associatedTopology B S hS (Over.forget (𝒳.val.val.p.obj y.obj)) B.topology) := by
  have := isEquivalence_sliceLift B S hS y
  have hq : (Over.forget y.obj ⋙ 𝒳.val.val.p).IsFiberedInGroupoids :=
    Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.over_forget y.obj)
      𝒳.val.isFiberedInGroupoids
  have hT := Functor.IsFiberedInGroupoids.over_forget (𝒳.val.val.p.obj y.obj)
  obtain ⟨G, hG, η, ε, -, -⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (Over.forget (𝒳.val.val.p.obj y.obj)) (Over.forget y.obj ⋙ 𝒳.val.val.p) hT hq
    (sliceLift B S hS y) (sliceLift_comp_forget_comp_p B S hS y) inferInstance
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have : (Over.forget y.obj ⋙ 𝒳.val.val.p).IsFibered := hq.isFibered
  have : (Over.forget (𝒳.val.val.p.obj y.obj)).IsFibered := hT.isFibered
  have htop := Functor.inheritedTopology_overForget_comp 𝒳.val.val.p
    ((B.topology).over (B.obj hS)) y.obj
  refine ⟨CategoryTheory.Equivalence.mk (sliceLift B S hS y) G η.symm ε, rfl, ?_, ?_⟩
  · show (sliceLift B S hS y).IsContinuous _ _
    rw [← htop]
    exact ((Functor.isFibredOneMorphism_of_isFiberedInGroupoids hq
      (sliceLift_comp_forget_comp_p B S hS y)).isContinuous_and_isCocontinuous_inheritedTopology
      _).1
  · show G.IsContinuous _ _
    rw [← htop]
    exact ((Functor.isFibredOneMorphism_of_isFiberedInGroupoids hT hG
      ).isContinuous_and_isCocontinuous_inheritedTopology _).1

section Presentations

/-- The slice 1-morphism of `y` is continuous for the fppf topologies of the scheme stack of `T`
and of `𝒳`. -/
local instance instIsContinuousSliceMorphism :
    (ambientSliceMorphism B S hS y).hom.hom.toFunctor.IsContinuous
      (associatedTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p
        B.topology)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
  (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS
    (ambientSliceMorphism B S hS y) B.topology).1

/-- The equivalence `(Sch/T)_{fppf} ≌ 𝒳_{fppf}/y` of `exists_sliceLiftEquivalence`, with the
scheme stack of `T` as the source, lies over the slice 1-morphism of `y`. -/
private theorem exists_equivalence_forget_comp_eq_sliceMorphism :
    ∃ e : (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.obj ≌ Over y.obj,
      e.functor ⋙ Over.forget y.obj = (ambientSliceMorphism B S hS y).hom.hom.toFunctor ∧
      e.functor.IsContinuous (associatedTopology B S hS
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p B.topology)
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over y.obj) ∧
      e.inverse.IsContinuous ((associatedTopology B S hS 𝒳.val.val.p B.topology).over y.obj)
        (associatedTopology B S hS
          (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj)).val.val.p B.topology) := by
  obtain ⟨e, he, h1, h2⟩ := exists_sliceLiftEquivalence B S hS y
  exact ⟨e, by rw [he]; rfl, h1, h2⟩

/-- **`M|_{𝒳/y}` has a global presentation exactly when `y^{-1}M` does**, at the universe of the
sections: the slice `𝒳/y` is the big site of the scheme below `y` (Stacks 06WI), and the
restriction of `M` along that equivalence is the inverse image `y^{-1}M` along the 1-morphism
named by `y`. -/
theorem isPresentedByGlobalSections_over_iff
    (M : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)) :
    (M.over y.obj).IsPresentedByGlobalSections ↔
      ((FlatFppf.moduleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)).obj
        M).IsPresentedByGlobalSections := by
  obtain ⟨e', he', _, _⟩ := exists_equivalence_forget_comp_eq_sliceMorphism B S hS y
  have := essentiallySmall_obj_algebraicStack B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  exact isPresentedByGlobalSections_pushforward_iff e' (Over.forget y.obj) _ he'
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl
      (ambientSliceMorphism B S hS y)) M

/-- **`M|_{𝒳/y}` has a finite global presentation exactly when `y^{-1}M` does**, at the universe
of the sections. -/
theorem isFinitelyPresentedByGlobalSections_over_iff
    (M : _root_.SheafOfModules.{u} (FlatFppf.ambientRingStructureSheaf B S hS 𝒳)) :
    (M.over y.obj).IsFinitelyPresentedByGlobalSections ↔
      ((FlatFppf.moduleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)).obj
        M).IsFinitelyPresentedByGlobalSections := by
  obtain ⟨e', he', _, _⟩ := exists_equivalence_forget_comp_eq_sliceMorphism B S hS y
  have := essentiallySmall_obj_algebraicStack B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y.obj))
  exact isFinitelyPresentedByGlobalSections_pushforward_iff e' (Over.forget y.obj) _ he'
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology le_rfl
      (ambientSliceMorphism B S hS y)) M

end Presentations

end AlgebraicGeometry.Stack

end
