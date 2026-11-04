module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel

/-!
# Finite presentation on the equi-universe model of the small étale ringed site

`AlgebraicGeometry.Space.modulesEquivModelModules` identifies the `𝒪_F`-modules of an algebraic
space `F` with the sheaves of modules on the equi-universe model
`AlgebraicGeometry.Space.smallEtaleModelRingedSite` of its small étale ringed site.  This file
shows that `SheafOfModules.IsFinitePresentation` is carried along that identification.

## Main results

* `Stacks.SheafOfModules.ModelFinitePresentation.isDenseSubsite_overPost`: Stacks 03CH (2) for
  an equivalence of sites whose two underlying categories live in *independent* universes.
* `Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward`: reindexing
  along such an equivalence of sites preserves finite presentation.
* `AlgebraicGeometry.Space.isFinitePresentation_modulesEquivModelModules`: **an `𝒪_F`-module of
  finite presentation stays of finite presentation on the equi-universe model.**

## Implementation notes

No `@[stacks]` attribute is carried: nothing here is a statement of the Stacks project.

The input is Mathlib's `SheafOfModules.QuasicoherentData.pushforward`, whose local presentations
are images under `SheafOfModules.Presentation.map` of the given ones; that construction keeps the
types of generators and of relations, so finiteness of a presentation survives it.  Mathlib
states it with the two sites in independent universes, but asks for the continuity of
`CategoryTheory.Over.post` on every slice and for colimit preservation by the slice pushforward.
Those are supplied here, also at independent universes: the tree's existing packaging,
`Stacks.SheafOfModules.overPost_isDenseSubsite` of
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence`, forces the two
underlying categories into the same pair of universes, which is exactly what the small étale
site and its model rule out.

The sheafification hypotheses of `isFinitePresentation_pushforward` are *named* instance
binders.  They have to be, because the underlying category of the small étale ringed site is
reachable in two ways — as `AlgebraicGeometry.Space.SmallEtale` and as the projection `.C` of
`AlgebraicGeometry.Space.smallEtaleRingedSite` — whose `CategoryTheory.Category` instances are
definitionally equal but not syntactically equal, and instance search sees only one of them at a
time.  Naming the binders lets `isFinitePresentation_modulesEquivModelModules` hand over the
instances of the ringed-site development explicitly, which a definitional-equality check then
accepts.

On the model side the two sheafification hypotheses are found by instance search, the model
being a small category, and its fibre products are transported from the small étale site along
the model equivalence.

## References

* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.ModelFinitePresentation

universe w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- **Stacks 03CH (2) for an equivalence of sites with independent universes.**  Localizing an
equivalence of sites at an object again gives an equivalence of sites. -/
instance isDenseSubsite_overPost (e : C' ≌ C) [e.functor.IsDenseSubsite J' J] (V : C') :
    (Over.post (X := V) e.functor).IsDenseSubsite (J'.over V) (J.over (e.functor.obj V)) where
  functorPushforward_mem_iff := by
    intro X T
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact e.functor.functorPushforward_mem_iff J' J

variable {R : Sheaf J RingCat.{w}}
  [hsheafify : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [hlocBij : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [hsheafify' : ∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{w}]
  [hlocBij' : ∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Reindexing along an equivalence of sites preserves finite presentation.**  The
quasi-coherent data of `M` is pushed forward by `SheafOfModules.QuasicoherentData.pushforward`,
whose local presentations are the images of the given ones under
`SheafOfModules.Presentation.map`; that construction keeps the types of generators and of
relations, so finiteness survives.  The two underlying categories are allowed to live in
different universes. -/
theorem isFinitePresentation_pushforward (e : C' ≌ C) [hdense : e.functor.IsDenseSubsite J' J]
    [hpull : HasPullbacks C] [hpull' : HasPullbacks C'] {S : Sheaf J' RingCat.{w}}
    (φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R) [IsIso φ]
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    (M : SheafOfModules.{w} R) [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  have h : ∀ (X : C') (Y : C) (f : e.functor.obj X ⟶ Y),
      PreservesColimitsOfSize.{w, w} <|
      SheafOfModules.pushforward.{w} (R := (R.over Y))
        (F := Over.post (X := X) e.functor ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ) := by
    intro X Y f
    have _ : (Over.post (X := X) e.functor ⋙ Over.map f).IsContinuous (J'.over X) (J.over Y) :=
      Functor.isContinuous_comp _ _ _ (J.over _) _
    have _ : (Over.post (X := X) e.functor ⋙ Over.map f).IsCocontinuous (J'.over X) (J.over Y) :=
      isCocontinuous_comp _ _ _ (J.over _)
    let a : S.over X ⟶ ((Over.post (X := X) e.functor ⋙ Over.map f).sheafPushforwardContinuous
        RingCat.{w} (J'.over X) (J.over Y)).obj (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ
    have _ : IsIso a := inferInstanceAs
      (IsIso (((Over.forget X).sheafPushforwardContinuous RingCat.{w} (J'.over X) J').map φ))
    have _ : (SheafOfModules.pushforward.{w} a).IsLeftAdjoint :=
      SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
    infer_instance
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have _ := hσ
  have _ : (σ.pushforward e.functor φ η h).IsFinitePresentation := by
    refine ⟨fun i => ⟨⟨?_⟩, ⟨?_⟩⟩⟩
    · exact SheafOfModules.GeneratingSections.IsFiniteType.finite
        (σ := (σ.presentation i.2.1).generators)
    · exact SheafOfModules.GeneratingSections.IsFiniteType.finite
        (σ := (σ.presentation i.2.1).relations)
  exact ⟨(σ.pushforward e.functor φ η h).shrink, inferInstance⟩

end Stacks.SheafOfModules.ModelFinitePresentation

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The model of the small étale site has fibre products, transported from the small étale
site along the model equivalence. -/
instance smallEtaleModel_hasPullbacks : HasPullbacks (SmallEtaleModel B S hS F) :=
  Adjunction.hasLimitsOfShape_of_equivalence (smallEtaleModelEquivalence B S hS F).functor

/-- The model equivalence exhibits the model site as a dense subsite of the small étale site:
the topology of the model is the one induced along it. -/
instance smallEtaleModelEquivalence_functor_isDenseSubsite :
    (smallEtaleModelEquivalence B S hS F).functor.IsDenseSubsite
      (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F) :=
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale B S hS F)).inverse.IsDenseSubsite
    ((equivSmallModel.{u} (SmallEtale B S hS F)).inverse.inducedTopology
      (SmallEtale.topology B S hS F)) (SmallEtale.topology B S hS F))

/-- **Finite presentation is carried to the equi-universe model.**  If an `𝒪_F`-module is of
finite presentation, so is the sheaf of modules it becomes on
`AlgebraicGeometry.Space.smallEtaleModelRingedSite`.  This is one of the two inputs that the
proof of Stacks 07U7 in
`AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model`
carries as a hypothesis. -/
theorem isFinitePresentation_modulesEquivModelModules (hF : IsAlgebraicSpace B S hS F)
    (G : Modules.{u, u} B S hS F hF) [G.IsFinitePresentation] :
    ((modulesEquivModelModules B S hS F hF).functor.obj G).IsFinitePresentation :=
  Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward
    (hsheafify := smallEtaleRingedSite_hasSheafify_over B S hS F hF)
    (hlocBij := smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS F hF)
    (hdense := smallEtaleModelEquivalence_functor_isDenseSubsite B S hS F)
    (hpull := SmallEtale.instHasPullbacks B S hS F)
    (J' := smallEtaleModelTopology B S hS F) (smallEtaleModelEquivalence B S hS F)
    (𝟙 _) (Iso.refl _) G

end AlgebraicGeometry.Space

end
