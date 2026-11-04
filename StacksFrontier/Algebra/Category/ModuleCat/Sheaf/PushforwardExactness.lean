module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# Exactness of the direct image of sheaves of modules along a continuous functor

Let `u : C ⥤ D` be a continuous functor of sites and `R` a sheaf of rings on `D`. Restriction
along `u`, that is, the direct image `Mod(R) ⥤ Mod(u_* R)` of Mathlib's
`SheafOfModules.pushforward` for the identity of `u_* R`, is precomposition with `u.op` on
underlying presheaves of modules. It preserves finite limits, and when `u` is moreover
cocontinuous it preserves epimorphisms and finite colimits, so it is an exact functor on sheaves
of modules.

## Main definitions

* `Stacks.SheafOfModules.restriction`: restriction of sheaves of modules along a continuous
  functor of sites.

## Main results

* `Stacks.SheafOfModules.pushforward_preservesEpimorphisms`: the direct image along a
  cocontinuous `u`, for an arbitrary morphism of sheaves of rings, preserves epimorphisms.
* `Stacks.SheafOfModules.restriction_preservesFiniteLimits` and
  `Stacks.SheafOfModules.restriction_preservesFiniteColimits`: restriction along a continuous
  and cocontinuous `u` is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ w

namespace Stacks.SheafOfModules

section Epi

variable {C : Type u₁} [Category.{v₁} C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [u.IsContinuous J K]
  (φ : S ⟶ (u.sheafPushforwardContinuous RingCat.{w} J K).obj R)

/-- The direct image of sheaves of modules along a continuous functor is additive. -/
instance pushforward_additive : (_root_.SheafOfModules.pushforward.{w} φ).Additive where
  map_add := by intros; rfl

/-- The direct image of sheaves of modules along a functor which is continuous and cocontinuous
preserves epimorphisms. -/
theorem pushforward_preservesEpimorphisms [u.IsCocontinuous J K]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] :
    (_root_.SheafOfModules.pushforward.{w} φ).PreservesEpimorphisms := by
  refine ⟨fun {A B} g hg => ?_⟩
  have : Presheaf.IsLocallySurjective K ((_root_.SheafOfModules.toSheaf R).map g).hom :=
    LocalCokernel.locallySurjective_of_epi g
  have : Presheaf.IsLocallySurjective J
      ((_root_.SheafOfModules.toSheaf S).map
        ((_root_.SheafOfModules.pushforward.{w} φ).map g)).hom :=
    Presheaf.isLocallySurjective_whisker J K u ((_root_.SheafOfModules.toSheaf R).map g).hom
  have : Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf S).map
        ((_root_.SheafOfModules.pushforward.{w} φ).map g)) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2 this
  have := Sheaf.epi_of_isLocallySurjective
    ((_root_.SheafOfModules.toSheaf S).map ((_root_.SheafOfModules.pushforward.{w} φ).map g))
  refine ⟨fun k k' hk => (_root_.SheafOfModules.toSheaf S).map_injective
    (this.left_cancellation _ _ ?_)⟩
  simpa only [Functor.map_comp] using congrArg (_root_.SheafOfModules.toSheaf S).map hk

end Epi

section Exact

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K] (R : Sheaf K RingCat.{w})

/-- Restriction along a continuous functor of sites, on sheaves of modules: the direct image
for the identity structure map `u_* R ⟶ u_* R`. -/
noncomputable abbrev restriction :
    _root_.SheafOfModules.{w} R ⥤
      _root_.SheafOfModules.{w} ((u.sheafPushforwardContinuous RingCat.{w} J K).obj R) :=
  _root_.SheafOfModules.pushforward.{w}
    (𝟙 ((u.sheafPushforwardContinuous RingCat.{w} J K).obj R))

/-- Restriction of sheaves of modules along a continuous functor preserves finite limits. -/
theorem restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction J K u R) := by
  refine ⟨fun A _ _ => ⟨fun {G} => ⟨fun {c} hc => ?_⟩⟩⟩
  refine ⟨isLimitOfReflects (_root_.SheafOfModules.forget
    ((u.sheafPushforwardContinuous RingCat.{w} J K).obj R)) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  exact isLimitOfPreserves
    (_root_.SheafOfModules.evaluation R (Opposite.op (u.obj W.unop))) hc

/-- Restriction of sheaves of modules along a functor which is continuous and cocontinuous
preserves finite colimits, hence is exact. -/
theorem restriction_preservesFiniteColimits [u.IsCocontinuous J K]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] :
    PreservesFiniteColimits (restriction J K u R) :=
  let F := restriction J K u R
  let : PreservesFiniteLimits F := restriction_preservesFiniteLimits J K u R
  let : F.PreservesEpimorphisms := pushforward_preservesEpimorphisms _
  LocalCokernel.finiteColimits_of_finiteLimits_epi F

end Exact

end Stacks.SheafOfModules

end
