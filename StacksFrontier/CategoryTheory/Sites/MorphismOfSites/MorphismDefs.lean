module

public import Mathlib.CategoryTheory.Sites.Continuous
import StacksCore.Tactic.EgaSgaAttribute

/-! # Composition of morphisms of sites

## Main results

* `IsMorphismOfSites`: a continuous functor defines a morphism of sites when the pushforward
  on sheaves has a left exact left adjoint.
* `isMorphismOfSites_comp`: morphisms of sites compose (Stacks 03CB).

Tags covered: 03CB.
-/

@[expose] public section

open CategoryTheory

universe w

/-- A continuous functor `F : C ⥤ D` between sites *defines a morphism of sites* if the induced
pushforward on categories of sheaves admits a left exact left adjoint. -/
@[sga "4 IV 4.9.1"]
class IsMorphismOfSites
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    : Prop extends F.IsContinuous J K where
  /-- The pushforward `F.sheafPushforwardContinuous` has a left adjoint preserving finite
  limits. -/
  hasExactLeftAdjoint :
    ∃ (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)),
      Nonempty (L ⊣ F.sheafPushforwardContinuous (Type w) J K) ∧
      Limits.PreservesFiniteLimits L

/-- **Stacks 03CB.** If `v : C₃ ⥤ C₂` and `u : C₂ ⥤ C₁` are continuous functors defining
morphisms of sites, then so is `v ⋙ u`: the left adjoints compose, and a composition of left
exact functors is left exact. -/
@[stacks 03CB]
theorem isMorphismOfSites_comp
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
    (J₃ : GrothendieckTopology C₃)
    (v : C₃ ⥤ C₂) (u : C₂ ⥤ C₁)
    [IsMorphismOfSites.{w} v J₃ J₂] [IsMorphismOfSites.{w} u J₂ J₁] :
    IsMorphismOfSites.{w} (v ⋙ u) J₃ J₁ := by
  have : (v ⋙ u).IsContinuous J₃ J₁ := Functor.isContinuous_comp v u J₃ J₂ J₁
  obtain ⟨Lu, ⟨adjU⟩, _⟩ := (‹IsMorphismOfSites.{w} u J₂ J₁›).hasExactLeftAdjoint
  obtain ⟨Lv, ⟨adjV⟩, _⟩ := (‹IsMorphismOfSites.{w} v J₃ J₂›).hasExactLeftAdjoint
  exact ⟨Lv ⋙ Lu, ⟨(adjV.comp adjU).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp v u (Type w) J₃ J₂ J₁)⟩,
    Limits.comp_preservesFiniteLimits Lv Lu⟩
