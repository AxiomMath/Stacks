module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of sites

A *morphism of sites* `f : D → C` is given by a functor `u : C ⥤ D` in the *opposite*
direction which is continuous and for which the induced functor on sheaves of sets
`u_s : Sh(C) ⥤ Sh(D)`, the left adjoint `f⁻¹` of `u^s = f_*`, is exact. Since `u_s` is a left
adjoint it preserves all colimits, so the condition reduces to left exactness of `u_s`.

The file also records the continuity of the identity functor from a topology to any finer one,
and the image of a presieve under a composite functor.

## Main definitions

* `CategoryTheory.Functor.IsMorphismOfSites`: a continuous functor whose induced functor on
  sheaves of sets is exact.
* `CategoryTheory.Functor.sheafPullbackComp`: the isomorphism `(u ⋙ u')_s ≅ u_s ⋙ u'_s`.

## Main results

* `CategoryTheory.Functor.preservesFiniteColimits_sheafPullback`: `u_s` is right exact.
* `CategoryTheory.Functor.isMorphismOfSites_iff_preservesFiniteLimits`: a continuous functor is a
  morphism of sites if and only if `u_s` is left exact.
* `CategoryTheory.Functor.IsMorphismOfSites.comp`: the composite of two morphisms of sites is a
  morphism of sites.
* `CategoryTheory.Functor.isContinuous_id_of_le`: the identity functor is continuous from a
  topology to any finer one.
* `CategoryTheory.Presieve.map_comp`: the image of a presieve under a composite functor is the
  image of its image.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Presieve

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- The image of a presieve under a composite functor is the image of its image. -/
theorem map_comp (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm ?_ ?_
  · rintro W f ⟨h⟩
    exact map_map (map_map h)
  · rintro W f ⟨⟨h⟩⟩
    exact map_map h

/-- `CategoryTheory.Presieve.map_comp` read from right to left: mapping a presieve along two
functors in turn is mapping it along their composite. -/
theorem map_map_eq_map_comp (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    (R.map F).map G = R.map (F ⋙ G) :=
  (map_comp F G R).symm

end CategoryTheory.Presieve

namespace CategoryTheory.Functor

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {E : Type u}
  [SmallCategory E]

/-- A *morphism of sites* `f : D → C` between the sites `(C, J)` and `(D, K)` is given by a
functor `u : C ⥤ D` in the opposite direction which is continuous and whose induced functor on
sheaves of sets `u_s = f⁻¹ : Sh(C) ⥤ Sh(D)` is exact, i.e. preserves both finite limits and
finite colimits. Here `u_s` is `Functor.sheafPullback`, the left adjoint of the pushforward
`u^s = f_* = Functor.sheafPushforwardContinuous`.

Continuity here is Mathlib's `Functor.IsContinuous` (restriction preserves sheaves), which is the
conclusion of Stacks 00WW and is weaker than continuity in the sense of Stacks 00WV. The notion of
Stacks 00X1 itself, built on Stacks continuity, is `Stacks.Sites.Site.IsMorphismOfSites`. -/
@[sga "4 IV 4.9.1"]
structure IsMorphismOfSites (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  /-- The functor `u : C ⥤ D` is continuous. -/
  isContinuous : u.IsContinuous J K
  /-- `u_s` is left exact. -/
  preservesFiniteLimits :
    haveI := isContinuous
    PreservesFiniteLimits (u.sheafPullback (Type u) J K)
  /-- `u_s` is right exact. -/
  preservesFiniteColimits :
    haveI := isContinuous
    PreservesFiniteColimits (u.sheafPullback (Type u) J K)

attribute [sga "4 IV 4.9" "morphism of sites def"] IsMorphismOfSites

/-- For a continuous `u`, the induced functor `u_s` on sheaves of sets is right exact. -/
theorem preservesFiniteColimits_sheafPullback (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    PreservesFiniteColimits (u.sheafPullback (Type u) J K) :=
  have : PreservesColimitsOfSize.{u, u} (u.sheafPullback (Type u) J K) :=
    (u.sheafAdjunctionContinuous (Type u) J K).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- For a continuous `u`, being a morphism of sites is exactly left exactness of `u_s`: the
right-exactness half of Stacks 00X1 holds automatically. -/
theorem isMorphismOfSites_iff_preservesFiniteLimits (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    u.IsMorphismOfSites J K ↔ PreservesFiniteLimits (u.sheafPullback (Type u) J K) :=
  ⟨fun h => h.preservesFiniteLimits,
    fun h => ⟨inferInstance, h, preservesFiniteColimits_sheafPullback u J K⟩⟩

/-- The comparison isomorphism `(u ⋙ u')_s ≅ u_s ⋙ u'_s` between the functor on sheaves of sets
induced by a composite of continuous functors and the composite of the induced functors. -/
noncomputable def sheafPullbackComp (u : C ⥤ D) (u' : D ⥤ E) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (L : GrothendieckTopology E)
    [u.IsContinuous J K] [u'.IsContinuous K L] :
    haveI := Functor.isContinuous_comp u u' J K L
    (u ⋙ u').sheafPullback (Type u) J L ≅
      u.sheafPullback (Type u) J K ⋙ u'.sheafPullback (Type u) K L :=
  haveI := Functor.isContinuous_comp u u' J K L
  ((u ⋙ u').sheafAdjunctionContinuous (Type u) J L).leftAdjointUniq
    (((u.sheafAdjunctionContinuous (Type u) J K).comp
        (u'.sheafAdjunctionContinuous (Type u) K L)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp u u' (Type u) J K L))

/-- The *composition* of morphisms of sites. If `f : D → C` is a morphism of sites given by
`u : C ⥤ D` and `g : E → D` is one given by `u' : D ⥤ E`, then the composite functor
`u ⋙ u' : C ⥤ E` is again continuous with exact induced functor on sheaves of sets, so it defines
a morphism of sites `E → C`, the composition `f ∘ g`. -/
@[stacks 03CC "The composition of two morphisms of sites is a morphism of sites, given by
  the composite of the two underlying continuous functors; this is what makes the
  composition of Stacks 03CC well defined."]
theorem IsMorphismOfSites.comp {u : C ⥤ D} {u' : D ⥤ E} {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    (h : u.IsMorphismOfSites J K) (h' : u'.IsMorphismOfSites K L) :
    (u ⋙ u').IsMorphismOfSites J L := by
  have := h.isContinuous
  have := h'.isContinuous
  have := h.preservesFiniteLimits
  have := h'.preservesFiniteLimits
  have := Functor.isContinuous_comp u u' J K L
  rw [isMorphismOfSites_iff_preservesFiniteLimits]
  have : PreservesFiniteLimits
      (u.sheafPullback (Type u) J K ⋙ u'.sheafPullback (Type u) K L) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (sheafPullbackComp u u' J K L).symm

section ChangeOfTopology

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C]

/-- The identity functor is compatibility-preserving for every topology. -/
theorem compatiblePreserving_id (K : GrothendieckTopology C) :
    CompatiblePreserving K (𝟭 C) := by
  refine ⟨?_⟩
  intro _ _ _ _ hx _ _ _ f₁ f₂ _ _ hg₁ hg₂ hcomp
  exact hx f₁ f₂ hg₁ hg₂ (by simpa using hcomp)

/-- The identity functor is continuous from a topology to any finer one: if `J ≤ K` then `𝟭 C` is
a continuous functor from `(C, K)` to `(C, J)`, so restriction along it carries `J`-sheaves to
`K`-sheaves. This generalizes `CategoryTheory.Functor.isContinuous_id`, which is the case
`J = K`. -/
theorem isContinuous_id_of_le (J K : GrothendieckTopology C) (h : J ≤ K) :
    (𝟭 C).IsContinuous J K :=
  isContinuous_of_coverPreserving (compatiblePreserving_id K)
    ⟨fun hR => by simpa using h _ hR⟩

end ChangeOfTopology

end CategoryTheory.Functor
