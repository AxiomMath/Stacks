module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Continuity and functoriality of base change on small étale sites

Base change `smallEtaleBaseChange f : Y.Etale ⥤ X.Etale` along `f : X ⟶ Y` is the site functor
underlying the geometric morphism `X_étale ⟶ Y_étale`. This file proves that it is *continuous*: it
carries covering sieves of the small étale site of `Y` to covering sieves of that of `X`.

It also records the functoriality of base change in `f`, which is Mathlib's
`MorphismProperty.Over.pullbackComp` specialised to étale morphisms, and the induced composition
isomorphism for the direct image functors on sheaves of sets.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_preservesFiniteLimits` and
  `Stacks.EtaleCohomology.smallEtaleBaseChange_representablyFlat` — base change is left exact,
  hence representably flat.
* `Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous` — base change is a continuous
  functor of small étale sites.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp` — base change along `f ≫ g` is base change
  along `g` followed by base change along `f`.
* `Stacks.EtaleCohomology.smallEtalePushforwardCompIso` — the resulting isomorphism
  `g_* ∘ f_* ≅ (f ≫ g)_*` of direct image functors on sheaves of sets.

## References

* [Stacks Project, Tag 04DK](https://stacks.math.columbia.edu/tag/04DK)
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- Base change between small étale sites is left exact. -/
public instance smallEtaleBaseChange_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (smallEtaleBaseChange f) := by
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.HasPullbacksAlong f := ⟨fun _ _ ↦ inferInstance⟩
  let : P.IsStableUnderBaseChangeAlong f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F := smallEtaleBaseChange f
  let G := Scheme.Etale.forget Y
  let H := Scheme.Etale.forget X
  have hcomp : G ⋙ Over.pullback f = F ⋙ H := rfl
  let : PreservesLimitsOfShape WalkingCospan (F ⋙ H) := by
    rw [← hcomp]
    infer_instance
  let : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_reflects_of_preserves F H
  let : PreservesLimit (Functor.empty.{0} Y.Etale) (F ⋙ H) := by
    rw [← hcomp]
    infer_instance
  let : PreservesLimit (Functor.empty.{0} Y.Etale) F :=
    preservesLimit_of_reflects_of_preserves F H
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesLimitsOfShape_pempty_of_preservesTerminal F
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

/-- Base change between small étale sites is representably flat. -/
public instance smallEtaleBaseChange_representablyFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RepresentablyFlat (smallEtaleBaseChange f) :=
  flat_of_preservesFiniteLimits _

/-- Base change along a scheme morphism is a continuous functor of small étale sites: it carries
covering sieves to covering sieves. -/
@[sga "4 IV 4.10.6" "1°, special case"]
public instance smallEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).IsContinuous
      (smallEtaleTopology Y) (smallEtaleTopology X) := by
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.IsMultiplicative := inferInstance
  let : P.IsStableUnderBaseChange := inferInstance
  let : P.HasPullbacksAlong f := ⟨fun _ _ ↦ inferInstance⟩
  let : P.IsStableUnderBaseChangeAlong f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F := smallEtaleBaseChange f
  let G := Scheme.Etale.forget Y
  let H := Scheme.Etale.forget X
  let : G.LocallyCoverDense (Scheme.etaleTopology.over Y) := by
    change (MorphismProperty.Over.forget P ⊤ Y).LocallyCoverDense _
    infer_instance
  let : H.LocallyCoverDense (Scheme.etaleTopology.over X) := by
    change (MorphismProperty.Over.forget P ⊤ X).LocallyCoverDense _
    infer_instance
  have hcomp : G ⋙ Over.pullback f = F ⋙ H := rfl
  let : PreservesFiniteLimits F := smallEtaleBaseChange_preservesFiniteLimits f
  let : RepresentablyFlat F := smallEtaleBaseChange_representablyFlat f
  rw [Functor.isContinuous_iff_coverPreserving]
  refine ⟨?_⟩
  intro U S hS
  have hS0 : S ∈ G.restrictedTopology (Scheme.etaleTopology.over Y) U := by
    change S ∈ (MorphismProperty.Over.forget P ⊤ Y).restrictedTopology
      (Scheme.etaleTopology.over Y) U
    exact hS
  have hS' : S.functorPushforward G ∈ Scheme.etaleTopology.over Y (G.obj U) :=
    (Functor.mem_restrictedTopology_iff (G := G) (K := Scheme.etaleTopology.over Y)).1 hS0
  have hS'' : (S.functorPushforward G).functorPushforward (Over.pullback f) ∈
      Scheme.etaleTopology.over X ((Over.pullback f).obj (G.obj U)) :=
    (CoverPreserving.of_isContinuous (F := Over.pullback f)
      (J := Scheme.etaleTopology.over Y) (K := Scheme.etaleTopology.over X)).cover_preserve hS'
  have hS''' : (S.functorPushforward F).functorPushforward H ∈
      Scheme.etaleTopology.over X ((F ⋙ H).obj U) := by
    have hSsingle : S.functorPushforward (G ⋙ Over.pullback f) ∈
        Scheme.etaleTopology.over X ((G ⋙ Over.pullback f).obj U) := by
      rw [Sieve.functorPushforward_comp]
      exact hS''
    rw [hcomp] at hSsingle
    simpa only [Sieve.functorPushforward_comp] using hSsingle
  exact (Functor.mem_restrictedTopology_iff (G := H)
    (K := Scheme.etaleTopology.over X)).2 hS'''

/-- Base change along a composite is the composite of the base changes, in the reverse order:
`(f ≫ g)^* ≅ g^* ⋙ f^*` as functors `Z.Etale ⥤ X.Etale`. -/
public def smallEtaleBaseChangeComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleBaseChange (f ≫ g) ≅
      smallEtaleBaseChange g ⋙ smallEtaleBaseChange f := by
  letI : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g

/-- The canonical composition isomorphism `g_* ∘ f_* ≅ (f ≫ g)_*` for direct image of sheaves of
sets along small étale sites. -/
public def smallEtalePushforwardCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X) ⋙
      (smallEtaleBaseChange g).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Z) (smallEtaleTopology Y) ≅
    (smallEtaleBaseChange (f ≫ g)).sheafPushforwardContinuous
      (Type (max (u + 1) v)) (smallEtaleTopology Z) (smallEtaleTopology X) :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm _ _ _ _

end Stacks.EtaleCohomology

end
