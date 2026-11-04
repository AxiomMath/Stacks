module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic

/-!
# When the stabilizer square of a morphism of groupoid schemes is cartesian

Let `F : (U', R', s', t', c') ⟶ (U, R, s, t, c)` be a morphism of groupoid schemes over `S`
whose source square

    R' --F--> R
    |s'       |s
    v         v
    U' --F--> U

is cartesian. Then the stabilizer square

    G' --F--> G
    |         |
    v         v
    U' --F--> U

is cartesian as soon as an arrow of `R'` whose image in `R` has equal source and target has equal
source and target itself.

## Main results

* `AlgebraicGeometry.isPullback_stabilizerMap_of_isPullback_source`: the criterion, in schemes
  over `S`.
* `AlgebraicGeometry.isPullback_stabilizerMap_left_of_isPullback_source`: the same criterion for
  the underlying morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- The first projection of the stabilizer, followed by the target, is the second projection. -/
@[reassoc]
theorem stabilizer_fst_target :
    pullback.fst (sourceTarget G) (diagonal G) ≫ G.target =
      pullback.snd (sourceTarget G) (diagonal G) := by
  have h := pullback.condition (f := sourceTarget G) (g := diagonal G)
  have := congrArg (· ≫ fst G.objects G.objects) h
  simpa [sourceTarget, diagonal] using this

/-- The first projection of the stabilizer, followed by the source, is the second projection. -/
@[reassoc]
theorem stabilizer_fst_source :
    pullback.fst (sourceTarget G) (diagonal G) ≫ G.source =
      pullback.snd (sourceTarget G) (diagonal G) := by
  have h := pullback.condition (f := sourceTarget G) (g := diagonal G)
  have := congrArg (· ≫ snd G.objects G.objects) h
  simpa [sourceTarget, diagonal] using this

/-- An arrow with equal target and source factors through the stabilizer. -/
theorem sourceTarget_eq_diagonal {T : Over S} (r : T ⟶ G.arrows) (b : T ⟶ G.objects)
    (ht : r ≫ G.target = b) (hs : r ≫ G.source = b) :
    r ≫ sourceTarget G = b ≫ diagonal G := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [sourceTarget, diagonal, ht, hs]

/-- **The stabilizer criterion.** If the source square of a morphism of groupoid schemes is
cartesian and every arrow of `R'` whose image in `R` has equal target and source has equal target
and source, then the stabilizer square is cartesian. -/
theorem isPullback_stabilizerMap_of_isPullback_source
    (hsource : IsPullback F.mapArrows G'.source G.source F.mapObjects)
    (hstab : ∀ (T : Over S) (r : T ⟶ G'.arrows),
      r ≫ F.mapArrows ≫ G.target = r ≫ F.mapArrows ≫ G.source →
        r ≫ G'.target = r ≫ G'.source) :
    IsPullback (stabilizerMap F) (pullback.snd (sourceTarget G') (diagonal G'))
      (pullback.snd (sourceTarget G) (diagonal G)) F.mapObjects := by
  have key : ∀ (T : Over S) (a : T ⟶ stabilizerOverBase G) (b : T ⟶ G'.objects),
      a ≫ pullback.snd (sourceTarget G) (diagonal G) = b ≫ F.mapObjects →
      ∃ l : T ⟶ stabilizerOverBase G', l ≫ stabilizerMap F = a ∧
        l ≫ pullback.snd (sourceTarget G') (diagonal G') = b := by
    intro T a b hab
    let r := a ≫ pullback.fst (sourceTarget G) (diagonal G)
    have hr : r ≫ G.source = b ≫ F.mapObjects := by
      simpa only [r, Category.assoc, stabilizer_fst_source] using hab
    let r' := hsource.lift r b hr
    have hr'F : r' ≫ F.mapArrows = r := hsource.lift_fst _ _ _
    have hr's : r' ≫ G'.source = b := hsource.lift_snd _ _ _
    have hr't : r' ≫ G'.target = b := by
      have h₁ : r' ≫ F.mapArrows ≫ G.target = r' ≫ F.mapArrows ≫ G.source := by
        simp only [← Category.assoc, hr'F]
        simp only [r, Category.assoc, stabilizer_fst_target, stabilizer_fst_source]
      rw [hstab _ r' h₁, hr's]
    refine ⟨pullback.lift r' b (sourceTarget_eq_diagonal r' b hr't hr's), ?_,
      pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc, stabilizerMap_fst, pullback.lift_fst_assoc, hr'F]
    · rw [Category.assoc, stabilizerMap_snd, pullback.lift_snd_assoc, hab]
  have uniq : ∀ (T : Over S) (m₁ m₂ : T ⟶ stabilizerOverBase G'),
      m₁ ≫ stabilizerMap F = m₂ ≫ stabilizerMap F →
      m₁ ≫ pullback.snd (sourceTarget G') (diagonal G') =
        m₂ ≫ pullback.snd (sourceTarget G') (diagonal G') → m₁ = m₂ := by
    intro T m₁ m₂ h₁ h₂
    apply pullback.hom_ext
    · apply hsource.hom_ext
      · have := congrArg (· ≫ pullback.fst (sourceTarget G) (diagonal G)) h₁
        simpa only [Category.assoc, stabilizerMap_fst] using this
      · rw [Category.assoc, Category.assoc, stabilizer_fst_source, h₂]
    · exact h₂
  choose l hl₁ hl₂ using key
  refine ⟨⟨by rw [stabilizerMap_snd]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => l c.pt c.fst c.snd c.condition) (fun c => hl₁ _ _ _ _) (fun c => hl₂ _ _ _ _) ?_⟩⟩
  intro c m hm₁ hm₂
  exact uniq _ _ _ (hm₁.trans (hl₁ _ _ _ c.condition).symm) (hm₂.trans (hl₂ _ _ _ c.condition).symm)

/-- **The stabilizer criterion on underlying schemes.** If the source square of a morphism of
groupoid schemes is cartesian and every arrow of `R'` whose image in `R` has equal target and
source has equal target and source, then the stabilizer square of underlying schemes is
cartesian. -/
theorem isPullback_stabilizerMap_left_of_isPullback_source
    (hsource : IsPullback F.mapArrows G'.source G.source F.mapObjects)
    (hstab : ∀ (T : Over S) (r : T ⟶ G'.arrows),
      r ≫ F.mapArrows ≫ G.target = r ≫ F.mapArrows ≫ G.source →
        r ≫ G'.target = r ≫ G'.source) :
    IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left :=
  (isPullback_stabilizerMap_of_isPullback_source F hsource hstab).map (Over.forget S)

end AlgebraicGeometry

end
