module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.TwistedEtaleChart
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantQuotientOpens
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StabilizerBaseChangeMorphism

/-!
# The invariant spectra of the invariant affine opens of an étale cartesian groupoid

Let `F : G' ⟶ G` be a morphism of groupoid schemes over `S` whose source and target squares are
cartesian and which reflects arrows with equal source and target, with `G` affine and finite
locally free and `F` étale on object schemes. The object scheme `W` of `G'` need not be affine.
For an invariant affine open `V ⊆ W` the restriction `G'|_V` is affine and finite locally free and
its morphism to `G` has the three cartesian squares of Stacks 0DT9, so its invariant spectrum
`N_V` is étale over the invariant spectrum `M` of `G`, with `V = N_V ×_M U`.

This is the per-piece step of the proof of Stacks 0DUS: the moduli space `M'` of `𝒳'` is glued
from the `N_V` for an open covering of `W` by invariant affine opens. The argument is the one of
`AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.exists_etale_chart`, for an arbitrary
morphism with cartesian squares rather than for a twisted base change.

## Main results

* `AlgebraicGeometry.GroupoidScheme.invariantOpenCompHom`: the morphism `G'|_V ⟶ G`.
* `AlgebraicGeometry.GroupoidScheme.etale_restrictHom_invariantSpectrum` and
  `AlgebraicGeometry.GroupoidScheme.isPullback_restrictHom`: Stacks 0DT9 for it.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
  (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
  (hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ G'.arrows.left),
    (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left →
      r ≫ G'.source.left = r ≫ G'.target.left)
  (V : G'.objects.left.Opens) (hV : IsInvariantOpen G' V)

/-- The morphism from the restriction of `G'` to an invariant open to `G`. -/
abbrev invariantOpenCompHom : GroupoidScheme.Hom (restrictInvariantOpen G' V hV) G :=
  GroupoidScheme.Hom.comp (restrictInvariantOpenHom G' V hV) F

include hsource in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] in
/-- The square formed by the morphism `G'|_V ⟶ G` on arrows and objects and the source maps is
cartesian. -/
theorem isPullback_restrictHom_source :
    IsPullback (invariantOpenCompHom F V hV).mapArrows.left
      (restrictInvariantOpen G' V hV).source.left G.source.left
      (invariantOpenCompHom F V hV).mapObjects.left :=
  (isPullback_restrictInvariantOpenHom_source G' V hV).paste_horiz hsource

include htarget in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] in
/-- The square formed by the morphism `G'|_V ⟶ G` on arrows and objects and the target maps is
cartesian. -/
theorem isPullback_restrictHom_target :
    IsPullback (invariantOpenCompHom F V hV).mapArrows.left
      (restrictInvariantOpen G' V hV).target.left G.target.left
      (invariantOpenCompHom F V hV).mapObjects.left :=
  (isPullback_restrictInvariantOpenHom_target G' V hV).paste_horiz htarget

include hsrc in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left] in
/-- The morphism `G'|_V ⟶ G` reflects arrows with equal source and target. -/
theorem restrictHom_source_eq_target {T : Scheme.{u}}
    (r : T ⟶ (restrictInvariantOpen G' V hV).arrows.left)
    (hr : (r ≫ (invariantOpenCompHom F V hV).mapArrows.left) ≫ G.source.left =
      (r ≫ (invariantOpenCompHom F V hV).mapArrows.left) ≫ G.target.left) :
    r ≫ (restrictInvariantOpen G' V hV).source.left =
      r ≫ (restrictInvariantOpen G' V hV).target.left := by
  have h₀ : (invariantOpenCompHom F V hV).mapArrows.left =
      (restrictInvariantOpenHom G' V hV).mapArrows.left ≫ F.mapArrows.left := rfl
  rw [h₀] at hr
  have h₁ := hsrc (r ≫ (restrictInvariantOpenHom G' V hV).mapArrows.left)
    (by simpa only [Category.assoc] using hr)
  rw [← cancel_mono (restrictInvariantOpenHom G' V hV).mapObjects.left, Category.assoc,
    Category.assoc, ← (restrictInvariantOpenHom G' V hV).map_source_left,
    ← (restrictInvariantOpenHom G' V hV).map_target_left]
  simpa only [Category.assoc] using h₁

include hsource in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.target.left] in
/-- The source map of `G'` is finite locally free, being a base change of that of `G`. -/
theorem isFiniteLocallyFree_source_of_isPullback : IsFiniteLocallyFree G'.source.left :=
  isFiniteLocallyFree_of_isPullback hsource

include htarget in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left] in
/-- The target map of `G'` is finite locally free, being a base change of that of `G`. -/
theorem isFiniteLocallyFree_target_of_isPullback : IsFiniteLocallyFree G'.target.left :=
  isFiniteLocallyFree_of_isPullback htarget

include hsource in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.target.left] in
/-- The source map of the restriction to an invariant open is finite locally free. -/
theorem isFiniteLocallyFree_restrict_source :
    IsFiniteLocallyFree (restrictInvariantOpen G' V hV).source.left :=
  isFiniteLocallyFree_of_isPullback (isPullback_restrictHom_source F hsource V hV)

include htarget in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left] in
/-- The target map of the restriction to an invariant open is finite locally free. -/
theorem isFiniteLocallyFree_restrict_target :
    IsFiniteLocallyFree (restrictInvariantOpen G' V hV).target.left :=
  isFiniteLocallyFree_of_isPullback (isPullback_restrictHom_target F htarget V hV)

include hsource in
omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.target.left] in
/-- The arrow scheme of the restriction to an invariant affine open is affine: it is finite over
the affine object scheme. -/
theorem isAffine_restrict_arrows (hVa : IsAffineOpen V) :
    IsAffine (restrictInvariantOpen G' V hV).arrows.left := by
  have : IsAffine (restrictInvariantOpen G' V hV).objects.left := hVa
  have := isFiniteLocallyFree_restrict_source F hsource V hV
  have hsfin : IsFinite (restrictInvariantOpen G' V hV).source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1 inferInstance).1
  exact isAffine_of_isAffineHom (restrictInvariantOpen G' V hV).source.left

section ZeroDT9

variable [IsAffine (restrictInvariantOpen G' V hV).objects.left]
  [IsAffine (restrictInvariantOpen G' V hV).arrows.left]
  [IsFiniteLocallyFree (restrictInvariantOpen G' V hV).source.left]
  [IsFiniteLocallyFree (restrictInvariantOpen G' V hV).target.left]
  [Etale F.mapObjects.left]

include hsource htarget hsrc in
/-- **Stacks 0DT9 for the restriction to an invariant affine open, first conclusion:** the
invariant spectrum of the restriction is étale over that of `G`. -/
theorem etale_restrictHom_invariantSpectrum :
    Etale (Spec.map (CommRingCat.ofHom (invariantRingMap (invariantOpenCompHom F V hV)))) := by
  have : Etale (invariantOpenCompHom F V hV).mapObjects.left := by
    change Etale (_ ≫ F.mapObjects.left)
    infer_instance
  exact HasRingHomProperty.Spec_iff.mpr (etale_invariantRingMap (invariantOpenCompHom F V hV)
    (isPullback_restrictHom_source F hsource V hV) (isPullback_restrictHom_target F htarget V hV)
    (isPullback_stabilizerMap (invariantOpenCompHom F V hV)
      (isPullback_restrictHom_target F htarget V hV)
      (restrictHom_source_eq_target F hsrc V hV)))

include hsource htarget hsrc in
/-- **Stacks 0DT9 for the restriction to an invariant affine open, second conclusion:**
`V = N_V ×_M U`. -/
theorem isPullback_restrictHom :
    IsPullback (invariantOpenCompHom F V hV).mapObjects.left
      (objectsToInvariantSpectrum (restrictInvariantOpen G' V hV))
      (objectsToInvariantSpectrum G)
      (Spec.map (CommRingCat.ofHom (invariantRingMap (invariantOpenCompHom F V hV)))) := by
  have : Etale (invariantOpenCompHom F V hV).mapObjects.left := by
    change Etale (_ ≫ F.mapObjects.left)
    infer_instance
  exact isPullback_mapObjects (invariantOpenCompHom F V hV)
    (isPullback_restrictHom_source F hsource V hV) (isPullback_restrictHom_target F htarget V hV)
    (isPullback_stabilizerMap (invariantOpenCompHom F V hV)
      (isPullback_restrictHom_target F htarget V hV)
      (restrictHom_source_eq_target F hsrc V hV))

end ZeroDT9

end AlgebraicGeometry.GroupoidScheme

end
