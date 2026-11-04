module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ConstructingInvariantOpens
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-!
# Restricting a finite locally free groupoid to an invariant open

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose source map is finite locally free,
and let `g : U' ⟶ U` be an open immersion whose image is invariant: every arrow whose source
lies in the image has its target there too. Then the arrow scheme of the restriction of the
groupoid along `g` is the source preimage `s⁻¹(U')`, and the source and target maps of the
restriction are finite locally free. The arrow scheme of the restriction is affine as soon as
`U'` is.

## Main results

* `AlgebraicGeometry.isIso_restrictionArrows_snd`: for an invariant open immersion the second
  projection out of the arrow scheme of the restriction is an isomorphism, so that arrow
  scheme is the source preimage.
* `AlgebraicGeometry.restrictionSource_isFiniteLocallyFree`: the source map of the canonical
  arrow scheme of the restriction is finite locally free.
* `AlgebraicGeometry.restriction_source_isFiniteLocallyFree` and
  `AlgebraicGeometry.restriction_target_isFiniteLocallyFree`: the same for the source and
  target maps of any groupoid scheme realizing the restriction, in particular for
  `AlgebraicGeometry.GroupoidScheme.restrict`.
* `AlgebraicGeometry.restriction_isAffine_arrows`: the arrow scheme of the restriction is
  affine when the scheme being restricted to is.
* `AlgebraicGeometry.forall_mem_range_of_isInvariantOpen`: an open immersion whose image is an
  invariant open of the objects has invariant image.

## References

* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-! ### Two categorical facts about pullbacks along a monomorphism -/

/-- A square one of whose vertical legs is an identity is Cartesian as soon as its horizontal
legs are a factorization of the bottom map through the monomorphism on the right. -/
private theorem isPullback_id_of_fac {C : Type*} [Category C] {A B R : C} {f : A ⟶ R}
    {h : B ⟶ R} [Mono f] (k : B ⟶ A) (hk : k ≫ f = h) : IsPullback k (𝟙 B) f h := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simpa using hk)
    (fun s => s.snd) (fun s => ?_) (fun s => by simp) (fun s m _ h₂ => by simpa using h₂))
  exact (cancel_mono f).1 (by rw [Category.assoc, hk, ← s.condition])

/-- If the second leg of a cospan factors through the first and the first is a monomorphism,
then the second projection out of the pullback is an isomorphism. -/
private theorem isIso_pullback_snd_of_fac {C : Type*} [Category C] {A B R : C} {f : A ⟶ R}
    {h : B ⟶ R} [Mono f] [HasPullback f h] (k : B ⟶ A) (hk : k ≫ f = h) :
    IsIso (pullback.snd f h) := by
  have hsq := isPullback_id_of_fac k hk
  have key : hsq.isoPullback.inv = pullback.snd f h := by
    simpa using hsq.isoPullback_inv_snd
  rw [← key]
  infer_instance

/-! ### The arrow scheme of a restriction to an invariant open -/

variable {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)

/-- If `V` is an invariant open of the objects and the image of `g` is `V`, then every arrow
whose source lies in the image of `g` has its target in the image of `g`. -/
theorem forall_mem_range_of_isInvariantOpen {V : G.objects.left.Opens}
    (hV : IsInvariantOpen G V) (hg : Set.range g.left.base = (V : Set G.objects.left))
    (r : G.arrows.left) (hr : G.source.left.base r ∈ Set.range g.left.base) :
    G.target.left.base r ∈ Set.range g.left.base := by
  rw [hg] at hr ⊢
  exact hV r hr

/-- An open immersion of schemes over `S` is a monomorphism in the category of schemes over
`S`. -/
private theorem mono_of_isOpenImmersion_left [IsOpenImmersion g.left] : Mono g :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono g.left))

/-- For an open immersion `g` with invariant image, the source preimage maps into the image of
`g` under the target map. -/
private theorem range_comp_target_subset [IsOpenImmersion g.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    Set.range ((pullback.fst G.source g).left ≫ G.target.left) ⊆ Set.range g.left := by
  rintro y ⟨x, rfl⟩
  have hcond : (pullback.fst G.source g).left ≫ G.source.left =
      (pullback.snd G.source g).left ≫ g.left := by
    simpa using congrArg Over.Hom.left (pullback.condition (f := G.source) (g := g))
  refine hinv ((pullback.fst G.source g).left.base x) ?_
  refine ⟨(pullback.snd G.source g).left.base x, ?_⟩
  simpa [Scheme.Hom.comp_apply] using
    (congrArg (fun k : _ ⟶ G.objects.left => k.base x) hcond).symm

/-- For an open immersion `g` with invariant image, the source preimage is a cone over the
cospan defining the target preimage, compatibly with the projections to the arrow scheme. -/
private theorem exists_fac_pullback_snd [IsOpenImmersion g.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    ∃ k : pullback G.source g ⟶ pullback g G.target,
      k ≫ pullback.snd g G.target = pullback.fst G.source g := by
  have hrange := range_comp_target_subset G g hinv
  have hfac : IsOpenImmersion.lift g.left
      ((pullback.fst G.source g).left ≫ G.target.left) hrange ≫ g.left =
        (pullback.fst G.source g).left ≫ G.target.left :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨pullback.lift (Over.homMk (IsOpenImmersion.lift g.left
    ((pullback.fst G.source g).left ≫ G.target.left) hrange) ?_)
      (pullback.fst G.source g) ?_, pullback.lift_snd _ _ _⟩
  · calc _ = IsOpenImmersion.lift g.left ((pullback.fst G.source g).left ≫ G.target.left)
            hrange ≫ g.left ≫ G.objects.hom := by rw [Over.w g]
      _ = ((pullback.fst G.source g).left ≫ G.target.left) ≫ G.objects.hom := by
            rw [← Category.assoc, hfac]
      _ = (pullback G.source g).hom := by
            rw [Category.assoc, Over.w G.target, Over.w (pullback.fst G.source g)]
  · exact Over.OverMorphism.ext (by simp)

/-- **The arrow scheme of a restriction to an invariant open is the source preimage.** For an
open immersion `g` with invariant image the second projection out of
`AlgebraicGeometry.restrictionArrows` is an isomorphism onto `pullback G.source g`. -/
theorem isIso_restrictionArrows_snd [IsOpenImmersion g.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    IsIso (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g)) := by
  have _ : Mono g := mono_of_isOpenImmersion_left G g
  have _ : Mono (pullback.snd g G.target) := inferInstance
  obtain ⟨k, hk⟩ := exists_fac_pullback_snd G g hinv
  exact isIso_pullback_snd_of_fac k hk

/-! ### Finite local freeness and affineness of the restriction -/

/-- The left component of an isomorphism of schemes over `S` is an isomorphism. -/
private theorem isIso_left_of_isIso {X Y : Over S} (f : X ⟶ Y) [IsIso f] : IsIso f.left :=
  inferInstanceAs (IsIso ((Over.forget S).map f))

/-- The projection of the source preimage to the scheme being restricted to is finite locally
free. -/
private theorem pullback_snd_isFiniteLocallyFree [IsFiniteLocallyFree G.source.left] :
    IsFiniteLocallyFree (pullback.snd G.source g).left := by
  have hsq := (IsPullback.of_hasPullback G.source g).map (Over.forget S)
  simp only [Over.forget_map] at hsq
  exact MorphismProperty.of_isPullback (P := @IsFiniteLocallyFree) hsq inferInstance

/-- The source map of the canonical arrow scheme of the restriction along an invariant open
immersion is finite locally free. -/
theorem restrictionSource_isFiniteLocallyFree [IsOpenImmersion g.left]
    [IsFiniteLocallyFree G.source.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    IsFiniteLocallyFree (restrictionSource G g).left := by
  have _ := isIso_restrictionArrows_snd G g hinv
  have _ := isIso_left_of_isIso (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g))
  show IsFiniteLocallyFree (pullback.snd (pullback.snd g G.target)
    (pullback.fst G.source g) ≫ pullback.snd G.source g).left
  rw [Over.comp_left, MorphismProperty.cancel_left_of_respectsIso
    (P := @IsFiniteLocallyFree) _ _]
  exact pullback_snd_isFiniteLocallyFree G g

/-- The source map of any groupoid scheme realizing the restriction along an invariant open
immersion is finite locally free. -/
theorem restriction_source_isFiniteLocallyFree (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsFiniteLocallyFree G.source.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    IsFiniteLocallyFree R.groupoid.source.left := by
  have _ := isIso_left_of_isIso (eqToHom R.arrows_eq)
  have _ := isIso_left_of_isIso (eqToHom R.objects_eq.symm)
  rw [R.source_eq]
  dsimp only [Over.comp_left, Over.Hom.left]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsFiniteLocallyFree) _ _,
    MorphismProperty.cancel_right_of_respectsIso (P := @IsFiniteLocallyFree) _ _]
  exact restrictionSource_isFiniteLocallyFree G g hinv

/-- The target map of any groupoid scheme realizing the restriction along an invariant open
immersion is finite locally free. -/
theorem restriction_target_isFiniteLocallyFree (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsFiniteLocallyFree G.source.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    IsFiniteLocallyFree R.groupoid.target.left := by
  have _ : IsIso R.groupoid.inverse.left := groupoidInverse_left_isIso R.groupoid
  rw [← R.groupoid.source_inverse]
  show IsFiniteLocallyFree (R.groupoid.inverse.left ≫ R.groupoid.source.left)
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsFiniteLocallyFree) _ _]
  exact restriction_source_isFiniteLocallyFree G g R hinv

/-- The arrow scheme of a restriction along an invariant open immersion with affine source is
affine. -/
theorem restriction_isAffine_arrows (R : GroupoidScheme.Restriction G g)
    [IsOpenImmersion g.left] [IsFiniteLocallyFree G.source.left] [IsAffine U'.left]
    (hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base) :
    IsAffine R.groupoid.arrows.left := by
  have hobj : R.groupoid.objects.left = U'.left := congrArg Over.left R.objects_eq
  have _ : IsAffine R.groupoid.objects.left := by rw [hobj]; infer_instance
  have _ : IsAffineHom R.groupoid.source.left :=
    (restriction_source_isFiniteLocallyFree G g R hinv).toIsAffineHom
  exact isAffine_of_isAffineHom R.groupoid.source.left

end AlgebraicGeometry

end
