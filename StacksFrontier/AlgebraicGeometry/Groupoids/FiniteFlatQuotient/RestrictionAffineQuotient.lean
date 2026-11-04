module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.InvariantAffineCover
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.FppfLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas

/-!
# The affine quotient of a finite locally free groupoid restricted to an invariant affine open

Let a groupoid scheme over `S` have finite locally free source and target maps and let its pair
of target and source maps be an equivalence relation.  Restricting it to an invariant affine
open of its object scheme gives a groupoid whose object and arrow schemes are both affine and
whose source and target maps are again finite locally free, and whose pair of target and source
maps is again an equivalence relation.  Such a groupoid has an affine quotient: an affine
`S`-scheme, no larger than the invariant open it is a quotient of, receiving a surjective finite
locally free morphism whose kernel pair is the restricted relation (Stacks 03BM).

## Main results

* `AlgebraicGeometry.GroupoidScheme.mono_groupoidPreRelation`: the pre-relation underlying a
  groupoid scheme whose target and source maps form an equivalence relation is a
  monomorphism.
* `AlgebraicGeometry.GroupoidScheme.mono_groupoidPreRelation_restriction` and
  `AlgebraicGeometry.GroupoidScheme.isEquivalenceRelation_restriction`: the target and source
  maps of a restriction of such a groupoid again form an equivalence relation.
* `AlgebraicGeometry.GroupoidScheme.exists_affineQuotient_of_isInvariantOpen`: the affine
  quotient of the restriction to an invariant affine open.
* `AlgebraicGeometry.GroupoidScheme.isIso_quotientSheafToPoints_of_isPullback`: a finite
  locally free surjection out of the object scheme whose kernel pair is the arrow scheme
  represents the fppf quotient sheaf.
* `AlgebraicGeometry.GroupoidScheme.isPullback_restrictionArrowsToArrows_of_isInvariantSet`:
  the arrow scheme of the restriction to an invariant open is the fibre product of the arrow
  scheme with that open along the source map, and
  `AlgebraicGeometry.GroupoidScheme.exists_lift_target_of_isInvariantSet`: an arrow whose
  source lifts along an invariant open immersion has its target lift too.

## Implementation notes

In `AlgebraicGeometry.GroupoidScheme.isIso_quotientSheafToPoints_of_isPullback` the finiteness
and surjectivity of `π` are explicit hypotheses rather than instances: at the call sites `π` is
a morphism out of the object scheme of a restricted groupoid, and instance search does not find
such properties of it.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 02VD](https://stacks.math.columbia.edu/tag/02VD)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- The pre-relation given by the target and the source of a groupoid scheme is a monomorphism
as soon as that pair is an equivalence relation. -/
theorem mono_groupoidPreRelation (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] : Mono (groupoidPreRelation G) :=
  ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation (groupoidPreRelation G)).1
    (by simpa [groupoidPreRelation, PreRelation.target, PreRelation.source] using
      ‹IsEquivalenceRelation G.target G.source›)).1

/-- The pre-relation of a restriction of a groupoid scheme whose target and source maps form an
equivalence relation is a monomorphism. -/
theorem mono_groupoidPreRelation_restriction (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] {U' : Over S} (g : U' ⟶ G.objects)
    (H : Restriction G g) : Mono (groupoidPreRelation H.groupoid) := by
  have _ : Mono (groupoidPreRelation G) := mono_groupoidPreRelation G
  have hmr : Mono (prod.lift (restrictionTarget G g) (restrictionSource G g)) := by
    rw [← restrictionIso_relation G g]
    have _ : Mono (PreRelation.restrict (groupoidPreRelation G) g) := by
      change Mono (pullback.fst (prod.map g g) (groupoidPreRelation G))
      infer_instance
    infer_instance
  have hexp : groupoidPreRelation H.groupoid =
      eqToHom H.arrows_eq ≫ prod.lift (restrictionTarget G g) (restrictionSource G g) ≫
        prod.map (eqToHom H.objects_eq.symm) (eqToHom H.objects_eq.symm) := by
    rw [groupoidPreRelation, H.source_eq, H.target_eq]
    simp
  rw [hexp]
  have _ : IsIso (eqToHom H.arrows_eq) := inferInstance
  have _ : IsIso (prod.map (eqToHom H.objects_eq.symm) (eqToHom H.objects_eq.symm)) :=
    inferInstance
  infer_instance

/-- If the target and the source of a groupoid scheme form an equivalence relation, then so do
the target and the source of any restriction of it. -/
instance isEquivalenceRelation_restriction (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source] {U' : Over S} (g : U' ⟶ G.objects)
    (H : Restriction G g) :
    IsEquivalenceRelation H.groupoid.target H.groupoid.source := by
  have h := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (groupoidPreRelation H.groupoid)).2
    ⟨mono_groupoidPreRelation_restriction G g H,
      groupoidPreRelation_isPreEquivalenceRelation H.groupoid⟩
  simpa [groupoidPreRelation, PreRelation.target, PreRelation.source] using h

/-- Let a groupoid scheme over `S` have finite locally free source and target maps and let its
target and source maps form an equivalence relation. Restricting it to an invariant affine open
`V` of its object scheme gives an equivalence relation on `V` with affine arrow scheme and finite
locally free source and target, and it has a quotient (Stacks 03BM): an affine `S`-scheme, of
size at most that of `V`, receiving from `V` a surjective finite locally free morphism whose
kernel pair is the restricted relation. -/
theorem exists_affineQuotient_of_isInvariantOpen (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (V : G.objects.left.Opens) (hVinv : IsInvariantOpen G V) (hVaff : IsAffineOpen V)
    (g : Over.mk (V.ι ≫ G.objects.hom) ⟶ G.objects) (hg : g.left = V.ι) :
    ∃ (A : Type u) (_ : CommRing A) (q : Spec (.of A) ⟶ S)
      (π : (restrict G g).groupoid.objects ⟶ Over.mk q),
      (Spec (CommRingCat.of A)).size ≤ V.toScheme.size ∧
        IsFiniteLocallyFree π.left ∧ Surjective π.left ∧
        IsPullback (restrict G g).groupoid.target (restrict G g).groupoid.source π π := by
  have hoL : (restrict G g).groupoid.objects.left = V.toScheme :=
    congrArg Over.left (restrict G g).objects_eq
  have haL : (restrict G g).groupoid.arrows.left = (restrictionArrows G g).left :=
    congrArg Over.left (restrict G g).arrows_eq
  have _ : IsAffine V.toScheme := hVaff
  have _ : IsAffine (restrict G g).groupoid.objects.left := by rw [hoL]; infer_instance
  have _ : IsFinite G.source.left :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp inferInstance |>.1
  have _ : IsAffineHom G.source.left := inferInstance
  have _ : IsAffine (restrict G g).groupoid.arrows.left := by
    rw [haL]
    exact isAffine_restrictionArrows_of_isInvariantOpen G V hVinv hVaff g hg
  obtain ⟨hsrc, htgt⟩ := property_restrict_source_target_of_isInvariantOpen
    (@IsFiniteLocallyFree.{u}) G V hVinv inferInstance g hg
  have _ := hsrc
  have _ := htgt
  obtain ⟨A, _, q, π, hsize, hflf, hsurj, hpb⟩ :=
    Space.exists_quotient_of_isFiniteLocallyFree_relation S
      (restrict G g).groupoid.target (restrict G g).groupoid.source
  exact ⟨A, ‹_›, q, π, by rw [← hoL]; exact hsize, hflf, hsurj, hpb⟩

/-! ### Representation of the quotient sheaf by a finite locally free kernel-pair quotient -/

/-- The target map of the pre-relation attached to a groupoid scheme is its target map. -/
theorem groupoidPreRelation_target (K : GroupoidScheme S) :
    (groupoidPreRelation K).target = K.target := prod.lift_fst _ _

/-- The source map of the pre-relation attached to a groupoid scheme is its source map. -/
theorem groupoidPreRelation_source (K : GroupoidScheme S) :
    (groupoidPreRelation K).source = K.source := prod.lift_snd _ _

/-- Let `K` be a groupoid scheme over `S` and let `π` be a morphism from its object scheme which is
finite locally free and surjective and which exhibits the target and the source of `K` as its
kernel pair. Then the canonical map from the fppf quotient sheaf of `K` to the functor of points of
the target of `π` is an isomorphism. -/
theorem isIso_quotientSheafToPoints_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (K : GroupoidScheme S) {M : Over S} (π : K.objects ⟶ M)
    (hflf : IsFiniteLocallyFree π.left) (hsurj : Surjective π.left)
    (hpb : IsPullback K.target K.source π π)
    (hw : (groupoidPreRelation K).target ≫ π = (groupoidPreRelation K).source ≫ π) :
    IsIso (quotientSheafToPoints (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (groupoidPreRelation K) π hw (isSheaf_points B S hS M)) := by
  have _ := hflf
  have _ := hsurj
  have _ : Flat π.left := IsFiniteLocallyFree.flat π.left
  have _ : LocallyOfFinitePresentation π.left :=
    IsFiniteLocallyFree.locallyOfFinitePresentation π.left
  have hk : IsIso (pullback.lift (groupoidPreRelation K).target
      (groupoidPreRelation K).source hw) := by
    have he : pullback.lift (groupoidPreRelation K).target (groupoidPreRelation K).source hw =
        hpb.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, hpb.isoPullback_hom_fst, groupoidPreRelation_target]
      · rw [pullback.lift_snd, hpb.isoPullback_hom_snd, groupoidPreRelation_source]
    rw [he]
    infer_instance
  have _ := hk
  exact isIso_quotientSheafToPoints _ _ (groupoidPreRelation K) π hw _
    (isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS π)
    inferInstance

/-! ### The source square of a restriction to an invariant open is cartesian -/

/-- For an open immersion `g` of schemes over `S` into the object scheme whose range is invariant
under the arrows of the groupoid, a generalized point of the arrow scheme whose image under the
source map factors through `g` has its image under the target map factor through `g` as well. -/
theorem exists_lift_target_of_isInvariantSet (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : IsInvariantSet G (Set.range g.left.base)) {T : Over S} (x : T ⟶ G.arrows)
    (y : T ⟶ U') (hxy : x ≫ G.source = y ≫ g) :
    ∃ z : T ⟶ U', z ≫ g = x ≫ G.target := by
  have hrange : Set.range (x ≫ G.target).left.base ⊆ Set.range g.left.base := by
    rintro w ⟨τ, rfl⟩
    have hs : G.source.left.base (x.left.base τ) ∈ Set.range g.left.base := by
      refine ⟨y.left.base τ, ?_⟩
      have h := congrArg (fun k : T ⟶ G.objects => k.left.base τ) hxy
      simpa [Over.comp_left, Scheme.Hom.comp_apply] using h.symm
    simpa [Over.comp_left, Scheme.Hom.comp_apply] using hg (x.left.base τ) hs
  refine ⟨Over.homMk (IsOpenImmersion.lift g.left (x ≫ G.target).left hrange) ?_, ?_⟩
  · have hw : g.left ≫ G.objects.hom = U'.hom := Over.w g
    rw [← hw, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (x ≫ G.target)
  · apply Over.OverMorphism.ext
    simp

/-- The point of the arrow scheme of a restriction along an invariant open immersion determined
by an arrow together with a lift of its source. -/
private noncomputable def restrictionLift (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : IsInvariantSet G (Set.range g.left.base)) {T : Over S} (x : T ⟶ G.arrows)
    (y : T ⟶ U') (hxy : x ≫ G.source = y ≫ g) : T ⟶ restrictionArrows G g :=
  pullback.lift
    (pullback.lift (exists_lift_target_of_isInvariantSet G g hg x y hxy).choose x
      (exists_lift_target_of_isInvariantSet G g hg x y hxy).choose_spec)
    (pullback.lift x y hxy) (by rw [pullback.lift_snd, pullback.lift_fst])

private theorem restrictionLift_arrows (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : IsInvariantSet G (Set.range g.left.base)) {T : Over S} (x : T ⟶ G.arrows)
    (y : T ⟶ U') (hxy : x ≫ G.source = y ≫ g) :
    restrictionLift G g hg x y hxy ≫ restrictionArrowsToArrows G g = x :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd g G.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_snd _ _ _))

private theorem restrictionLift_source (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : IsInvariantSet G (Set.range g.left.base)) {T : Over S} (x : T ⟶ G.arrows)
    (y : T ⟶ U') (hxy : x ≫ G.source = y ≫ g) :
    restrictionLift G g hg x y hxy ≫ restrictionSource G g = y :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd G.source g) (pullback.lift_snd _ _ _)).trans
      (pullback.lift_snd _ _ _))

/-- For an open immersion `g` into the object scheme of a groupoid scheme whose range is invariant
under the arrows, the square formed by the projection to the original arrow scheme, the source map
of the restriction, the source map of the groupoid and `g` is cartesian. -/
theorem isPullback_restrictionArrowsToArrows_of_isInvariantSet (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) [IsOpenImmersion g.left]
    (hg : IsInvariantSet G (Set.range g.left.base)) :
    IsPullback (restrictionArrowsToArrows G g) (restrictionSource G g) G.source g := by
  classical
  have _ : Mono g := Over.mono_of_mono_left g
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (restriction_condition G g).symm
    (fun s => restrictionLift G g hg s.fst s.snd s.condition)
    (fun s => restrictionLift_arrows G g hg s.fst s.snd s.condition)
    (fun s => restrictionLift_source G g hg s.fst s.snd s.condition)
    (fun s m hm₁ hm₂ => ?_))
  have key : ∀ k : s.pt ⟶ restrictionArrows G g,
      (k ≫ restrictionTarget G g) ≫ g = (k ≫ restrictionArrowsToArrows G g) ≫ G.target := by
    intro k
    rw [Category.assoc, Category.assoc, restriction_condition']
  refine restriction_hom_ext G g m _ ?_ ?_ ?_
  · rw [hm₂, restrictionLift_source]
  · refine (cancel_mono g).mp ?_
    rw [key m, key (restrictionLift G g hg s.fst s.snd s.condition), hm₁,
      restrictionLift_arrows]
  · rw [hm₁, restrictionLift_arrows]

end AlgebraicGeometry.GroupoidScheme

end
