module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation

/-!
# Étale morphisms of affine groupoid schemes and their invariant rings

Let `f : (U', R', s', t', c') ⟶ (U, R, s, t, c)` be a morphism of groupoid schemes with all four
of `U`, `R`, `U'`, `R'` affine, with `s`, `t`, `s'`, `t'` finite locally free, with the squares
formed by `f` and the two target maps and by `f` and the two stabilizer group schemes cartesian,
and with `f : U' → U` étale. Writing `C` and `C'` for the rings of invariant functions, this file
constructs the canonical morphism `U' ⟶ Spec C' ×_{Spec C} U` and proves that it is surjective
and universally injective, hence that it is an isomorphism as soon as `C → C'` is étale.

The two point-set statements are proved by testing on morphisms out of the spectrum of an
algebraically closed field, where the fibre description of the quotient morphism
(`AlgebraicGeometry.GroupoidScheme.comp_objectsToInvariantSpectrum_eq_iff`, Tag 03BL) is
available. Universal injectivity is reduced to surjectivity of the diagonal, and the resulting
statement about two points of `U'` with the same image is exactly the place where the cartesian
stabilizer square is used: an arrow of `R'` joining two such points has equal source and target
after mapping to `R`, so it is a point of the stabilizer of `G`, and the cartesian stabilizer
square lifts it back to a point of the stabilizer of `G'`, which the cartesian target square
identifies with the original arrow.

## Main definitions

* `AlgebraicGeometry.stabilizerLift`: the point of the stabilizer determined by an arrow whose
  source and target agree.
* `AlgebraicGeometry.GroupoidScheme.invariantPullbackComparison`: the canonical morphism from
  the object scheme of `G'` to the fibre product of the object scheme of `G` with the invariant
  spectrum of `G'` over the invariant spectrum of `G`.

## Main results

* `AlgebraicGeometry.exists_stabilizer_lift`: an arrow whose source and target agree is a point
  of the stabilizer.
* `AlgebraicGeometry.mono_stabilizerArrow`: a point of the stabilizer is determined by the
  arrow underlying it.
* `AlgebraicGeometry.surjective_of_forall_isAlgClosed`: a morphism of schemes all of whose
  morphisms from the spectrum of an algebraically closed field lift is surjective.
* `AlgebraicGeometry.GroupoidScheme.surjective_invariantPullbackComparison` and
  `AlgebraicGeometry.GroupoidScheme.universallyInjective_invariantPullbackComparison`: the
  comparison morphism is surjective and universally injective.
* `AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects_of_etale_invariantRingMap`: if the
  induced map on invariant rings is étale then the square formed by the morphism on object
  schemes and the two quotient morphisms is cartesian — the implication from the first conclusion
  of [Stacks Project, Tag 0DT9] to the second.

## Implementation notes

The étaleness of `C → C'` — the first conclusion of [Stacks Project, Tag 0DT9] — is *not* proved
here; it is taken as a hypothesis of
`AlgebraicGeometry.GroupoidScheme.etale_invariantPullbackComparison` and of the two results
downstream of it, and that is the only input they need. Everything above it in this file,
including the two point-set statements that the source text passes over with "some details
omitted", is unconditional.

That hypothesis is discharged in
`StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleInvariantRingMapAssembly`, by
`AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap`, and the tag is registered there — on
the two unconditional conclusions
`AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap` and
`AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects`. It cannot be discharged in this file:
the proof of the first conclusion base changes to a strict henselization of `C`, and every module
that does so imports this one.

Surjectivity and universal injectivity are both instances of
`AlgebraicGeometry.surjective_of_forall_isAlgClosed`, which replaces the base change to strictly
henselian local rings of the source text: over an algebraically closed field the two towers of
residue field extensions that the source text has to compare are equal by construction, so the
pure inseparability argument is not needed.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### Points of the stabilizer -/

section Stabilizer

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The first projection of the stabilizer pullback followed by a map `e` out of the arrows is the
second projection, if `e` is a projection of the source-target pair. -/
private theorem stabilizer_fst_comp_eq_snd
    (m : MonoidalCategory.tensorObj G.objects G.objects ⟶ G.objects) (e : G.arrows ⟶ G.objects)
    (hm : diagonal G ≫ m = 𝟙 G.objects) (he : sourceTarget G ≫ m = e) :
    pullback.fst (sourceTarget G) (diagonal G) ≫ e =
      pullback.snd (sourceTarget G) (diagonal G) := by
  rw [← he, ← Category.assoc, pullback.condition, Category.assoc, hm, Category.comp_id]

/-- The arrow underlying a point of the stabilizer has the base point as its target. -/
theorem stabilizerArrow_comp_target : stabilizerArrow G ≫ G.target.left = (stabilizer G).hom :=
  congrArg Over.Hom.left
    (stabilizer_fst_comp_eq_snd G (fst _ _) _ (by simp [diagonal]) (by simp [sourceTarget]))

/-- The arrow underlying a point of the stabilizer has the base point as its source. -/
theorem stabilizerArrow_comp_source : stabilizerArrow G ≫ G.source.left = (stabilizer G).hom :=
  congrArg Over.Hom.left
    (stabilizer_fst_comp_eq_snd G (snd _ _) _ (by simp [diagonal]) (by simp [sourceTarget]))

/-- A point of the stabilizer is determined by the arrow of the groupoid underlying it, because
the arrow determines the base point as its source. -/
instance mono_stabilizerArrow : Mono (stabilizerArrow G) where
  right_cancellation k l h := by
    refine (overFibreProduct_isPullback (sourceTarget G) (diagonal G)).hom_ext h ?_
    change k ≫ (stabilizer G).hom = l ≫ (stabilizer G).hom
    rw [← stabilizerArrow_comp_source, ← Category.assoc, h, Category.assoc]

/-- **The point of the stabilizer determined by an arrow whose source and target agree.**

The stabilizer is a fibre product formed in the category of schemes over the base, so the point
is produced by making the test scheme a scheme over the base along the given arrow. -/
def stabilizerLift {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (hr : r ≫ G.source.left = r ≫ G.target.left) : T ⟶ (stabilizer G).left :=
  (pullback.lift (f := sourceTarget G) (g := diagonal G)
    (Over.homMk r : (Over.mk (r ≫ G.arrows.hom) : Over S) ⟶ G.arrows)
    ((Over.homMk r : (Over.mk (r ≫ G.arrows.hom) : Over S) ⟶ G.arrows) ≫ G.source) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [sourceTarget, diagonal, Category.assoc, lift_fst, Category.comp_id]
        exact Over.OverMorphism.ext (by simpa [Over.comp_left] using hr.symm)
      · simp only [sourceTarget, diagonal, Category.assoc, lift_snd,
          Category.comp_id])).left

/-- The arrow underlying `AlgebraicGeometry.stabilizerLift` is the given arrow. -/
@[reassoc]
theorem stabilizerLift_comp_stabilizerArrow {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (hr : r ≫ G.source.left = r ≫ G.target.left) :
    stabilizerLift G r hr ≫ stabilizerArrow G = r := by
  rw [stabilizerLift]
  exact congrArg Over.Hom.left (pullback.lift_fst _ _ _)

/-- The base point of `AlgebraicGeometry.stabilizerLift` is the source of the given arrow. -/
@[reassoc]
theorem stabilizerLift_comp_hom {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (hr : r ≫ G.source.left = r ≫ G.target.left) :
    stabilizerLift G r hr ≫ (stabilizer G).hom = r ≫ G.source.left := by
  rw [stabilizerLift]
  exact congrArg Over.Hom.left (pullback.lift_snd _ _ _)

/-- An arrow whose source and target agree factors through the stabilizer.

The stabilizer is a fibre product formed in the category of schemes over the base, so the
witness is produced by making the test scheme a scheme over the base along the given arrow. -/
theorem exists_stabilizer_lift {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (hr : r ≫ G.source.left = r ≫ G.target.left) :
    ∃ g : T ⟶ (stabilizer G).left, g ≫ stabilizerArrow G = r ∧
      g ≫ (stabilizer G).hom = r ≫ G.source.left :=
  ⟨stabilizerLift G r hr, stabilizerLift_comp_stabilizerArrow G r hr,
    stabilizerLift_comp_hom G r hr⟩

end Stabilizer

/-! ### Surjectivity tested on points over algebraically closed fields -/

/-- A morphism of schemes along which every morphism from the spectrum of an algebraically
closed field lifts is surjective.

Every point of the target is the image of the spectrum of the algebraic closure of its residue
field, so a lift of that morphism produces a preimage of the point. -/
theorem surjective_of_forall_isAlgClosed {X Y : Scheme.{u}} (g : X ⟶ Y)
    (H : ∀ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (y : Spec (.of K) ⟶ Y),
      ∃ x : Spec (.of K) ⟶ X, x ≫ g = y) : Surjective g := by
  rw [surjective_iff]
  intro z
  obtain ⟨x, hx⟩ := H (AlgebraicClosure (Y.residueField z)) inferInstance inferInstance
    (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField z) (AlgebraicClosure (Y.residueField z)))) ≫
      Y.fromSpecResidueField z)
  obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure (Y.residueField z)))) := inferInstance
  refine ⟨x.base p, ?_⟩
  change (x ≫ g).base p = z
  rw [hx]
  change (Y.fromSpecResidueField z).base _ = z
  exact Y.fromSpecResidueField_apply z _

namespace GroupoidScheme

/-! ### The comparison with the fibre product over the invariant spectrum -/

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- The canonical morphism from the object scheme of `G'` to the fibre product of the object
scheme of `G` with the invariant spectrum of `G'` over the invariant spectrum of `G`. -/
def invariantPullbackComparison [IsAffine G.objects.left] [IsAffine G.arrows.left] :
    G'.objects.left ⟶ pullback (objectsToInvariantSpectrum G)
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
  pullback.lift F.mapObjects.left (objectsToInvariantSpectrum G')
    (mapObjects_comp_objectsToInvariantSpectrum F)

/-- The comparison morphism followed by the first projection is the morphism of object schemes
induced by `F`. -/
@[reassoc (attr := simp)]
theorem invariantPullbackComparison_comp_fst [IsAffine G.objects.left]
    [IsAffine G.arrows.left] :
    invariantPullbackComparison F ≫ pullback.fst (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F))) = F.mapObjects.left :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection is the morphism from the object
scheme of `G'` to its invariant spectrum. -/
@[reassoc (attr := simp)]
theorem invariantPullbackComparison_comp_snd [IsAffine G.objects.left]
    [IsAffine G.arrows.left] :
    invariantPullbackComparison F ≫ pullback.snd (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F))) = objectsToInvariantSpectrum G' :=
  pullback.lift_snd _ _ _

/-! ### Surjectivity and universal injectivity of the comparison -/

/-- The comparison morphism is surjective.

Over an algebraically closed field a point of the fibre product is a point of the invariant
spectrum of `G'` together with a point of the object scheme of `G` with the same image in the
invariant spectrum of `G`. The first lifts to the object scheme of `G'` by Tag 03BL, its image
in the object scheme of `G` then has the same image in the invariant spectrum as the second, so
again by Tag 03BL the two are joined by an arrow of `R`, and the cartesian target square lifts
that arrow to `R'`. Its source is the required point. -/
theorem surjective_invariantPullbackComparison
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left) :
    Surjective (invariantPullbackComparison F) := by
  apply surjective_of_forall_isAlgClosed
  intro K _ _ y
  have hcond : (y ≫ pullback.fst (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F)))) ≫ objectsToInvariantSpectrum G =
      (y ≫ pullback.snd (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F)))) ≫
        Spec.map (CommRingCat.ofHom (invariantRingMap F)) := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨α', hα'⟩ := surjective_comp_objectsToInvariantSpectrum G' K
    (y ≫ pullback.snd (objectsToInvariantSpectrum G)
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))))
  replace hα' : α' ≫ objectsToInvariantSpectrum G' =
      y ≫ pullback.snd (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F))) := hα'
  have heq : (α' ≫ F.mapObjects.left) ≫ objectsToInvariantSpectrum G =
      (y ≫ pullback.fst (objectsToInvariantSpectrum G)
        (Spec.map (CommRingCat.ofHom (invariantRingMap F)))) ≫
        objectsToInvariantSpectrum G := by
    rw [Category.assoc, mapObjects_comp_objectsToInvariantSpectrum, ← Category.assoc, hα',
      hcond]
  obtain ⟨r, hrt, hrs⟩ := (comp_objectsToInvariantSpectrum_eq_iff G K
    (α' ≫ F.mapObjects.left) _).mp heq
  refine ⟨htarget.lift r α' hrt ≫ G'.source.left, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, invariantPullbackComparison_comp_fst, Category.assoc,
      ← F.map_source_left, ← Category.assoc, htarget.lift_fst, hrs]
  · rw [Category.assoc, invariantPullbackComparison_comp_snd, Category.assoc,
      source_comp_objectsToInvariantSpectrum, ← Category.assoc, htarget.lift_snd, hα']

/-- The comparison morphism is universally injective.

Universal injectivity is surjectivity of the diagonal, which over an algebraically closed field
says that two points of the object scheme of `G'` with the same image in the object scheme of
`G` and in the invariant spectrum of `G'` are equal. By Tag 03BL such a pair is joined by an
arrow `r'` of `R'`; its image in `R` has equal source and target, hence is a point of the
stabilizer of `G`, and the cartesian stabilizer square lifts it to a point of the stabilizer of
`G'` whose arrow has the same image in `R` as `r'` and the same target, so the cartesian target
square identifies it with `r'`. Its source and target therefore agree. -/
theorem universallyInjective_invariantPullbackComparison
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left) :
    UniversallyInjective (invariantPullbackComparison F) := by
  rw [UniversallyInjective.iff_diagonal]
  apply surjective_of_forall_isAlgClosed
  intro K _ _ y
  have hu : (y ≫ pullback.fst (invariantPullbackComparison F)
        (invariantPullbackComparison F)) ≫ invariantPullbackComparison F =
      (y ≫ pullback.snd (invariantPullbackComparison F)
        (invariantPullbackComparison F)) ≫ invariantPullbackComparison F := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hdiag : ∀ {W : Scheme.{u}} (a : _ ⟶ W) (b : G'.objects.left ⟶ W),
      invariantPullbackComparison F ≫ a = b →
      (y ≫ pullback.fst (invariantPullbackComparison F) (invariantPullbackComparison F)) ≫ b =
        (y ≫ pullback.snd (invariantPullbackComparison F) (invariantPullbackComparison F)) ≫ b := by
    intro W a b h
    rw [← h, ← Category.assoc, ← Category.assoc, hu]
  have hf := hdiag _ _ (invariantPullbackComparison_comp_fst F)
  have hm := hdiag _ _ (invariantPullbackComparison_comp_snd F)
  obtain ⟨r', hr't, hr's⟩ := (comp_objectsToInvariantSpectrum_eq_iff G' K _ _).mp hm
  have hrt : (r' ≫ F.mapArrows.left) ≫ G.target.left =
      (y ≫ pullback.fst (invariantPullbackComparison F)
        (invariantPullbackComparison F)) ≫ F.mapObjects.left := by
    rw [Category.assoc, F.map_target_left, ← Category.assoc, hr't]
  have hrs : (r' ≫ F.mapArrows.left) ≫ G.source.left =
      (y ≫ pullback.snd (invariantPullbackComparison F)
        (invariantPullbackComparison F)) ≫ F.mapObjects.left := by
    rw [Category.assoc, F.map_source_left, ← Category.assoc, hr's]
  obtain ⟨g, hg1, hg2⟩ := exists_stabilizer_lift G (r' ≫ F.mapArrows.left) (by rw [hrs, hrt, hf])
  have hwlift : g ≫ (stabilizer G).hom =
      (y ≫ pullback.fst (invariantPullbackComparison F)
        (invariantPullbackComparison F)) ≫ F.mapObjects.left := by rw [hg2, hrs, ← hf]
  have key : hstab.lift g _ hwlift ≫ stabilizerArrow G' = r' := by
    refine htarget.hom_ext ?_ ?_
    · rw [Category.assoc, ← stabilizerMap_left_comp_stabilizerArrow, ← Category.assoc,
        hstab.lift_fst, hg1]
    · rw [Category.assoc, stabilizerArrow_comp_target, hstab.lift_snd, hr't]
  refine ⟨y ≫ pullback.fst (invariantPullbackComparison F) (invariantPullbackComparison F),
    pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, ← hr's, ← key,
      Category.assoc, stabilizerArrow_comp_source, hstab.lift_snd]

/-! ### The cartesian square from étaleness of the map on invariant rings -/

/-- **Stacks Project, Tag 02GW.** If the induced map on invariant rings is étale then the
comparison morphism is étale, being a morphism over the object scheme of `G` between two
schemes which are étale over it. -/
theorem etale_invariantPullbackComparison [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [Etale F.mapObjects.left] (hC : (invariantRingMap F).Etale) :
    Etale (invariantPullbackComparison F) := by
  have : Etale (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
    HasRingHomProperty.Spec_iff.mpr hC
  have : Etale (pullback.fst (objectsToInvariantSpectrum G)
    (Spec.map (CommRingCat.ofHom (invariantRingMap F)))) := inferInstance
  exact etale_of_etale_over _ (invariantPullbackComparison_comp_fst F)

/-- **Stacks Project, Tag 02LC.** If the induced map on invariant rings is étale then the
comparison morphism is an isomorphism, being étale, universally injective and surjective. -/
theorem isIso_invariantPullbackComparison
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    [Etale F.mapObjects.left] (hC : (invariantRingMap F).Etale) :
    IsIso (invariantPullbackComparison F) :=
  have := etale_invariantPullbackComparison F hC
  have := universallyInjective_invariantPullbackComparison F htarget hstab
  have := surjective_invariantPullbackComparison F htarget
  Stacks.Etale.isIso_of_etale_of_universallyInjective_of_surjective _

/-- **The implication from the first conclusion of [Stacks Project, Tag 0DT9] to the second**: if
the induced map on invariant rings is étale, then the object scheme of `G'` is the fibre product of
the object scheme of `G` with the invariant spectrum of `G'` over the invariant spectrum of `G`.
In the notation of the source, `U' = Spec C' ×_{Spec C} U`.

Of the four hypotheses of the source, all but the cartesian `s'/s` square are present: that `U`,
`R`, `U'`, `R'` are affine is the four `IsAffine` instances; that `s`, `t`, `s'`, `t'` are finite
locally free is the four `IsFiniteLocallyFree` instances; the cartesian `t'/t` and `G'/G` squares
are `htarget` and `hstab`; and that `f : U' → U` is étale is `[Etale F.mapObjects.left]`. The
cartesian `s'/s` square is not needed for this implication, so it is not assumed.

The first conclusion of the tag — étaleness of the map `C → C'` on invariant functions — is carried
as the hypothesis `hC`. It is proved, from the four hypotheses of the source, by
`AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap`, and
`AlgebraicGeometry.GroupoidScheme.isPullback_mapObjects` is this theorem with `hC` so discharged;
the tag is registered there, on the two unconditional conclusions. This theorem keeps `hC` as a
hypothesis because it is the general implication, and because it is upstream of the proof of the
first conclusion: `AlgebraicGeometry.GroupoidScheme.etale_invariantRingMap` is obtained by base
changing to a strict henselization, and the modules that do so import this one. -/
theorem isPullback_mapObjects_of_etale_invariantRingMap
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    [Etale F.mapObjects.left] (hC : (invariantRingMap F).Etale) :
    IsPullback F.mapObjects.left (objectsToInvariantSpectrum G')
      (objectsToInvariantSpectrum G) (Spec.map (CommRingCat.ofHom (invariantRingMap F))) :=
  have := isIso_invariantPullbackComparison F htarget hstab hC
  IsPullback.of_iso_pullback ⟨mapObjects_comp_objectsToInvariantSpectrum F⟩
    (asIso (invariantPullbackComparison F)) (by simp) (by simp)

end GroupoidScheme

end AlgebraicGeometry

end
