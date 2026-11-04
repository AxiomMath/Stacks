module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a groupoid scheme twice

For a groupoid scheme `G` and composable maps `g' : U'' ⟶ U'` and `g : U' ⟶ U` into its scheme
of objects, the two fibre products which occur on restricting first along `g` and then along
`g'` fit into a diagram of two cartesian squares.  The right-hand square is the fibre product of
the two source maps `U' ×_U R ⟶ U` and `U'' ×_U R ⟶ U`; the left-hand square compares it with
`U'' ×_{U'} R'`, where `R'` is the arrow scheme of the first restriction.  The comparison sends
a pair of arrows with a common source to the composite of the second with the inverse of the
first.

## Main definitions

* `AlgebraicGeometry.DoubleRestrictionDiagram` records the comparison morphism and the two
  cartesian squares.

## Main results

* `AlgebraicGeometry.doubleRestrictionDiagram` is the canonical double-restriction diagram.

## Implementation notes

The arrow scheme of the first restriction is represented by the chosen iterated pullback
`AlgebraicGeometry.restrictionArrows`.  The formula for the upper-left map is recorded after
projection to the original arrow scheme; its other two components are recorded separately.  This
is the categorical version of `((u', r₀), (u'', r₁)) ↦ (u'', (r₁ ∘ r₀⁻¹, (g' u'', u')))`.

## References

* [Stacks Project, Tag 04MW](https://stacks.math.columbia.edu/tag/04MW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The space `U' ×_U R` occurring in the first restriction. -/
public noncomputable def firstArrowSource {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : Over S :=
  pullback g G.target

/-- The map `s ∘ pr₁ : U' ×_U R ⟶ U`. -/
public noncomputable def firstSourceMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : firstArrowSource G g ⟶ G.objects :=
  pullback.snd g G.target ≫ G.source

/-- The space `U'' ×_U R` obtained using the composite `g' ≫ g`. -/
public noncomputable def compositeArrowSource {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') : Over S :=
  pullback (g' ≫ g) G.target

/-- The map `s ∘ pr₁ : U'' ×_U R ⟶ U`. -/
public noncomputable def compositeSourceMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeArrowSource G g g' ⟶ G.objects :=
  pullback.snd (g' ≫ g) G.target ≫ G.source

/-- The upper-middle object in the double-restriction diagram. -/
public noncomputable def commonSourcePairs {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') : Over S :=
  pullback (firstSourceMap G g) (compositeSourceMap G g g')

/-- The upper-left object `U'' ×_{U'} R'`, where `R'` is the arrow scheme of the
restriction along `g`. -/
public noncomputable def secondArrowSource {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') : Over S :=
  pullback g' (restrictionTarget G g)

/-- The left vertical map `s' ∘ pr₁` in the double-restriction diagram. -/
public noncomputable def secondSourceMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    secondArrowSource G g g' ⟶ U' :=
  pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g

/-- The comparison map together with its pointwise formula and the two cartesian
squares in the double-restriction diagram. -/
public structure DoubleRestrictionDiagram {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') where
  /-- The upper-left horizontal arrow. -/
  comparison : commonSourcePairs G g g' ⟶ secondArrowSource G g g'
  /-- Its `U''` component is the evident projection. -/
  comparison_fst :
    comparison ≫ pullback.fst g' (restrictionTarget G g) =
      pullback.snd (firstSourceMap G g) (compositeSourceMap G g g') ≫
        pullback.fst (g' ≫ g) G.target
  /-- Its source lift in the first restriction is the `U'` component of the
  first pair. -/
  comparison_source :
    comparison ≫ pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g =
      pullback.fst (firstSourceMap G g) (compositeSourceMap G g g') ≫
        pullback.fst g G.target
  /-- The two arrows in the formula for the comparison are composable. -/
  comparison_composable :
    (pullback.snd (firstSourceMap G g) (compositeSourceMap G g g') ≫
        pullback.snd (g' ≫ g) G.target) ≫ G.source =
      (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g') ≫
        pullback.snd g G.target ≫ G.inverse) ≫ G.target
  /-- On arrows of the original groupoid, the comparison sends `(r₀, r₁)` to
  `r₁ ∘ r₀⁻¹`. -/
  comparison_arrow :
    comparison ≫ pullback.snd g' (restrictionTarget G g) ≫
        restrictionArrowsToArrows G g =
      G.compose
        (pullback.snd (firstSourceMap G g) (compositeSourceMap G g g') ≫
          pullback.snd (g' ≫ g) G.target)
        (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g') ≫
          pullback.snd g G.target ≫ G.inverse) comparison_composable
  /-- The left-hand square is cartesian. -/
  left_isPullback :
    IsPullback comparison
      (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g'))
      (secondSourceMap G g g') (pullback.fst g G.target)
  /-- The right-hand square is cartesian. -/
  right_isPullback :
    IsPullback
      (pullback.snd (firstSourceMap G g) (compositeSourceMap G g g'))
      (pullback.fst (firstSourceMap G g) (compositeSourceMap G g g'))
      (compositeSourceMap G g g') (firstSourceMap G g)

/-- The projection of the upper-middle object to the first fibre product. -/
public noncomputable abbrev commonFst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    commonSourcePairs G g g' ⟶ firstArrowSource G g :=
  pullback.fst (firstSourceMap G g) (compositeSourceMap G g g')

/-- The projection of the upper-middle object to the composite fibre product. -/
public noncomputable abbrev commonSnd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    commonSourcePairs G g g' ⟶ compositeArrowSource G g g' :=
  pullback.snd (firstSourceMap G g) (compositeSourceMap G g g')

/-- The projection of `U' ×_U R` to `U'`. -/
public noncomputable abbrev firstFst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : firstArrowSource G g ⟶ U' :=
  pullback.fst g G.target

/-- The projection of `U' ×_U R` to the arrow scheme. -/
public noncomputable abbrev firstSnd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : firstArrowSource G g ⟶ G.arrows :=
  pullback.snd g G.target

/-- The projection of `U'' ×_U R` to `U''`. -/
public noncomputable abbrev compositeFst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeArrowSource G g g' ⟶ U'' :=
  pullback.fst (g' ≫ g) G.target

/-- The projection of `U'' ×_U R` to the arrow scheme. -/
public noncomputable abbrev compositeSnd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeArrowSource G g g' ⟶ G.arrows :=
  pullback.snd (g' ≫ g) G.target

/-- The defining relation of the upper-middle fibre product. -/
public lemma common_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    commonFst G g g' ≫ firstSourceMap G g =
      commonSnd G g g' ≫ compositeSourceMap G g g' := pullback.condition

/-- The defining relation of `U'' ×_U R`. -/
public lemma composite_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    compositeFst G g g' ≫ g' ≫ g = compositeSnd G g g' ≫ G.target := pullback.condition

/-- The defining relation of `U' ×_U R`. -/
public lemma first_condition {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    firstFst G g ≫ g = firstSnd G g ≫ G.target := pullback.condition

/-- The second arrow of a pair with a common source is composable with the inverse of the
first. -/
public lemma comparisonComposable {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    (commonSnd G g g' ≫
        compositeSnd G g g') ≫ G.source =
      (commonFst G g g' ≫
        firstSnd G g ≫ G.inverse) ≫ G.target := by
  simp only [Category.assoc, G.target_inverse]
  exact (common_condition G g g').symm

/-- The arrow `r₁ ∘ r₀⁻¹` attached to a pair of arrows with a common source. -/
public noncomputable abbrev comparisonArrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    commonSourcePairs G g g' ⟶ G.arrows :=
  G.compose
    (commonSnd G g g' ≫
      compositeSnd G g g')
    (commonFst G g g' ≫
      firstSnd G g ≫ G.inverse) (comparisonComposable G g g')

/-- The target of `comparisonArrow` is the image in `U` of the `U''` component. -/
public lemma comparisonArrow_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    comparisonArrow G g g' ≫ G.target =
      commonSnd G g g' ≫
        compositeFst G g g' ≫ g' ≫ g := by
  rw [comparisonArrow, Stacks.Groupoids.GroupoidScheme.compose, Category.assoc, G.target_comp,
    ← Category.assoc, pullback.lift_fst]
  simpa only [Category.assoc] using
    congrArg (fun k => commonSnd G g g' ≫ k)
      (composite_condition G g g').symm

/-- The source of `comparisonArrow` is the image in `U` of the `U'` component. -/
public lemma comparisonArrow_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    comparisonArrow G g g' ≫ G.source =
      commonFst G g g' ≫
        firstFst G g ≫ g := by
  rw [comparisonArrow, Stacks.Groupoids.GroupoidScheme.compose, Category.assoc, G.source_comp,
    ← Category.assoc, pullback.lift_snd]
  simp only [Category.assoc, G.source_inverse]
  simpa only [Category.assoc] using
    congrArg (fun k => commonFst G g g' ≫ k)
      (first_condition G g).symm

/-- The lift of `comparisonArrow` to an arrow of the first restriction. -/
public noncomputable abbrev comparisonRestrictionArrow {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' U'' : Over S} (g : U' ⟶ G.objects)
    (g' : U'' ⟶ U') : commonSourcePairs G g g' ⟶ restrictionArrows G g :=
  pullback.lift
    (pullback.lift
      (commonSnd G g g' ≫
        compositeFst G g g' ≫ g')
      (comparisonArrow G g g') (by
        simpa only [Category.assoc] using (comparisonArrow_target G g g').symm))
    (pullback.lift (comparisonArrow G g g')
      (commonFst G g g' ≫
        firstFst G g) (by
        simpa only [Category.assoc] using comparisonArrow_source G g g'))
    (by rw [pullback.lift_snd, pullback.lift_fst])

/-- The target of `comparisonRestrictionArrow` is the `U''` component. -/
public lemma comparisonRestrictionArrow_target {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' U'' : Over S} (g : U' ⟶ G.objects)
    (g' : U'' ⟶ U') :
    comparisonRestrictionArrow G g g' ≫ restrictionTarget G g =
      commonSnd G g g' ≫ compositeFst G g g' ≫ g' := by
  rw [restrictionTarget]
  unfold restrictionArrows
  simp only [comparisonRestrictionArrow, ← Category.assoc, pullback.lift_fst]

/-- The source of `comparisonRestrictionArrow` is the `U'` component. -/
public lemma comparisonRestrictionArrow_source {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' U'' : Over S} (g : U' ⟶ G.objects)
    (g' : U'' ⟶ U') :
    comparisonRestrictionArrow G g g' ≫ restrictionSource G g =
      commonFst G g g' ≫ firstFst G g := by
  unfold restrictionSource restrictionArrows
  simp only [comparisonRestrictionArrow,
    pullback.lift_snd_assoc, pullback.lift_snd]

/-- The underlying arrow of `comparisonRestrictionArrow` is `comparisonArrow`. -/
public lemma comparisonRestrictionArrow_arrow {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' U'' : Over S} (g : U' ⟶ G.objects)
    (g' : U'' ⟶ U') :
    comparisonRestrictionArrow G g g' ≫ restrictionArrowsToArrows G g =
      comparisonArrow G g g' := by
  unfold restrictionArrowsToArrows restrictionArrows
  simp only [comparisonRestrictionArrow, pullback.lift_fst_assoc, pullback.lift_snd]

/-- The canonical map on arrows of a restriction is compatible with the source maps. -/
public lemma restrictionArrow_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    restrictionArrowsToArrows G g ≫ G.source = restrictionSource G g ≫ g := by
  exact (AlgebraicGeometry.GroupoidScheme.restriction_condition G g).symm

/-- The first component of a lift into a nested fibre product. -/
public lemma nestedPullbackLiftSndFst {S : Scheme.{u}}
    {W A B C D E : Over S} (h : B ⟶ E) (i : C ⟶ E)
    (f : A ⟶ D) (k : pullback h i ⟶ D)
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    (w₁ : b ≫ h = c ≫ i)
    (w₂ : a ≫ f = pullback.lift b c w₁ ≫ k) :
    pullback.lift a (pullback.lift b c w₁) w₂ ≫ pullback.snd f k ≫
      pullback.fst h i = b := by
  rw [← Category.assoc, pullback.lift_snd, pullback.lift_fst]

/-- The second component of a lift into a nested fibre product. -/
public lemma nestedPullbackLiftSndSnd {S : Scheme.{u}}
    {W A B C D E : Over S} (h : B ⟶ E) (i : C ⟶ E)
    (f : A ⟶ D) (k : pullback h i ⟶ D)
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    (w₁ : b ≫ h = c ≫ i)
    (w₂ : a ≫ f = pullback.lift b c w₁ ≫ k) :
    pullback.lift a (pullback.lift b c w₁) w₂ ≫ pullback.snd f k ≫
      pullback.snd h i = c := by
  rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- An arrow of a restriction is determined by its source, its target and its underlying arrow
of the original groupoid. -/
public lemma restrictionArrows_hom_ext {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' W : Over S} (g : U' ⟶ G.objects)
    {a b : W ⟶ restrictionArrows G g}
    (ht : a ≫ restrictionTarget G g = b ≫ restrictionTarget G g)
    (hs : a ≫ restrictionSource G g = b ≫ restrictionSource G g)
    (hr : a ≫ restrictionArrowsToArrows G g = b ≫ restrictionArrowsToArrows G g) :
    a = b := by
  exact AlgebraicGeometry.GroupoidScheme.restriction_hom_ext G g a b hs ht hr

/-- The comparison morphism of the double-restriction diagram. -/
public noncomputable abbrev comparisonMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    commonSourcePairs G g g' ⟶ secondArrowSource G g g' :=
  pullback.lift
    (commonSnd G g g' ≫
      compositeFst G g g')
    (comparisonRestrictionArrow G g g') (by
      simpa only [Category.assoc] using (comparisonRestrictionArrow_target G g g').symm)

/-- **Stacks Project, Tag 04MW.** Restricting a groupoid scheme successively
along `g` and `g'` gives a comparison diagram whose two squares are cartesian;
the comparison arrow is given by composing the second arrow with the inverse of
the first. -/
@[stacks 04MW]
public noncomputable def doubleRestrictionDiagram {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.objects) (g' : U'' ⟶ U') :
    DoubleRestrictionDiagram G g g' := by
  let comparison : commonSourcePairs G g g' ⟶
      pullback g' (restrictionTarget G g) := comparisonMap G g g'
  have comparison_fst :
      comparison ≫ pullback.fst g' (restrictionTarget G g) =
        commonSnd G g g' ≫ compositeFst G g g' := by
    dsimp only [comparison, comparisonMap]
    simp only [pullback.lift_fst]
  have comparison_snd :
      comparison ≫ pullback.snd g' (restrictionTarget G g) =
        comparisonRestrictionArrow G g g' := by
    dsimp only [comparison, comparisonMap]
    simp only [pullback.lift_snd]
  have comparison_source :
      comparison ≫ pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g =
        commonFst G g g' ≫ firstFst G g := by
    rw [← Category.assoc, comparison_snd]
    exact comparisonRestrictionArrow_source G g g'
  have comparison_arrow :
      comparison ≫ pullback.snd g' (restrictionTarget G g) ≫
        restrictionArrowsToArrows G g = comparisonArrow G g g' := by
    calc
      comparison ≫ pullback.snd g' (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g =
        comparisonRestrictionArrow G g g' ≫ restrictionArrowsToArrows G g := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ restrictionArrowsToArrows G g) comparison_snd
      _ = _ := comparisonRestrictionArrow_arrow G g g'
  refine
    { comparison := comparison
      comparison_fst := ?_
      comparison_source := ?_
      comparison_composable := comparisonComposable G g g'
      comparison_arrow := ?_
      left_isPullback := ?_
      right_isPullback :=
        (IsPullback.of_hasPullback
          (firstSourceMap G g) (compositeSourceMap G g g')).flip }
  · exact comparison_fst
  · exact comparison_source
  · exact comparison_arrow
  · let lift : ∀ s : PullbackCone
        (pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g) (firstFst G g),
        s.pt ⟶ commonSourcePairs G g g' := by
      intro s
      let r : s.pt ⟶ G.arrows :=
        s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫
          restrictionArrowsToArrows G g
      let p : s.pt ⟶ G.arrows := s.snd ≫ firstSnd G g
      have hrs : r ≫ G.source = (p ≫ G.inverse) ≫ G.source := by
        calc
          r ≫ G.source =
              s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫
                restrictionSource G g ≫ g := by
                  simp only [r, Category.assoc, restrictionArrow_source]
          _ = s.snd ≫ firstFst G g ≫ g := by
            simpa only [secondSourceMap, Category.assoc] using
              congrArg (fun k => k ≫ g) s.condition
          _ = p ≫ G.target := by
            simpa only [p, Category.assoc] using
              congrArg (fun k => s.snd ≫ k) (first_condition G g)
          _ = (p ≫ G.inverse) ≫ G.source := by
            simp only [Category.assoc, G.source_inverse]
      let q := (G.comp_source_isPullback).lift r (p ≫ G.inverse) hrs
      let r₁ : s.pt ⟶ G.arrows := q ≫ pullback.fst G.source G.target
      have hqcomp : q ≫ G.comp = r :=
        (G.comp_source_isPullback).lift_fst r (p ≫ G.inverse) hrs
      have hqsnd : q ≫ pullback.snd G.source G.target = p ≫ G.inverse :=
        (G.comp_source_isPullback).lift_snd r (p ≫ G.inverse) hrs
      have hrt : r₁ ≫ G.target =
          s.fst ≫ pullback.fst g' (restrictionTarget G g) ≫ g' ≫ g := by
        calc
          r₁ ≫ G.target = r ≫ G.target := by
            calc
              _ = q ≫ G.comp ≫ G.target := by
                simp only [r₁, Category.assoc, G.target_comp]
              _ = _ := by rw [← Category.assoc, hqcomp]
          _ = s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫
              restrictionTarget G g ≫ g := by
                simp only [r, Category.assoc,
                  AlgebraicGeometry.GroupoidScheme.restriction_condition']
          _ = _ := by
            simpa only [Category.assoc] using
              congrArg (fun k => s.fst ≫ k ≫ g)
                (pullback.condition (f := g') (g := restrictionTarget G g)).symm
      let b : s.pt ⟶ compositeArrowSource G g g' :=
        pullback.lift
          (s.fst ≫ pullback.fst g' (restrictionTarget G g)) r₁ hrt.symm
      have hbsource : s.snd ≫ firstSourceMap G g =
          b ≫ compositeSourceMap G g g' := by
        calc
          s.snd ≫ firstSourceMap G g = p ≫ G.source := by rfl
          _ = (p ≫ G.inverse) ≫ G.target := by
            simp only [Category.assoc, G.target_inverse]
          _ = q ≫ pullback.snd G.source G.target ≫ G.target := by
            rw [← Category.assoc, hqsnd]
          _ = r₁ ≫ G.source := by
            simpa only [r₁, Category.assoc] using
              congrArg (fun k => q ≫ k)
                (pullback.condition (f := G.source) (g := G.target)).symm
          _ = b ≫ compositeSourceMap G g g' := by
            simpa only [b, compositeSourceMap, compositeArrowSource,
              Category.assoc] using
              (congrArg (fun k => k ≫ G.source)
                (pullback.lift_snd
                  (s.fst ≫ pullback.fst g' (restrictionTarget G g))
                  r₁ hrt.symm)).symm
      exact pullback.lift s.snd b hbsource
    have facLeft : ∀ s : PullbackCone
        (pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g) (firstFst G g),
        lift s ≫ comparison = s.fst := by
      intro s
      let r : s.pt ⟶ G.arrows :=
        s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫ restrictionArrowsToArrows G g
      let p : s.pt ⟶ G.arrows := s.snd ≫ firstSnd G g
      have hrs : r ≫ G.source = (p ≫ G.inverse) ≫ G.source := by
        calc
          r ≫ G.source = s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫
              restrictionSource G g ≫ g := by
                simp only [r, Category.assoc, restrictionArrow_source]
          _ = s.snd ≫ firstFst G g ≫ g := by
            simpa only [Category.assoc] using congrArg (fun k => k ≫ g) s.condition
          _ = p ≫ G.target := by
            simpa only [p, Category.assoc] using
              congrArg (fun k => s.snd ≫ k) (first_condition G g)
          _ = (p ≫ G.inverse) ≫ G.source := by
            simp only [Category.assoc, G.source_inverse]
      let q := (G.comp_source_isPullback).lift r (p ≫ G.inverse) hrs
      have hqcomp : q ≫ G.comp = r :=
        (G.comp_source_isPullback).lift_fst r (p ≫ G.inverse) hrs
      have hqsnd : q ≫ pullback.snd G.source G.target = p ≫ G.inverse :=
        (G.comp_source_isPullback).lift_snd r (p ≫ G.inverse) hrs
      have hliftfst : lift s ≫ commonFst G g g' = s.snd := by
        simp only [lift, commonFst]
        exact pullback.lift_fst _ _ _
      have hfst : (lift s ≫ comparison) ≫ pullback.fst g' (restrictionTarget G g) =
          s.fst ≫ pullback.fst g' (restrictionTarget G g) := by
        calc
          (lift s ≫ comparison) ≫ pullback.fst g' (restrictionTarget G g) =
              lift s ≫ commonSnd G g g' ≫ compositeFst G g g' := by
                simp only [Category.assoc, comparison_fst]
          _ = s.fst ≫ pullback.fst g' (restrictionTarget G g) := by
            simp only [lift, commonSnd, compositeFst]
            exact nestedPullbackLiftSndFst (g' ≫ g) G.target
              (firstSourceMap G g) (compositeSourceMap G g g')
              s.snd (s.fst ≫ pullback.fst g' (restrictionTarget G g)) _ _ _
      have hBArrow : lift s ≫ commonSnd G g g' ≫ compositeSnd G g g' =
          q ≫ pullback.fst G.source G.target := by
        simp only [lift, commonSnd, compositeSnd]
        exact nestedPullbackLiftSndSnd (g' ≫ g) G.target
          (firstSourceMap G g) (compositeSourceMap G g g')
          s.snd (s.fst ≫ pullback.fst g' (restrictionTarget G g))
          (q ≫ pullback.fst G.source G.target) _ _
      have hAArrow : lift s ≫ commonFst G g g' ≫ firstSnd G g = p := by
        simpa only [p, Category.assoc] using
          congrArg (fun k => k ≫ firstSnd G g) hliftfst
      have hPair :
          lift s ≫ pullback.lift
            (commonSnd G g g' ≫ compositeSnd G g g')
            (commonFst G g g' ≫ firstSnd G g ≫ G.inverse)
            (comparisonComposable G g g') = q := by
        apply pullback.hom_ext
        · simpa only [Category.assoc, pullback.lift_fst] using hBArrow
        · calc
            (lift s ≫ pullback.lift
                (commonSnd G g g' ≫ compositeSnd G g g')
                (commonFst G g g' ≫ firstSnd G g ≫ G.inverse)
                (comparisonComposable G g g')) ≫ pullback.snd G.source G.target =
              p ≫ G.inverse := by
                simpa only [Category.assoc, pullback.lift_snd] using
                  congrArg (fun k => k ≫ G.inverse) hAArrow
            _ = q ≫ pullback.snd G.source G.target := hqsnd.symm
      apply pullback.hom_ext
      · exact hfst
      · apply restrictionArrows_hom_ext G g
        · calc
            ((lift s ≫ comparison) ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionTarget G g =
              ((lift s ≫ comparison) ≫ pullback.fst g' (restrictionTarget G g)) ≫ g' := by
                simpa only [Category.assoc] using
                  congrArg (fun k => (lift s ≫ comparison) ≫ k)
                    (pullback.condition (f := g') (g := restrictionTarget G g)).symm
            _ = (s.fst ≫ pullback.fst g' (restrictionTarget G g)) ≫ g' := by
              rw [hfst]
            _ = (s.fst ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionTarget G g := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => s.fst ≫ k)
                      (pullback.condition (f := g') (g := restrictionTarget G g))
        · calc
            ((lift s ≫ comparison) ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionSource G g =
              (lift s ≫ commonFst G g g') ≫ firstFst G g := by
                simpa only [Category.assoc] using
                  congrArg (fun k => lift s ≫ k) comparison_source
            _ = s.snd ≫ firstFst G g := by rw [hliftfst]
            _ = (s.fst ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionSource G g := by
                  simpa only [Category.assoc] using s.condition.symm
        · calc
            ((lift s ≫ comparison) ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionArrowsToArrows G g = lift s ≫ comparisonArrow G g g' := by
                  simpa only [Category.assoc] using
                    congrArg (fun k => lift s ≫ k) comparison_arrow
            _ = (lift s ≫ pullback.lift
                (commonSnd G g g' ≫ compositeSnd G g g')
                (commonFst G g g' ≫ firstSnd G g ≫ G.inverse)
                (comparisonComposable G g g')) ≫ G.comp := by
                  simp only [comparisonArrow, Stacks.Groupoids.GroupoidScheme.compose,
                    Category.assoc]
            _ = q ≫ G.comp := by rw [hPair]
            _ = r := hqcomp
            _ = (s.fst ≫ pullback.snd g' (restrictionTarget G g)) ≫
                restrictionArrowsToArrows G g := rfl
    have facRight : ∀ s : PullbackCone
        (pullback.snd g' (restrictionTarget G g) ≫ restrictionSource G g) (firstFst G g),
        lift s ≫ commonFst G g g' = s.snd := by
      intro s
      simp only [lift, commonFst]
      exact pullback.lift_fst _ _ _
    refine IsPullback.of_isLimit
      (PullbackCone.IsLimit.mk comparison_source lift facLeft facRight ?_)
    · intro s m hm₁ hm₂
      let pair : commonSourcePairs G g g' ⟶ pullback G.source G.target :=
        pullback.lift
          (commonSnd G g g' ≫ compositeSnd G g g')
          (commonFst G g g' ≫ firstSnd G g ≫ G.inverse)
          (comparisonComposable G g g')
      have hArrowPair : comparisonArrow G g g' = pair ≫ G.comp := rfl
      have hpairComp : (m ≫ pair) ≫ G.comp = (lift s ≫ pair) ≫ G.comp := by
        calc
          (m ≫ pair) ≫ G.comp = m ≫ comparisonArrow G g g' := by
            rw [hArrowPair, Category.assoc]
          _ = (m ≫ comparison) ≫ pullback.snd g' (restrictionTarget G g) ≫
              restrictionArrowsToArrows G g := by
                simpa only [Category.assoc] using
                  congrArg (fun k => m ≫ k) comparison_arrow.symm
          _ = s.fst ≫ pullback.snd g' (restrictionTarget G g) ≫
              restrictionArrowsToArrows G g := by rw [hm₁]
          _ = (lift s ≫ comparison) ≫ pullback.snd g' (restrictionTarget G g) ≫
              restrictionArrowsToArrows G g := by rw [facLeft s]
          _ = lift s ≫ comparisonArrow G g g' := by
                simpa only [Category.assoc] using
                  congrArg (fun k => lift s ≫ k) comparison_arrow
          _ = (lift s ≫ pair) ≫ G.comp := by
            rw [hArrowPair, Category.assoc]
      have hpairSnd0 : pair ≫ pullback.snd G.source G.target =
          commonFst G g g' ≫ firstSnd G g ≫ G.inverse := by
        dsimp only [pair]
        exact pullback.lift_snd _ _ _
      have hpairSnd : (m ≫ pair) ≫ pullback.snd G.source G.target =
          (lift s ≫ pair) ≫ pullback.snd G.source G.target := by
        calc
          (m ≫ pair) ≫ pullback.snd G.source G.target =
              (m ≫ commonFst G g g') ≫ firstSnd G g ≫ G.inverse := by
                simpa only [Category.assoc] using
                  congrArg (fun k => m ≫ k) hpairSnd0
          _ = s.snd ≫ firstSnd G g ≫ G.inverse := by rw [hm₂]
          _ = (lift s ≫ commonFst G g g') ≫ firstSnd G g ≫ G.inverse := by
            rw [facRight s]
          _ = (lift s ≫ pair) ≫ pullback.snd G.source G.target := by
            simpa only [Category.assoc] using
              (congrArg (fun k => lift s ≫ k) hpairSnd0).symm
      have hpair : m ≫ pair = lift s ≫ pair :=
        (G.comp_source_isPullback).hom_ext hpairComp hpairSnd
      have hpairFst0 : pair ≫ pullback.fst G.source G.target =
          commonSnd G g g' ≫ compositeSnd G g g' := by
        dsimp only [pair]
        exact pullback.lift_fst _ _ _
      apply pullback.hom_ext
      · calc
          m ≫ commonFst G g g' = s.snd := hm₂
          _ = lift s ≫ commonFst G g g' := (facRight s).symm
      · apply pullback.hom_ext
        · calc
            (m ≫ commonSnd G g g') ≫ compositeFst G g g' =
              (m ≫ comparison) ≫ pullback.fst g' (restrictionTarget G g) := by
                simpa only [Category.assoc] using
                  congrArg (fun k => m ≫ k) comparison_fst.symm
            _ = s.fst ≫ pullback.fst g' (restrictionTarget G g) := by rw [hm₁]
            _ = (lift s ≫ comparison) ≫ pullback.fst g' (restrictionTarget G g) := by
              rw [facLeft s]
            _ = (lift s ≫ commonSnd G g g') ≫ compositeFst G g g' := by
              simpa only [Category.assoc] using
                congrArg (fun k => lift s ≫ k) comparison_fst
        · calc
            (m ≫ commonSnd G g g') ≫ compositeSnd G g g' =
              (m ≫ pair) ≫ pullback.fst G.source G.target := by
                simpa only [Category.assoc] using
                  (congrArg (fun k => m ≫ k) hpairFst0).symm
            _ = (lift s ≫ pair) ≫ pullback.fst G.source G.target := by rw [hpair]
            _ = (lift s ≫ commonSnd G g g') ≫ compositeSnd G g g' := by
              simpa only [Category.assoc] using
                congrArg (fun k => lift s ≫ k) hpairFst0

end AlgebraicGeometry
