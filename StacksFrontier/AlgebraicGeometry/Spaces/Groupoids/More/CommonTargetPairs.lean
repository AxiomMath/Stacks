module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Diagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentTransition

/-!
# Pairs of arrows with a common target

For a groupoid in algebraic spaces `G` over `B`, with object space `U` and arrow space `R`, the
space `R ×_{t, U, t} R` of pairs of arrows with a common target is canonically isomorphic to the
space `R ×_{s, U, t} R` of composable pairs. The isomorphism is the one sending a pair `(α, β)`
with a common target to the composable pair `(α, α⁻¹ ∘ β)`; it preserves the first arrow and
turns composition into the second arrow of the original pair.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso`: the comparison of the
  space of pairs of arrows with a common target with the space of composable pairs.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.inverseFirstPair`: the morphism `(i, 1)`, which
  inverts the first arrow of a pair with a common target.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsComparison`: the vertical map
  `pr_0 × c ∘ (i, 1)` as it is drawn in the diagram.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso_hom_fst` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso_hom_comp`: the comparison
  preserves the first arrow and sends composition to the second arrow. Together with
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso_inv_fst` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso_inv_snd` these two equations
  determine the comparison, and they are the commutativity of the two upper squares of **Stacks
  0450**.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_source_eq_snd_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.fst_source_eq_snd_target`: the commutativity of
  the two lower squares of **Stacks 0450**, namely `c ≫ s = pr₁ ≫ s` and `pr₀ ≫ s = pr₁ ≫ t`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isPullback_fst_snd_source_target`: the
  lower-left square of **Stacks 0450** for the projections is cartesian. The lower-left
  square for composition is `AlgebraicGeometry.Space.isPullback_comp_source`, on which the
  tags are registered below.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsIso_hom_eq`: the map drawn in
  the diagram is that comparison, hence an isomorphism. With
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsComparison_comp_firstArrow`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.commonTargetPairsComparison_comp_comp` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.id_comp_target`, and with the four statements of
  the two lower left squares above, this is the full diagram of **Stacks 0451**, which is the
  diagram of **Stacks 0450** restated for this chapter: every square commutes, the two top rows
  are isomorphic via the vertical maps given, and the two lower left squares are cartesian.

## Implementation notes

The two equations below specify the comparison without choosing inverses of arrows pointwise:
the space of pairs with a common target and the space of composable pairs are two fibre products
of the *same* cospan `t, t : R ⟶ U`, the first by
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` and the second by
`AlgebraicGeometry.Space.isPullback_fst_comp`, whose two projections are
the first arrow and the composite. So the comparison is the canonical isomorphism of two fibre
products of one cospan, and the two equations are its two projection formulas.

That description is identified with the map `pr_0 × c ∘ (i, 1)` that the diagram actually draws
by `commonTargetPairsIso_hom_eq`: the drawn map has the same two projections, the second of them
being the groupoid identity `α ∘ (α⁻¹ ∘ β) = β`. That identity is proved from associativity, the
left inverse law and the left unit law of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Stabilizer/Composition.lean`, applied to the two
projections of `R ×_{t, U, t} R` as generalized arrows. Without it the drawn map is not known to
be the canonical comparison, and the two squares on the left of the top two rows are not known
to commute.

The two lower-left squares of the diagram of **Stacks 0450** are the two lower squares of
**Stacks 043Z**, and the content of both is a general result: the projections square is
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, which holds for any two morphisms
of algebraic spaces with a common target, and the composition square is
`AlgebraicGeometry.Space.isPullback_comp_source`, whose proof uses the groupoid structure. The
projections square is restated here for the groupoid's own source and target by a one-line
appeal to the first of those; the two commutativities are the commutative squares underlying
the two cartesian squares. The tag is registered on both general results below, recording
where the content lives.

**Stacks 0451** is the same diagram, restated in this chapter, and carries the same three
assertions, so its tag sits on the same declarations rather than on restatements of them. The
four statements of the two lower left squares are the ones specialized to this groupoid, not the
general results at the end of the file, which are about arbitrary fibre products.

## References

* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 0450](https://stacks.math.columbia.edu/tag/0450)
* [Stacks Project, Tag 0451](https://stacks.math.columbia.edu/tag/0451)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **Stacks 0450.** The canonical comparison `(α, β) ↦ (α, α⁻¹ ∘ β)` of the space of pairs of
arrows of a groupoid in algebraic spaces with a common target with the space of composable pairs
of arrows. -/
@[stacks 0450 "the comparison of the two upper rows",
  stacks 0451 "the displayed diagram, through its vertical comparison pr_0 × c ∘ (i,1)"]
noncomputable def commonTargetPairsIso (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS G.target G.target ≅
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).isoIsPullback _ _
    (Space.isPullback_fst_comp G)

/-- **Stacks 0450.** The comparison of pairs with a common target with composable pairs
preserves the first arrow. -/
@[stacks 0450 "commutativity for the first projection"]
theorem commonTargetPairsIso_hom_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    (commonTargetPairsIso G).hom ≫
        (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) =
      ObjectProperty.homMk (pullback.fst G.target.hom G.target.hom) :=
  IsPullback.isoIsPullback_hom_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target)
    (Space.isPullback_fst_comp G)

/-- **Stacks 0450.** Composing the comparison of pairs with a common target with composable pairs
and the composition of the groupoid recovers the second arrow. -/
@[stacks 0450 "commutativity for composition"]
theorem commonTargetPairsIso_hom_comp (G : GroupoidInAlgebraicSpaces C S hS B) :
    (commonTargetPairsIso G).hom ≫ G.comp =
      ObjectProperty.homMk (pullback.snd G.target.hom G.target.hom) :=
  IsPullback.isoIsPullback_hom_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target)
    (Space.isPullback_fst_comp G)

/-- **Stacks 0450.** The inverse comparison, from composable pairs to pairs with a common target,
preserves the first arrow. -/
@[stacks 0450 "the inverse comparison on the first projection"]
theorem commonTargetPairsIso_inv_fst (G : GroupoidInAlgebraicSpaces C S hS B) :
    (commonTargetPairsIso G).inv ≫
        (ObjectProperty.homMk (pullback.fst G.target.hom G.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows) =
      ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :=
  IsPullback.isoIsPullback_inv_fst _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target)
    (Space.isPullback_fst_comp G)

/-- **Stacks 0450.** The inverse comparison, from composable pairs to pairs with a common target,
sends the second arrow to the composite. -/
@[stacks 0450 "the inverse comparison on the second projection"]
theorem commonTargetPairsIso_inv_snd (G : GroupoidInAlgebraicSpaces C S hS B) :
    (commonTargetPairsIso G).inv ≫
        (ObjectProperty.homMk (pullback.snd G.target.hom G.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows) =
      G.comp :=
  IsPullback.isoIsPullback_inv_snd _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target)
    (Space.isPullback_fst_comp G)

/-- **Stacks 0450**, the commutativity of the lower square for composition: `c ≫ s = pr₁ ≫ s`.
The composite of a composable pair of arrows of a groupoid in algebraic spaces has the same
source as the second arrow of the pair. -/
@[stacks 0450 "commutativity of the lower square for composition, c ≫ s = pr₁ ≫ s",
  stacks 0451 "commutativity of the upper of the two lower left squares"]
theorem comp_source_eq_snd_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.comp ≫ G.source =
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) ≫ G.source :=
  (Space.isPullback_comp_source G).w

/-- **Stacks 0450**, the commutativity of the lower square for the projections:
`pr₀ ≫ s = pr₁ ≫ t`. The first arrow of a composable pair of arrows of a groupoid in algebraic
spaces has as its source the target of the second arrow of the pair. -/
@[stacks 0450 "commutativity of the lower square for the projections, pr₀ ≫ s = pr₁ ≫ t",
  stacks 0451 "commutativity of the lower of the two lower left squares"]
theorem fst_source_eq_snd_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) ≫ G.source =
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) ≫ G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).w

/-- **Stacks 0450**, the lower-left square for the projections. The two projections out of the
space of composable pairs of arrows of a groupoid in algebraic spaces form a cartesian square
with the source and the target morphisms: a composable pair is exactly a pair of arrows whose
first arrow has as its source the target of the second. -/
@[stacks 0450 "the lower-left square for the projections is cartesian",
  stacks 0451 "the lower of the two lower left squares is cartesian",
  stacks 04P9 "the lower-left square"]
theorem isPullback_fst_snd_source_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
      G.source G.target :=
  AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target

/-- The first projection `pr_0 : R ×_{t, U, t} R ⟶ R` out of the space of pairs of arrows with a
common target. -/
noncomputable abbrev commonTargetFirstArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.fst G.target.hom G.target.hom)

/-- The second projection `pr_1 : R ×_{t, U, t} R ⟶ R` out of the space of pairs of arrows with
a common target. -/
noncomputable abbrev commonTargetSecondArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶ G.arrows :=
  ObjectProperty.homMk (pullback.snd G.target.hom G.target.hom)

/-- The two arrows of a pair with a common target have, as the name says, the same target. -/
theorem commonTargetFirstArrow_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    commonTargetFirstArrow G ≫ G.target = commonTargetSecondArrow G ≫ G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.target G.target).w

/-- The morphism `(i, 1) : R ×_{t, U, t} R ⟶ R ×_{s, U, t} R` of the diagram of **Stacks 0451**:
inverting the first arrow of a pair with a common target makes the pair composable. -/
noncomputable def inverseFirstPair (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (commonTargetFirstArrow G ≫ inverseArrow G) (commonTargetSecondArrow G) <| by
      rw [Category.assoc, inverseArrow_comp_source]
      exact commonTargetFirstArrow_comp_target G

/-- The first arrow of the composable pair `(i, 1)` produces is the inverse of the first arrow
of the original pair. -/
@[simp]
theorem inverseFirstPair_comp_firstArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    inverseFirstPair G ≫ firstArrow G = commonTargetFirstArrow G ≫ inverseArrow G :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _

/-- The second arrow of the composable pair `(i, 1)` produces is the second arrow of the
original pair. -/
@[simp]
theorem inverseFirstPair_comp_secondArrow (G : GroupoidInAlgebraicSpaces C S hS B) :
    inverseFirstPair G ≫ secondArrow G = commonTargetSecondArrow G :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _

/-- **Stacks 0451.** The vertical comparison `pr_0 × c ∘ (i, 1)` of the diagram: it sends a pair
`(α, β)` of arrows with a common target to the composable pair `(α, α⁻¹ ∘ β)`. -/
@[stacks 0451 "the vertical comparison pr_0 × c ∘ (i, 1)"]
noncomputable def commonTargetPairsComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    AlgebraicSpaces.fiberProduct C S hS G.target G.target ⟶
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (commonTargetFirstArrow G) (inverseFirstPair G ≫ G.comp) <| by
      calc commonTargetFirstArrow G ≫ G.source
          = commonTargetFirstArrow G ≫ inverseArrow G ≫ G.target := by
            rw [inverseArrow_comp_target]
        _ = (inverseFirstPair G ≫ firstArrow G) ≫ G.target := by
            rw [inverseFirstPair_comp_firstArrow, Category.assoc]
        _ = (inverseFirstPair G ≫ G.comp) ≫ G.target := by
            rw [Category.assoc, Category.assoc, comp_comp_target]

/-- **Stacks 0451**, the lower of the two squares on the left of the top two rows: the vertical
comparison preserves the first arrow. -/
@[stacks 0451 "the lower square on the left of the top two rows"]
theorem commonTargetPairsComparison_comp_firstArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    commonTargetPairsComparison G ≫ firstArrow G = commonTargetFirstArrow G :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _

/-- The second arrow of the composable pair produced by the vertical comparison is the
composite `α⁻¹ ∘ β` of the inverted first arrow with the second. -/
@[simp]
theorem commonTargetPairsComparison_comp_secondArrow
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    commonTargetPairsComparison G ≫ secondArrow G = inverseFirstPair G ≫ G.comp :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _

/-- A morphism into the space of composable pairs of arrows, followed by the composition of the
groupoid, is the composite of its two components read as generalized arrows. -/
private theorem comp_hom_eq_groupoidCompose (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (k : T ⟶ (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj) (a b : T ⟶ G.arrows.obj)
    (ha : k ≫ pullback.fst G.source.hom G.target.hom = a)
    (hb : k ≫ pullback.snd G.source.hom G.target.hom = b)
    (w : a ≫ G.source.hom = b ≫ G.target.hom) :
    k ≫ G.comp.hom = groupoidCompose G a b w := by
  subst ha hb
  exact congrArg (fun z => z ≫ G.comp.hom)
    (pullback.hom_ext (pullback.lift_fst _ _ _).symm (pullback.lift_snd _ _ _).symm)

/-- In a groupoid in algebraic spaces, an arrow composed after the composite of its inverse with
a second arrow having the same target is that second arrow: `α ∘ (α⁻¹ ∘ β) = β`. -/
private theorem groupoidCompose_inverse_cancel (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.arrows.obj)
    (hab : a ≫ G.target.hom = b ≫ G.target.hom)
    (wbc : (a ≫ groupoidInverse G) ≫ G.source.hom = b ≫ G.target.hom)
    (wR : a ≫ G.source.hom =
      groupoidCompose G (a ≫ groupoidInverse G) b wbc ≫ G.target.hom) :
    groupoidCompose G a (groupoidCompose G (a ≫ groupoidInverse G) b wbc) wR = b := by
  have wab : a ≫ G.source.hom = (a ≫ groupoidInverse G) ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_target]
  have wL : groupoidCompose G a (a ≫ groupoidInverse G) wab ≫ G.source.hom =
      b ≫ G.target.hom := by
    rw [groupoidCompose_source]; exact wbc
  have hid : groupoidCompose G a (a ≫ groupoidInverse G) wab = identityAfterTarget G b :=
    (groupoidCompose_inverseLeft G a).trans <| by
      simp only [identityAfterTarget, ← Category.assoc, hab]
  calc groupoidCompose G a (groupoidCompose G (a ≫ groupoidInverse G) b wbc) wR
      = groupoidCompose G (groupoidCompose G a (a ≫ groupoidInverse G) wab) b wL :=
        (groupoidCompose_assoc G a (a ≫ groupoidInverse G) b wab wbc wL wR).symm
    _ = groupoidCompose G (identityAfterTarget G b) b
          (identityAfterTarget_composable G b) :=
        groupoidCompose_congr G wL (identityAfterTarget_composable G b) hid rfl
    _ = b := groupoidCompose_leftIdentity G b

/-- **Stacks 0451**, the upper of the two squares on the left of the top two rows: composing the
vertical comparison with the composition of the groupoid recovers the second arrow, because
`α ∘ (α⁻¹ ∘ β) = β`. -/
@[stacks 0451 "the upper square on the left of the top two rows"]
theorem commonTargetPairsComparison_comp_comp (G : GroupoidInAlgebraicSpaces C S hS B) :
    commonTargetPairsComparison G ≫ G.comp = commonTargetSecondArrow G := by
  apply ObjectProperty.hom_ext
  have hab : pullback.fst G.target.hom G.target.hom ≫ G.target.hom =
      pullback.snd G.target.hom G.target.hom ≫ G.target.hom := pullback.condition
  have wbc : (pullback.fst G.target.hom G.target.hom ≫ groupoidInverse G) ≫ G.source.hom =
      pullback.snd G.target.hom G.target.hom ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]; exact hab
  have wR : pullback.fst G.target.hom G.target.hom ≫ G.source.hom =
      groupoidCompose G (pullback.fst G.target.hom G.target.hom ≫ groupoidInverse G)
        (pullback.snd G.target.hom G.target.hom) wbc ≫ G.target.hom := by
    rw [groupoidCompose_target, Category.assoc, groupoidInverse_target]
  have hifst : (inverseFirstPair G).hom ≫ pullback.fst G.source.hom G.target.hom =
      pullback.fst G.target.hom G.target.hom ≫ groupoidInverse G :=
    congrArg (·.hom) (inverseFirstPair_comp_firstArrow G)
  have hisnd : (inverseFirstPair G).hom ≫ pullback.snd G.source.hom G.target.hom =
      pullback.snd G.target.hom G.target.hom :=
    congrArg (·.hom) (inverseFirstPair_comp_secondArrow G)
  have hcfst : (commonTargetPairsComparison G).hom ≫
      pullback.fst G.source.hom G.target.hom = pullback.fst G.target.hom G.target.hom :=
    congrArg (·.hom) (commonTargetPairsComparison_comp_firstArrow G)
  have hcsnd : (commonTargetPairsComparison G).hom ≫
      pullback.snd G.source.hom G.target.hom = (inverseFirstPair G).hom ≫ G.comp.hom :=
    congrArg (·.hom) (commonTargetPairsComparison_comp_secondArrow G)
  have hY := comp_hom_eq_groupoidCompose G (inverseFirstPair G).hom _ _ hifst hisnd wbc
  exact (comp_hom_eq_groupoidCompose G (commonTargetPairsComparison G).hom _ _ hcfst
    (hcsnd.trans hY) wR).trans (groupoidCompose_inverse_cancel G _ _ hab wbc wR)

/-- **Stacks 0451.** The vertical comparison drawn in the diagram, `pr_0 × c ∘ (i, 1)`, is the
canonical comparison of the two fibre products, hence an isomorphism: this is the assertion that
the two top rows of the diagram are isomorphic via the vertical maps given, the other two
vertical maps being the identities. -/
@[stacks 0451 "the two top rows are isomorphic via the vertical maps given"]
theorem commonTargetPairsIso_hom_eq (G : GroupoidInAlgebraicSpaces C S hS B) :
    (commonTargetPairsIso G).hom = commonTargetPairsComparison G :=
  (Space.isPullback_fst_comp G).hom_ext
    ((commonTargetPairsIso_hom_fst G).trans
      (commonTargetPairsComparison_comp_firstArrow G).symm)
    ((commonTargetPairsIso_hom_comp G).trans
      (commonTargetPairsComparison_comp_comp G).symm)

/-- The vertical comparison of the diagram of **Stacks 0451** is an isomorphism. -/
instance isIso_commonTargetPairsComparison (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsIso (commonTargetPairsComparison G) := by
  rw [← commonTargetPairsIso_hom_eq]
  infer_instance

/-- **Stacks 0451**, the square on the right of the top two rows: both of its vertical maps are
identities, of the arrow space and of the object space, and its two horizontal maps are the
target. -/
@[stacks 0451 "the square on the right of the top two rows"]
theorem id_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    𝟙 G.arrows ≫ G.target = G.target ≫ 𝟙 G.objects := by
  rw [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

add_to_stacks 0450 "the lower-left square for the projections"
  AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct

add_to_stacks 0450 "the lower-left square for composition"
  AlgebraicGeometry.Space.isPullback_comp_source

-- The upper of the two lower left squares of the diagram of Stacks 0451 is the lower-left
-- square for composition of Stacks 0450, so it is the same general result, registered here for
-- this chapter's tag as well.  Its cartesianness is not restated: a composable pair is
-- determined by its second arrow together with its composite, which is Stacks 043Z.
add_to_stacks 0451 "the upper of the two lower left squares is cartesian"
  AlgebraicGeometry.Space.isPullback_comp_source

end
