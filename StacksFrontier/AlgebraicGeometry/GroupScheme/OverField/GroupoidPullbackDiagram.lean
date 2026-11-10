module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation

/-!
# The pullback diagram of a groupoid scheme

For a groupoid scheme, a pair of arrows with the same target can be changed into a composable
pair by sending `(α, β)` to `(α, α⁻¹ ∘ β)`.  This change of coordinates is an isomorphism, and
it fits into the standard commutative diagram whose two lower squares are cartesian.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.inverseCompSnd` composes the inverse of the first arrow of
  a pair with equal targets with its second arrow.
* `AlgebraicGeometry.GroupoidScheme.targetPullbackToComposable` is the change-of-coordinates
  morphism from pairs with equal target to composable pairs.

## Main results

* `AlgebraicGeometry.GroupoidScheme.targetPullbackToComposable_fst` and
  `AlgebraicGeometry.GroupoidScheme.targetPullbackToComposable_comp` give the two commutative
  triangles in the top left of the diagram.
* `AlgebraicGeometry.GroupoidScheme.id_target_comm` gives the commutativity of the upper right
  square, whose vertical maps are identities.
* `AlgebraicGeometry.GroupoidScheme.targetPullbackToComposable_isIso` says that the two top
  rows are isomorphic through the displayed vertical maps.
* `AlgebraicGeometry.GroupoidScheme.fst_source_isPullback` and
  `Stacks.Groupoids.GroupoidScheme.comp_source_isPullback` give the two lower cartesian
  squares.
* `AlgebraicGeometry.GroupoidScheme.diagram_pull` collects all of this into the single
  statement that the displayed diagram is commutative, that its two top rows are isomorphic
  through the displayed vertical maps, and that its two lower left squares are cartesian.

## Implementation notes

The schemes and their structure maps are regarded as objects and morphisms in `Over S`.  The
lower projection square is the chosen pullback square for `source` and `target`, so
`fst_source_isPullback` is immediate.  The other lower square is exactly
`Stacks.Groupoids.GroupoidScheme.comp_source_isPullback`, with horizontal maps `comp` and
`source` and vertical maps the second projection and `source` respectively.  Together with the
two computation lemmas for the comparison map and the commutativity of the upper right square,
these declarations express all commutativity and cartesianness assertions in the source.

The displayed diagram has five squares.  Between the two top rows there are three: the two on
the left, one for each of the two parallel arrows, given by the two computation lemmas for the
comparison map, and the right-hand one, given by `id_target_comm`.  Between the two bottom rows
there are the two lower left squares, again one for each of the two parallel arrows; these are
the cartesian ones, and their commutativity comes with their cartesianness.

## References

* [Stacks Project, Tag 03C6](https://stacks.math.columbia.edu/tag/03C6)
* [Stacks Project, Tag 04LG](https://stacks.math.columbia.edu/tag/04LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.GroupoidScheme

universe u

/-- For two arrows with the same target, form the composite of the inverse of the first
arrow with the second arrow. -/
@[implicit_reducible]
noncomputable def inverseCompSnd {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    pullback G.target G.target ⟶ G.arrows :=
  pullback.lift (pullback.fst G.target G.target ≫ G.inverse)
      (pullback.snd G.target G.target)
      (by simp only [Category.assoc, G.source_inverse, pullback.condition]) ≫
    G.comp

/-- The vertical map in the top left of the diagram: it sends a pair `(α, β)` with equal
targets to the composable pair `(α, α⁻¹ ∘ β)`. -/
@[stacks 03C6 "the vertical comparison",
  implicit_reducible,
  stacks 04LG "the vertical map `(pr₀, c ∘ (i, 1))` of the displayed diagram"]
noncomputable def targetPullbackToComposable {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) :
    pullback G.target G.target ⟶ pullback G.source G.target :=
  pullback.lift (pullback.fst G.target G.target) (inverseCompSnd G)
    (by
      simp only [inverseCompSnd, Category.assoc, G.target_comp,
        pullback.lift_fst_assoc, G.target_inverse])

add_to_stacks 04LG "cartesianness: the upper of the two lower left squares, the one taken \
with the composition on top and the source along the bottom"
  Stacks.Groupoids.GroupoidScheme.comp_source_isPullback

/-- The square formed by the two projections of the scheme of composable pairs together with
the source and the target maps is a pullback square.  This is the lower-left square of the
diagram taken with the lower horizontal maps, and it is cartesian because the scheme of
composable pairs is by definition the fibre product of the source and the target. -/
@[stacks 03C6 "the lower projection square",
  stacks 04LG "cartesianness: the lower of the two lower left squares, the one taken with \
the first projection on top and the target along the bottom"]
theorem fst_source_isPullback {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    IsPullback (pullback.fst G.source G.target) (pullback.snd G.source G.target)
      G.source G.target :=
  IsPullback.of_hasPullback _ _

/-- The upper-right square of the diagram commutes.  Both of its vertical maps are
identities, of the arrow scheme and of the object scheme respectively, and both of its
horizontal maps are the target map. -/
@[stacks 03C6 "commutativity of the upper right square",
  stacks 04LG "commutativity: the right-hand square between the two top rows, whose vertical \
maps are the identities"]
theorem id_target_comm {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    𝟙 G.arrows ≫ G.target = G.target ≫ 𝟙 G.objects := by
  rw [Category.id_comp, Category.comp_id]

/-- The comparison map preserves the first projection.  This is the lower of the two
commutative triangles in the top left of the diagram. -/
@[stacks 03C6 "commutativity with the first projection",
  stacks 04LG "commutativity: the left square between the two top rows taken with the first \
projections"]
theorem targetPullbackToComposable_fst {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) :
    targetPullbackToComposable G ≫ pullback.fst G.source G.target =
      pullback.fst G.target G.target :=
  pullback.lift_fst _ _ _

/-- Composing `x` with `b` is `b` when `x` is the identity over the target of `b`. -/
private theorem lift_comp_eq_of_eq_target_identity {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) {T : Over S} (x b : T ⟶ G.arrows)
    (w : x ≫ G.source = b ≫ G.target) (hx : x = b ≫ G.target ≫ G.identity) :
    pullback.lift x b w ≫ G.comp = b := by
  subst hx
  exact G.left_identity T b w

/-- Composing a pair after the change of coordinates recovers its second member.  This is
the upper of the two commutative triangles in the top left of the diagram. -/
@[stacks 03C6 "commutativity with composition",
  stacks 04LG "commutativity: the left square between the two top rows taken with the second \
projection on top and the composition along the bottom"]
theorem targetPullbackToComposable_comp {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) :
    targetPullbackToComposable G ≫ G.comp = pullback.snd G.target G.target := by
  simp only [targetPullbackToComposable, inverseCompSnd]
  let P := pullback G.target G.target
  let a : P ⟶ G.arrows := pullback.fst G.target G.target
  let b : P ⟶ G.arrows := pullback.snd G.target G.target
  have wab : a ≫ G.target = b ≫ G.target := pullback.condition
  have wainv : a ≫ G.source = (a ≫ G.inverse) ≫ G.target := by
    simp only [Category.assoc, G.target_inverse]
  have winvb : (a ≫ G.inverse) ≫ G.source = b ≫ G.target := by
    simpa only [Category.assoc, G.source_inverse] using wab
  have wleft :
      (pullback.lift a (a ≫ G.inverse) wainv ≫ G.comp) ≫ G.source = b ≫ G.target := by
    simpa only [Category.assoc, G.source_comp, pullback.lift_snd_assoc,
      G.source_inverse] using wab
  have wright :
      a ≫ G.source = (pullback.lift (a ≫ G.inverse) b winvb ≫ G.comp) ≫ G.target := by
    simp only [Category.assoc, G.target_comp, pullback.lift_fst_assoc, G.target_inverse]
  rw [← G.assoc P a (a ≫ G.inverse) b wainv winvb wleft wright]
  exact lift_comp_eq_of_eq_target_identity G _ b _
    ((G.right_inverse P a wainv).trans (by rw [← Category.assoc, wab, Category.assoc]))

/-- Composing a composable pair and then changing coordinates back recovers its second
member. -/
private theorem inverse_comp_comp {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    pullback.lift (pullback.fst G.source G.target) G.comp
          (by simp only [G.target_comp]) ≫
        inverseCompSnd G =
      pullback.snd G.source G.target := by
  let P := pullback G.source G.target
  let a : P ⟶ G.arrows := pullback.fst G.source G.target
  let b : P ⟶ G.arrows := pullback.snd G.source G.target
  have wab : a ≫ G.source = b ≫ G.target := pullback.condition
  have winv : (a ≫ G.inverse) ≫ G.source = a ≫ G.target := by
    simp only [Category.assoc, G.source_inverse]
  have wleft :
      (pullback.lift (a ≫ G.inverse) a winv ≫ G.comp) ≫ G.source = b ≫ G.target := by
    simpa only [Category.assoc, G.source_comp, pullback.lift_snd_assoc] using wab
  have wright :
      (a ≫ G.inverse) ≫ G.source = (pullback.lift a b wab ≫ G.comp) ≫ G.target := by
    simp only [Category.assoc, G.source_inverse, G.target_comp, pullback.lift_fst_assoc]
  have hab : pullback.lift a b wab = 𝟙 P := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.id_comp]
      rfl
    · simp only [pullback.lift_snd, Category.id_comp]
      rfl
  have hlift :
      pullback.lift a G.comp (by exact G.target_comp.symm) ≫
          pullback.lift (pullback.fst G.target G.target ≫ G.inverse)
            (pullback.snd G.target G.target)
            (by simp only [Category.assoc, G.source_inverse, pullback.condition]) =
        pullback.lift (a ≫ G.inverse) (pullback.lift a b wab ≫ G.comp) wright := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd]
      exact (congrArg (· ≫ G.comp) hab).symm
  simp only [inverseCompSnd]
  change (pullback.lift a G.comp _ ≫
      pullback.lift (pullback.fst G.target G.target ≫ G.inverse)
        (pullback.snd G.target G.target) _) ≫ G.comp = b
  rw [hlift]
  rw [← G.assoc P (a ≫ G.inverse) a b winv wab wleft wright]
  exact lift_comp_eq_of_eq_target_identity G _ b _
    ((G.left_inverse P a winv).trans (by rw [← Category.assoc, wab, Category.assoc]))

/-- The vertical comparison between pairs with the same target and composable pairs is an
isomorphism. -/
@[stacks 03C6 "the top rows are isomorphic",
  stacks 04LG "the two top rows are isomorphic via the vertical maps given"]
theorem targetPullbackToComposable_isIso {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) :
    IsIso (targetPullbackToComposable G) := by
  let inv : pullback G.source G.target ⟶ pullback G.target G.target :=
    pullback.lift (pullback.fst G.source G.target) G.comp
      (by simp only [G.target_comp])
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · dsimp only [inv]
      simpa only [Category.id_comp, Category.assoc, pullback.lift_fst] using
        targetPullbackToComposable_fst G
    · dsimp only [inv]
      simpa only [Category.id_comp, Category.assoc, pullback.lift_snd] using
        targetPullbackToComposable_comp G
  · apply pullback.hom_ext
    · dsimp only [inv]
      simp only [Category.id_comp, Category.assoc, targetPullbackToComposable_fst,
        pullback.lift_fst]
    · dsimp only [inv]
      rw [Category.id_comp, Category.assoc]
      rw [show targetPullbackToComposable G ≫ pullback.snd G.source G.target =
        inverseCompSnd G from pullback.lift_snd _ _ _]
      exact inverse_comp_comp G

/-- Every assertion made about the displayed diagram, in one statement.

Each square is written as `left ≫ bottom = top ≫ right`, so that the vertical maps which are
identities are displayed rather than suppressed.  The first three conjuncts are the
commutativity of the three squares between the two top rows: the two on the left, one for each
of the two parallel arrows, and the right-hand one whose vertical maps are the identity of the
arrow scheme and the identity of the object scheme.  Together with the fourth conjunct, which
says that the remaining vertical map is an isomorphism, they say that the two top rows are
isomorphic through the vertical maps given.  The last two conjuncts say that the two lower left
squares, again one for each of the two parallel arrows, are cartesian; the commutativity of
those two squares is part of the same assertions. -/
@[stacks 04LG "the whole diagram: it is commutative, its two top rows are isomorphic via the \
vertical maps given, and its two lower left squares are cartesian"]
theorem diagram_pull {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) :
    targetPullbackToComposable G ≫ G.comp =
          pullback.snd G.target G.target ≫ 𝟙 G.arrows ∧
      targetPullbackToComposable G ≫ pullback.fst G.source G.target =
          pullback.fst G.target G.target ≫ 𝟙 G.arrows ∧
      𝟙 G.arrows ≫ G.target = G.target ≫ 𝟙 G.objects ∧
      IsIso (targetPullbackToComposable G) ∧
      IsPullback G.comp (pullback.snd G.source G.target) G.source G.source ∧
      IsPullback (pullback.fst G.source G.target) (pullback.snd G.source G.target)
        G.source G.target :=
  ⟨by rw [Category.comp_id]; exact targetPullbackToComposable_comp G,
    by rw [Category.comp_id]; exact targetPullbackToComposable_fst G,
    id_target_comm G,
    targetPullbackToComposable_isIso G,
    G.comp_source_isPullback,
    fst_source_isPullback G⟩

end AlgebraicGeometry.GroupoidScheme

end
