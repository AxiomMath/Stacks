module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations

/-!
# Groupoid schemes and equivalence relations

The target and source maps of a groupoid scheme determine a morphism from its scheme of arrows
to the product of its scheme of objects with itself, and that pre-relation is a pre-equivalence
relation.  Conversely an equivalence relation on a scheme over a base scheme has a unique
extension to a groupoid scheme: reflexivity gives identity arrows, symmetry gives inverses and
transitivity gives composition.

## Main definitions

* `AlgebraicGeometry.groupoidPreRelation` is the pre-relation given by the target and source
  maps of a groupoid scheme.
* `AlgebraicGeometry.ExtendsRelation` records that a groupoid scheme has the prescribed schemes
  of objects and arrows and the prescribed source and target maps.
* `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation` is the canonical groupoid scheme
  extending an equivalence relation.

## Main results

* `AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation` states that the pre-relation
  of a groupoid scheme is a pre-equivalence relation.
* `AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation` states that an
  equivalence relation extends uniquely to a groupoid scheme.
* `AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_extendsRelation` identifies the
  canonical groupoid scheme with the given relation.

## Implementation notes

The source denotes the morphism to the product by `j`; the order `(target, source)` agrees with
the convention for pre-relations of Tag 022P.

The fields of `ExtendsRelation` allow the schemes of objects and arrows in the bundled groupoid
scheme to be propositionally, rather than only definitionally, the schemes appearing in the
relation; the source and target maps are compared after transport along these equalities.  Its
field projections give the object, arrow, source and target identification API for the
canonical construction.  Thus uniqueness includes composition, identity, inverse and all the
groupoid laws, while retaining the bundled groupoid interface of Tag 0231.

## References

* [Stacks Project, Tag 0232](https://stacks.math.columbia.edu/tag/0232)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry

universe u

/-- The pre-relation on the objects of a groupoid scheme defined by its target and source
maps. -/
noncomputable abbrev groupoidPreRelation {S : Scheme.{u}} (G : GroupoidScheme S) :
    PreRelation G.arrows G.objects :=
  prod.lift G.target G.source

/-- The pre-relation underlying a groupoid scheme is a pre-equivalence relation. -/
@[stacks 0232]
theorem groupoidPreRelation_isPreEquivalenceRelation {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPreEquivalenceRelation (groupoidPreRelation G) := by
  intro T
  suffices h : Equivalence (fun x y : T ⟶ G.objects =>
      ∃ r : T ⟶ G.arrows, r ≫ G.target = x ∧ r ≫ G.source = y) by
    convert h using 1
    funext x y
    simp [PreRelation.Rel, PreRelation.target, PreRelation.source, groupoidPreRelation]
  constructor
  · intro x
    exact ⟨x ≫ G.identity, by simp [Category.assoc, G.target_identity],
      by simp [Category.assoc, G.source_identity]⟩
  · rintro x y ⟨r, hrx, hry⟩
    exact ⟨r ≫ G.inverse, by simpa [Category.assoc, G.target_inverse] using hry,
      by simpa [Category.assoc, G.source_inverse] using hrx⟩
  · rintro x y z ⟨r, hrx, hry⟩ ⟨q, hqy, hqz⟩
    exact ⟨G.compose r q (by rw [hry, hqy]),
      by simpa [GroupoidScheme.compose, Category.assoc, pullback.lift_fst_assoc,
        G.target_comp] using hrx,
      by simpa [GroupoidScheme.compose, Category.assoc, pullback.lift_snd_assoc,
        G.source_comp] using hqz⟩

variable {S : Scheme.{u}} {R U : Over S}

/-- A groupoid scheme extends a pre-relation when its schemes of objects and arrows are the
ones in the relation and its source and target maps are the two projections of the relation. -/
structure ExtendsRelation (j : PreRelation R U) (G : GroupoidScheme S) : Prop where
  objects_eq : G.objects = U
  arrows_eq : G.arrows = R
  source_eq : eqToHom arrows_eq.symm ≫ G.source ≫ eqToHom objects_eq = j.source
  target_eq : eqToHom arrows_eq.symm ≫ G.target ≫ eqToHom objects_eq = j.target

/-- The groupoid scheme built from a chosen witness that a pre-relation is an equivalence
relation: composition is transitivity, the identity is reflexivity and the inverse is
symmetry. -/
private noncomputable def groupoidScheme (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] : GroupoidScheme S := by
  let e : EquivalenceRelation j.target j.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  let k : pullback j.source j.target ⟶ e.c.pt :=
    PullbackCone.IsLimit.lift e.isLimit (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition
  let m : pullback j.source j.target ⟶ R := k ≫ e.t
  refine
    { objects := U
      arrows := R
      source := j.source
      target := j.target
      comp := m
      identity := e.r
      inverse := e.s
      source_identity := e.reflexivity₂
      target_identity := e.reflexivity₁
      source_inverse := e.symmetry₂
      target_inverse := e.symmetry₁
      source_comp := by simp [m, k, Category.assoc, e.transitivity₂]
      target_comp := by simp [m, k, Category.assoc, e.transitivity₁]
      left_identity := ?_
      right_identity := ?_
      left_inverse := ?_
      right_inverse := ?_
      assoc := ?_ }
  all_goals
    intros
    dsimp [m, k] at *
    apply e.right_cancellation <;>
      simp only [Category.assoc, e.transitivity₁, e.transitivity₂,
        PullbackCone.IsLimit.lift_fst_assoc, PullbackCone.IsLimit.lift_snd_assoc,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, e.reflexivity₁, e.reflexivity₂,
        e.symmetry₁, e.symmetry₂, Category.comp_id]

/-- An equivalence relation on a scheme over `S` extends in a unique way to a groupoid scheme
over `S`. -/
@[stacks 0233]
theorem existsUnique_groupoidScheme_of_isEquivalenceRelation (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] :
    ∃! G : GroupoidScheme S, ExtendsRelation j G := by
  refine ⟨groupoidScheme j, ?_, ?_⟩
  · dsimp [groupoidScheme]
    exact ⟨rfl, rfl, rfl, rfl⟩
  intro G hG
  rcases hG with ⟨hobjects, harrows, hsource, htarget⟩
  rcases G with ⟨objects, arrows, source, target, comp, identity, inverse,
    source_identity, target_identity, source_inverse, target_inverse,
    source_comp, target_comp, left_identity, right_identity, left_inverse,
    right_inverse, assoc⟩
  dsimp only at hobjects harrows
  subst objects arrows
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsource htarget
  cases htarget
  cases hsource
  let e : EquivalenceRelation j.target j.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  let k : pullback j.source j.target ⟶ e.c.pt :=
    PullbackCone.IsLimit.lift e.isLimit (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition
  obtain rfl : comp = k ≫ e.t := by
    apply e.right_cancellation
    · rw [target_comp]
      dsimp [k]
      simp only [Category.assoc, e.transitivity₁, PullbackCone.IsLimit.lift_fst_assoc]
    · rw [source_comp]
      dsimp [k]
      simp only [Category.assoc, e.transitivity₂, PullbackCone.IsLimit.lift_snd_assoc]
  obtain rfl : identity = e.r :=
    e.right_cancellation identity e.r (target_identity.trans e.reflexivity₁.symm)
      (source_identity.trans e.reflexivity₂.symm)
  obtain rfl : inverse = e.s :=
    e.right_cancellation inverse e.s (target_inverse.trans e.symmetry₁.symm)
      (source_inverse.trans e.symmetry₂.symm)
  rfl

/-- The canonical groupoid scheme extending an equivalence relation. -/
noncomputable def groupoidSchemeOfIsEquivalenceRelation (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] : GroupoidScheme S :=
  Classical.choose (existsUnique_groupoidScheme_of_isEquivalenceRelation j).exists

/-- The canonical groupoid scheme has the prescribed objects, arrows, source, and target.
The four identifications are available as the field projections of this result. -/
theorem groupoidSchemeOfIsEquivalenceRelation_extendsRelation (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] :
    ExtendsRelation j (groupoidSchemeOfIsEquivalenceRelation j) :=
  Exists.choose_spec (existsUnique_groupoidScheme_of_isEquivalenceRelation j).exists

end AlgebraicGeometry

end
