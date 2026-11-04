module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.InvarianceSquare

/-!
# The criterion for a morphism to be an orbit space

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, let
`j : R ⟶ U ×_Z U` be a set-theoretic pre-equivalence relation, and let `φ : U ⟶ X` be a
morphism over `Z` whose target is an algebraic space. Then `φ` is an orbit space for `j` in
the sense of **Stacks 0493** exactly when the three conditions of **Stacks 049Z** hold:

1. `φ` is invariant, that is `t ≫ φ = s ≫ φ`;
2. the induced morphism `(t, s) : R ⟶ U ×_X U` is surjective;
3. `φ` itself is surjective.

The second condition only makes sense once the first one holds — the morphism `(t, s)` is
built from a proof of invariance — so the conjunction is written as an existential over that
proof, which is how the other quotient conditions of this chapter are spelled (see
`AlgebraicGeometry.Space.IsGoodQuotient` and
`AlgebraicGeometry.Space.IsGeometricQuotient`). A variant with invariance assumed is provided
for the common case where it is already known.

## Main results

* `AlgebraicGeometry.Space.isOrbitSpace_iff_isSurjective_toSelfFibreProduct`: **Stacks
  049Z**, both directions and all three conditions.
* `AlgebraicGeometry.Space.isOrbitSpace_iff_of_isInvariant`: the same criterion with
  invariance taken as a hypothesis, so that the two remaining conditions are a plain
  conjunction.
* `AlgebraicGeometry.Space.isOrbitSpace_iff_of_isPreEquivalenceRelation`,
  `AlgebraicGeometry.Space.isOrbitSpace_iff_groupoidPreRelation` and
  `AlgebraicGeometry.Space.isOrbitSpace_iff_groupoidOfAction`: the three cases the source
  singles out as examples of the hypothesis — a pre-equivalence relation, the pre-relation of
  a groupoid in algebraic spaces over `B`, and the pre-relation of an action of a group
  algebraic space over `B` on `U`.

## Implementation notes

The whole content is **Stacks 049Y**, part (4), which is
`AlgebraicGeometry.Space.separatesOrbits_iff_isSurjective_toSelfFibreProduct`: for an
invariant `φ` under a set-theoretic pre-equivalence relation, separation of orbits is
surjectivity of `(t, s) : R ⟶ U ×_X U`. Unfolding the orbit-space condition of **Stacks
0493** into invariance, separation of orbits and surjectivity of `φ`, and substituting that
equivalence for the middle conjunct, is the lemma.

The hypothesis `IsAlgebraicSpace B S hS X.left` is the standing assumption of the source's
situation (**Stacks 048C**), where every object in sight is an algebraic space over `B`; it
is what **Stacks 049Y** needs in order to descend an equality of sections of `X` obtained
after a field extension. The hypothesis `IsSetTheoreticPreEquivalenceRelation j` is the one
written into the statement of the source.

Surjectivity is that of **Stacks 03ME**, `AlgebraicGeometry.Space.IsSurjective`, measured on
the underlying morphisms of presheaves, as everywhere else in this directory.

## References

* [Stacks Project, Tag 049Z](https://stacks.math.columbia.edu/tag/049Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U X : Over Z}

/-- **Stacks 049Z.** Let `j : R ⟶ U ×_Z U` be a set-theoretic pre-equivalence relation and
let `φ : U ⟶ X` be a morphism over the base whose target is an algebraic space. Then `φ` is
an orbit space for `j` if and only if

1. `φ` is invariant, `t ≫ φ = s ≫ φ`,
2. the induced morphism `(t, s) : R ⟶ U ×_X U` is surjective, and
3. the morphism `φ : U ⟶ X` is surjective.

Condition (2) is stated for the morphism `(t, s)` built from the proof of condition (1), so
the three conditions appear as an existential over that proof. -/
@[stacks 049Z]
theorem isOrbitSpace_iff_isSurjective_toSelfFibreProduct
    (hX : IsAlgebraicSpace B S hS X.left) (j : PreRelation R U) (φ : U ⟶ X)
    (hj : IsSetTheoreticPreEquivalenceRelation j) :
    IsOrbitSpace j φ.left ↔
      ∃ hφ : IsInvariant j φ.left,
        IsSurjective B S hS (j.toSelfFibreProduct φ hφ).left ∧
          IsSurjective B S hS φ.left :=
  ⟨fun ⟨hφ, hsep, hsurj⟩ ↦
      ⟨hφ, (separatesOrbits_iff_isSurjective_toSelfFibreProduct hX j φ hφ hj).mp hsep, hsurj⟩,
    fun ⟨hφ, hts, hsurj⟩ ↦
      ⟨hφ, (separatesOrbits_iff_isSurjective_toSelfFibreProduct hX j φ hφ hj).mpr hts, hsurj⟩⟩

/-- **Stacks 049Z** with condition (1) assumed: an invariant morphism to an algebraic space
is an orbit space for a set-theoretic pre-equivalence relation exactly when the induced
morphism `(t, s) : R ⟶ U ×_X U` and the morphism `φ` itself are surjective. -/
theorem isOrbitSpace_iff_of_isInvariant (hX : IsAlgebraicSpace B S hS X.left)
    (j : PreRelation R U) (φ : U ⟶ X) (hφ : IsInvariant j φ.left)
    (hj : IsSetTheoreticPreEquivalenceRelation j) :
    IsOrbitSpace j φ.left ↔
      IsSurjective B S hS (j.toSelfFibreProduct φ hφ).left ∧ IsSurjective B S hS φ.left :=
  (isOrbitSpace_iff_isSurjective_toSelfFibreProduct hX j φ hj).trans
    ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hφ, h⟩⟩

/-! ### The cases the source singles out -/

/-- **Stacks 049Z.** The criterion applies to a pre-equivalence relation, which is a
set-theoretic pre-equivalence relation by **Stacks 0492**, part (1). -/
theorem isOrbitSpace_iff_of_isPreEquivalenceRelation
    (hX : IsAlgebraicSpace B S hS X.left) (j : PreRelation R U) (φ : U ⟶ X)
    (hj : IsPreEquivalenceRelation j) :
    IsOrbitSpace j φ.left ↔
      ∃ hφ : IsInvariant j φ.left,
        IsSurjective B S hS (j.toSelfFibreProduct φ hφ).left ∧
          IsSurjective B S hS φ.left :=
  isOrbitSpace_iff_isSurjective_toSelfFibreProduct hX j φ
    (isSetTheoreticPreEquivalenceRelation_of_isPreEquivalenceRelation j hj)

/-- **Stacks 049Z.** The criterion applies to the pre-relation of a groupoid in algebraic
spaces over the base. -/
theorem isOrbitSpace_iff_groupoidPreRelation
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A) {Y : Over A.obj}
    (hY : IsAlgebraicSpace B S hS Y.left)
    (φ : Over.mk G.objectsToBase.hom ⟶ Y) :
    IsOrbitSpace (groupoidPreRelation G) φ.left ↔
      ∃ hφ : IsInvariant (groupoidPreRelation G) φ.left,
        IsSurjective B S hS ((groupoidPreRelation G).toSelfFibreProduct φ hφ).left ∧
          IsSurjective B S hS φ.left :=
  isOrbitSpace_iff_isSurjective_toSelfFibreProduct hY _ φ
    (isSetTheoreticPreEquivalenceRelation_groupoidPreRelation G)

/-- **Stacks 049Z.** The criterion applies to the pre-relation coming from the action of a
group algebraic space over the base on an algebraic space. -/
theorem isOrbitSpace_iff_groupoidOfAction
    (A : AlgebraicSpaces B S hS) (G W : Over A.obj) [GrpObj G] [ModObj G W]
    (hG : IsAlgebraicSpace B S hS G.left) (hW : IsAlgebraicSpace B S hS W.left)
    {Y : Over A.obj} (hY : IsAlgebraicSpace B S hS Y.left)
    (φ : Over.mk (groupoidOfAction A G W hG hW).groupoid.objectsToBase.hom ⟶ Y) :
    IsOrbitSpace (groupoidPreRelation (groupoidOfAction A G W hG hW).groupoid) φ.left ↔
      ∃ hφ : IsInvariant
          (groupoidPreRelation (groupoidOfAction A G W hG hW).groupoid) φ.left,
        IsSurjective B S hS
            ((groupoidPreRelation (groupoidOfAction A G W hG hW).groupoid).toSelfFibreProduct
              φ hφ).left ∧
          IsSurjective B S hS φ.left :=
  isOrbitSpace_iff_isSurjective_toSelfFibreProduct hY _ φ
    (isSetTheoreticPreEquivalenceRelation_groupoidOfAction A G W hG hW)

end AlgebraicGeometry.Space

end
