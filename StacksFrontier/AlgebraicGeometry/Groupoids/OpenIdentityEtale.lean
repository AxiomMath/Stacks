module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.EtaleOfOpenIdentity

/-!
# Equivalence-relation groupoid schemes: joint monicity and the inverse

Let `(U, R, s, t, c)` be a groupoid scheme over `S`. When its target and source maps form an
equivalence relation they are jointly monomorphic — the internal form of "the arrows of `R`
between two objects are unique" — and the inverse of a groupoid with jointly monomorphic target
and source is an involution, hence an isomorphism.

These are the two facts about an equivalence-relation groupoid that the quotient criterion
[Stacks, Tag 02WW] is fed with in
`StacksFrontier.AlgebraicGeometry.Groupoids.OpenIdentityQuotient`, next to the étaleness of the
source and target of a groupoid whose identity is an open immersion, which is
`Stacks.Groupoids.GroupoidScheme.etale_source_of_isOpenImmersion_identity` and
`Stacks.Groupoids.GroupoidScheme.etale_target_of_isOpenImmersion_identity` of
`StacksFrontier.AlgebraicGeometry.Groupoids.EtaleOfOpenIdentity` and needs no joint monicity.

## Main results

* `Stacks.Groupoids.GroupoidScheme.jointlyMono_of_isEquivalenceRelation`: the target and source
  of an equivalence-relation groupoid are jointly monomorphic.
* `Stacks.Groupoids.GroupoidScheme.isIso_inverse_of_jointlyMono`: the inverse of a groupoid whose
  source and target are jointly monomorphic is an involution, hence an isomorphism.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The target and the source of a groupoid scheme which is an equivalence relation are jointly
monomorphic. -/
theorem jointlyMono_of_isEquivalenceRelation [IsEquivalenceRelation G.target G.source] :
    JointlyMono₂ G.target G.source :=
  IsEquivalenceRelation.nonempty_equivalenceRelation.some.toJointlyMono₂

/-- The inverse of a groupoid scheme whose target and source are jointly monomorphic is an
involution, hence an isomorphism: it has the same source and target as its own inverse. -/
theorem isIso_inverse_of_jointlyMono [JointlyMono₂ G.target G.source] : IsIso G.inverse := by
  have h : G.inverse ≫ G.inverse = 𝟙 G.arrows := by
    apply JointlyMono₂.right_cancellation (p₁ := G.target) (p₂ := G.source) <;>
      simp [Category.assoc, G.source_inverse, G.target_inverse]
  exact ⟨⟨G.inverse, h, h⟩⟩

end Stacks.Groupoids.GroupoidScheme

end
