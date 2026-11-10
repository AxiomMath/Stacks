module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Colimits

/-!
# A pseudofilteredness criterion for exactness of the pullback of abelian sheaves

Let `u : C ⥤ D` be a continuous functor of small sites and let `A` be an abelian coefficient
category with exact filtered colimits. The pullback of `A`-valued sheaves along `u` is the
sheafification of the left Kan extension along `u.op`, and that Kan extension is computed
pointwise as a colimit over a costructured-arrow category. So the pullback is exact as soon as
those colimits are exact, and for that it suffices that every `(StructuredArrow V u)ᵒᵖ` be
pseudofiltered, in the two-condition form of Stacks 002X: spans can be completed to commutative
squares, and parallel pairs can be coequalized.

Pseudofilteredness is strictly weaker than `CategoryTheory.RepresentablyFlat u`, which asks every
`StructuredArrow V u` to be cofiltered. A comma category that is a *disjoint union* of cofiltered
categories is never cofiltered once it has two summands, but it is pseudofiltered, and a colimit
over it is still exact — the colimit is the direct sum of the colimits over the summands, and
direct sums are exact by AB4.

## Main results

* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_lan_of_span_and_coequalizer`: the left Kan
  extension along `u.op` preserves finite limits.
* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_span_and_coequalizer` and
  `.preservesMonomorphisms_sheafPullback_of_span_and_coequalizer`: the pullback of sheaves is
  left exact, and in particular preserves monomorphisms.
* `Stacks.Sites.AbelianPullback.span_and_coequalizer_op_of_weaklyInitial`: a sufficient condition
  for the two hypotheses which is checkable summand by summand — below every object there is one
  that maps to all its predecessors and admits at most one map to any object.
* `Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_weaklyInitial`: the two
  statements combined.

## Implementation notes

The exactness of a pseudofiltered colimit is Stacks 04B0, i.e.
`CategoryTheory.hasExactColimitsOfShape_of_isPseudofiltered`, and the pointwise description of
the Kan extension is `CategoryTheory.lanEvaluationIsoColim`. In place of the concreteness
hypotheses of `CategoryTheory.lan_preservesFiniteLimits_of_flat`, the coefficient category
satisfies the Grothendieck axioms.

The coefficient category has the morphism universe of the sites, so that the pointwise Kan
extension is the colimit `CategoryTheory.lanEvaluationIsoColim` computes. The statements are
about the abstract `CategoryTheory.Functor.sheafPullback`, the chosen left adjoint of
restriction, which `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`
identifies with the left Kan extension construction.

The weak-initiality criterion asks, for each object `x`, for an object `W` admitting a morphism
to every object that maps to `x`, and admitting at most one morphism to any object at all. Both
clauses are automatic for an initial object of the connected component of `x`, and the second is
vacuous for objects outside that component, so the criterion is exactly "every connected
component has an initial object" in a usable form.

## References

* [Stacks Project, Tag 002X](https://stacks.math.columbia.edu/tag/002X)
* [Stacks Project, Tag 04B0](https://stacks.math.columbia.edu/tag/04B0)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe uA u

namespace Stacks.Sites.AbelianPullback

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
  (A : Type uA) [Category.{u} A] [Abelian A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]

/-- The two conditions of Stacks 002X on the opposite of a comma category of `u`: every span is
completed by a commutative square, and every parallel pair is coequalized. -/
def SpanAndCoequalizerOp : Prop :=
  (∀ (V : D) ⦃x y z : (StructuredArrow V u)ᵒᵖ⦄ (a : x ⟶ y) (b : x ⟶ z),
      ∃ (t : (StructuredArrow V u)ᵒᵖ) (c : y ⟶ t) (d : z ⟶ t), a ≫ c = b ≫ d) ∧
    ∀ (V : D) ⦃x y : (StructuredArrow V u)ᵒᵖ⦄ (a b : x ⟶ y),
      ∃ (z : (StructuredArrow V u)ᵒᵖ) (c : y ⟶ z), a ≫ c = b ≫ c

/-- If every `(StructuredArrow V u)ᵒᵖ` is pseudofiltered, then the left Kan extension along
`u.op` on presheaves with values in an abelian category with exact filtered colimits preserves
finite limits. -/
theorem preservesFiniteLimits_lan_of_span_and_coequalizer (h : SpanAndCoequalizerOp u) :
    PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro I _ _
  apply preservesLimitsOfShape_of_evaluation (u.op.lan : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) I
  intro Y
  have : HasExactColimitsOfShape (StructuredArrow Y.unop u)ᵒᵖ A :=
    CategoryTheory.hasExactColimitsOfShape_of_isPseudofiltered (h.1 Y.unop) (h.2 Y.unop)
  have : HasExactColimitsOfShape (CostructuredArrow u.op Y) A :=
    HasExactColimitsOfShape.of_domain_equivalence _ (structuredArrowOpEquivalence u Y.unop)
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
  [HasSheafify K A]

/-- **Stacks 04BH, with the fibre-product hypotheses replaced by pseudofilteredness.** If every
`(StructuredArrow V u)ᵒᵖ` is pseudofiltered, then the pullback of sheaves with values in an
abelian category with exact filtered colimits preserves finite limits. -/
theorem preservesFiniteLimits_sheafPullback_of_span_and_coequalizer
    (h : SpanAndCoequalizerOp u) :
    PreservesFiniteLimits (u.sheafPullback A J K) := by
  have : PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) :=
    preservesFiniteLimits_lan_of_span_and_coequalizer u A h
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u A J K) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J A ⋙ u.op.lan ⋙ presheafToSheaf K A)
    apply comp_preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u A J K).symm

/-- If every `(StructuredArrow V u)ᵒᵖ` is pseudofiltered, then the pullback of sheaves with values
in an abelian category with exact filtered colimits preserves monomorphisms. -/
theorem preservesMonomorphisms_sheafPullback_of_span_and_coequalizer
    (h : SpanAndCoequalizerOp u) : (u.sheafPullback A J K).PreservesMonomorphisms := by
  have := preservesFiniteLimits_sheafPullback_of_span_and_coequalizer u A J K h
  infer_instance

end Stacks.Sites.AbelianPullback

namespace Stacks.Sites.AbelianPullback

variable {J : Type u} [Category.{u} J]

/-- If below every object of `J` there is an object `W` which maps to every object mapping to it
and admits at most one morphism to any object, then `Jᵒᵖ` satisfies the two conditions of
Stacks 002X. -/
theorem span_and_coequalizer_op_of_weaklyInitial
    (h : ∀ x : J, ∃ W : J, (∀ {y : J}, (y ⟶ x) → Nonempty (W ⟶ y)) ∧
      ∀ {y : J} (q q' : W ⟶ y), q = q') :
    (∀ ⦃x y z : Jᵒᵖ⦄ (a : x ⟶ y) (b : x ⟶ z),
        ∃ (t : Jᵒᵖ) (c : y ⟶ t) (d : z ⟶ t), a ≫ c = b ≫ d) ∧
      ∀ ⦃x y : Jᵒᵖ⦄ (a b : x ⟶ y), ∃ (z : Jᵒᵖ) (c : y ⟶ z), a ≫ c = b ≫ c := by
  constructor
  · intro w x y a b
    obtain ⟨W, hfac, hsub⟩ := h w.unop
    obtain ⟨q₁⟩ := hfac a.unop
    obtain ⟨q₂⟩ := hfac b.unop
    exact ⟨op W, q₁.op, q₂.op, Quiver.Hom.unop_inj (hsub _ _)⟩
  · intro x y a b
    obtain ⟨W, hfac, hsub⟩ := h x.unop
    obtain ⟨q⟩ := hfac a.unop
    exact ⟨op W, q.op, Quiver.Hom.unop_inj (hsub _ _)⟩

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
  (A : Type uA) [Category.{u} A] [Abelian A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
  (Jt : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous Jt K]
  [HasSheafify K A]

/-- The pullback of abelian sheaves along a continuous functor each of whose comma categories has
weakly initial objects below every object preserves monomorphisms. -/
theorem preservesMonomorphisms_sheafPullback_of_weaklyInitial
    (h : ∀ (V : D) (x : StructuredArrow V u), ∃ W : StructuredArrow V u,
      (∀ {y : StructuredArrow V u}, (y ⟶ x) → Nonempty (W ⟶ y)) ∧
        ∀ {y : StructuredArrow V u} (q q' : W ⟶ y), q = q') :
    (u.sheafPullback A Jt K).PreservesMonomorphisms :=
  preservesMonomorphisms_sheafPullback_of_span_and_coequalizer u A Jt K
    ⟨fun V => (span_and_coequalizer_op_of_weaklyInitial (h V)).1,
      fun V => (span_and_coequalizer_op_of_weaklyInitial (h V)).2⟩

end Stacks.Sites.AbelianPullback

end
