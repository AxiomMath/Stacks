module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of lower shriek on abelian sheaves, from representable flatness

Let `u : C ⥤ D` be a continuous functor between sites which is **representably flat**, that is,
all the comma categories `I_V^u = StructuredArrow V u` of [Stacks, Tag 00VC] are cofiltered.  Then
lower shriek from abelian sheaves on `C` to abelian sheaves on `D` preserves finite limits, hence
monomorphisms, and the direct image `u^s` consequently carries injective abelian sheaves to
injective abelian sheaves.

This is the content of [Stacks, Tag 00X5] for abelian coefficients, **at independent universes**:
the two sites have objects and morphisms in arbitrary universes and the coefficients are
`AddCommGrpCat.{w}` for an arbitrary `w`.  That is what distinguishes it from the two existing
forms in the library, both of which are unusable for a site whose objects live one universe above
its morphisms:

* `CategoryTheory.Functor.preservesFiniteLimits_sheafPullback` and
  `CategoryTheory.Functor.isMorphismOfSites_of_representablyFlat` are stated for
  `[SmallCategory C]`, `[SmallCategory D]` and sheaves of sets;
* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_span_and_coequalizer`
  weakens flatness to pseudofilteredness but is also stated for small categories.

The one existing general-universe statement,
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`, asks instead that `C` have fibre
products and equalizers *which `u` preserves* — the hypotheses of [Stacks, Tag 00X6].  Those are
strictly stronger than flatness and are exactly what is unavailable for the inclusion of a
subsite whose limits are not computed in the ambient site.  This file replaces them by flatness,
which is the hypothesis a comma-category computation produces directly.

## Main results

All in the namespace `Stacks.Sites.LowerShriek`.

* `span_and_parallelPair_completion_of_isFiltered` — a filtered category satisfies the two
  conditions of [Stacks, Tag 002X].
* `preservesFiniteLimits_lan_ab_of_representablyFlat` — the left Kan extension along `u.op` on
  abelian presheaves preserves finite limits.
* `gShriek_preservesFiniteLimits_of_representablyFlat`,
  `preservesFiniteLimits_sheafPullback_of_representablyFlat` — **lower shriek on abelian sheaves
  preserves finite limits**, for the left-Kan-extension construction and for the abstract chosen
  left adjoint.
* `preservesMonomorphisms_sheafPullback_of_representablyFlat` — it preserves monomorphisms.
* `preservesInjectiveObjects_sheafPushforward_of_representablyFlat` — **the direct image along a
  continuous representably flat functor preserves injective abelian sheaves**, which is
  [Stacks, Tag 015Z] applied to the exact left adjoint.

## What is and is not proved

What is proved is the left-exactness half of [Stacks, Tag 04BH] for abelian coefficients with
flatness in place of preserved fibre products, and its consequence [Stacks, Tag 015Z].  No tag
attribute is placed: [Stacks, Tag 00X5] asserts that a continuous flat functor defines a
*morphism of sites*, a statement about sheaves of sets, and that is
`CategoryTheory.Functor.isMorphismOfSites_of_representablyFlat` for small sites; what is proved
here is the abelian analogue of its analytic core, not the tagged statement.

## Implementation notes

The pointwise description of the left Kan extension is taken from
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/LowerShriekTypeExactness.lean`, where
`Stacks.Sites.LowerShriek.lanPointwise` and `Stacks.Sites.LowerShriek.lanEvaluationIsoColim` are
public and already universe-polymorphic enough for the use made of them here.  Of the four
equivalence-transport helpers, `comp_counitInv_app_map_assoc`, `hasSpanCocone_of_equivalence`
and `hasCoequalizingHom_of_equivalence` are imported from
`StacksFrontier/CategoryTheory/Sites/Continuous.lean`, which is where they are declared, and
`hasExactColimitsOfShape_of_span_and_coequalizer` from
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/LowerShriekExactness.lean`.  Only
`preservesFiniteLimits_lan_ab_of_representablyFlat` differs from its counterpart there, and only
in how the pseudofilteredness of `(I_V^u)ᵒᵖ` is obtained: from flatness through
`span_and_parallelPair_completion_of_isFiltered` instead of from preserved fibre products and
equalizers through `CategoryTheory.structuredArrow_op_span_and_parallelPair_completion`.

The span completion in a filtered category is `CategoryTheory.IsFiltered.coeq` applied to the two
legs of the span composed into `IsFiltered.max`, which is why only `IsFiltered` and not
`IsFilteredOrEmpty` is assumed: `IsFiltered.max` needs the category to be nonempty.  Flatness
supplies that.

## References

* [Stacks Project, Tag 002X](https://stacks.math.columbia.edu/tag/002X)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
* [Stacks Project, Tag 04B0](https://stacks.math.columbia.edu/tag/04B0)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w vA uA vC vD uC uD

namespace Stacks.Sites.LowerShriek

/-- **A filtered-or-empty category satisfies the two conditions of [Stacks, Tag 002X]**: every
span is completed by a commutative square, and every parallel pair is coequalized.

This needs no nonemptiness: the two feet of a span are objects of the category, so the cocone
over them that `CategoryTheory.IsFilteredOrEmpty` supplies is available, and both conditions are
vacuous when the category is empty. -/
theorem span_and_parallelPair_completion_of_isFilteredOrEmpty {J : Type uC} [Category.{vC} J]
    [IsFilteredOrEmpty J] :
    (∀ (w x y : J) (a : w ⟶ x) (b : w ⟶ y),
        ∃ (z : J) (c : x ⟶ z) (d : y ⟶ z), a ≫ c = b ≫ d) ∧
      ∀ (x y : J) (a b : x ⟶ y), ∃ (z : J) (c : y ⟶ z), a ≫ c = b ≫ c := by
  refine ⟨fun w x y f g => ?_, fun x y f g => IsFilteredOrEmpty.cocone_maps f g⟩
  obtain ⟨m, p, q, -⟩ := IsFilteredOrEmpty.cocone_objs x y
  obtain ⟨t, r, hr⟩ := IsFilteredOrEmpty.cocone_maps (f ≫ p) (g ≫ q)
  exact ⟨t, p ≫ r, q ≫ r, by rw [← Category.assoc, ← Category.assoc, hr]⟩

/-- **A filtered category satisfies the two conditions of [Stacks, Tag 002X]**: every span is
completed by a commutative square, and every parallel pair is coequalized.

The square is obtained by composing the two legs of the span into `IsFiltered.max` and then
coequalizing the two resulting morphisms out of the apex. -/
theorem span_and_parallelPair_completion_of_isFiltered {J : Type uC} [Category.{vC} J]
    [IsFiltered J] :
    (∀ (w x y : J) (a : w ⟶ x) (b : w ⟶ y),
        ∃ (z : J) (c : x ⟶ z) (d : y ⟶ z), a ≫ c = b ≫ d) ∧
      ∀ (x y : J) (a b : x ⟶ y), ∃ (z : J) (c : y ⟶ z), a ≫ c = b ≫ c :=
  span_and_parallelPair_completion_of_isFilteredOrEmpty

/-- The left Kan extension along `u.op` on abelian presheaves preserves finite limits, when
every comma category `StructuredArrow V u` is cofiltered or empty. -/
@[sga "4 I 2.10" "special case"]
theorem preservesFiniteLimits_lan_ab_of_cofilteredOrEmpty
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) [∀ V : D, IsCofilteredOrEmpty (StructuredArrow V u)]
    [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F] :
    PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) := by
  let U := AddCommGrpCat.uliftFunctor.{max (max uC vD) vC, w}
  let R₁ := (Functor.whiskeringRight Cᵒᵖ Ab.{w} Ab.{max w (max (max uC vD) vC)}).obj U
  let R₂ := (Functor.whiskeringRight Dᵒᵖ Ab.{w} Ab.{max w (max (max uC vD) vC)}).obj U
  let : U.PreservesPointwiseLeftKanExtensions u.op := fun F ↦ by infer_instance
  let : ∀ F : Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)},
      u.op.HasPointwiseLeftKanExtension F := by infer_instance
  have hLarge : PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}) ⥤
        (Dᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)})) := by
    apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max w (max (max uC vD) vC)}
    intro I _ _
    apply preservesLimitsOfShape_of_evaluation _ I
    intro Y
    let E := Ab.{max w (max (max uC vD) vC)}
    let := Limits.hasColimitsOfSizeShrink.{vC, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    let := Limits.hasColimitsOfSizeShrink.{max uC vD, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    let := Limits.hasColimitsOfSizeShrink.{max vC (max uC vD), max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    let := AB5OfSize_shrink.{vC, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    let := AB5OfSize_shrink.{max uC vD, max uC vD,
      max w (max (max uC vD) vC), max w (max (max uC vD) vC)} E
    let : HasExactColimitsOfShape (StructuredArrow (Y.unop) u)ᵒᵖ E :=
      hasExactColimitsOfShape_of_span_and_coequalizer (A := E)
        (span_and_parallelPair_completion_of_isFilteredOrEmpty
            (J := (StructuredArrow (Y.unop) u)ᵒᵖ)).1
          (span_and_parallelPair_completion_of_isFilteredOrEmpty
            (J := (StructuredArrow (Y.unop) u)ᵒᵖ)).2
    let : HasExactColimitsOfShape (CostructuredArrow u.op Y) E :=
      HasExactColimitsOfShape.of_domain_equivalence _
        (structuredArrowOpEquivalence u Y.unop)
    exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm
  let : PreservesFiniteLimits (R₁ ⋙
      (u.op.lan : (Cᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}) ⥤
        (Dᵒᵖ ⥤ Ab.{max w (max (max uC vD) vC)}))) := comp_preservesFiniteLimits R₁ _
  have hComp : PreservesFiniteLimits
      ((u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) ⋙ R₂) :=
    preservesFiniteLimits_of_natIso (Functor.lanCompIsoOfPreserves U u.op).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ R₂

/-- The left Kan extension along `u.op` on abelian presheaves preserves finite limits, when `u`
is representably flat. -/
theorem preservesFiniteLimits_lan_ab_of_representablyFlat
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (u : C ⥤ D) [RepresentablyFlat u]
    [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F] :
    PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) := by
  exact preservesFiniteLimits_lan_ab_of_cofilteredOrEmpty u

section SheafPullbackCofilteredOrEmpty

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [∀ V : D, IsCofilteredOrEmpty (StructuredArrow V u)]
  [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F]
  [HasSheafify K Ab.{w}]

omit [u.IsContinuous J K] in
/-- **Lower shriek on abelian sheaves preserves finite limits** when every comma category of `u`
is cofiltered or empty, in the left-Kan-extension construction of it.  This is
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` with the preserved fibre products and
equalizers of [Stacks, Tag 00X6] replaced by a hypothesis weaker than the flatness of
[Stacks, Tag 00X5]. -/
theorem gShriek_preservesFiniteLimits_of_cofilteredOrEmpty :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u Ab.{w} J K) := by
  let : PreservesFiniteLimits (u.op.lan : (Cᵒᵖ ⥤ Ab.{w}) ⥤ (Dᵒᵖ ⥤ Ab.{w})) :=
    preservesFiniteLimits_lan_ab_of_cofilteredOrEmpty u
  show PreservesFiniteLimits
    (sheafToPresheaf J Ab.{w} ⋙ u.op.lan ⋙ presheafToSheaf K Ab.{w})
  apply comp_preservesFiniteLimits

/-- **Lower shriek on abelian sheaves preserves finite limits**, for the abstract chosen left
adjoint of the direct image.  The two models of lower shriek are identified by
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`. -/
theorem preservesFiniteLimits_sheafPullback_of_cofilteredOrEmpty :
    PreservesFiniteLimits (u.sheafPullback Ab.{w} J K) :=
  have := gShriek_preservesFiniteLimits_of_cofilteredOrEmpty.{w} u J K
  preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u Ab.{w} J K).symm

/-- Lower shriek on abelian sheaves preserves monomorphisms, being left exact. -/
theorem preservesMonomorphisms_sheafPullback_of_cofilteredOrEmpty :
    (u.sheafPullback Ab.{w} J K).PreservesMonomorphisms :=
  have := preservesFiniteLimits_sheafPullback_of_cofilteredOrEmpty.{w} u J K
  inferInstance

/-- **The direct image of abelian sheaves along a continuous functor whose comma categories are
cofiltered or empty preserves injective objects.**  Its left adjoint is lower shriek, which is
left exact and so preserves monomorphisms, and a right adjoint of a mono-preserving functor
preserves injectives ([Stacks, Tag 015Z]). -/
@[sga "4½ Arcata 2.3.3" "more general"]
theorem preservesInjectiveObjects_sheafPushforward_of_cofilteredOrEmpty :
    (u.sheafPushforwardContinuous Ab.{w} J K).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_sheafPullback_of_cofilteredOrEmpty.{w} u J K
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (u.sheafAdjunctionContinuous Ab.{w} J K)

end SheafPullbackCofilteredOrEmpty

section SheafPullback

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K] [RepresentablyFlat u]
  [∀ F : Cᵒᵖ ⥤ Ab.{w}, u.op.HasPointwiseLeftKanExtension F]
  [HasSheafify K Ab.{w}]

omit [u.IsContinuous J K] in
/-- **Lower shriek on abelian sheaves along a continuous representably flat functor preserves
finite limits**, in the left-Kan-extension construction of it.  This is
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` with the preserved fibre products and
equalizers of [Stacks, Tag 00X6] replaced by the flatness of [Stacks, Tag 00X5]. -/
@[sga "4 I 5.8.3" "special case"]
theorem gShriek_preservesFiniteLimits_of_representablyFlat :
    PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback u Ab.{w} J K) := by
  exact gShriek_preservesFiniteLimits_of_cofilteredOrEmpty u J K

/-- **Lower shriek on abelian sheaves along a continuous representably flat functor preserves
finite limits**, for the abstract chosen left adjoint of the direct image.  The two models of
lower shriek are identified by
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`. -/
theorem preservesFiniteLimits_sheafPullback_of_representablyFlat :
    PreservesFiniteLimits (u.sheafPullback Ab.{w} J K) :=
  have := gShriek_preservesFiniteLimits_of_representablyFlat.{w} u J K
  preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso u Ab.{w} J K).symm

/-- Lower shriek on abelian sheaves along a continuous representably flat functor preserves
monomorphisms, being left exact. -/
theorem preservesMonomorphisms_sheafPullback_of_representablyFlat :
    (u.sheafPullback Ab.{w} J K).PreservesMonomorphisms :=
  have := preservesFiniteLimits_sheafPullback_of_representablyFlat.{w} u J K
  inferInstance

/-- **The direct image of abelian sheaves along a continuous representably flat functor
preserves injective objects.**  Its left adjoint is lower shriek, which is left exact and so
preserves monomorphisms, and a right adjoint of a mono-preserving functor preserves injectives
([Stacks, Tag 015Z]). -/
@[sga "4½ Arcata 2.3.3" "more general"]
theorem preservesInjectiveObjects_sheafPushforward_of_representablyFlat :
    (u.sheafPushforwardContinuous Ab.{w} J K).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_sheafPullback_of_representablyFlat.{w} u J K
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (u.sheafAdjunctionContinuous Ab.{w} J K)

end SheafPullback

end Stacks.Sites.LowerShriek

end
