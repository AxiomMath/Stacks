module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionExistencePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniquenessPoints
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict

/-!
# A closed immersion of algebraic stacks satisfies the valuative criterion (Stacks 0CLP)

**Stacks 0CLP.** A closed immersion of algebraic stacks satisfies both the existence and the
uniqueness part of the valuative criterion. Both clauses are proved here.

## Main results

* `AlgebraicGeometry.Stack.isClosedImmersion_relocalizeToYoneda_of_isClosedImmersion`: the closed
  immersion condition of Stacks 04YL, read on the structural morphism of the lower-shriek
  extension of a presheaf representing a base change.
* `AlgebraicGeometry.Stack.subsingleton_baseChange_of_isClosedImmersion`: that presheaf has at
  most one section over every object of the site of the point.
* `AlgebraicGeometry.Stack.valuativeCriterionUniqueness_of_isClosedImmersion`: **Stacks 0CLP**,
  the uniqueness part (**Stacks 0CLG**).
* `AlgebraicGeometry.Stack.valuativeCriterionExistence_of_isClosedImmersion`: **Stacks 0CLP**,
  the existence part (**Stacks 0CLK**).
* `AlgebraicGeometry.Stack.valuativeCriterion_of_isClosedImmersion`: the two together, as the
  source states them.

## Implementation notes

The source's hint is to reduce to a closed immersion of schemes by Stacks 0CLJ and 0CLN, and that
is what happens: Stacks 0CLJ
(`AlgebraicGeometry.Stack.valuativeCriterionUniqueness_iff_baseChange`) for the uniqueness part
and Stacks 0CLN
(`AlgebraicGeometry.Stack.valuativeCriterionExistence_of_baseChange`) for the existence part. Each
says that a 1-morphism representable by algebraic spaces satisfies its half of the criterion as
soon as, for every object `U` of the site, every scheme-valued point of the target over `U` and
every presheaf `F` over `U` representing the base change, every morphism `p : F ⟶ h_{1_U}` to the
terminal presheaf satisfies that half for presheaves (Stacks 03IX). So the content here is to get
the closed immersion hypothesis into that shape, and there are two changes of shape to make.

First, Stacks 04YL imposes the closed immersion condition on the structural morphism of the
*lower-shriek extension* `Λ_U F ⟶ h_U` of `F`, read over the site of `S`, not on `p`, which lives
over the site of `U`. `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff` identifies the two
spellings of that structural morphism; this is
`isClosedImmersion_relocalizeToYoneda_of_isClosedImmersion`, shared by both clauses.

Second, that is a statement about `Λ_U F` and the criteria are statements about `F`. A section of
`Λ_U F` over an object of the site of `S` is a factorization through `U` together with a section
of `F` over that factorization, and the structural morphism reads off the factorization. For
uniqueness this gives
`CategoryTheory.OverShriek.subsingleton_of_injective_relocalizeToYoneda`: two sections of `F` over
one object produce two sections of `Λ_U F` with the same image, so a monomorphism forces them
equal, `F` has at most one section over each object, and then *every* morphism out of `F` is a
monomorphism — in particular `p`, whence
`AlgebraicGeometry.Space.valuativeCriterionUniqueness_of_mono`. For existence it gives
`AlgebraicGeometry.Space.valuativeCriterionExistence_of_isClosedImmersion_relocalizeToYoneda`: a
lift for `Λ_U F ⟶ h_U` whose bottom edge is a prescribed factorization *is* an extension of a
section of `F` across the spectrum of the valuation ring, and because the target of `p` is
terminal the bottom triangle of the resulting lift for `p` is automatic. No field extension and no
dominating valuation ring is needed on either side, so the dominating extension produced is the
identity one.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CLJ](https://stacks.math.columbia.edu/tag/0CLJ)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLN](https://stacks.math.columbia.edu/tag/0CLN)
* [Stacks Project, Tag 0CLP](https://stacks.math.columbia.edu/tag/0CLP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The closed immersion condition of Stacks 04YL, read on the structural morphism of the
lower-shriek extension.** Stacks 04YL imposes it on the structural morphism of Stacks 04SG of a
presheaf representing a base change; `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`
identifies that with the structural morphism `Λ_U F ⟶ h_U` of the relocalization, which is the
form both halves of Stacks 0CLP are verified in. -/
theorem isClosedImmersion_relocalizeToYoneda_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
  (prop_algebraicSpaceMap_iff B S hS (Space.closedImmersionProperty B S hS) U F hF).mp
    (hf.2 U y hy F hF ⟨e⟩)

/-- **A presheaf representing a base change of a closed immersion of algebraic stacks has at most
one section over every object.** The structural morphism of the lower-shriek extension of the
representing presheaf is a closed immersion, hence a monomorphism, and a monomorphism there sees
every section of the presheaf itself. -/
theorem subsingleton_baseChange_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y f.hom.hom.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) : Subsingleton (F.obj W) := by
  have hmono : Mono (OverShriek.relocalizeToYoneda U.hom F) :=
    Space.mono_of_isClosedImmersion B S hS _
      (isClosedImmersion_relocalizeToYoneda_of_isClosedImmersion B S hS f hf U y hy F hF e)
  refine OverShriek.subsingleton_of_injective_relocalizeToYoneda U.hom F (fun V => ?_) W
  exact (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono V)

/-- **Stacks 0CLP, the uniqueness part.** A closed immersion of algebraic stacks over `S`
satisfies the uniqueness part of the valuative criterion (**Stacks 0CLG**).

By Stacks 0CLJ it is enough that every presheaf representing a base change of `f` along a
scheme-valued point of `𝒴` have structural morphism satisfying the uniqueness criterion for
presheaves; those presheaves have at most one section over every object by
`AlgebraicGeometry.Stack.subsingleton_baseChange_of_isClosedImmersion`, so every morphism out of
them is a monomorphism. -/
@[stacks 0CLP "uniqueness"]
theorem valuativeCriterionUniqueness_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) :
    ValuativeCriterion.Uniqueness B S hS f := by
  rw [valuativeCriterionUniqueness_iff_baseChange B S hS f hf.1]
  intro U
  dsimp only
  intro y hy F hF e p
  have hsub := subsingleton_baseChange_of_isClosedImmersion B S hS f hf U y hy F hF e
  refine Space.valuativeCriterionUniqueness_of_mono B U.left.1 U.left.2 p ?_
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [mono_iff_injective]
  exact fun a b _ => (hsub W).allEq a b

/-- **Stacks 0CLP, the existence part.** A closed immersion of algebraic stacks over `S` satisfies
the existence part of the valuative criterion (**Stacks 0CLK**).

By Stacks 0CLN it is enough that every presheaf representing a base change of `f` along a
scheme-valued point of `𝒴` have structural morphism satisfying the existence criterion for
presheaves. The closed immersion condition of Stacks 04YL is a condition on the structural
morphism of the lower-shriek extension of that presheaf, and
`AlgebraicGeometry.Space.valuativeCriterionExistence_of_isClosedImmersion_relocalizeToYoneda`
turns it into the existence criterion for every morphism from the presheaf to the terminal
presheaf on the site of the point — which is the shape Stacks 0CLN asks for. -/
@[stacks 0CLP "existence"]
theorem valuativeCriterionExistence_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) :
    ValuativeCriterion.Existence B S hS f := by
  refine valuativeCriterionExistence_of_baseChange B S hS f hf.1 ?_
  intro U y hy F hF e p
  exact Space.valuativeCriterionExistence_of_isClosedImmersion_relocalizeToYoneda B S hS U F
    (isClosedImmersion_relocalizeToYoneda_of_isClosedImmersion B S hS f hf U y hy F hF e) p

/-- **Stacks 0CLP.** A closed immersion of algebraic stacks over `S` satisfies both the existence
and the uniqueness part of the valuative criterion. -/
theorem valuativeCriterion_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsClosedImmersion B S hS f) :
    ValuativeCriterion.Existence B S hS f ∧ ValuativeCriterion.Uniqueness B S hS f :=
  ⟨valuativeCriterionExistence_of_isClosedImmersion B S hS f hf,
    valuativeCriterionUniqueness_of_isClosedImmersion B S hS f hf⟩

end AlgebraicGeometry.Stack

end
