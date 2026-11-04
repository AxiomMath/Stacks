module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackChangeBigSite
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackCongruence

/-!
# The inverse image of a stack under an enlargement of the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and write `f`
for the morphism of sites that the localized inclusion determines. For a category `𝒳` over the
localized big fppf site of `S` which is fibred in groupoids, Stacks 04WJ exhibits the inverse image
`f⁻¹𝒳` as the stackification of the fibred category `u_p 𝒳` of Stacks 04WG. This file makes that
object for an arbitrary such `𝒳`, in the explicit three-stage form of Stacks 02ZN, and shows that
equivalent categories over the smaller site have equivalent inverse images.

For the quotient stack of a groupoid in algebraic spaces this is
`AlgebraicGeometry.Stack.pullbackQuotientStack` on the nose.

## Main definitions

* `AlgebraicGeometry.Stack.pullbackStackProj`: the structure functor of `u_p 𝒳` with its codomain
  written as the enlarged localized big fppf site.
* `AlgebraicGeometry.Stack.pullbackStack`: **`f⁻¹𝒳`**.

## Main results

* `AlgebraicGeometry.Stack.isStack_pullbackStack`: `f⁻¹𝒳` is a stack over the enlarged localized
  big fppf site.
* `AlgebraicGeometry.Stack.pullbackStack_quotientStack`: for a quotient stack the construction is
  `AlgebraicGeometry.Stack.pullbackQuotientStack`.
* `AlgebraicGeometry.Stack.nonempty_equivalenceOver_pullbackStack`: categories equivalent over the
  smaller localized site have inverse images equivalent over the larger one.

## Implementation notes

The universes are those of `AlgebraicGeometry.Stack.quotientStack`: the total category of `𝒳` has
its objects and its morphisms in `Type (u + 1)` and `Type u` respectively, which is what makes the
comma category of Stacks 04WF and its localization land in the universes the three-stage
stackification of Stacks 02ZN requires. The inverse image is not in those universes — the
morphisms of a stackification are not small — so a statement about it is read at the universes it
lands in, or transported to a small model.

`AlgebraicGeometry.Stack.pullbackStackProj` repeats
`AlgebraicGeometry.Stack.pullbackQuotientStackProj` for an arbitrary `𝒳`, and for the same reason:
`CategoryTheory.Comma.pullbackProj` reports its codomain as a `CategoryTheory.Over` category and
`AlgebraicGeometry.BigFppfOver` is not reducible, so the enlarged site's fppf topology is not
accepted there by instance synthesis although the two types are definitionally equal.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WF](https://stacks.math.columbia.edu/tag/04WF)
* [Stacks Project, Tag 04WG](https://stacks.math.columbia.edu/tag/04WG)
* [Stacks Project, Tag 04WJ](https://stacks.math.columbia.edu/tag/04WJ)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v t

variable {B B' : BigFppfSite.{u}} (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- **Stacks 04WG** for an arbitrary fibred category over the localized big fppf site of `S`:
`u_p 𝒳` is a fibred category over the enlarged localized big fppf site. -/
theorem isFibered_pullbackProj (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] :
    (Comma.pullbackProj 𝒳.p (inclusionOver h S hS)).IsFibered :=
  have : HasNonemptyFiniteLimits (BigFppfOver B S hS) := hasNonemptyFiniteLimits_bigFppfOver S hS
  Comma.isFibered_pullbackProj _ _ (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS)

/-- The structure functor of `u_p 𝒳`, with its codomain written as the enlarged localized big
fppf site rather than as the `CategoryTheory.Over` category that site unfolds to. -/
noncomputable def pullbackStackProj (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] :
    Comma.pullbackLocalization 𝒳.p (inclusionOver h S hS) ⥤
      BigFppfOver B' S (largerContains h hS) :=
  Comma.pullbackProj 𝒳.p (inclusionOver h S hS)

/-- `u_p 𝒳` is a fibred category over the enlarged localized big fppf site, in the retyped
form. -/
instance isFibered_pullbackStackProj (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] : (pullbackStackProj h S hS 𝒳).IsFibered :=
  isFibered_pullbackProj h S hS 𝒳

/-- **`f⁻¹𝒳`, the inverse image of a fibred category over the localized big fppf site of `S` along
an enlargement of the big fppf site**: the stackification of `u_p 𝒳` over the enlarged localized
big fppf site, which is what Stacks 04WJ exhibits the pullback of a stack as. -/
noncomputable def pullbackStack (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] : BasedCategory (BigFppfOver B' S (largerContains h hS)) :=
  BasedCategory.ofFunctor ((pullbackStackProj h S hS 𝒳).stageThreeProj
    (BigFppfOver.topology B' S (largerContains h hS)))

/-- `f⁻¹𝒳` is a fibred category over the enlarged localized big fppf site. -/
instance isFibered_pullbackStack (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] : (pullbackStack h S hS 𝒳).p.IsFibered :=
  Functor.isFibered_stageThreeProj _ _

/-- `f⁻¹𝒳` satisfies descent for the fppf topology of the enlarged localized big site. -/
theorem isStack_pullbackStack (𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] :
    (pullbackStack h S hS 𝒳).p.IsStack (BigFppfOver.topology B' S (largerContains h hS)) :=
  Functor.isStack_stageThreeProj _ _

/-- For the quotient stack of a groupoid in algebraic spaces, the inverse image is the right-hand
side of Stacks 04WX. -/
theorem pullbackStack_quotientStack {Bs : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Bs) :
    pullbackStack h S hS (quotientStack G) = pullbackQuotientStack h S hS G :=
  rfl

/-- **Categories equivalent over the localized big fppf site of `S` have inverse images equivalent
over the enlarged one.** -/
theorem nonempty_equivalenceOver_pullbackStack
    (𝒳 𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)) [𝒳.p.IsFibered] [𝒴.p.IsFibered]
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (pullbackStack h S hS 𝒳).p (pullbackStack h S hS 𝒴).p) := by
  have hschemes : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  exact Comma.nonempty_equivalenceOver_stageThreeProj_pullbackProj 𝒳.p 𝒴.p
    (inclusionOver h S hS) (BigFppfOver.topology B' S (largerContains h hS))
    inferInstance inferInstance inferInstance
    (inclusionOver_preservesFiniteLimits (τ := .fppf) B B' h S hS)
    (isFibered_pullbackProj h S hS 𝒳) (isFibered_pullbackProj h S hS 𝒴) e

/-- **The inverse image of a category over the smaller localized site is unchanged, up to
equivalence over the enlarged one, by replacing that category with one equivalent to it over the
smaller site**, where the morphisms of the first category sit one universe above those of the
second, as the morphisms of a quotient stack do. -/
theorem nonempty_equivalenceOver_pullbackStack_of_quotient
    (𝒳 : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS))
    (𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    [𝒳.p.IsFibered] [𝒴.p.IsFibered]
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.p 𝒴.p) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (pullbackStack h S hS 𝒳).p (pullbackStack h S hS 𝒴).p) := by
  obtain ⟨E⟩ := Functor.nonempty_equivalenceOver_of_isEquivalence
    (p := Comma.pullbackProj 𝒳.p (inclusionOver h S hS))
    (q := Comma.pullbackProj 𝒴.p (inclusionOver h S hS)) (isFibered_pullbackProj h S hS 𝒳)
    (pullbackLocalizationMap (inclusionOver h S hS)
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)
    (Comma.pullbackLocalizationMap_isEquivalence (inclusionOver h S hS) e)
    (pullbackLocalizationMap_comp_pullbackProj (inclusionOver h S hS)
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)
  exact ⟨Functor.stageThreeCongr.{u, u + 1, u + 1, u}
    (BigFppfOver.topology B' S (largerContains h hS)) E⟩

end AlgebraicGeometry.Stack

end
