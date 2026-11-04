module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeClosedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions

/-!
# Factoring through the residual gerbe at a closed point (Stacks 0H26)

**Stacks 0H26** is a remark following **Stacks 0H25**. Lemma 0H25 says that a 1-morphism
`f : 𝒴 ⟶ 𝒳` of algebraic stacks with `𝒴` reduced and `|f|(|𝒴|) ⊆ {x}` factors through the
residual gerbe `𝒵_x` of `𝒳` at `x`, provided `𝒳` is decent or locally Noetherian and the inertia
`I_𝒳 ⟶ 𝒳` is quasi-compact. The remark records that the Stacks project does not know whether the
lemma survives when `𝒳` is only assumed locally Noetherian, and asserts one positive case: if `x`
is a closed point, it is true, by **Stacks 0H27** (for `𝒳` locally Noetherian, `x` is closed
exactly when `𝒵_x ⟶ 𝒳` is a closed immersion).

Only that positive case is mathematics the remark asserts, and only it is formalized. The open
question, the general locally Noetherian case, is not stated here.

The argument is the one the remark points to. The residual gerbe at a closed point `x` exists
without any appeal to **Stacks 0H22**: the reduced closed substack with `|𝒵| = {x}`
(**Stacks 0509**) is one, by the proof of Stacks 0H27. When `𝒵_x ⟶ 𝒳` is a closed immersion, the
residual gerbe is a closed substack of `𝒳` whose only point lies over `x`; since `𝒴` is reduced and
every point of `𝒴` maps to `x`, **Stacks 050B** factors `f` through it.

## Main results

* `Stack.factorsThroughSubstack_residualGerbe_of_isClosed_singleton`:
  **Stacks 0H26**, the closed-point case the remark asserts.
* `Stack.factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion`:
  a 1-morphism from a reduced algebraic stack whose points all map to `x` factors through any
  residual gerbe at `x` whose inclusion is a closed immersion.
* `Stack.forall_factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion`:
  the same for every residual gerbe at `x`, once one of them has closed immersion inclusion, by
  the uniqueness assertion of **Stacks 06MT**.

## Implementation notes

The residual gerbe is, as everywhere in the library, an object property `P` of `𝒳` satisfying
`AlgebraicGeometry.Stack.IsResidualGerbeAt`, and its inclusion is
`AlgebraicGeometry.Stack.residualGerbeInclusion`. Factoring through it is
`AlgebraicGeometry.Stack.FactorsThroughSubstack`. The hypothesis `|f|(|𝒴|) ⊆ {x}` is read as the
containment of the range of `AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap f` in `{x}`.

## References

* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 0H25](https://stacks.math.columbia.edu/tag/0H25)
* [Stacks Project, Tag 0H26](https://stacks.math.columbia.edu/tag/0H26)
* [Stacks Project, Tag 0H27](https://stacks.math.columbia.edu/tag/0H27)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Factoring through a residual gerbe with closed immersion inclusion.** Let `P` cut out a
residual gerbe of `𝒳` at `x` whose inclusion `𝒵_x ⟶ 𝒳` is a closed immersion, and let
`f : 𝒴 ⟶ 𝒳` be a 1-morphism from a reduced algebraic stack with `|f|(|𝒴|) ⊆ {x}`. Then `f`
factors through `𝒵_x`.

The residual gerbe is then a closed substack whose single point lies over `x`, so this is
**Stacks 050B**. -/
theorem factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsResidualGerbeAt B S hS 𝒳 x P)
    (himm : AlgebraicStacks.IsClosedImmersion B S hS (residualGerbeInclusion B S hS 𝒳 x P hP))
    (hred : IsReducedStack B S hS 𝒴)
    (hf : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x}) :
    FactorsThroughSubstack f P := by
  have hcl : IsClosedSubstack 𝒳 P := ⟨hP.1, hP.2.choose, himm⟩
  refine (factorsThroughSubstack_iff_range_pointsMap_subset B S hS f hcl hP.2.choose hred).2 ?_
  intro q hq
  obtain ⟨_, _, _, _, z, -, hzx⟩ := hP
  rw [hf hq]
  exact ⟨z, hzx⟩

/-- **Factoring through every residual gerbe, once one has closed immersion inclusion.** If some
residual gerbe of `𝒳` at `x` has closed immersion inclusion, then every 1-morphism
`f : 𝒴 ⟶ 𝒳` from a reduced algebraic stack with `|f|(|𝒴|) ⊆ {x}` factors through every residual
gerbe of `𝒳` at `x`: they are all equal, by the uniqueness assertion of **Stacks 06MT**
(`AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap`). -/
theorem forall_factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsResidualGerbeAt B S hS 𝒳 x P)
    (himm : AlgebraicStacks.IsClosedImmersion B S hS (residualGerbeInclusion B S hS 𝒳 x P hP))
    (hred : IsReducedStack B S hS 𝒴)
    (hf : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x})
    (Q : ObjectProperty 𝒳.val.val.obj) (hQ : IsResidualGerbeAt B S hS 𝒳 x Q) :
    FactorsThroughSubstack f Q := by
  obtain rfl := eq_of_isResidualGerbeAt_of_bootstrap B S hS hP hQ
  exact factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion B S hS f x hP himm
    hred hf

/-- **Stacks 0H26, the closed-point case.** Let `𝒳` be a locally Noetherian algebraic stack over
`S`, let `x ∈ |𝒳|` be a closed point, and let `f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks with
`𝒴` reduced and `|f|(|𝒴|) ⊆ {x}`. Then the residual gerbe `𝒵_x` of `𝒳` at `x` exists and `f`
factors through it: every object property of `𝒳` cutting out a residual gerbe at `x` is one `f`
factors through.

This is the conclusion of **Stacks 0H25** with its quasi-compact-inertia hypothesis dropped, which
the remark says is true at a closed point because of **Stacks 0H27**. The remark's open question,
whether the conclusion holds at every point of a locally Noetherian `𝒳`, is not asserted.

The residual gerbe is the reduced closed substack on `{x}` (**Stacks 0509**), which is a residual
gerbe at `x` as in the proof of Stacks 0H27; every residual gerbe at `x` has closed immersion
inclusion by Stacks 0H27, so `f` factors through it by **Stacks 050B**. -/
@[stacks 0H26 "the closed-point case the remark asserts: for X locally Noetherian and x a closed \
point, f : Y -> X with Y reduced and |f|(|Y|) in {x} factors through the residual gerbe at x, which \
exists (via 0H27). The remark's open question, whether Lemma 0H25 holds for every point of a \
locally Noetherian X without the quasi-compact inertia hypothesis, is NOT asserted"]
theorem factorsThroughSubstack_residualGerbe_of_isClosed_singleton
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h𝒳 : IsLocallyNoetherianStack B S hS 𝒳)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hx : @IsClosed _ (pointTopology B S hS 𝒳.val) {x})
    (f : 𝒴 ⟶ 𝒳) (hf : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆ {x})
    (hred : IsReducedStack B S hS 𝒴) :
    (∃ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P) ∧
      ∀ P : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x P →
        FactorsThroughSubstack f P := by
  obtain ⟨Q, ⟨hQc, hpts, hQred⟩, -⟩ := existsUnique_reducedClosedSubstack B S hS 𝒳 {x} hx
  refine ⟨⟨Q, isResidualGerbeAt_of_isClosedSubstack_of_range_eq_singleton B S hS 𝒳 h𝒳 x Q hQc
    hpts hQred⟩, fun P hP => ?_⟩
  exact factorsThroughSubstack_of_isResidualGerbeAt_of_isClosedImmersion B S hS f x hP
    ((isClosed_singleton_iff_isClosedImmersion_residualGerbeInclusion B S hS 𝒳 h𝒳 x P hP).1 hx)
    hred hf

end AlgebraicGeometry.Stack

end
