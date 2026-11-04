module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack

/-!
# Fppf descent of smoothness for 1-morphisms of algebraic stacks (Stacks 0DN7)

**Stacks 0DN7** says that a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is smooth as
soon as its base change `𝒵 ×_𝒴 𝒳 ⟶ 𝒵` along a surjective, flat, locally finitely presented
1-morphism `g : 𝒵 ⟶ 𝒴` is smooth.

The source's proof is two sentences: smoothness satisfies the two hypotheses of **Stacks 0DN6**,
being smooth local on the source-and-target and fppf local on the target. Both are available
here. Smooth locality on the source-and-target is `AlgebraicGeometry.Space.`
`isSmoothLocalOnSourceAndTarget_smooth`, the smooth case of **Stacks 06FC**; locality at the
target for the fppf precoverage is `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf`, which
is **Stacks 0429** carried from the fpqc precoverage along
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`.

No conversion between the two smooth-diagram criteria of **Stacks 06FM** is needed, unlike for
the sister descent statements for local finite presentation (Stacks 06Q8) and local finite type:
smoothness of 1-morphisms of algebraic stacks, **Stacks 075U**, *is* the existential criterion,
which is the one Stacks 0DN6 is stated over. Likewise the hypothesis is read on the 2-fibre
product of the cospan `(g, f)` in the orientation Stacks 0DN6 already uses, so no passage
between the two apexes of the cospan is needed either.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_baseChange`: **Stacks 0DN7**.

## References

* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DN6](https://stacks.math.columbia.edu/tag/0DN6)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DN7.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and let
`g : 𝒵 ⟶ 𝒴` be surjective, flat and locally of finite presentation. If the base change
`𝒵 ×_𝒴 𝒳 ⟶ 𝒵` of `f` along `g` is smooth, then so is `f`. -/
@[stacks 0DN7]
theorem isSmooth_of_baseChange
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hgs : Stack.IsSurjective B S hS g)
    (hgflat : IsFlat B S hS g)
    (hglfp : IsLocallyOfFinitePresentation B S hS g)
    (hbase : IsSmooth B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst) :
    IsSmooth B S hS f :=
  Stack.hasProperty_of_baseChange.{u, u + 1, w} B S hS (fun _ _ h => Space.IsSmooth B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS) f g hgs hgflat hglfp hbase

end AlgebraicGeometry.Stack.AlgebraicStacks

end
