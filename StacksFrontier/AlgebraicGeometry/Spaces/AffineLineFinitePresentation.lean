module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf

/-!
# The affine line is locally of finite presentation over the base

The affine line over `S`, viewed as an algebraic space over `S` through
`AlgebraicGeometry.Space.affineLineSpace`, is locally of finite presentation over the base,
in the sense of Stacks 03XP, part (1): every commuting square of étale scheme charts of its
structure morphism induces a morphism of schemes which is locally of finite presentation.

## Main results

* `AlgebraicGeometry.Space.toScheme_map_affineLineToBase`: the structure morphism
  `AlgebraicGeometry.Space.affineLineToBase` of the affine line over `S` is, on underlying
  schemes, the projection from affine one-space over `S`.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_affineLineSpace`: the affine line
  over `S` is locally of finite presentation over the terminal presheaf.

## Implementation notes

The structure morphism of the affine line as an algebraic space is `terminal.from`, a morphism
into the terminal object `⊤_` of the category of presheaves on the site. The presheaf
represented by the terminal object `Over.mk (𝟙 (B.obj hS))` of the site is *also* terminal
there, by `AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`, but it is not the object a
`CategoryTheory.Limits.HasTerminal` instance produces; the two are identified by the unique
isomorphism between terminal objects, and the represented base changes of a morphism are
insensitive to composing that isomorphism after it, the relatively representable form of a
property respecting isomorphisms.

So the content is carried by the morphism `AlgebraicGeometry.Space.affineLineToBase` of the
site, whose underlying morphism of schemes is the projection `𝔸¹_S → S`. That projection is
locally of finite presentation by the Mathlib instance for affine `n`-space with `n` finite,
`PUnit` being finite; a morphism of the site inherits the relatively representable form of any
base-change stable property of its underlying scheme morphism
(`AlgebraicGeometry.Space.presheaf_yoneda_map_of_inverseImage`), and that form implies the
every-étale-chart form in which local finite presentation of algebraic spaces is stated, by the
implication of Stacks 03MJ
(`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp`). The
hypothesis that implication asks of the property is satisfied here because an étale morphism of
schemes is locally of finite presentation and that class is stable under composition.

*Why `inferInstanceAs` and not `rw`.* The scheme-level instance is reached by
`inferInstanceAs (LocallyOfFinitePresentation (AffineSpace PUnit.{u + 1} S ↘ S))` rather than
by `rw [toScheme_map_affineLineToBase]; infer_instance`, and the second **fails**. Rewriting
the morphism leaves the *implicit* source and target scheme arguments of
`LocallyOfFinitePresentation` as `(BigFppfOver.toScheme B S hS).obj …`, which do not reducibly
match the head `𝔸(n; S)` of the Mathlib instance, so synthesis fails — even though
`example : LocallyOfFinitePresentation (AffineSpace PUnit.{u + 1} S ↘ S) := inferInstance`
succeeds on its own. `inferInstanceAs` is legitimate here precisely because
`toScheme_map_affineLineToBase` is `rfl`: the two morphisms are definitionally equal, so the
ascription changes nothing but the syntactic form the instance search sees. Anyone extending
this file should expect the same behaviour at any other transport of a scheme-level instance across
`BigFppfOver.toScheme`.

*The two spellings of the affine line are unrelated in this development.*
`AlgebraicGeometry.Space.affineSpaceOver` in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineSpaceOver.lean` — whose `n = 1` case is also the
affine line — is connected to `AlgebraicGeometry.Space.affineLineSpace` by no lemma anywhere in
the tree, and that file contains no theorems at all. The statement below is proved for
`affineLineSpace`, which is the spelling
`AlgebraicGeometry.Space.globalFunctionsHomEquiv` uses, so its consumers need no bridge; a
consumer that happens to hold the other spelling does, and none exists.

This is the one statement the limit comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/GlobalFunctionsColimit.lean` was missing: global
regular functions on an algebraic space are its morphisms to the affine line, so the colimit
statement for global functions is an instance of the approximation results for morphisms into a
target locally of finite presentation.

## References

* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On underlying schemes, the structure morphism of the affine line over `S` is the projection
from affine one-space. -/
theorem toScheme_map_affineLineToBase :
    (BigFppfOver.toScheme B S hS).map (affineLineToBase B S hS) =
      (AffineSpace PUnit.{u + 1} S ↘ S) :=
  rfl

/-- **The affine line over `S` is locally of finite presentation over the base.** Its structure
morphism of schemes is the projection from affine one-space, which is locally of finite
presentation, and the every-étale-chart condition of Stacks 03XP, part (1) follows from the
relatively representable form by the implication of Stacks 03MJ. -/
theorem isLocallyOfFinitePresentation_affineLineSpace :
    IsLocallyOfFinitePresentation B S hS
      (terminal.from (affineLineSpace B S hS).obj) := by
  have hlfp : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (affineLineToBase B S hS)) :=
    inferInstanceAs (LocallyOfFinitePresentation (AffineSpace PUnit.{u + 1} S ↘ S))
  have hmap := presheaf_yoneda_map_of_inverseImage B S hS
    (P := @LocallyOfFinitePresentation.{u}) inferInstance (affineLineToBase B S hS) hlfp
  have hiso : IsIso (terminal.from
      (yoneda.obj (Over.mk (𝟙 (B.obj hS))) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isIso_of_isTerminal (isTerminal_yoneda_obj_base B S hS) terminalIsTerminal _
  have hpre : (MorphismProperty.inverseImage (@LocallyOfFinitePresentation.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (terminal.from (affineLineSpace B S hS).obj) := by
    have hrw : terminal.from (affineLineSpace B S hS).obj =
        yoneda.map (affineLineToBase B S hS) ≫ terminal.from _ := terminal.hom_ext _ _
    rw [hrw]
    exact MorphismProperty.RespectsIso.postcomp _ _ _ hmap
  refine presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS _
    (fun i q hi hq => ?_) _ hpre
  have _ : Etale i := hi
  have _ : LocallyOfFinitePresentation q := hq
  infer_instance

end AlgebraicGeometry.Space

end
