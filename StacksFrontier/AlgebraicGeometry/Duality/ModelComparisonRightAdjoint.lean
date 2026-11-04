module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingComplexModelTransport
public import StacksFrontier.AlgebraicGeometry.Duality.ProperDualizingTraceUnit
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts

/-!
# `a(K)` is a dualizing complex when `K` is, at either model of `D(𝒪_X)`

Let `f : X ⟶ Y` be a proper morphism with `Y` Noetherian and let `a` be the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. If `K ∈ D_QCoh(𝒪_Y)` is a dualizing
complex on `Y` ([Stacks, Tag 0A87]) then `a(K)` is a dualizing complex on `X`.

For a proper morphism `a` is the exceptional inverse image `f^!` of [Stacks, Tag 0A9Y] computed
at the identity compactification (`Stacks.Duality.upperShriekProperIso`), so this is
[Stacks, Tag 0AA3] for that compactification. The source's statement is about a morphism of
schemes separated and of finite type over a Noetherian base; a proper morphism `f : X ⟶ Y` with
`Y` Noetherian is such a morphism over `Y` itself, which is what
`Stacks.Duality.ftsHomToBase` records.

## The two models

`CategoryTheory.HasDerivedCategory.{w} X.Modules` is a *chosen* localization of the cochain
complexes of `𝒪_X`-modules at the quasi-isomorphisms, and this development works with two
choices: the locally small one of [Stacks, Tag 079Q], at which Brown representability and hence
[Stacks, Tag 0A9E] have content, and `CategoryTheory.HasDerivedCategory.standard`, at which the
derived internal hom of [Stacks, Tag 08DI] and the duality statements of [Stacks, Section 0AU3]
are phrased. The two have the same objects but morphisms in different universes, so
`Stacks.Duality.IsDualizingComplex` read at one is a different predicate from the same expression
read at the other, and `f^!` — built from the right adjoint that Brown representability produces
— exists only at the locally small one.

The statement is therefore made twice. At the locally small model it is the source's lemma read
through `Stacks.Duality.upperShriekProperIso`. At the standard model it is obtained from that by
transport along the comparison equivalence of the two models, and the transport needs two
ingredients, both already available:

* the comparison of the *predicate*, `Stacks.Duality.isDualizingComplex_modelEquiv_iff`: being a
  dualizing complex is carried across `StacksDraft.DerivedModel.modelEquiv` in both directions;
* the comparison of the *functor* `a`, `Stacks.Duality.StandardModel.twistedInverseImageModelIso`:
  the comparison equivalences intertwine the two right adjoints, because they intertwine the two
  readings of `Rf_*` and a right adjoint is unique up to canonical isomorphism.

## Main results

All in the namespace `Stacks.Duality`.

* `isDualizingComplex_twistedInverseImage_obj_of_isProper` — `a(K)` is dualizing at the locally
  small model, which is the model `a` is constructed at.
* `isDualizingComplex_properRightAdjoint_obj` — `a(K)` is dualizing at
  `CategoryTheory.HasDerivedCategory.standard`.

## Implementation notes

*No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes.*
Both statements are [Stacks, Tag 0AA3] at one compactification, which
`Stacks.Duality.isDualizingComplex_upperShriek_obj` carries and states for every compactification
of every morphism of `AlgebraicGeometry.FTS S`; specialising it to the identity compactification
of a proper morphism makes it weaker, not stronger, and transporting a statement along an
equivalence of two chosen localizations adds nothing to it.

The model of each derived category is written into the statements with `@` rather than fixed by a
local instance attribute, as `Duality/DualizingComplexModelTransport.lean` and
`Duality/UpperShriekChartModelComparison.lean` do and for the same reason: which model each side
is read at is exactly the content here, and an attribute in the file header would hide it. The
locally small instances are global, so the unannotated occurrences below are at the locally small
model.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open StacksDraft.DerivedModel

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y]
  [IsProper f] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/-- **`a(K)` is a dualizing complex when `K` is, at the locally small model of `D(𝒪_X)`.** Let
`f : X ⟶ Y` be proper with `Y` Noetherian, and let `a` be the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. If `K ∈ D_QCoh(𝒪_Y)` is a dualizing
complex then so is `a(K)`.

A proper morphism with Noetherian target is separated, of finite type and quasi-compact over its
target, so `f` is a morphism of `AlgebraicGeometry.FTS Y` from `X` to the terminal object; and it
is its own compactification, at which `f^!` is `a` by
`Stacks.Duality.upperShriekProperIso`. So this is [Stacks, Tag 0AA3] at that compactification. -/
theorem isDualizingComplex_twistedInverseImage_obj_of_isProper
    (K : quasiCoherentDerivedCategory Y) (hK : IsDualizingComplex K.obj) :
    IsDualizingComplex
      ((twistedInverseImage f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K).obj :=
  have : IsProper (ftsHomToBase f).left := ‹IsProper f›
  isDualizingComplex_of_iso
    ((ObjectProperty.ι _).mapIso ((upperShriekProperIso (ftsHomToBase f)).app K))
    (isDualizingComplex_upperShriek_obj (ftsHomToBase f)
      (properCompactification (ftsHomToBase f)) K hK)

/-- **`a(K)` is a dualizing complex when `K` is, at
`CategoryTheory.HasDerivedCategory.standard`.** Let `f : X ⟶ Y` be proper with `Y` Noetherian and
let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E], read at
the standard model of the two derived categories. If `K ∈ D_QCoh(𝒪_Y)` is a dualizing complex
then so is `a(K)`.

This is the previous statement transported across the comparison of the two models. The
comparison equivalences carry `a(K)` at the standard model to `a` at the locally small model
applied to the image of `K`, by
`Stacks.Duality.StandardModel.twistedInverseImageModelIso`; and being a dualizing complex is
carried in both directions by `Stacks.Duality.isDualizingComplex_modelEquiv_iff`. So `K`
dualizing at the standard model makes its image dualizing at the locally small model, hence `a`
of that image dualizing there, hence the image of `a(K)` dualizing there, hence `a(K)` dualizing
at the standard model. -/
theorem isDualizingComplex_properRightAdjoint_obj
    (K : @quasiCoherentDerivedCategory Y (HasDerivedCategory.standard Y.Modules))
    (hK : @IsDualizingComplex Y _ (HasDerivedCategory.standard Y.Modules) K.obj) :
    @IsDualizingComplex X _ (HasDerivedCategory.standard X.Modules)
      ((properRightAdjoint f).obj K).obj := by
  refine (isDualizingComplex_modelEquiv_iff (HasDerivedCategory.standard X.Modules)
    (Scheme.Modules.hasDerivedCategory X) ((properRightAdjoint f).obj K).obj).1 ?_
  refine isDualizingComplex_of_iso
    ((ObjectProperty.ι _).mapIso
      ((StandardModel.twistedInverseImageModelIso f).app K)).symm ?_
  exact isDualizingComplex_twistedInverseImage_obj_of_isProper f _
    ((isDualizingComplex_modelEquiv_iff (HasDerivedCategory.standard Y.Modules)
      (Scheme.Modules.hasDerivedCategory Y) K.obj).2 hK)

end Stacks.Duality

end
