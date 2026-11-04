module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Étale charts with separated underlying scheme

Let `X` be a presheaf on the big fppf site of a scheme `S` and let `U` be an object of that
site whose underlying scheme is separated.  Stacks 03FZ asserts that an étale morphism
`yoneda.obj U ⟶ X` from such a `U` to an algebraic space is a separated morphism of algebraic
spaces, and that the self-fibre product `U ×_X U` is represented by a separated scheme.

The proof runs through the two separatedness criteria of
`StacksFrontier/AlgebraicGeometry/Spaces/SeparatedTfae.lean` and needs nothing about étaleness.
A representable morphism of presheaves is separated exactly when its underlying morphism of
schemes is, because Yoneda and the functor to schemes both preserve fibre products and
therefore carry a relative diagonal to a relative diagonal; this is
`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff`.  Applied to the structure morphism of
`U`, whose target is a terminal object of the site, it says that `yoneda.obj U` is separated
over `S`, and every morphism out of a presheaf separated over `S` is separated.  For the
second statement, the second projection `U ×_X U ⟶ U` is a base change of `yoneda.obj U ⟶ X`,
hence a separated morphism of the site, and a scheme separated over a separated scheme is
separated.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSeparatedOver_yoneda_obj`: the presheaf represented by an object
  of the site with separated underlying scheme is separated over `S`.
* `AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated` is the first
  assertion of Stacks 03FZ, that the morphism is separated.
* `AlgebraicGeometry.Space.isSeparated_scheme_pullback` is the second assertion of
  Stacks 03FZ, that the scheme representing the self-fibre product is separated.

## Implementation notes

Neither conclusion uses the étale hypothesis of the source, and the first uses neither the
étale hypothesis nor the algebraic-space hypothesis: the unused hypotheses are retained, with
an underscore, so that the statements are those of Stacks 03FZ. The algebraic-space
hypothesis is used in the *statement* of the second result, where the representability of the
diagonal of `X` is what produces the object of the site representing `U ×_X U`.

`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff`, which both assertions rest on, lives in
`StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae` alongside the structural facts about the
representable closed-immersion property that its proof uses, and beside
`AlgebraicGeometry.Space.isSeparated_yoneda_map_of_isAffine`, the special case for a morphism
between objects with affine underlying schemes which it strictly generalizes.

## References

* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- The big fppf category over `S` has binary products: a binary product in a slice is a fibre
product over the base, and the big fppf category has fibre products by Stacks 021U.
`CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback` is deliberately a
theorem and not an instance in Mathlib, so it is registered as a local instance here, where it
is needed to form the absolute diagonal of a presheaf on the site. -/
attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

/-- **An object of the site with separated underlying scheme represents a presheaf separated
over the base.** Its structure morphism is a morphism of the site whose target is a terminal
object, and the underlying morphism of schemes is separated because its source is a separated
scheme. -/
theorem isSeparatedOver_yoneda_obj (U : BigFppfOver B S hS)
    (hU : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U)) :
    IsSeparatedOver B S hS (yoneda.obj U) := by
  have hterminal : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  refine (isSeparatedOver_iff_isSeparated_of_isTerminal B S hS hterminal
    (yoneda.map (Over.homMk U.hom (by simp) : U ⟶ Over.mk (𝟙 (B.obj hS))))).2 ?_
  refine (isSeparated_yoneda_map_iff B S hS _).2 ?_
  have : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) := hU
  infer_instance

/-- **Stacks 03FZ, first assertion.** An étale morphism to an algebraic space from an object of
the site whose underlying scheme is separated is a separated morphism of algebraic spaces. -/
@[stacks 03FZ "the étale morphism is separated"]
theorem isSeparated_of_isEtale_of_scheme_isSeparated
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS)
    (hU : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U))
    (f : yoneda.obj U ⟶ X) (_hf : IsEtale B S hS f) :
    IsSeparated B S hS f :=
  isSeparated_of_isSeparatedOver B S hS (isSeparatedOver_yoneda_obj B S hS U hU) f

/-- **Stacks 03FZ, second assertion.** The object of the site representing the self-fibre
product of an étale chart with separated underlying scheme has separated underlying scheme.
Its second projection is a base change of the chart, hence a separated morphism, and its
target is a separated scheme. -/
@[stacks 03FZ "the self-fibre product is a separated scheme"]
theorem isSeparated_scheme_pullback
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS)
    (hU : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U))
    (f : yoneda.obj U ⟶ X) (_hf : IsEtale B S hS f) :
    Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj
      ((hX.diagonal_representable.of_diag f).pullback f)) := by
  set hrep := hX.diagonal_representable.of_diag f
  have hstable : ((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbase : IsSeparated B S hS (yoneda.map (hrep.snd f)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.diagonal)
      (hrep.isPullback f)
      (isSeparated_of_isEtale_of_scheme_isSeparated B S hS X hX U hU f _hf)
  have hproj : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd f)) :=
    (isSeparated_yoneda_map_iff B S hS _).1 hbase
  have : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U) := hU
  exact ⟨by
    rw [← terminal.comp_from ((BigFppfOver.toScheme B S hS).map (hrep.snd f))]
    infer_instance⟩

end AlgebraicGeometry.Space

end
