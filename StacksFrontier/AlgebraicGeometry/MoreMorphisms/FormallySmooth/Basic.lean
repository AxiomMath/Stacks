module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Formally smooth morphisms of schemes

A morphism of schemes is formally smooth, `AlgebraicGeometry.FormallySmooth`, when every morphism
to its source from the closed subscheme of a first-order thickening of affine schemes extends,
over the target, to the whole thickening. This file proves the three stability properties of that
condition — closure under composition, under arbitrary base change, and under restriction to
compatible open subschemes — and the affine criterion identifying it with formal smoothness of the
map on global sections.

## Main results

* `AlgebraicGeometry.FormallySmooth.comp`: a composition of formally smooth morphisms is formally
  smooth.
* `AlgebraicGeometry.FormallySmooth.pullback_snd`: an arbitrary base change of a formally smooth
  morphism is formally smooth.
* `AlgebraicGeometry.FormallySmooth.resLE`: formal smoothness is preserved by restriction to
  compatible open subschemes.
* `AlgebraicGeometry.formallySmooth_iff_appTop_formallySmooth`: a morphism of affine schemes is
  formally smooth if and only if its map on global sections is a formally smooth ring
  homomorphism.

## Implementation notes

The base change of `f : X ⟶ S` along `g : S' ⟶ S` is represented by the canonical projection
`CategoryTheory.Limits.pullback.snd f g : X ×[S] S' ⟶ S'`, and the restriction of `f` to opens
`U ≤ f ⁻¹ᵁ V` by `AlgebraicGeometry.Scheme.Hom.resLE`.

`AlgebraicGeometry.FormallySmooth` and `Stacks.Smooth.FormallySmoothScheme` unfold to the same
lifting property, and `Stacks.Smooth.formallySmoothScheme_iff` identifies it with the
ring-theoretic `Stacks.Smooth.FormallySmooth`, which quantifies over surjections of rings with
square-zero kernel instead of over affine thickenings.

## References

* [Stacks Project, Tag 02H1](https://stacks.math.columbia.edu/tag/02H1)
* [Stacks Project, Tag 02H2](https://stacks.math.columbia.edu/tag/02H2)
* [Stacks Project, Tag 02H3](https://stacks.math.columbia.edu/tag/02H3)
* [Stacks Project, Tag 02H4](https://stacks.math.columbia.edu/tag/02H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A composition of formally smooth morphisms is formally smooth. -/
@[stacks 02H1]
theorem FormallySmooth.comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (hf : FormallySmooth f) (hg : FormallySmooth g) :
    FormallySmooth (f ≫ g) := by
  intro T T' hT hT' i hi x h hcomp
  obtain ⟨y, hy, hiy⟩ := hg hT hT' i hi (x ≫ f) h (by simpa [Category.assoc] using hcomp)
  obtain ⟨x', hx, hix⟩ := hf hT hT' i hi x y hiy.symm
  exact ⟨x', by rw [← Category.assoc, hx, hy], hix⟩

/-- An arbitrary base change of a formally smooth morphism is formally smooth. -/
@[stacks 02H2]
theorem FormallySmooth.pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (hf : FormallySmooth f) :
    FormallySmooth (pullback.snd f g) := by
  intro T T' hT hT' i hi k h compat
  obtain ⟨x, hx, hix⟩ := hf hT hT' i hi (k ≫ pullback.fst f g) (h ≫ g) (by
    simpa only [Category.assoc, pullback.condition] using congrArg (· ≫ g) compat)
  refine ⟨pullback.lift x h hx, pullback.lift_snd _ _ _, pullback.hom_ext ?_ ?_⟩
  · simpa only [Category.assoc, pullback.lift_fst] using hix
  · simpa only [Category.assoc, pullback.lift_snd] using compat.symm

/-- Formal smoothness is preserved by restriction to compatible open subschemes. -/
@[stacks 02H3]
theorem FormallySmooth.resLE {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmooth f) (U : X.Opens) (V : S.Opens)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    FormallySmooth (f.resLE V U hUV) :=
  Stacks.Smooth.formallySmoothScheme_of_formallySmooth
    ((Stacks.Smooth.formallySmooth_of_formallySmoothScheme hf).resLE hUV)

/-- A morphism of affine schemes is formally smooth if and only if its map on global sections is
formally smooth. -/
@[stacks 02H4]
theorem formallySmooth_iff_appTop_formallySmooth
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    FormallySmooth f ↔ f.appTop.hom.FormallySmooth :=
  (Stacks.Smooth.formallySmoothScheme_iff f).trans (Stacks.Smooth.formallySmooth_iff_of_isAffine f)

end AlgebraicGeometry

end
