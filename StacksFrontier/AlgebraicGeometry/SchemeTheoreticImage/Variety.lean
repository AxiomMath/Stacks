module

public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The scheme-theoretic image of an irreducible scheme, of an integral scheme, and of a variety

For a quasi-compact morphism `f : X ⟶ Y` the morphism `X ⟶ f.image` onto the scheme-theoretic
image is dominant, so the image inherits irreducibility from `X`; combined with
`AlgebraicGeometry.Scheme.Hom.isReduced_image` this makes the image of an integral scheme
integral, and then the image of a variety a variety, its structure morphism being the inclusion
of the image followed by that of the target.

## Main results

* `AlgebraicGeometry.Scheme.Hom.irreducibleSpace_image`: the scheme-theoretic image of an
  irreducible scheme is irreducible.
* `AlgebraicGeometry.Scheme.Hom.isIntegral_image`: the scheme-theoretic image of an integral
  scheme is integral.
* `AlgebraicGeometry.Scheme.Hom.isVariety_image`: the scheme-theoretic image of an integral
  scheme inside a separated scheme of finite type over a field is a variety over that field.

## Implementation notes

Irreducibility is read off the dominance of `AlgebraicGeometry.Scheme.Hom.toImage`, which Mathlib
supplies for a quasi-compact morphism, rather than off the description of the support of the
kernel ideal sheaf: the image of an irreducible space is irreducible and so is its closure, and
the closure of the range of `toImage` is everything.

`isVariety_image` asks for integrality of the source rather than for a variety structure on it:
of the four components of `AlgebraicGeometry.IsVariety` only integrality of the source is used,
the other three being inherited from the target's structure morphism through the closed immersion
`AlgebraicGeometry.Scheme.Hom.imageι`. A variety structure on the source supplies the integrality,
so the stated form covers the case of a morphism of varieties while also covering a morphism whose
source carries no structure morphism to the base.

The three hypotheses on the structure morphism of the target hold for projective space over a
field, which is the case the Moving Lemma, Stacks 0B0E, uses: the images `X_j, Z_j, T_{i, j}` of
its chain of projections are the scheme-theoretic images of finite morphisms into `𝐏(V_j)`, and
what the induction needs of them is exactly that they are varieties.

## References

* [Stacks Project, Tag 020D](https://stacks.math.columbia.edu/tag/020D)
* [Stacks Project, Tag 056B](https://stacks.math.columbia.edu/tag/056B)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- **The scheme-theoretic image of an irreducible scheme is irreducible.** The morphism onto the
scheme-theoretic image of a quasi-compact morphism is dominant, and the closure of the image of an
irreducible space is irreducible. -/
@[ega "I 9.5.9" "(ii), irreducible case"]
public instance irreducibleSpace_image (f : X ⟶ Y) [IrreducibleSpace X] [QuasiCompact f] :
    IrreducibleSpace f.image := by
  refine (irreducibleSpace_def _).mpr ?_
  rw [Set.top_eq_univ, ← f.toImage.denseRange.closure_range]
  have himg := ((IrreducibleSpace.isIrreducible_univ X).image _
    f.toImage.continuous.continuousOn).closure
  rwa [Set.image_univ] at himg

/-- **The scheme-theoretic image of an integral scheme is integral.** It is reduced by
`AlgebraicGeometry.Scheme.Hom.isReduced_image` and irreducible by
`AlgebraicGeometry.Scheme.Hom.irreducibleSpace_image`. -/
@[ega "I 9.5.9" "(ii), integral case"]
public instance isIntegral_image (f : X ⟶ Y) [IsIntegral X] [QuasiCompact f] :
    IsIntegral f.image :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- **The scheme-theoretic image of an integral scheme is a variety.** Let `f : X ⟶ Y` be
quasi-compact with `X` integral and let `Y` be separated and of finite type over a field `k`.
Then the scheme-theoretic image of `f`, with the structure morphism obtained by composing the
inclusion of the image with that of `Y`, is a variety over `k`.

Integrality of the image is `AlgebraicGeometry.Scheme.Hom.isIntegral_image`; the remaining three
conditions pass from the structure morphism of `Y` to that of the image along the closed immersion
`AlgebraicGeometry.Scheme.Hom.imageι`. -/
@[ega "I 9.5.9" "(ii), integral case"]
public theorem isVariety_image (k : Type u) [Field k] (f : X ⟶ Y) (gS : Y ⟶ Spec (.of k))
    [IsIntegral X] [QuasiCompact f] [IsSeparated gS] [LocallyOfFiniteType gS] [QuasiCompact gS] :
    IsVariety k (f.imageι ≫ gS) :=
  IsVariety.mk

end AlgebraicGeometry.Scheme.Hom

end
