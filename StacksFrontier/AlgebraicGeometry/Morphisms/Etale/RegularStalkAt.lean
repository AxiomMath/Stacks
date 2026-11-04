module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry

/-!
# Regularity of a local ring across a morphism étale at one point

Tag 0AH7 compares the local rings of the source and target of a morphism which is étale
*everywhere*. Étaleness at a single point is étaleness of the restriction to some open
neighbourhood of that point, and the local rings of an open subscheme are those of the ambient
scheme, so the comparison holds at a point of étaleness with no hypothesis on the rest of the
morphism.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etaleAt`: at a point where a morphism is
  étale, the local ring of the source is regular if and only if the local ring of the target at
  the image is.

## Implementation notes

Both directions come for free from the global statement, so the result is an iff; the direction
the Moving Lemma, Stacks 0B0E, uses is the one carrying regularity *forward*. Its chain of
projections `r_{n + 1} ∘ ⋯ ∘ r_N` passes through images `X_j` which are singular away from the
chosen points, while the generic-projection input
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_etaleAt_projection_restrict` asks for a
point of `regularLocus X_j`; since `regularLocus` is by definition the set of points with regular
local ring, this is what supplies that hypothesis at the next stage of the induction from
étaleness at the previous one.

Nothing here extracts flatness of the stalk map, and neither finite presentation nor local
Noetherianness is assumed: the route through the open neighbourhood reduces everything to
`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etale` and
`AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_isOpenImmersion`. The alternative route — pull
flatness out of `AlgebraicGeometry.etaleAt_tfae` and appeal to the descent of regularity along a
flat local homomorphism, `IsRegularLocalRing.of_flat_of_isLocalHom` — needs both of those extra
hypotheses and gives only one direction.

## References

* [Stacks Project, Tag 0AH7](https://stacks.math.columbia.edu/tag/0AH7)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Regularity of the local ring is unchanged across a point of étaleness.** If `f : X ⟶ Y` is
étale at `x`, then `𝒪_{X, x}` is a regular local ring if and only if `𝒪_{Y, f x}` is.

Étaleness at `x` is étaleness of `U.ι ≫ f` for some open `U ∋ x`, to which Tag 0AH7 applies, and
the local ring of `U` at `x` is that of `X`.

Since `AlgebraicGeometry.regularLocus` is the set of points whose local ring is regular, this
says that a point of étaleness lies in the regular locus of the source exactly when its image
lies in the regular locus of the target. -/
public theorem isRegularLocalRing_stalk_iff_of_etaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (hf : EtaleAt f x) :
    IsRegularLocalRing (X.presheaf.stalk x) ↔
      IsRegularLocalRing (Y.presheaf.stalk (f.base x)) := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp hf
  have := hU
  have hopen := isRegularLocalRing_stalk_iff_of_isOpenImmersion U.ι (⟨x, hxU⟩ : U.toScheme)
  have hetale := isRegularLocalRing_stalk_iff_of_etale (U.ι ≫ f) (⟨x, hxU⟩ : U.toScheme)
  exact hopen.symm.trans hetale

end AlgebraicGeometry

end
