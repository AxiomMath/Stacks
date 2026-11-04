module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLineOpenRestriction

/-!
# An open subscheme through the generic point has the same delta-dimension

Let `X` be an integral scheme and `U ⊆ X` an open subscheme containing the generic point of
`X` — equivalently, by `Stacks.Chow.genericPoint_mem_iff_nonempty`, any nonempty open. Then `U`
is again integral, and the open immersion `U.ι` carries the generic point of `U` to the generic
point of `X`: the closure of a point of `U` is cut out of its ambient closure by `U`, and the
ambient closure of `U`'s generic point is dense, hence everything.

Because the delta-dimension of an irreducible scheme over a base carrying a dimension function
is read off at the generic point (`Stacks.Chow.schemeDeltaDimension_eq_genericPoint`), and
because the relative dimension of Stacks 02JW does not see an open immersion
(`Stacks.Chow.relativeDimension_opensι_comp`), the delta-dimension of `U` over the base agrees
with that of `X`. This is the bookkeeping that lets an argument about an integral scheme over a
base be localized to a nonempty open without tracking a change of dimension.

## Main results

* `Stacks.Chow.genericPoint_opens_eq` — an open subscheme of an integral scheme containing the
  generic point has that same point as its generic point.
* `Stacks.Chow.schemeDeltaDimension_opensι_comp'` — such an open subscheme has the same
  delta-dimension over the base as the ambient scheme.

## References

* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **The generic point of an open subscheme through the generic point.** If `X` is integral and
the open `U ⊆ X` contains the generic point of `X`, then the generic point of `U` is carried by
the open immersion `U.ι` to the generic point of `X`.

This is Mathlib's `AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion` with the irreducibility
of `U` supplied from the hypothesis: `U` is nonempty because it contains the generic point, hence
integral by `Stacks.Chow.isIntegral_opens_of_mem`, hence irreducible. -/
theorem genericPoint_opens_eq {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    (hU : genericPoint ↥X ∈ U) :
    haveI : IsIntegral (U : Scheme.{u}) := isIntegral_opens_of_mem U ⟨genericPoint ↥X, hU⟩
    U.ι.base (genericPoint ↥U.toScheme) = genericPoint ↥X := by
  have : IsIntegral (U : Scheme.{u}) := isIntegral_opens_of_mem U ⟨genericPoint ↥X, hU⟩
  exact genericPoint_eq_of_isOpenImmersion U.ι

/-- **Delta-dimension is insensitive to passing to an open subscheme through the generic
point.** For `p : X ⟶ C.S` locally of finite type on an integral `X`, and `U ⊆ X` an open
containing the generic point of `X`, the delta-dimension of `U` over the base equals that of
`X`.

Both sides are the relative dimension at the respective generic points, and
`Stacks.Chow.relativeDimension_opensι_comp` identifies the relative dimension of the generic
point of `U` with that of its image, which is the generic point of `X` by
`Stacks.Chow.genericPoint_opens_eq`. -/
theorem schemeDeltaDimension_opensι_comp' (C : ChowSituation.{u}) {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (U : X.Opens) (hU : genericPoint ↥X ∈ U) :
    schemeDeltaDimension C (U.ι ≫ p) = schemeDeltaDimension C p := by
  have : IsIntegral U.toScheme := isIntegral_opens_of_mem U ⟨genericPoint ↥X, hU⟩
  rw [schemeDeltaDimension_eq_genericPoint, schemeDeltaDimension_eq_genericPoint,
    relativeDimension_opensι_comp, genericPoint_opens_eq U hU]

end Stacks.Chow

end
