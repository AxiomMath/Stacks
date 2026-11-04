module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor

/-!
# The canonical functor inverts the quasi-isomorphisms of `K^b(A)`

The last assertion of Tag 0F8I is that on a quasi-compact, quasi-separated scheme with the
resolution property the canonical functor `K^b(A) ⥤ D_perf(O_X)` presents `D_perf(O_X)` as the
localization of `K^b(A)` at the system `S` of quasi-isomorphisms.
`CategoryTheory.Functor.IsLocalization` has two fields: that the functor inverts `S`, and that
the induced functor `S⁻¹K^b(A) ⥤ D_perf(O_X)` is an equivalence. The first holds with no
hypothesis on `X` and is proved here; it is the clause of Tag 0F8I asserting that the functor
*factors* through the localization, and it is registered against that tag below. The second
field is not proved anywhere yet: an equivalence is essentially surjective, so it asserts in
particular that every perfect object of `D(O_X)` is isomorphic to the image of a bounded
complex of finite locally free modules, which is Tag 0F8F. That tag is in the trees:
`Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_affineDiagonal`
proves it for a scheme whose diagonal is assumed affine, and
`Perfect.BoundedLocallyFreeComplexes.exists_boundedFiniteLocallyFree_iso_of_hasResolutionProperty`
deduces that affine diagonal from the resolution property alone, Tag 0F8C being
unconditional. So the equivalence waits only on the transport of Tags 0F8G and 0F8H from maps of
complexes to morphisms of the two categories, which supply the fullness and the faithfulness;
that transport is carried out in
`StacksFrontier/AlgebraicGeometry/Perfect/BoundedLocallyFreeComplexes/Localization.lean`.

## Main results

* `Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_isInvertedBy_perfectComplexFunctor`:
  the canonical functor
  `K^b(A) ⥤ D_perf(O_X)` inverts the quasi-isomorphisms of `K^b(A)`.

## Implementation notes

A morphism of `K^b(A)` lies in `S` exactly when its image in `K(O_X)` is a quasi-isomorphism,
and `CategoryTheory.DerivedCategory.Qh` is a localization at those, so the image of the
morphism in `D(O_X)` is invertible. The canonical functor is
`CategoryTheory.ObjectProperty.lift`, whose action on morphisms is *definitionally* that of the
functor it lifts (`CategoryTheory.ObjectProperty.ι_obj_lift_map`), so the image in `D(O_X)` is
literally the image of the morphism under the inclusion of `D_perf(O_X)`; the inclusion of a
full subcategory is fully faithful and therefore reflects the invertibility.

The intermediate step is stated as a hypothesis with its type written out rather than rewritten
into the goal: `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor` is a `def`, which
  neither `rw` nor `simp` can
see through, while `exact` checks the definitional equality at default transparency.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 0F8F](https://stacks.math.columbia.edu/tag/0F8F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace StrictlyPerfect
  Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical functor `K^b(A) ⥤ D_perf(O_X)` inverts the quasi-isomorphisms of `K^b(A)`.**
A morphism of `K^b(A)` is a quasi-isomorphism exactly when its image in `K(O_X)` is one, so
`CategoryTheory.DerivedCategory.Qh` sends it to an isomorphism; that image is the image of the
morphism under the fully faithful inclusion of `D_perf(O_X)`, which therefore reflects the
invertibility. -/
@[stacks 0F8I "the canonical functor inverts the system `S` of quasi-isomorphisms, so that it \
factors through `S⁻¹K^b(A)`; this is the first field of `Functor.IsLocalization`, for every \
scheme X"]
theorem quasiIsomorphisms_isInvertedBy_perfectComplexFunctor (X : Scheme.{u}) :
    (quasiIsomorphisms X).IsInvertedBy (perfectComplexFunctor X) := by
  intro E₁ E₂ f hf
  let P : ObjectProperty (DerivedCategory X.Modules) :=
    fun K => IsPerfect (X := X.toRingedSpace) K
  have : IsIso (P.ι.map ((perfectComplexFunctor X).map f)) :=
    Localization.inverts (DerivedCategory.Qh (C := X.Modules))
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ hf
  exact isIso_of_fully_faithful P.ι ((perfectComplexFunctor X).map f)

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
