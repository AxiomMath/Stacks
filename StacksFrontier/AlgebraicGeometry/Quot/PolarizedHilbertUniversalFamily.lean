/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertBoundedUniversal
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeFlat

/-!
# The universal family of `Hilb^P_{Pn_Z/Z}` as a polarized family

The hypothesis `huniv` of
`AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily` (Stacks 0E96) is
Stacks 0D3W at the Hilbert functor of `Pn_Z` over `Spec Z`: for an object `U₀` of the site whose
represented presheaf is `Quot^P_{OO/Pn_Z/Z}`, a polarized family `x₀` over `U₀` to which every
polarized scheme over a field satisfying conditions (1) and (2) of Stacks 0E96 maps.

This file produces the family. The universal element of `Quot^P` over `U₀` is the image of the
identity of `U₀` under the given isomorphism (`AlgebraicGeometry.universalHilbertFamily`); it cuts
out a closed subscheme of `Pn_{U₀}` (Stacks 01QQ,
`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_ker_eq_idealOfFamily_of_mem`) which is
flat and of finite presentation over `U₀`
(`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_flat_finitePresentation_of_mem`), and
`AlgebraicGeometry.hilbertPolarizedFamily` polarizes it by the restriction of `OO(1)`.

## Main definitions

* `AlgebraicGeometry.universalHilbertFamily`: the universal element of `Quot^P_{OO/Pn_Z/Z}` over
  `U₀`, the image of the identity of `U₀`.

## Main results

* `AlgebraicGeometry.universalHilbertFamily_mem`: it is a member of `Quot^P`.
* `AlgebraicGeometry.exists_isClosedImmersion_flat_finitePresentation_universalHilbertFamily`:
  **it cuts out a closed subscheme of `Pn_{U₀}` which is flat and of finite presentation over
  `U₀`.**
* `AlgebraicGeometry.exists_polarizedFamily_base_eq_universalHilbertFamily`: **so the universal
  family is a polarized family over `U₀`** -- the object half of `huniv`.

## Implementation notes

No tag attribute is placed, for Stacks 0D3W or for Stacks 0E96. Stacks 0D3W is already on base,
on `AlgebraicGeometry.Space.morEquivSpaceHilbertFamilyOfScheme`, at the spelling of the
Hilbert presheaf of a morphism of algebraic spaces with `F = OO_X`; and what is proved here is
only the object half of `huniv`, not `huniv`. The whole of `huniv`, and with it Stacks 0E96, is
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertBoundedUnconditional.lean`.

**What `huniv` needs beyond the object half.** Writing `x₀` for the polarized family produced
here, the remaining obligation is its mapping property: for every scheme `U` of the site, every
field `k` with an
isomorphism `e` of `U` with `Spec k`, and every closed immersion `i : Z ⟶ Pn_U` whose composite
to `U` is flat and of finite presentation and for which
`AlgebraicGeometry.polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e` takes the
values of `P`, a morphism of polarized families
`hilbertPolarizedFamily n U i hfl hfp ⟶ x₀`. Two steps go into it, neither of them in the tree
when this file was written:

* **the Hilbert-polynomial comparison.** To read `(Z, i)` back as a member of
  `Quot^P_{OO/Pn/Z}(U)` one needs the fibrewise Hilbert polynomial of `i_* OO_Z` on `Pn_U`
  (the membership condition
  `AlgebraicGeometry.ProjectiveQuot.HasFibreHilbertPolynomial`) to be the Hilbert polynomial of
  `OO(1)|_Z` on the fibres of `Z ⟶ U` (the value of
  `AlgebraicGeometry.polarizedHilbertFunction`). On the fibre over a point this is the projection
  formula together with the invariance of the cohomology of a quasi-coherent module along an
  affine morphism, the step
  `AlgebraicGeometry.Space.QuotPushforwardSituation.twistedEuler_directImageQuotient` carries out
  for the algebraic-space Quot situations; it is not available on `Pn_T`, and the comparison of
  the fibre of `Z ⟶ U` with the scheme-theoretic fibre is extra.
* **base change.** The classifying morphism `g : U ⟶ U₀` of that member satisfies
  `AlgebraicGeometry.ProjectiveQuot.baseChange g (universalHilbertFamily …) = K`, by naturality of
  the given isomorphism. Turning that into the cartesian square of
  `AlgebraicGeometry.PolarizedFamily.Hom` needs the closed subscheme cut out by
  `baseChange g K₀` to be the pullback along `Pn_U ⟶ Pn_{U₀}` of the one cut out by `K₀` -- that
  `AlgebraicGeometry.ProjectiveQuot.idealOfFamily` commutes with inverse image, and that the
  closed subscheme of a pulled-back sheaf of ideals is the pullback of the closed subscheme. The
  comparison of polarizations is then the compatibility of
  `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf` with
  `AlgebraicGeometry.projectiveSpaceOverMap`.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (n : ℕ) (P : Polynomial ℚ)
  (U₀ : BigFppfOver B S hS)
  (eH : yoneda.obj U₀ ⋙ uliftFunctor.{u + 1} ≅
    (BigFppfOver.toScheme B S hS).op ⋙ ProjectiveQuot.hilbertFunctor.{u} n 1 P)

/-- **The universal element of `Quot^P_{OO/Pn_Z/Z}` over `U₀`.** For an object `U₀` of the site
whose represented presheaf is the Hilbert functor, presented by the isomorphism `eH`, this is the
submodule of `OO^{+1}` on `Pn_{U₀}` corresponding to the identity of `U₀`. -/
def universalHilbertFamily :
    Subobject (ProjectiveQuot.freeModule n 1 (B.inclusion.obj U₀.left)) :=
  (eH.hom.app (op U₀) (ULift.up (𝟙 U₀))).1

/-- **The universal element is a member of `Quot^P_{OO/Pn_Z/Z}(U₀)`.** -/
theorem universalHilbertFamily_mem :
    universalHilbertFamily B hS n P U₀ eH ∈
      ProjectiveQuot.hilbertFamilies n 1 P (B.inclusion.obj U₀.left) :=
  (eH.hom.app (op U₀) (ULift.up (𝟙 U₀))).2

include eH in
/-- **The universal family of `Hilb^P_{Pn_Z/Z}` is a closed subscheme of `Pn_{U₀}`, flat and of
finite presentation over `U₀`.** This is
`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_flat_finitePresentation_of_mem` at the
universal element. -/
theorem exists_isClosedImmersion_flat_finitePresentation_universalHilbertFamily :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U₀.left)),
      IsClosedImmersion i ∧
        Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U₀.left) ↘ B.inclusion.obj U₀.left)) ∧
          FinitePresentation
            (i ≫ (projectiveSpaceOver n (B.inclusion.obj U₀.left) ↘ B.inclusion.obj U₀.left)) :=
  ProjectiveQuot.exists_isClosedImmersion_flat_finitePresentation_of_mem
    (universalHilbertFamily_mem B hS n P U₀ eH).1

include eH in
/-- **The universal family of `Hilb^P_{Pn_Z/Z}` is a polarized family over `U₀`**: the closed
subscheme it cuts out of `Pn_{U₀}` is proper, flat and of finite presentation over `U₀`, polarized
by the restriction of `OO(1)` (`AlgebraicGeometry.hilbertPolarizedFamily`).

This is the object half of the hypothesis `huniv` of
`AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily`; the mapping
property is recorded in the implementation notes of this file and is still owed. -/
theorem exists_polarizedFamily_base_eq_universalHilbertFamily :
    ∃ x₀ : PolarizedFamily B, x₀.base = U₀.left := by
  obtain ⟨Z, i, hi, hfl, hfp⟩ :=
    exists_isClosedImmersion_flat_finitePresentation_universalHilbertFamily B hS n P U₀ eH
  have := hi
  exact ⟨hilbertPolarizedFamily n U₀.left i hfl hfp, rfl⟩

end AlgebraicGeometry

end
