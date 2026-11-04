module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSheafifyForgetHom
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero

/-!
# The vanishing and degree-`0` clauses of Stacks 0D0Y

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.  Stacks 0D0Y
asserts three things about the cohomology sheaves of the naive cotangent complex `NL_{X/Y}` of
Stacks 0D0V: they are quasi-coherent, they vanish outside degrees `-1` and `0`, and in degree `0`
the cohomology sheaf is the sheaf of differentials `Ω_{X/Y}`.

This file proves the two clauses that the source gets from the construction of the naive
cotangent complex in Modules on Sites, Section 08TT: `NL_{X/Y}` is a two-term complex
concentrated in degrees `-1` and `0`, so its cohomology vanishes elsewhere, and its degree-`0`
cohomology sheaf is the module of differentials of the homomorphism of sheaves of rings
`f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, which is what Stacks 04CT means by `Ω_{X/Y}`.  The full statement of
Stacks 0D0Y, with the quasi-coherence clause, is
`AlgebraicGeometry.Space.naiveCotangentComplex_homology` in
`StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentHomologyQuasicoherent`, which also identifies
the degree-`0` cohomology sheaf with this development's `Ω_{X/Y}`,
`AlgebraicGeometry.Space.sheafOfDifferentials`.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_naiveCotangentComplex`: the cohomology sheaves of
  `NL_{X/Y}` vanish in every degree other than `-1` and `0`.

## Main definitions

* `AlgebraicGeometry.Space.naiveCotangentComplexHomologyZeroIso`: the degree-`0` cohomology
  sheaf of `NL_{X/Y}` is the module of differentials of `f♯`.

## Implementation notes

Both statements are the general site-level statements about the naive cotangent complex of a
homomorphism of sheaves of commutative rings, read at the small étale site of `X` and at the
homomorphism `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` that `AlgebraicGeometry.Space.naiveCotangentComplex` is built
from: `Stacks.SheafOfModules.naiveCotangentComplex_isZero_X` for the vanishing, which gives the
vanishing of the *terms* and hence exactness, and
`Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso` (Stacks 08TY in degree `0`) for the
degree-`0` identification.

The module of differentials appears here as
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite` of `f♯`, the Modules-on-Sites
module of differentials of Stacks 04BN.  The small étale site of an algebraic space over
`S : Scheme.{u}` has its objects in `Type (u + 1)` while its structure rings have sections in
`Type u`, and the site-level naive cotangent complex puts its module sections at the maximum of
the two, that is at `u + 1` (this is the implementation note of
`AlgebraicGeometry.Space.naiveCotangentComplex`), so this module of differentials has its sections
in `Type (u + 1)`.  `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoUlift`
identifies it with the universe lift of `AlgebraicGeometry.Space.sheafOfDifferentials`.

Sheafification of `AddCommGrpCat.{u + 1}`-valued presheaves on the small étale site is needed for
the degree-`0` cohomology sheaf to exist at all, and the site's own instances stop at the
universe of the structure rings; `AlgebraicGeometry.Space.objUniverseHasSheafify` supplies it from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, alongside the companion
`AlgebraicGeometry.Space.objUniverseWEqualsLocallyBijective` which is already in the library.

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V), the naive cotangent
  complex of a morphism of algebraic spaces.
* [Stacks Project, Tag 08TT](https://stacks.math.columbia.edu/tag/08TT), the construction of the
  naive cotangent complex on a site.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the degree-`0`
  cohomology sheaf of the naive cotangent complex.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces.
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheafification of presheaves of abelian groups whose sections lie at the universe of the
objects of the small étale site, which is one above the universe of its structure rings.  The
site's own sheafification instances are stated at the universe of the structure rings, so they do
not cover this case; it is the companion of
`AlgebraicGeometry.Space.objUniverseWEqualsLocallyBijective`, and like it the content is only a
universe specialization — the site is essentially small at the universe of its schemes. -/
instance objUniverseHasSheafify (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

variable {X Y : AlgebraicSpaces B S hS}

/-- **The vanishing clause of Stacks 0D0Y.**  The cohomology sheaves of the naive cotangent complex
`NL_{X/Y}` of a morphism of algebraic spaces vanish outside degrees `-1` and `0`: the complex has
no terms in those degrees, so it is exact there. -/
theorem isZero_homology_naiveCotangentComplex (f : X ⟶ Y) (i : ℤ) (hneg : i ≠ -1)
    (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex B S hS f).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X.{u, u + 1, u, u}
      (smallEtaleRingedTopos B S hS X).J (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
      i hneg hzero)).isZero_homology

/-- **The degree-zero clause of Stacks 0D0Y.**  The degree-`0` cohomology sheaf of the naive
cotangent complex `NL_{X/Y}` of a morphism of algebraic spaces is the sheaf of differentials
`Ω_{X/Y}`, that is the module of differentials of Stacks 04BN of the homomorphism of sheaves of
rings `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, which is what Stacks 04CT defines `Ω_{X/Y}` to be.

This is Stacks 08TY in degree `0`, read at the small étale site of `X`.  `Ω_{X/Y}` is read at the
module universe of the complex, which is the universe of the objects of the small étale site and
not that of its structure rings; see the implementation notes.  The full statement of
Stacks 0D0Y is `AlgebraicGeometry.Space.naiveCotangentComplex_homology`. -/
noncomputable def naiveCotangentComplexHomologyZeroIso (f : X ⟶ Y) :
    (naiveCotangentComplex B S hS f).homology 0 ≅
      moduleOfDifferentialsOfSite.{u, u + 1, u, u} (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) :=
  Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIso.{u, u + 1, u, u}
    (smallEtaleRingedTopos B S hS X).J (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)

end AlgebraicGeometry.Space

end
