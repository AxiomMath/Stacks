module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceKernelIdealFirstMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The conormal sequence of a general immersion

Let `B` be an algebraic space over a scheme `S` and let `i : Z ⟶ X` be an **immersion** of
algebraic spaces over `B`, with structure morphism `b : X ⟶ B`.  Stacks 05ZA attaches to it the
canonical sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
This file carries its first arrow and the vanishing of its composite **at an arbitrary
immersion**, not only at a closed subspace, and so at the generality the tag is stated in.

## Why no reduction to the closed case is needed

The source reduces to a closed immersion by replacing `X` with the complement of the boundary of
`Z`.  That reduction is not performed here, and it does not have to be: the arrow is built
directly from the kernel ideal sheaf `𝓘_i = ker(i♯ : 𝒪_X ⟶ i_*𝒪_Z)`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceKernelIdealFirstMap.lean`, for an arbitrary
morphism of algebraic spaces — the annihilation of a direct image by that kernel, which is the
one place the ideal is used, is Stacks 04CJ part (3) and holds with no hypothesis.  What the
reduction is needed for is the *identification of the source of the arrow with the conormal
module*, and that identification is already available at arbitrary immersion generality:
`AlgebraicGeometry.Space.conormalAlgebra_piece_one` reads `i^*𝓘_i` as the degree-one piece of the
conormal algebra of `i`, and `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` of
Stacks 09RR identifies that piece with the degree-one piece of the conormal algebra of the closed
factorization of Stacks 04CE, which is `AlgebraicGeometry.Space.immersionConormalModule`, the
conormal module `𝒞_{Z/X}` of Stacks 04CN for a general immersion.  The reduction is thus carried
once, inside that isomorphism, rather than again here.

## Main definitions

* `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion`: **Stacks 05ZA**, the canonical
  first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` induced by `d_{X/B}`, for an arbitrary immersion.

## Main results

* `Space.conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero`:
  **Stacks 05ZA**, the composite of the two arrows is zero, for an arbitrary immersion.

Exactness at the right term, for an arbitrary immersion, is
`AlgebraicGeometry.Space.epi_pullbackDifferentialsMap_of_isImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceEpiImmersion.lean`.

## Implementation notes

**The `eqToHom` is on an equality of sheaves of modules, not an isomorphism.**
`AlgebraicGeometry.Space.conormalAlgebra_piece_one` is an equality of objects of the category of
`𝒪_Z`-modules — the degree-`n` piece of the conormal algebra is *defined* as `i^*(𝓘ⁿ)` — so the
arrow out of the conormal module is the transport along it of the arrow out of `i^*𝓘_i`, and no
isomorphism is being inverted at that step.

## What is not proved

* **Exactness at the middle term is PROVED for this arrow**, the arrow of a general immersion,
  and this bullet is the record of the route.  It is
  `AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, carrying
  nothing beyond the immersion.  At a **subspace inclusion** the clause is proved directly, and
  not by transport from the scheme case: `AlgebraicGeometry.Space.conormalSequenceAt_exact` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean` derives it inside
  the small étale topos, from the descent of derivations along the structure map of a closed
  immersion.  The transport of that clause onto this arrow over the ambient open of Stacks 04CE
  goes through the comparison of the two first arrows,
  `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient`, and **not** through the arrow
  identification of the item below, which remains an independent gap.
* **What separates this sequence from its scheme-level counterpart is the arrow, not the
  modules.**  The module comparisons are all in place.  Stacks 04CS is proved:
  `AlgebraicGeometry.SmallEtale.differentialsIso` of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean` is the
  canonical isomorphism, and `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean` is that clause
  for a morphism of schemes of the site, read on the small étale site of the represented
  algebraic space; `AlgebraicGeometry.Space.sheafOfDifferentialsChartComparison` and
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing` carry what Stacks 04G9 and
  Stacks 04CV ask for, and the chart identification
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsEtaleLocalization.lean` is proved
  unconditionally.  So the scheme-level results about this sequence —
  `Stacks.ConormalSequenceRight.conormalShortComplex_exact` for Stacks 01UZ and
  `Stacks.ConormalSequenceSplit.conormalShortComplexSplitting_of_retraction` for Stacks 0474,
  which *includes* monomorphy of the first arrow — are not separated from the spaces-level
  statements by a missing comparison of modules.  What separates them is the **arrow**: nothing
  identifies this arrow, through
  `AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso` and those differentials
  comparisons, with `Stacks.ConormalSequenceRight.conormalDifferential`.  The *adjunction*
  half of that identification is proved, in two links, and is not part of this gap:
  `AlgebraicGeometry.SmallEtale.homEquiv_symm_associatedModuleBaseChange` and
  `AlgebraicGeometry.Space.homEquiv_symm_representedModulePullback` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleHomEquivTransport.lean` say that the
  transposition the scheme-level arrow is defined by and the transposition this arrow is defined
  by correspond, under `AlgebraicGeometry.SmallEtale.associatedModule` and under
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` respectively.  What is still
  owed is the ideal-sheaf and differentials inputs read at those statements.
* **This arrow is not identified with
  `AlgebraicGeometry.Space.conormalSequenceFirstMap`** at the inclusion of a closed subspace.
  The two sources agree — `AlgebraicGeometry.Space.conormalAlgebra_piece_one_eq_conormalModule`
  and `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` identify
  `AlgebraicGeometry.Space.immersionConormalModule` at a closed subspace inclusion with
  `AlgebraicGeometry.Space.conormalModule` — but no declaration composes them, which is a gap
  `ConormalModuleImmersionEtaleRestriction.lean` already records for the modules themselves, and
  the arrows inherit it.  The two arrows *are* the same at the level of the kernel ideal sheaf:
  `AlgebraicGeometry.Space.kernelConormalFirstMap_eq_conormalSequenceIdealPullbackMap`.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module of an
  immersion.
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE), the factorization of an
  immersion as a closed immersion followed by an open immersion.
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR), the conormal algebra of
  an immersion and its étale localization.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map that
  is the second arrow.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Z Bb : AlgebraicSpaces B S hS}

/-- **The conormal module of an immersion is `i^*𝓘_i`.**  For an immersion `i : Z ⟶ X` of
algebraic spaces, the conormal module `𝒞_{Z/X}` of Stacks 04CN is the inverse image along `i` of
the kernel ideal sheaf `𝓘_i = ker(i♯)`.

This is `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` of Stacks 09RR at degree
one — which is where the reduction of Stacks 04CE from an immersion to a closed immersion is
carried out — followed by `AlgebraicGeometry.Space.conormalAlgebra_piece_one`, the equality that
reads the degree-one piece of the conormal algebra as `i^*𝓘_i`.  It is the identification that
lets the first arrow be built at arbitrary immersion generality. -/
noncomputable def conormalModuleOfImmersionKernelPullbackIso (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    immersionConormalModule B S hS i hi ≅
      (modulePullback B S hS i).obj (kernelIdealSheaf B S hS i).toSheafOfModules :=
  (conormalAlgebraOfImmersionPieceIso B S hS i hi 1).symm ≪≫
    eqToIso (conormalAlgebra_piece_one B S hS i)

/-- **Stacks 05ZA, the canonical first arrow, for an arbitrary immersion.**  For an immersion
`i : Z ⟶ X` of algebraic spaces over `B` with structure morphism `b : X ⟶ B`, the arrow
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B}
```
induced by `d_{X/B}`.

It is `AlgebraicGeometry.Space.kernelConormalFirstMap`, the arrow built from the kernel ideal
sheaf of `i` by restricting `d_{X/B}` followed by the unit of `i^* ⊣ i_*` to it, read out of the
conormal module: `AlgebraicGeometry.Space.conormalAlgebra_piece_one` says the source of that
arrow *is* the degree-one piece of the conormal algebra of `i`, and
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` identifies that piece with the
conormal module of the immersion. -/
@[stacks 05ZA "the canonical first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` induced by `d_{X/B}`, for an \
arbitrary immersion"]
noncomputable def conormalSequenceFirstMapOfImmersion (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) :
    immersionConormalModule B S hS i hi ⟶
      (modulePullback B S hS i).obj (sheafOfDifferentials B S hS b) :=
  (conormalModuleOfImmersionKernelPullbackIso B S hS i hi).hom ≫
    kernelConormalFirstMap B S hS i b

/-- **Stacks 05ZA, the composite of the two arrows is zero, for an arbitrary immersion.**  The
first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` followed by the second arrow `i^*Ω_{X/B} ⟶ Ω_{Z/B}`, the
comparison map of Stacks 04CX for the square over the identity of `B`, is the zero morphism.

The first arrow factors through
`AlgebraicGeometry.Space.kernelConormalFirstMap`, for which the clause is
`AlgebraicGeometry.Space.kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero`. -/
@[stacks 05ZA "the composite `𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B}` of the two arrows is zero, for an \
arbitrary immersion"]
theorem conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) :
    conormalSequenceFirstMapOfImmersion B S hS i hi b ≫
      pullbackDifferentialsMap B S hS i b = 0 := by
  simp only [conormalSequenceFirstMapOfImmersion, Category.assoc,
    kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero, Limits.comp_zero]

end AlgebraicGeometry.Space

end
