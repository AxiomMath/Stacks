module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceClosedImmersionExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionFirstMap

/-!
# Exactness at the middle term for a general immersion, reduced to the kernel ideal sheaf

[Stacks Project, Tag 05ZA] attaches to an **immersion** `i : Z ⟶ X` of algebraic spaces over `B`
with structure morphism `b : X ⟶ Bb` the sequence
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0
```
Its first arrow is `AlgebraicGeometry.Space.conormalSequenceFirstMapOfImmersion`, the vanishing
of the composite and the right exactness are proved at immersion generality, and exactness at
the middle term is proved for a closed immersion in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceClosedImmersionExactness.lean`.

This file records that exactness at the middle term for a general immersion is **exactly**
exactness of the sequence written out of the kernel ideal sheaf
`𝓘_i = ker(i♯)`, with the conormal module of the immersion played by `i^*𝓘_i`.  Nothing about
the conormal module of [Stacks Project, Tag 04CN], the conormal algebra of
[Stacks Project, Tag 09RN] or the closed factorisation of [Stacks Project, Tag 04CE] is left in
the way: the first arrow of the tag is, by its own definition,
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` followed by
`AlgebraicGeometry.Space.kernelConormalFirstMap`, and the first factor is an **isomorphism**, so
the two short complexes differ by an isomorphism of their left-hand terms alone and have the same
exactness at the middle.

## Main results

* `AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact_of_kernelConormalFirstMap`:
  **exactness at the middle term of the conormal sequence of a general immersion follows from
  exactness of the sequence at the kernel ideal sheaf.**

## Where the kernel-ideal clause is proved

Exactness at the kernel ideal sheaf for a general immersion is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, as
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isImmersion`, and fed to the reduction
below as `AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact`.  The route the source
takes is to replace `X` by the open subspace of [Stacks Project, Tag 04CE], where the immersion
becomes closed, and every arrow of that replacement is available here:

* the factorisation itself is `AlgebraicGeometry.Space.immersionClosedFactorization` with
  `AlgebraicGeometry.Space.immersionClosedFactorization_comp_immersionAmbientInclusion`, the
  ambient inclusion is étale by
  `AlgebraicGeometry.Space.isEtale_immersionAmbientInclusion`, the closed factorisation is a
  closed immersion by `AlgebraicGeometry.Space.isClosedImmersion_boundaryComplementLift`, and
  the square with `𝟙 Z` on top is cartesian by
  `AlgebraicGeometry.Space.isPullback_immersionClosedFactorization`;
* the closed case at the ambient open is
  `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion`, which asks for a
  closed immersion only and no closed subspace;
* the left-hand terms already agree: the degree-one piece of the conormal algebra of the
  factorisation **is** the inverse image of the kernel ideal sheaf of the factorisation, by
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersion_piece` and
  `AlgebraicGeometry.Space.kernelIdealSheafZPow_one`, and it is identified with `i^*𝓘_i` by
  `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` of [Stacks Project, Tag 09RR];
* the middle terms are compared by `AlgebraicGeometry.Space.modulePullbackCompIso` of
  [Stacks Project, Tag 03LU] with the étale-source localisation
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` of
  [Stacks Project, Tag 04CU];
* the **second** arrows then agree by the uniqueness clause of [Stacks Project, Tag 04CX],
  `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`, because both composites are
  comparison maps for the same square: the étale-localisation map is one by
  `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`, the second
  arrow is one by
  `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_pullbackDifferentialsMap`, and composites
  of such maps are such maps by
  `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp`.

* the **first** arrows agree by
  `AlgebraicGeometry.Space.kernelConormalFirstMap_etaleAmbient_compPullbackMap` of
  `ConormalSequenceImmersionFirstMapComparison.lean`: the comparison of inverse images of
  [Stacks Project, Tag 03LU] together with the comparison
  `AlgebraicGeometry.Space.kernelIdealCompPullbackMap` of the kernel ideal sheaves, and together
  with the étale-source localisation on the other side, intertwine
  `AlgebraicGeometry.Space.kernelConormalFirstMap` at `i₀ ≫ ι` with the same map at `i₀`.  It
  carries no hypothesis.  The form at an arbitrary comparison map of [Stacks Project, Tag 04CX]
  is `AlgebraicGeometry.Space.kernelConormalFirstMap_compPullbackMap`, and the form at an
  arbitrary pinned comparison of the kernel ideal sheaves is
  `AlgebraicGeometry.Space.kernelConormalFirstMap_comp`.

The assembly itself — the comparison of the two short complexes as an isomorphism, whose
left-hand leg is invertible because the comparison of inverse images is and because the
comparison of the kernel ideal sheaves is the degree-one case of
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_hom_app_kernelIdealSheafZPow` —
is carried out in `ConormalSequenceImmersionKernelExactness.lean`.  Exactness transfers from
`AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion` at the factorisation
by `CategoryTheory.ShortComplex.exact_iff_of_iso`, and feeds
`AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact_of_kernelConormalFirstMap` below.

No `@[stacks]` attribute is claimed here: the reduction below is a step of the tag's proof and
not a clause of it, and the clauses themselves are registered where they are proved.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Bb Z : AlgebraicSpaces B S hS}

variable (i : Z ⟶ X) (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb)

include hi in
/-- **Exactness at the middle term of the conormal sequence of [Stacks Project, Tag 05ZA] for a
general immersion is exactness of the sequence at the kernel ideal sheaf.**  The first arrow of
the tag is `AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` — an
isomorphism — followed by `AlgebraicGeometry.Space.kernelConormalFirstMap`, so the two short
complexes differ by an isomorphism of their left-hand terms and nothing else.

This is what reduces the remaining clause of the tag to a statement in which the conormal
module, the conormal algebra and the closed factorisation of [Stacks Project, Tag 04CE] play no
part. -/
theorem conormalSequenceOfImmersion_exact_of_kernelConormalFirstMap
    (hex : (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i b)).Exact) :
    (ShortComplex.mk _ _
      (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero
        B S hS i hi b)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).mpr hex
  refine ShortComplex.isoMk
    (conormalModuleOfImmersionKernelPullbackIso B S hS i hi) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [conormalSequenceFirstMapOfImmersion]
  · simp

end AlgebraicGeometry.Space

end
