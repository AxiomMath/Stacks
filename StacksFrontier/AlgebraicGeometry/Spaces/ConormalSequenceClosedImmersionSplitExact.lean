module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceClosedImmersionExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitting

/-!
# Split exactness of the conormal sequence at the kernel ideal sheaf of a closed immersion

Let `j : Zs ⟶ X` be a closed immersion of algebraic spaces over an algebraic space `Bb`, with
structure morphism `b : X ⟶ Bb`, and let `g : X ⟶ Zs` be a left inverse of `j` over `Bb`.
Stacks 05ZB says the conormal sequence of Stacks 05ZA is split exact.

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitExact.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceSplitMono.lean` prove this for the
inclusion of a bundled `AlgebraicGeometry.Space.ClosedSubspaces`.  This file carries the two
clauses that are available without that binder over to **an arbitrary closed immersion, with the
sequence read off the kernel ideal sheaf** — the shape the general case of the tag needs, since
the closed immersion that Stacks 04CE factors an immersion through is not the inclusion of a
bundled closed subspace.

## Main results

* `AlgebraicGeometry.Space.conormalSequenceKernel_splitExact_of_isClosedImmersion`: the sequence
  `j^*𝓘_j ⟶ j^*Ω_{X/Bb} ⟶ Ω_{Zs/Bb}` is exact at its middle term and its second arrow is a split
  epimorphism.  Both clauses carry nothing beyond the closed immersion and the left inverse:
  exactness is `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion` and
  splitness is `AlgebraicGeometry.Space.isSplitEpi_pullbackDifferentialsMap_of_retraction`,
  which is stated at an arbitrary morphism already.
* `Space.nonempty_conormalSequenceKernel_splitting_iff_mono_of_isClosedImmersion`:
  under those hypotheses the sequence admits a `CategoryTheory.ShortComplex.Splitting` **if and
  only if** its first arrow `AlgebraicGeometry.Space.kernelConormalFirstMap` is a monomorphism.

## Where the injectivity clause comes from

**Injectivity of the first arrow holds at this generality**, as
`AlgebraicGeometry.Space.mono_kernelConormalFirstMap` in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionSplitMono.lean`: the derivation
of Stacks 02HP is run on the split surjection `f_*f⁻¹𝒪_Y ⟶ f_*𝒪_X` with the morphism a free
variable and the kernel ideal sheaf of Stacks 03MB in place of the defining ideal sheaf of a
bundled subspace, and the invertibility of the counit of a closed immersion is what identifies
the kernel of that surjection with `f_*f⁻¹𝓘_f`.

Fed through the equivalence below that gives
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting`, Stacks 05ZB's global clause
at an arbitrary closed immersion, and with
`AlgebraicGeometry.Space.isSplitEpi_map_pullbackDifferentialsMap_of_etale` — already stated at
an arbitrary morphism — the étale-local clause
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_of_etale`.  The generality the
tag is stated at, an arbitrary immersion, is reached from those two by the open-subspace reduction
of Stacks 04CE in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionSplitExact.lean`, which is where
the tag is registered.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the conormal sequence.
* [Stacks Project, Tag 010G](https://stacks.math.columbia.edu/tag/010G), the splitting of a short
  exact sequence from a section and a monomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Zs Bb : AlgebraicSpaces B S hS}

/-- **Stacks 05ZB's exactness and splitness clauses, at an arbitrary closed immersion.**  Let
`j : Zs ⟶ X` be a closed immersion of algebraic spaces over `Bb` with structure morphism
`b : X ⟶ Bb`, and let `g : X ⟶ Zs` be a left inverse of `j` over `Bb`.  Then the conormal
sequence of
Stacks 05ZA read off the kernel ideal sheaf
```
  j^*𝓘_j ⟶ j^*Ω_{X/Bb} ⟶ Ω_{Zs/Bb} ⟶ 0
```
is exact at its middle term and its second arrow is a split epimorphism, hence an epimorphism,
which is exactness at the right term.  The vanishing of the composite is the short complex
itself.

**No closed subspace of `X` is assumed and nothing is carried beyond the left inverse.**
Injectivity of the first arrow is not among the clauses; see the module documentation and the
equivalence
`AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_iff_mono_of_isClosedImmersion`
below. -/
theorem conormalSequenceKernel_splitExact_of_isClosedImmersion (j : Zs ⟶ X)
    (hj : IsClosedImmersion B S hS j.hom) (b : X ⟶ Bb) (g : X ⟶ Zs) (hg : j ≫ g = 𝟙 Zs)
    (hgb : g ≫ j ≫ b = b) :
    (ShortComplex.mk _ _
          (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS j b)).Exact ∧
      IsSplitEpi (pullbackDifferentialsMap B S hS j b) :=
  ⟨conormalSequenceKernel_exact_of_isClosedImmersion B S hS j hj b,
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS j b g hg hgb⟩

/-- **What is left of Stacks 05ZB at an arbitrary closed immersion: the sequence is split exact
in Mathlib's full sense exactly when its first arrow is injective.**

Under the hypotheses of
`AlgebraicGeometry.Space.conormalSequenceKernel_splitExact_of_isClosedImmersion` the conormal
sequence of Stacks 05ZA at the kernel ideal sheaf admits a
`CategoryTheory.ShortComplex.Splitting` — a retraction `r` of the first arrow and a section `s`
of the second with `r ≫ f + g ≫ s = 𝟙` — **if and only if** its first arrow is a monomorphism.

Both directions carry nothing beyond those hypotheses.  Forwards is
`CategoryTheory.ShortComplex.Splitting.mono_f`; backwards is
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection` of Stacks 010G, fed with the exactness
of `AlgebraicGeometry.Space.conormalSequenceKernel_exact_of_isClosedImmersion` and the section
underlying the split epimorphism.

This is the arbitrary-closed-immersion counterpart of
`AlgebraicGeometry.Space.nonempty_conormalSequenceAt_splitting_iff_mono`, and the hypothesis is
satisfiable for the same reason: at `Zs := X`, `j := 𝟙 X` the kernel ideal sheaf is zero and the
first arrow is a monomorphism between zero objects. -/
theorem nonempty_conormalSequenceKernel_splitting_iff_mono_of_isClosedImmersion (j : Zs ⟶ X)
    (hj : IsClosedImmersion B S hS j.hom) (b : X ⟶ Bb) (g : X ⟶ Zs) (hg : j ≫ g = 𝟙 Zs)
    (hgb : g ≫ j ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
          (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS j b)).Splitting ↔
      Mono (kernelConormalFirstMap B S hS j b) := by
  have : IsSplitEpi (pullbackDifferentialsMap B S hS j b) :=
    isSplitEpi_pullbackDifferentialsMap_of_retraction B S hS j b g hg hgb
  refine ⟨fun h ↦ h.some.mono_f, fun hmono ↦ ⟨ShortComplex.Splitting.ofExactOfSection _
    (conormalSequenceKernel_exact_of_isClosedImmersion B S hS j hj b)
    (section_ (pullbackDifferentialsMap B S hS j b))
    (IsSplitEpi.id (pullbackDifferentialsMap B S hS j b)) hmono⟩⟩

end AlgebraicGeometry.Space

end
