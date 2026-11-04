module

public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LocalizedBase
public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.LiftingCriterion
public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra.PowerSeriesCase

/-!
# Smooth complete local algebras (Stacks 0DYL)

Let `R` be a Noetherian complete local `Λ`-algebra with residue field `k`. This file collects
the parts `CompleteLocalAlgebra/LocalizedBase`, `CompleteLocalAlgebra/LiftingCriterion` and
`CompleteLocalAlgebra/PowerSeriesCase`, which prove that smoothness of the restricted
representable category of `R` over `𝒞_Λ` is equivalent to formal smoothness of `Λ → R` in the
`m_R`-adic topology, and to flatness of `Λ → R` together with geometric regularity —
equivalently adic formal smoothness — of the special fibre over the image field
`k' = Λ / ker(Λ → k)`. When the base is classical these conditions say that `R` is a formal
power series algebra over `Λ`.

## Main definitions

* `Deformation.restrictedCoyonedaProjection` is the structure functor of the restricted
  representable category of `R`, as a morphism over `𝒞_Λ`.

## Main results

* `Deformation.smooth_formallySmooth_flat_specialFibre_tfae`: **Stacks 0DYL**, conditions
  (1)–(4).
* `Deformation.smooth_formallySmooth_flat_specialFibre_powerSeries_tfae`: **Stacks 0DYL**,
  condition (5) in the classical case.

## Implementation notes

Condition (1) of the source, that the underlined functor of `R` restricted to `𝒞_Λ` be
smooth, is smoothness of `restrictedCoyonedaProjection R`: the projection of
`restrictedRepresentable R` to the base category regarded as a based category over itself.
This is `Deformation.IsSmooth`, so (1) is literally the source's condition.

The special fibre is taken over the image field `k' = Λ / ker(Λ → k)`, not over `k`: the
source's `𝒞_Λ` only fixes `k` as the residue field of its objects, and `Λ` itself need not be
local. Accordingly the proof passes through the localization `T = Λ_p` at
`p = ker(Λ → k)`, whose residue field is `k'`: formal smoothness of `Λ → R` in the adic
topology is unchanged by inverting the elements outside `p`, because those already become
units in `R`, and `R ⊗[Λ] k'` is the special fibre of `T → R`. The three conditions over `T`
are then Stacks 07NQ, `flat_geometricallyRegular_specialFiber_formallySmooth_tfae`.

The equivalence of (1) with (2) is the lifting criterion: smoothness need only be tested on
small extensions (Stacks 06HH), and a lifting problem for the restricted representable
functor over a small extension is exactly the lifting problem defining adic formal smoothness
against a square-zero quotient of an Artinian local algebra. The passage from arbitrary
square-zero test objects to the Artinian ones in `𝒞_Λ` replaces a test algebra by its image,
which is small.

Condition (5) is Stacks 06HL applied to `Λ → R` viewed in the completed base category: in the
classical case `Λ` itself is an object of that category, so smoothness of the projection is
smoothness of the induced morphism of restricted representable categories, which 06HL
identifies with `R` being a power series algebra over `Λ`.

## References

* [Stacks Project, Tag 0DYL](https://stacks.math.columbia.edu/tag/0DYL)
-/
