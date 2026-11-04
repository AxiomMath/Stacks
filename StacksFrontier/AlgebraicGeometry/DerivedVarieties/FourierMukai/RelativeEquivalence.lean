module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The Fourier-Mukai kernel of a relative equivalence

Let `S` be a scheme and let `X ⟶ S` and `Y ⟶ S` be morphisms of schemes. A perfect object
`K ∈ D_perf(𝒪_{X ×_S Y})` is *the Fourier-Mukai kernel of a relative equivalence from `X` to `Y`
over `S`* when there is a perfect object `K' ∈ D_perf(𝒪_{Y ×_S X})` with

`Δ_{X/S,*}𝒪_X ≅ R pr_{13,*}(L pr_{12}^*K ⊗^𝐋_{𝒪_{X ×_S Y ×_S X}} L pr_{23}^*K')` in
`D(𝒪_{X ×_S X})`, and
`Δ_{Y/S,*}𝒪_Y ≅ R pr_{13,*}(L pr_{12}^*K' ⊗^𝐋_{𝒪_{Y ×_S X ×_S Y}} L pr_{23}^*K)` in
`D(𝒪_{Y ×_S Y})`.

This is [Stacks, Tag 0G0I]. Both right-hand sides are the convolution kernel of
[Stacks, Tag 0FYS], `AlgebraicGeometry.fourierMukaiConvolution`, at the two instantiations
`(X, Y, X)` and `(Y, X, Y)` of its triple of schemes over `S`; both left-hand sides are the
diagonal kernel of [Stacks, Tag 0FYV], `AlgebraicGeometry.diagonalKernel`. So the definition
below is assembled from those two, with nothing reinvented.

## Main definitions

* `AlgebraicGeometry.IsRelativeEquivalenceKernel` — **[Stacks, Tag 0G0I]**: the predicate
  defining the Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S`.

## Main results

* `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_inverse` — the object `K'` whose
  existence the definition asserts is itself the Fourier-Mukai kernel of a relative equivalence,
  from `Y` to `X` over `S`. This is the source's closing remark that the isomorphism class of
  `K` is an *invertible* arrow of the category of Section 0G0F.

## Implementation notes

*Where `K'` lives.* The source's displayed text puts `K'` in `D_perf(𝒪_{X ×_S Y})`, but the
first displayed isomorphism applies `L pr_{23}^*` to it along
`pr_{23} : X ×_S Y ×_S X ⟶ Y ×_S X`, so `K'` must be an object on `Y ×_S X`; the source's own
proof of [Stacks, Tag 0G0K] writes "Let `K' ∈ D_perf(𝒪_{Y ×_S X})`". The spelling on `Y ×_S X`
is the one taken here. This is the source's intent, not a change of statement: with `K` on
`X ×_S Y` and `K'` on `Y ×_S X` the two convolutions are the two composites of the arrows that
`K` and `K'` represent, which is what the definition is for.

*Perfectness.* `D_perf(𝒪_Z)` for a scheme `Z` is
`AlgebraicGeometry.Scheme.PerfectDerivedCategory Z`, the full subcategory of `D(𝒪_Z)` cut out by
`Stacks.Cohomology.PerfectComplexes.IsPerfect` ([Stacks, Tag 08CM]) read at
`Z.toRingedSpace`. The predicate below is stated on an object of `D(𝒪_{X ×_S Y})` together with
that condition, rather than on an object of the full subcategory, because the two convolutions
and the two diagonal kernels it compares all live in `D(𝒪_{X ×_S X})` and `D(𝒪_{Y ×_S Y})`; so
`IsRelativeEquivalenceKernel f g K` asserts, as its first conjunct, exactly that `K` is an
object of `D_perf(𝒪_{X ×_S Y})`, and nothing of the source's `D_perf` is dropped.

*The source's ambient hypotheses on `X ⟶ S` and `Y ⟶ S` are not baked in.* The source's
Definition 0G0I is stated for `X ⟶ S` and `Y ⟶ S` **smooth and proper**. Those hypotheses play
no part in the definition itself — the two convolutions and the two diagonal kernels exist for
arbitrary morphisms — so the predicate below is stated for arbitrary `f` and `g`. It is
therefore a generalization of the source's notion, not a weakening of it: at smooth proper
`f` and `g` it says exactly what the source says. Every consumer that needs smoothness or
properness (the source's Lemmas 0G0J, 0G0K, 0G0R) must carry those hypotheses itself.

*An isomorphism, not an equality.* The source writes `≅` on both displayed lines and the
objects compared are built from derived functors, determined only up to canonical isomorphism;
so each clause is `Nonempty (_ ≅ _)`, the assertion that an isomorphism exists, which is what
`≅` abbreviates inside a `Prop`.

*What is not here.* The source's Lemmas 0G0J (the two Fourier-Mukai functors attached to such a
`K` are equivalences) and 0G0K (stability under base change `S₁ ⟶ S`) are **not** formalized
below. Nothing below asserts or hypothesises either lemma. Example 0FYV's assertion that
`Φ_{𝒪_Δ}` is the identity, which 0G0J rests on, *is* available —
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso`, in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernelIdentity.lean`,
proved from the general projection formula [Stacks, Tag 0B55] at the closed immersion `Δ`; what
0G0J needs beyond it is the composition formula of [Stacks, Tag 0FYS], which this library
carries only on the hypotheses `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` and
`AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent`.

## References

* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the convolution
-- kernel of [Stacks, Tag 0FYS] and the diagonal kernel of [Stacks, Tag 0FYV] are read at, over
-- the locally small model arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **[Stacks, Tag 0G0I]**: `K` is *the Fourier-Mukai kernel of a relative equivalence from `X`
to `Y` over `S`*.

Explicitly: `K` is a perfect object of `D(𝒪_{X ×_S Y})`, and there is a perfect object `K'` of
`D(𝒪_{Y ×_S X})` such that the two convolutions of [Stacks, Tag 0FYS],

`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')` on `X ×_S X` and
`R pr_{13,*}(L pr_{12}^*K' ⊗^𝐋 L pr_{23}^*K)` on `Y ×_S Y`,

are isomorphic to the diagonal kernels `Δ_{X/S,*}𝒪_X` and `Δ_{Y/S,*}𝒪_Y` of
[Stacks, Tag 0FYV] respectively. In other words the isomorphism class of `K` is an invertible
arrow of the category of the source's Section 0G0F.

The source states this for smooth proper `f` and `g`; those hypotheses are not used by the
definition and are not imposed here, so this is a generalization — see the module docstring. -/
@[stacks 0G0I "the Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S`, as \
the predicate on a perfect object of `D(𝒪_{X ×_S Y})` asserting the existence of a perfect `K'` \
on `Y ×_S X` with the two convolution isomorphisms; stated for arbitrary `f` and `g` rather \
than only smooth proper ones"]
def IsRelativeEquivalenceKernel (K : DerivedCategory (Limits.pullback f g).Modules) : Prop :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Limits.pullback f g).toRingedSpace) K ∧
    ∃ K' : DerivedCategory (Limits.pullback g f).Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := (Limits.pullback g f).toRingedSpace) K' ∧
        Nonempty (diagonalKernel f ≅ fourierMukaiConvolution f g f K K') ∧
          Nonempty (diagonalKernel g ≅ fourierMukaiConvolution g f g K' K)

/-- **The inverse of a relative equivalence kernel is one.** If `K` is the Fourier-Mukai kernel
of a relative equivalence from `X` to `Y` over `S`, then the object `K'` whose existence
[Stacks, Tag 0G0I] asserts is the Fourier-Mukai kernel of a relative equivalence from `Y` to `X`
over `S`, with `K` itself as its partner. This is the source's closing remark that the
isomorphism class of `K` defines an *invertible* arrow. -/
theorem exists_isRelativeEquivalenceKernel_inverse
    {K : DerivedCategory (Limits.pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    ∃ K' : DerivedCategory (Limits.pullback g f).Modules,
      IsRelativeEquivalenceKernel g f K' ∧
        Nonempty (diagonalKernel f ≅ fourierMukaiConvolution f g f K K') ∧
          Nonempty (diagonalKernel g ≅ fourierMukaiConvolution g f g K' K) := by
  obtain ⟨hKperf, K', hK'perf, h₁, h₂⟩ := hK
  exact ⟨K', ⟨hK'perf, K, hKperf, h₂, h₁⟩, h₁, h₂⟩

end AlgebraicGeometry

end
