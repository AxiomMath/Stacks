module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent

/-!
# Principalizing an ideal supported at regular points of a surface

Let `X` be a scheme and `T` a finite set of closed points of `X` whose local rings are regular of
dimension two. A quasi-coherent sheaf of ideals `𝓘` with `𝒪_X / 𝓘` supported on `T` becomes an
invertible sheaf of ideals after a finite sequence of blowups at closed points lying over `T`.
This is [Stacks, Tag 0AHH].

## Main results

* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing` — [Stacks, Tag 0AHH].

## Implementation notes

The induction on the total colength is
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_isEffectiveCartierDivisor`, which takes the
inductive step as its hypothesis `descent`; that step is
`Stacks.ResolutionOfSurfaces.pointBlowupDescent`, which rests on [Stacks, Tag 0AGT] for the local
rings at the points of `T` and on flat base change ([Stacks, Tag 0805]).

A quasi-coherent sheaf of ideals is a `Scheme.IdealSheafData`, whose sections on affine opens
are ideals compatible with localization; its support is the support of `𝒪_X / 𝓘`, and "invertible
ideal sheaf" is `Stacks.Divisors.IsEffectiveCartierDivisor`. A sequence
`Xₙ → ⋯ → X₁ → X₀ = X` of blowups at closed points lying over `T` is a
`Stacks.ResolutionOfSurfaces.PointBlowupChain`, indexed by its composite `Xₙ ⟶ X`, and
`𝓘𝒪_{Xₙ}` is the inverse image `𝓘.comap` along it.

The source assumes `X` Noetherian. The argument does not use it: the only finiteness it needs is
that the local rings at the points of `T` are Noetherian, which regularity provides, so the
statement here is for an arbitrary scheme.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ResolutionOfSurfaces

/-- **Stacks Project, Tag 0AHH.** Let `X` be a scheme and `T` a finite set of closed points `x`
of `X` such that `𝒪_{X,x}` is regular of dimension two for `x ∈ T`. Let `𝓘` be a quasi-coherent
sheaf of ideals such that `𝒪_X / 𝓘` is supported on `T`. Then there is a sequence
`Xₙ → Xₙ₋₁ → ⋯ → X₁ → X₀ = X` in which each `Xᵢ₊₁ → Xᵢ` is the blowing up of `Xᵢ` at a closed
point lying over a point of `T`, such that `𝓘𝒪_{Xₙ}` is an invertible ideal sheaf.

The source assumes `X` Noetherian; the statement holds without it, since the finiteness the
argument uses is that of the local rings at the points of `T`, which regularity provides.

The proof is the source's induction on the total colength `Σ length(𝒪_{X,x} / 𝓘_x)`
(`Stacks.ResolutionOfSurfaces.totalColength`), run by
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_isEffectiveCartierDivisor`. Its inductive
step is `Stacks.ResolutionOfSurfaces.pointBlowupDescent`: blowing up a point of the support writes
the pulled-back ideal as `𝒪(-dE) · 𝓘'` with `𝓘'` of strictly smaller total colength, by
[Stacks, Tag 0AGT] and flat base change ([Stacks, Tag 0805]). The resulting ideal is invertible
as a product of the pulled-back exceptional divisor
(`PointBlowupChain.isEffectiveCartierDivisor_comap`, [Stacks, Tag 0809]) and an invertible ideal
([Stacks, Tag 01WU]). -/
@[stacks 0AHH "a quasi-coherent ideal sheaf whose quotient is supported on a finite set of \
closed points with regular two-dimensional local rings becomes invertible after a finite \
sequence of blowups at closed points lying over that set; stated for an arbitrary scheme"]
public theorem exists_pointBlowupChain_principalizing {X : Scheme.{u}} (T : Finset X)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (I : X.IdealSheafData) (hI : (I.support : Set X) ⊆ (T : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (T : Set X) Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) :=
  exists_pointBlowupChain_isEffectiveCartierDivisor pointBlowupDescent T hclosed hregular hdim I hI

end Stacks.ResolutionOfSurfaces

end
