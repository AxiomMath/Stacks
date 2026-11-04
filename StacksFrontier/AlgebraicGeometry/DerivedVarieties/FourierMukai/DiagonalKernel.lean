module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.QuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal kernel

Let `f : X ⟶ S` be a morphism of schemes with diagonal `Δ = Δ_{X/S} : X ⟶ X ×_S X`. The
*diagonal kernel* is

`𝒪_Δ = RΔ_*𝒪_X ∈ D(𝒪_{X ×_S X})`,

the derived direct image along `Δ` of the structure sheaf of `X` placed in degree `0`. For `f`
separated it is the Fourier-Mukai kernel of the identity functor on `D(𝒪_X)`; that is
[Stacks, Tag 0FYV], whose object this is.

## Main definitions

* `AlgebraicGeometry.diagonalKernel` — the object `𝒪_Δ = RΔ_{X/S,*}𝒪_X` of `D(𝒪_{X ×_S X})`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_diagonalKernel` — for `f` separated, every
  cohomology sheaf of `𝒪_Δ` is quasi-coherent.

See also `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`, in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernelIdentity.lean`, for
the assertion of 0FYV that `Φ_{𝒪_Δ}` is the identity functor of `D(𝒪_X)`.

## Implementation notes

*What of [Stacks, Tag 0FYV] is here, and what is not.* The source's Example 0FYV asserts four
things about a separated `f : X ⟶ S`:

1. the diagonal `Δ : X ⟶ X ×_S X` is a closed immersion;
2. `𝒪_Δ = Δ_*𝒪_X = RΔ_*𝒪_X` is a quasi-coherent `𝒪_{X ×_S X}`-module;
3. it is of finite type and flat over `X` under either projection;
4. the Fourier-Mukai functor `Φ_{𝒪_Δ}` is the identity on `D(𝒪_X)`.

Of these, (1) is Mathlib's `AlgebraicGeometry.IsSeparated.isClosedImmersion_diagonal`, which is
the field of the class `AlgebraicGeometry.IsSeparated` and is therefore available as an instance
wherever `f` is separated; it is used below, not restated. Item (2) is
`isQuasicoherent_homology_diagonalKernel`, proved here. Item (4) is
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso`, proved in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernelIdentity.lean`, which
needs the Fourier-Mukai functor of [Stacks, Tag 0FYQ] and therefore sits above this file; the
middle equality of the source's chain is Cohomology, Lemma 0B55, which this library has for an
arbitrary morphism of ringed spaces whose base map is a closed embedding
(`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`),
and the diagonal of a separated morphism is such a morphism. Item (3) — that `𝒪_Δ` is of finite
type and flat over `X` under either projection — is **not formalized**: no clause below or in
`DiagonalKernelIdentity.lean` asserts it, and none hypothesises it.

*The derived, not the ordinary, direct image.* `diagonalKernel` is `RΔ_*` of `𝒪_X[0]`, which is
the right-hand term of the source's own chain of identifications `𝒪_Δ = Δ_*𝒪_X = RΔ_*𝒪_X`. The
identification of `RΔ_*𝒪_X` with the ordinary `Δ_*𝒪_X` — which holds because `Δ` is a closed
immersion, so `Δ_*` is exact on quasi-coherent modules — is *not* formalized here, and nothing
below uses it. Taking the derived spelling is what makes the object available with no hypothesis
on `f` at all, and it is the spelling that the convolution formulas of [Stacks, Tag 0FYS] and
the definition of a relative equivalence, [Stacks, Tag 0G0I], compare against.

*No hypothesis on `f` for the object itself.* `RΔ_*𝒪_X` makes sense for an arbitrary morphism of
schemes, so `diagonalKernel` carries no hypothesis. Separatedness enters only where the source
uses it, namely in the quasi-coherence clause, where `Δ` has to be quasi-compact and
quasi-separated; both follow from `[IsSeparated f]`, the first because `Δ` is then a closed
immersion hence affine, the second because `Δ` is a split mono hence separated.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Basic.lean`, everything is read at
`CategoryTheory.HasDerivedCategory.standard`, given a raised local instance priority so that the
locally small model arriving with the imports does not compete; the quasi-coherence input
[Stacks, Tag 08D5] is stated at that model.

## References

* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, which the quasi-coherence
-- of the derived direct image is stated at, over the locally small model arriving with the
-- imports.
attribute [local instance 100000] HasDerivedCategory.standard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- **The diagonal kernel of [Stacks, Tag 0FYV]**: the object

`𝒪_Δ = RΔ_{X/S,*}𝒪_X ∈ D(𝒪_{X ×_S X})`,

the derived direct image along the diagonal `Δ : X ⟶ X ×_S X` of the structure sheaf of `X`
placed in degree `0`.

This is the object the source's Example 0FYV introduces, and the one against which the
convolution of [Stacks, Tag 0FYS] is compared in the definition of a relative equivalence,
[Stacks, Tag 0G0I]. The source writes it as `Δ_*𝒪_X` and identifies that with `RΔ_*𝒪_X` using
that `Δ` is a closed immersion for separated `f`; the derived spelling is taken here, so no
hypothesis on `f` is needed, and the identification with the ordinary direct image is not
formalized. That `Φ_{𝒪_Δ}` is the identity is
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso`; the assertion of 0FYV that `𝒪_Δ` is of
finite type and flat over either projection is not formalized — see the module docstring. -/
@[stacks 0FYV "the diagonal kernel `𝒪_Δ = RΔ_{X/S,*}𝒪_X` as an object of `D(𝒪_{X ×_S X})`; \
the clause that it is of finite type and flat over either projection is not covered, and the \
clause that `Φ_{𝒪_Δ}` is the identity functor of `D(𝒪_X)` is carried by \
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso` in \
`FourierMukai/DiagonalKernelIdentity.lean`"]
def diagonalKernel : DerivedCategory (Limits.pullback f f).Modules :=
  (derivedPushforwardModules (Limits.pullback.diagonal f)).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))

/-- **The diagonal kernel of a separated morphism has quasi-coherent cohomology**, which is the
assertion of [Stacks, Tag 0FYV] that `𝒪_Δ` is a quasi-coherent `𝒪_{X ×_S X}`-module.

The structure sheaf of `X` is quasi-coherent, and the derived direct image along a quasi-compact
quasi-separated morphism preserves quasi-coherence of cohomology ([Stacks, Tag 08D5] part (1),
here in the single-degree case). The diagonal of a separated morphism is a closed immersion,
hence affine, hence quasi-compact; and it is a split mono, hence separated, hence
quasi-separated. -/
@[stacks 0FYV "quasi-coherence of the diagonal kernel `𝒪_Δ`, for `f` separated"]
theorem isQuasicoherent_homology_diagonalKernel [IsSeparated f] (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules i).obj
      (diagonalKernel f)).IsQuasicoherent :=
  isQuasicoherent_homology_derivedPushforward_singleFunctor (Limits.pullback.diagonal f)
    (SheafOfModules.unit X.ringCatSheaf) inferInstance 0 i

end AlgebraicGeometry

end
