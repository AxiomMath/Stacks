module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonSource
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetMixedTensor

/-!
# The graded pieces of Section 0FMK against the target complex, degree by degree

[Stacks, Section 0FMK] identifies the `k`-th graded piece of the filtration of `Ω^•_{X/S}` by the
forms pulled back from `Y` with

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`.

The right-hand side is `Stacks.DeRhamSmooth.gradedTargetComplex`. **This file identifies the two
complexes term by term**: for every cut `k` and every `n = k + 1 + m`,

`(gr^kΩ^•_{X/S})^n  ≅  (f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^n`,

for `f` smooth. These isomorphisms are the components of the identification; the differentials
are not compared here.

Three identifications already available are composed, and nothing else enters:

* `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` reads the degree-`n` term of the graded
  piece of the *filtered complex* as the graded piece `gr^kΩ^n_{X/S}` of the *single sheaf*
  `Ω^n_{X/S}`. It assumes nothing of `f`.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison` is
  [Stacks, Section 0FMK] for that single sheaf: the comparison
  `f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}` is an isomorphism. This is where
  smoothness of `f` is used, and it is the only hypothesis of the result below.
* `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` is the underived half of
  [Stacks, Tag 08DE] at these binders, crossing from the tensor product over `𝒪_X` that the
  comparison's source is formed with to the tensor product over `f^{-1}𝒪_Y` that Section 50.12
  and `Stacks.DeRhamSmooth.gradedTargetComplex` are formed with.

## Main definitions

* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`: **the degreewise identification of
  [Stacks, Section 0FMK] against the target complex**, for `f` smooth and `n = k + 1 + m`.
* `Stacks.DeRhamSmooth.gradedTargetXIso`: the degree-`n` term of the target complex, for
  `n = k + j`, with its de Rham factor unwound to `Ω^j_{X/Y}` — including the cut `j = 0`,
  `n = k`, which the decomposition `n = k + 1 + m` does not reach.
* `Stacks.DeRhamSmooth.deRhamCochainXIso`: the degree-`j` term of the `ℤ`-indexed relative
  de Rham complex of `f` is `Ω^j_{X/Y}` read over `f^{-1}𝒪_Y`, for every `j : ℕ`.

## Implementation notes

The crossing to the coefficient ring `f^{-1}𝒪_Y` is not a convenience. The differential of
`Stacks.DeRhamSmooth.gradedTargetComplex` is `1 ⊗ d_{X/Y}`
(`Stacks.DeRhamSmooth.gradedTargetComplex_d`), and `d_{X/Y}` is `f^{-1}𝒪_Y`-linear and not
`𝒪_X`-linear: `Stacks.DeRhamDirectImage.deRhamCochainComplex` is a complex of
`f^{-1}𝒪_Y`-modules, and restriction of scalars along `f^{-1}𝒪_Y ⟶ 𝒪_X` — which is what
`Stacks.DeRhamDirectImage.pushforward_toInverseImageBase` says
`Stacks.DeRhamDirectImage.toInverseImageBase` pushes forward along — is faithful but not full, so
`d_{X/Y}` is not the pushforward of any morphism of `𝒪_X`-modules. Hence `1 ⊗ d_{X/Y}` cannot be
formed on the `𝒪_X`-tensor side at all, and in particular the naturality square
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso_naturality`, whose `φ` ranges over
morphisms of `𝒪_X`-modules, cannot be instantiated at a differential. The identification of the
graded pieces has to reach the `f^{-1}𝒪_Y` side before any differential is compared, which is
what the composite below does and what Section 50.12's choice of coefficient ring is for.

The degree-matching is `n = k + 1 + m` on the left, as
`Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` states it, and `n + -k` on the right, as the
shift `[-k]` of `Stacks.DeRhamSmooth.gradedTargetComplex` states it
(`Stacks.DeRhamSmooth.gradedTargetComplex_X`); `Stacks.DeRhamSmooth.gradedTargetXIso` reconciles
them, and also crosses the extension by zero that turns the `ℕ`-indexed de Rham complex of `f`
into the `ℤ`-indexed one.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.DeRhamSmooth

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degree-`j` term of `Ω^•_{X/Y}` as a `ℤ`-indexed complex is `Ω^j_{X/Y}`**, read over
`f^{-1}𝒪_Y`, for every `j : ℕ`. Two steps: the extension by zero that produces the `ℤ`-indexing
(`HomologicalComplex.extendXIso`), and
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_X`, which names the term of the `ℕ`-indexed complex
as the sheaf of relative `j`-forms restricted along `f^{-1}𝒪_Y ⟶ 𝒪_X`; that restriction of
scalars is the pushforward along `Stacks.DeRhamDirectImage.toInverseImageBase`
(`Stacks.DeRhamDirectImage.pushforward_toInverseImageBase`).

The degree is left as a natural number rather than fixed at `m + 1`, so that the identification
is available in degree `0` as well: that is the degree the de Rham factor of the target complex
of Section 0FMK has at the cut, where the decomposition `n = k + 1 + m` with `m : ℕ` does not
reach. Carrying the degree as a cast `(j : ℤ)` on both sides rather than as a free integer with
an equation is what keeps the identification free of a transport of the degree.

Costs 6,482 heartbeats against the default budget of 200,000. -/
def deRhamCochainXIso (j : ℕ) :
    (deRhamCochainComplex f).X ((j : ℕ) : ℤ) ≅
      (pushforward (toInverseImageBase f)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j : ℕ) : ℤ)) :=
  (AlgebraicGeometry.Scheme.Hom.deRhamComplex f).extendXIso ComplexShape.embeddingUpNat
      (i := j) (i' := ((j : ℕ) : ℤ)) rfl ≪≫
    eqToIso (AlgebraicGeometry.Scheme.Hom.deRhamComplex_X f j)

/-- **The degree-`n` term of the target complex of Section 0FMK is
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^j_{X/Y}`** for `n = k + j`, read over `(f ∘ g)^{-1}𝒪_S`.

The shift `[-k]` puts the de Rham factor in degree `n + -k`
(`Stacks.DeRhamSmooth.gradedTargetComplex_X`); this moves it to the degree `j` that
Section 0FMK's statement of the graded piece names, and unwinds it with
`Stacks.DeRhamSmooth.deRhamCochainXIso`. Nothing is assumed of `f`.

The complementary degree `j` and the total degree `n` are separate natural numbers tied by an
equation, rather than `j = m + 1` and `n = k + 1 + m`, so that the cut `j = 0`, `n = k` is
covered: `k + 0 = k`. The two spellings a consumer needs are then instances of one declaration —
`j = m + 1`, `n = k + 1 + m` for the degrees the decomposition reaches, and `j = 0`, `n = k`
for the cut — and in each the degrees appear as the casts the consumer already has, with the
arithmetic absorbed into the irrelevant proof argument instead of an `eqToIso`.

Costs 842 heartbeats against the default budget of 200,000. -/
def gradedTargetXIso (k j n : ℕ) (h : k + j = n) :
    (gradedTargetComplex f g k).X ((n : ℕ) : ℤ) ≅
      (coefficientRestriction f g).obj ((pulledBackTargetFormsTensor f g k).obj
        ((pushforward (toInverseImageBase f)).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j : ℕ) : ℤ)))) :=
  eqToIso (gradedTargetComplex_X f g k ((n : ℕ) : ℤ)) ≪≫
    (coefficientRestriction f g).mapIso ((pulledBackTargetFormsTensor f g k).mapIso
      ((deRhamCochainComplex f).XIsoOfEq
          (show ((n : ℕ) : ℤ) + -(k : ℤ) = ((j : ℕ) : ℤ) by omega) ≪≫
        deRhamCochainXIso f j))

/-- **Stacks Project, Section 0FMK, degreewise against the target complex.** For `f : X ⟶ Y`
smooth over a base `S`, a cut `k` and `n = k + 1 + m`, the degree-`n` term of the `k`-th graded
piece of the filtration of `Ω^•_{X/S}` by the forms pulled back from `Y` is the degree-`n` term
of `f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`:

`(gr^kΩ^•_{X/S})^n  ≅  (f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^n`.

These are the components of the identification of the graded pieces; the differentials are not
compared here, and the degree-`k` term — the one the decomposition `n = k + 1 + m` with `m : ℕ`
does not reach — is not covered.

At that degree the two sides have been separated into halves, both nonzero, and one of the two
is available. On the left `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` identifies
`(gr^kΩ^•_{X/S})^k` with the single sheaf `F^kΩ^k_{X/S}`, the image of
`⋀^k(f^*Ω_{Y/S}) ⟶ Ω^k_{X/S}`, the next step of the filtration having already vanished in that
degree. On the right `Stacks.DeRhamSmooth.gradedTargetXIso` at `j = 0`, `n = k` identifies
`(f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^k` with
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^0_{X/Y}`. What is missing between them is that
`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} ⋀^0Ω_{X/S} ⟶ Ω^k_{X/S}` is a monomorphism for `f` smooth, so that the
image is its source. **That monomorphism is available**, with nothing assumed beyond smoothness
of `f`: `AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsProdWedgeHom_of_eq_zero` of
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothWedgeDegreeZeroMono`. What is still owed at the cut
is the chain from it to the two halves — the image read as its source, carried across the
extension by zero and the restriction of scalars that separate the complex from the single sheaf,
and then the crossings of [Stacks, Tags 01CI and 08DE] at the complementary degree `0`.

Smoothness of `f` is the only hypothesis, and it enters once:
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison` is
[Stacks, Section 0FMK] for the single sheaf `Ω^n_{X/S}`, the statement that the comparison
`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}` is an isomorphism. The other two steps are
unconditional: `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` identifies the two models of
the graded piece, and `Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` crosses from
the tensor product over `𝒪_X` to the one over `f^{-1}𝒪_Y`.

Costs 18,978 heartbeats against the default budget of 200,000. -/
def gradedPieceXIsoGradedTargetX [Smooth f] (k m : ℕ) :
    (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).X
        ((k + 1 + m : ℕ) : ℤ) ≅
      (gradedTargetComplex f g k).X ((k + 1 + m : ℕ) : ℤ) :=
  haveI := AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison
    f g k m
  gradedPieceXIsoExteriorGraded f g k m ≪≫
    (pushforward (toInverseImageBase (f ≫ g))).mapIso
      (asIso (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison
        f g k m)).symm ≪≫
    (gradedSourceMixedTensorCoefficientIso f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((m + 1 : ℕ) : ℤ))).symm ≪≫
    (gradedTargetXIso f g k (m + 1) (k + 1 + m) (by omega)).symm

end Stacks.DeRhamSmooth

end
