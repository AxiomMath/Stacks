module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonDerivationSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiNaiveCotangentCompare

/-!
# Stacks 0D0X: `NL_{X/Y} = ε^*NL_{X₀/Y₀}` for a morphism of representable algebraic spaces

Let `S` be a scheme, `φ : U ⟶ V` a morphism of the big fppf site over `S`, `X₀`, `Y₀` the
underlying schemes, `f₀ : X₀ ⟶ Y₀` the underlying morphism of schemes, `X = h_U`, `Y = h_V` the
algebraic spaces they represent and `f = h_φ`.  Let `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X₀})` be
the comparison morphism of Stacks 08H7.

The canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}`
(`AlgebraicGeometry.Space.representedEpsilonNaiveCotangentMap`) is a quasi-isomorphism: on the
kernels of the differentials its adjunct is an isomorphism
(`AlgebraicGeometry.Space.isIso_representedEpsilonKernelHom_adjunct`), and on the cokernels too
(`AlgebraicGeometry.Space.isIso_representedEpsilonCokernelHom_adjunct`).  Both complexes vanish
outside degrees `-1` and `0`
(`AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentMap_of_isIso_homEquiv_symm`).

## Main results

* `AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentMap`: the canonical map
  `ε^*NL_{𝒪_{X₀}/f₀^{-1}𝒪_{Y₀}} ⟶ NL_{X/Y}` is a quasi-isomorphism.
* `AlgebraicGeometry.Space.quasiIso_representedEpsilonNaiveCotangentIdentification`: the same
  with source `ε^*` of the universe lift of `NL_{X₀/Y₀}` of Stacks 0D0H
  (`AlgebraicGeometry.Scheme.naiveCotangentComplex`) and target `NL_{X/Y}` of Stacks 0D0V
  (`AlgebraicGeometry.Space.naiveCotangentComplex`); this is Stacks 0D0X for `X = h_U` and
  `Y = h_V` on the nose, and
  `AlgebraicGeometry.Space.quasiIso_representableEpsilonNaiveCotangentIdentification` is the
  source's statement for arbitrary `X`, `Y` representable by schemes.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

attribute [local instance] abelianRepresentedSmallEtaleModules'

/-- **The canonical map `ε^*NL_{𝒪_{X₀}/f₀^{-1}𝒪_{Y₀}} ⟶ NL_{X/Y}` is a quasi-isomorphism.** -/
theorem quasiIso_representedEpsilonNaiveCotangentMap :
    QuasiIso (representedEpsilonNaiveCotangentMap B S hS φ) :=
  quasiIso_representedEpsilonNaiveCotangentMap_of_isIso_homEquiv_symm B S hS φ
    (isIso_representedEpsilonKernelHom_adjunct B S hS φ)
    (isIso_representedEpsilonCokernelHom_adjunct B S hS φ)

/-- **Stacks 0D0X for `X = h_U`, `Y = h_V` on the nose.**  For the morphism `f = h_φ : X ⟶ Y` of
the algebraic spaces represented by the objects `U`, `V` of the big fppf site over `S`, with
underlying schemes `X₀`, `Y₀` and `f₀ : X₀ ⟶ Y₀` the morphism of schemes underlying `φ`, the
canonical map `ε^*NL_{X₀/Y₀} ⟶ NL_{X/Y}` — the termwise pullback along `ε` of (the
universe lift of) the naive cotangent complex of `f₀` of Stacks 0D0H, followed by the map of
Stacks 08TX of the square of Stacks 08GH, into the naive cotangent complex of `f` of Stacks 0D0V —
is a quasi-isomorphism, so it identifies `NL_{X/Y}` with `ε^*NL_{X₀/Y₀}` in `D(𝒪_X)`.

The source's `X` and `Y` are arbitrary algebraic spaces representable by schemes, that is
isomorphic to `h_U` and `h_V`; that statement is
`AlgebraicGeometry.Space.quasiIso_representableEpsilonNaiveCotangentIdentification`, which
transports this one along the representing isomorphisms and carries the registration. -/
theorem quasiIso_representedEpsilonNaiveCotangentIdentification :
    QuasiIso ((((representedEpsilonModulePullback B S hS U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (representedZariskiNaiveCotangentComplexIso B S hS φ).inv) ≫
      representedEpsilonNaiveCotangentMap B S hS φ ≫
        eqToHom (representedSpaceNaiveCotangentComplex_eq B S hS φ).symm) := by
  have := quasiIso_representedEpsilonNaiveCotangentMap B S hS φ
  infer_instance

end AlgebraicGeometry.Space

end
