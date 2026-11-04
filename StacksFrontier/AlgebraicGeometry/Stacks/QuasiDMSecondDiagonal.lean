module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# Quasi-DM morphisms and the first two diagonals

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with no representability assumption. Part (3) of Stacks 04Z0 says that
`f` is quasi-DM, in the sense of Definition 04YW, exactly when its first relative diagonal
`Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal `Δ_{f,2}`, the relative diagonal
of `Δ_{f,1}`, are locally quasi-finite in the relative sense of Properties of Stacks,
Section 04XB.

The two diagonals are `AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, applied once
and twice, and local quasi-finiteness is `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`.

## Main results

* `AlgebraicGeometry.Stack.isQuasiDM_iff_isLocallyQuasiFinite_diagonals`: a 1-morphism of
  algebraic stacks is quasi-DM if and only if its first two relative diagonals are locally
  quasi-finite.

## References

* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` — with no representability
hypothesis — is quasi-DM, in the sense of Definition 04YW, if and only if its first relative
diagonal `Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal `Δ_{f,2}`, the
relative diagonal of `Δ_{f,1}`, are both locally quasi-finite in the relative sense of Properties
of Stacks, Section 04XB. -/
@[stacks 04Z0 "quasi_dm"]
theorem isQuasiDM_iff_isLocallyQuasiFinite_diagonals (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsQuasiDM B S hS f ↔
      (IsLocallyQuasiFinite B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom ∧
        IsLocallyQuasiFinite B S hS (relativeDiagonalAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)).hom) :=
  ⟨fun hf => ⟨hf, (isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
      B S hS (relativeDiagonalAlgebraicStacks B S hS f)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).2⟩,
    fun h => h.1⟩

end AlgebraicGeometry.Stack

end
