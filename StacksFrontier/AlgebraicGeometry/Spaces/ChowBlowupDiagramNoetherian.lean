module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowupUnconditional

/-!
# Stacks 088S: the blowup-and-compactify diagram over a Noetherian base

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `Y` Noetherian.  Stacks 088S asserts that there are a dense open subspace `U ⊆ X` and a
commutative diagram
```
        U
     ↙  ↓  ↘  ↘
   X ← X' → Z' → Z
     ↘  ↓  ↙    ↓
        Y  ←  ℙⁿ_Y
```
in which the arrows out of `U` are open immersions, `X' ⟶ X` is a `U`-admissible blowup,
`X' ⟶ Z'` is an open immersion, `Z' ⟶ Y` is proper and representable, `Z' ⟶ Z` is a
`U`-admissible blowup and `Z ⟶ ℙⁿ_Y` is a closed immersion.  The diagram is
`AlgebraicGeometry.Space.HasChowBlowupDiagram`.

The reduction of Stacks 088S to Stacks 088R through Stacks 088N is
`AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram_of_forall`, Stacks 088R for a
quasi-compact quasi-separated base from the conclusion of Stacks 088Q is
`AlgebraicGeometry.Space.hasChowBlowupDiagram_of_commonAdmissibleBlowup`, and Stacks 088Q is
proved in `StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowupUnconditional`.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram`: Stacks 088S.

## References

* [Stacks Project, Tag 088S](https://stacks.math.columbia.edu/tag/088S)
* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 088N](https://stacks.math.columbia.edu/tag/088N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 088S.**  Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces
over `S`, with `Y` Noetherian.  Then there are a dense open subspace `U ⊆ X`, an integer `n` and
an immersion `i : U ⟶ ℙⁿ_Y` over `Y` for which the diagram of Stacks 088S exists
(`AlgebraicGeometry.Space.HasChowBlowupDiagram`): a `U`-admissible blowup `X' ⟶ X`, an open
immersion `X' ⟶ Z'`, a proper representable `Z' ⟶ Y`, a `U`-admissible blowup `Z' ⟶ Z` and a
closed immersion `Z ⟶ ℙⁿ_Y`, with the arrows out of `U` open immersions and everything
commuting. -/
@[stacks 088S]
theorem exists_denseOpen_hasChowBlowupDiagram (hTop : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYnoeth : IsNoetherian B S hS hTop Y) :
    ∃ (U : Subfunctor X) (hU : IsOpenSubspace B S hS U),
      (letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X;
        DenseRange (pointsMap B S hS U.toFunctor U.ι)) ∧
      ∃ (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n),
        IsImmersion B S hS i ∧ i ≫ prod.fst = U.ι ≫ f ∧
          HasChowBlowupDiagram B S hS hX f U hU n i :=
  exists_denseOpen_hasChowBlowupDiagram_of_forall B S hS hTop hX hY f hsep hft hYnoeth
    fun U hU n i hUqc hi hiY =>
      hasChowBlowupDiagram_of_commonAdmissibleBlowup B S hS hTop
        (fun f₁ f₂ j₁ j₂ hYqc hYqs hj₁ hj₂ hj hUft hUsep hX₁ft hX₁sep hX₂ft hX₂sep =>
          exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion_unconditional f₁ f₂ j₁ j₂
            hYqc hYqs hj₁ hj₂ hj hUft hUsep hX₁ft hX₁sep hX₂ft hX₂sep)
        hX hY f U hU hUqc hYnoeth.1 hYnoeth.2.1 n i hi hiY hft hsep

end AlgebraicGeometry.Space

end
