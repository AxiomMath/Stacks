module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionFinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedFinitePresentationEmbeddingOfCutoffBoundedSystem

/-!
# A quasi-projective open is dominated by an admissible blowup inside a proper space

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated, let `U ⊆ X` be a quasi-compact open subspace and let
`i : U ⟶ ℙⁿ_Y` be an immersion over `Y`. Then there is a commutative diagram
```
        U
     ↙  ↓  ↘  ↘
   X ← X' → Z' → Z
     ↘  ↓  ↙    ↓
        Y  ←  ℙⁿ_Y
```
whose arrows out of `U` are open immersions, in which `X' ⟶ X` is a `U`-admissible blowup,
`X' ⟶ Z'` is an open immersion, `Z' ⟶ Y` is proper and representable, `Z' ⟶ Z` is a
`U`-admissible blowup and `Z ⟶ ℙⁿ_Y` is a closed immersion
(`AlgebraicGeometry.Space.HasChowBlowupDiagram`).

## Main results

* `AlgebraicGeometry.Space.hasChowBlowupDiagram_of_isFiniteType_of_isSeparated`: the existence of
  this diagram.

## References

* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A separated morphism of finite type `f : X ⟶ Y` of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated, factors as a closed immersion `i : X ⟶ X'` followed by a
separated morphism of finite presentation `f' : X' ⟶ Y`. -/
private theorem exists_closedImmersion_separated_finitePresentation_of_finiteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsSeparated B S hS f' ∧
        IsFinitePresentation B S hS f' ∧ IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hcomp⟩ :=
    exists_isClosedImmersion_isSeparated_isFinitePresentation_of_embedding_of_closedSubspaceLimits
      B S hS
      (fun hX hY f hf hXqc hXqs hYqc hYqs =>
        exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType B S hS hX hY f hf
          hXqc hXqs hYqc hYqs)
      (exists_isLimit_closedSubspaces_of_isClosedImmersion B S hS B.contains_terminal)
      hX hY f hft hsep hYqc hYqs
  exact ⟨X', f', i, hX', hf'sep, hf'fp, hi, hcomp⟩

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `U ⊆ X` be an open
subspace. Assume that `U` is quasi-compact, that `Y` is quasi-compact and quasi-separated, that
`i : U ⟶ ℙⁿ_Y` is an immersion over `Y`, and that `f` is of finite type and separated. Then there
is a commutative diagram
```
        U
     ↙  ↓  ↘  ↘
   X ← X' → Z' → Z
     ↘  ↓  ↙    ↓
        Y  ←  ℙⁿ_Y
```
in which the arrows with source `U` are open immersions, `X' ⟶ X` is a `U`-admissible blowup,
`X' ⟶ Z'` is an open immersion and `Z' ⟶ Y` is proper and representable; more precisely
`Z' ⟶ Z` is a `U`-admissible blowup and `Z ⟶ ℙⁿ_Y` is a closed immersion, through which `i`
factors (`AlgebraicGeometry.Space.HasChowBlowupDiagram`). -/
@[stacks 088R]
theorem hasChowBlowupDiagram_of_isFiniteType_of_isSeparated
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n) (hi : IsImmersion B S hS i)
    (hiY : i ≫ prod.fst = U.ι ≫ f)
    (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f) :
    HasChowBlowupDiagram B S hS hX f U hU n i :=
  hasChowBlowupDiagram_of_commonAdmissibleBlowup B S hS B.contains_terminal
    (fun f₁ f₂ j₁ j₂ hYqc hYqs hj₁ hj₂ hj hUft _ hX₁ft hX₁sep hX₂ft hX₂sep =>
      exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion B.contains_terminal
        f₁ f₂ j₁ j₂ hYqc hYqs hj₁ hj₂ hj hUft hX₁ft hX₁sep hX₂ft hX₂sep
        (fun g hX' hY' hg hY'qc hY'qs =>
          exists_integralFiniteSystem_of_isFinite B S hS g hX' hY' hg hY'qc hY'qs)
        (fun g hX' hY' hgft hgsep hY'qc hY'qs =>
          exists_closedImmersion_separated_finitePresentation_of_finiteType B S hS g hX' hY'
            hgft hgsep hY'qc hY'qs))
    hX hY f U hU hUqc hYqc hYqs n i hi hiY hft hsep

end AlgebraicGeometry.Space

end
