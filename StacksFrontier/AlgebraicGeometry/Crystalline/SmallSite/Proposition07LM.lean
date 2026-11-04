module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnectionComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalVanishingHypotheses
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Vanishing07LMProof

/-!
# The de Rham complex of a crystal under `Ru_{X/S, *}`

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and a crystal in
quasi-coherent `𝒪_{X/S}`-modules `F` on `Cris(X/S)`.  [Stacks, Tag 07LM] asserts that the
truncation map of complexes

`(F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯) ⟶ F[0]`

becomes a quasi-isomorphism after `Ru_{X/S, *}`, and in fact that
`Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for every `i > 0`.

## The statement

* The complex is `(crystalDeRhamSheafData hF).complex`, a complex of abelian sheaves on
  `Cris(X/S)` whose degree-`i` term is `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` (`tensorDifferentialFormsSheaf`)
  and whose differentials `crystalDeRhamDifferential` extend the canonical connection of `F` of
  [Stacks, Lemma 60.15.1, Tag 07J6] to all degrees by `d(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω`
  ([Stacks, Section 60.15, Tag 07J5]). The differentials are not `𝒪_{X/S}`-linear, so this is a
  complex of abelian sheaves and not of `𝒪_{X/S}`-modules.
* The truncation map is `(crystalDeRhamSheafData hF).truncation`, the identification
  `F ⊗ Ω⁰_{X/S} = F` in degree zero and zero above.
* `Ru_{X/S, *}` is `derivedZariskiDirectImageFunctor`, the right derived functor of `u_{X/S, *}`
  on `D⁺(Ab(Cris(X/S)))` with values in `D⁺(Ab(X_{Zar}))`, and "quasi-isomorphism after
  `Ru_{X/S, *}`" is "isomorphism of `D⁺(Ab(X_{Zar}))`".

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isIso_derivedZariskiDirectImage_crystalDeRhamTruncation` — the truncation map becomes an
  isomorphism after `Ru_{X/S, *}`.
* `stacks07LM` — both assertions of [Stacks, Tag 07LM] together.

## References

* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The leading assertion of [Stacks, Tag 07LM]**: for a crystal in quasi-coherent
`𝒪_{X/S}`-modules `F`, the truncation map `(F → F ⊗ Ω¹_{X/S} → F ⊗ Ω²_{X/S} → ⋯) ⟶ F[0]`, the
differentials being those of the canonical connection of `F`, becomes an isomorphism of
`D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`. -/
theorem isIso_derivedZariskiDirectImage_crystalDeRhamTruncation
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map
          (sheafPlusTruncation S (crystalDeRhamSheafData hF).complex
            (CrystalDeRhamSheafData.singleComplex (F := F))
            (crystalDeRhamSheafData hF).truncation)))) :=
  (crystalDeRhamSheafData hF).isIso_derivedZariskiDirectImage_map_truncation
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).1
    (satisfiesVanishingHypotheses_of_isQuasicoherentOnSite F hF).2

/-- Let `F` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`.  The truncation map
of complexes

`(F → F ⊗_{𝒪_{X/S}} Ω¹_{X/S} → F ⊗_{𝒪_{X/S}} Ω²_{X/S} → ⋯) ⟶ F[0]`

becomes a quasi-isomorphism after applying `Ru_{X/S, *}` — it is carried to an isomorphism of
`D⁺(Ab(X_{Zar}))` — and in fact `Ru_{X/S, *}(F ⊗_{𝒪_{X/S}} Ω^i_{X/S}) = 0` for every `i > 0`.

The complex is `(crystalDeRhamSheafData hF).complex`: its terms are the sheaves
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` and its differentials `crystalDeRhamDifferential hF i` are the
extensions `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection `∇(m) = p₁^* m - p₀^* m` of
[Stacks, Tag 07J6]. -/
@[stacks 07LM "the whole proposition: for F a crystal in quasi-coherent O_{X/S}-modules on \
Cris(X/S), Ru_{X/S,*} carries the truncation map (F → F ⊗ Ω¹ → F ⊗ Ω² → ⋯) ⟶ F[0] to an \
isomorphism of D⁺(Ab(X_Zar)), the differentials of the complex being the extensions of the \
canonical connection of F of 07J6; and Ru_{X/S,*}(F ⊗_{O_{X/S}} Ω^i_{X/S}) = 0 for every i > 0"]
theorem stacks07LM (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
        (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map
            (sheafPlusTruncation S (crystalDeRhamSheafData hF).complex
              (CrystalDeRhamSheafData.singleComplex (F := F))
              (crystalDeRhamSheafData hF).truncation)))) ∧
      ∀ i : ℕ, 0 < i →
        IsZero ((derivedZariskiDirectImage S).obj (tensorDifferentialFormsSheaf F i)) :=
  ⟨isIso_derivedZariskiDirectImage_crystalDeRhamTruncation F hF,
    fun i hi ↦ isZero_derivedZariskiDirectImage_tensorDifferentialFormsSheaf S F hF i hi⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
