module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingTensorStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# The morphism to the spectrum of the global functions, over `Spec ℤ`, and its base changes

Let `X` be a quasi-compact, quasi-separated algebraic space over a scheme `S` all of whose
quasi-coherent modules have vanishing first cohomology — the data of Stacks 07UY — and write
`A = Γ(X, 𝒪_X)`.  The canonical morphism `p : X ⟶ Spec A` is formed after regarding `X` as an
algebraic space over `Spec ℤ`: `Spec A` carries no morphism to `S`.  Here `Spec A` is presented by
an object `V` of the site whose underlying scheme is affine, together with a ring isomorphism
`Γ(V, 𝒪_V) ≅ Γ(X, 𝒪_X)`.
**Clause (2) of Stacks 07V0** then says that for every `A`-algebra `A'` the projection
`X' = X ×_{Spec A} Spec A' ⟶ X` is affine and `Γ(X', 𝒪_{X'}) = A'`.

## Main definitions

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.toSpecGlobalFunctionsOverIntegers`: the
  canonical morphism `X ⟶ Spec A` of Stacks 05Z1, for `X` viewed over `Spec ℤ` and an affine
  object `V` of the site presenting `Spec A`.

## Main results

* `…CohomologyVanishingSituation.pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers`:
  the canonical morphism induces the given identification on global functions.
* `…CohomologyVanishingSituation.isAffineHom_of_isPullback_toSpecGlobalFunctionsOverIntegers` and
  `…isAffineHom_snd_fiberProduct_toSpecGlobalFunctionsOverIntegers`: the affineness assertion of
  clause (2) of Stacks 07V0, for an arbitrary Cartesian square and for the canonical fibre
  product respectively.
* `…CohomologyVanishingSituation.surjective_sectionsMap_spaceOverIntegers` and
  `…isQuasiCompactSpace_spaceOverIntegers`: viewed over `Spec ℤ`, `X` keeps right exact global
  sections and stays quasi-compact.
* `…isAffineHom_and_bijective_of_isPullback_toSpecGlobalFunctionsOverIntegers`:
  **clause (2) of Stacks 07V0**: `X ×_{Spec A} Spec A' ⟶ X` is affine and
  `A' ⟶ Γ(X ×_{Spec A} Spec A', 𝒪)` is bijective.

## References

* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 058K](https://stacks.math.columbia.edu/tag/058K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})
    (V : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal)
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V, ⊤) ≃+*
      T.globalFunctions)

/-- **The canonical morphism `X ⟶ Spec A`** of Stacks 07UY, where `A = Γ(X, 𝒪_X)`, `X` is viewed
over `Spec ℤ`, and `Spec A` is presented by an affine object `V` of the site over `Spec ℤ`
through a ring isomorphism `Γ(V, 𝒪_V) ≅ A`: the morphism of algebraic spaces over `Spec ℤ` whose
action on global functions is that isomorphism. -/
def toSpecGlobalFunctionsOverIntegers :
    T.spaceOverIntegers ⟶ _root_.AlgebraicGeometry.schemeSpace V :=
  (morphismToAffineEquiv T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers V
    terminalIsTerminal).1.symm
      (T.spaceOverIntegersGlobalFunctionsEquiv.symm.toRingHom.comp e.toRingHom)

/-- The canonical morphism to `Spec A` pulls global functions back along the given
isomorphism. -/
theorem pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers :
    pullbackToGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers V
        (toSpecGlobalFunctionsOverIntegers T V e) =
      T.spaceOverIntegersGlobalFunctionsEquiv.symm.toRingHom.comp e.toRingHom :=
  (morphismToAffineEquiv T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers V
    terminalIsTerminal).1.apply_symm_apply _

/-- Every global function on `X` is the pullback along the canonical morphism of a function on
`Spec A`. -/
theorem surjective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers :
    Function.Surjective (pullbackToGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.spaceOverIntegers V (toSpecGlobalFunctionsOverIntegers T V e)) := by
  rw [pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers]
  exact T.spaceOverIntegersGlobalFunctionsEquiv.symm.surjective.comp e.surjective

/-- **The affineness assertion of clause (2) of Stacks 07V0.** Let `X` be as in Stacks 07UY, let
`A = Γ(X, 𝒪_X)`, and let `A'` be an `A`-algebra, presented by a morphism `q : W ⟶ V` of affine
objects of the site over the presentation of `Spec A`.  Then the projection
`X' = X ×_{Spec A} Spec A' ⟶ X` is affine. -/
theorem isAffineHom_of_isPullback_toSpecGlobalFunctionsOverIntegers
    {W : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal}
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj W)]
    (q : W ⟶ V) {X' : AlgebraicSpaces T.site (⊤_ Scheme.{u}) T.containsTerminal}
    {pr : X' ⟶ T.spaceOverIntegers} {pr' : X' ⟶ _root_.AlgebraicGeometry.schemeSpace W}
    (sq : IsPullback pr' pr (_root_.AlgebraicGeometry.schemeSpaceMap q)
      (toSpecGlobalFunctionsOverIntegers T V e)) :
    IsAffineHom T.site (⊤_ Scheme.{u}) T.containsTerminal pr.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
    (isAffineHom_yoneda_map T.site (⊤_ Scheme.{u}) T.containsTerminal q)

/-- The affineness assertion of clause (2) of Stacks 07V0 for the canonical fibre product of
Stacks 02X2: the second projection of `Spec A' ×_{Spec A} X` is affine. -/
theorem isAffineHom_snd_fiberProduct_toSpecGlobalFunctionsOverIntegers
    {W : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal}
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj W)]
    (q : W ⟶ V) :
    IsAffineHom T.site (⊤_ Scheme.{u}) T.containsTerminal
      (pullback.snd (_root_.AlgebraicGeometry.schemeSpaceMap q).hom
        (toSpecGlobalFunctionsOverIntegers T V e).hom) :=
  isAffineHom_of_isPullback_toSpecGlobalFunctionsOverIntegers T V e q
    (AlgebraicSpaces.isPullback_fiberProduct T.site (⊤_ Scheme.{u}) T.containsTerminal _ _)

end CohomologyVanishingSituation

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, u})
    (V : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal)
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj V, ⊤) ≃+*
      T.globalFunctions)

/-- **In Situation 07UY global sections of `X` viewed over `Spec ℤ` are right exact on
quasi-coherent modules.** -/
theorem surjective_sectionsMap_spaceOverIntegers :
    ∀ ⦃M N : Modules.{u, u} T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1
      T.spaceOverIntegers.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g) :=
  surjective_sectionsMap_relocalize T.site T.base (⊤_ Scheme.{u}) T.containsBase
    T.containsTerminal ⟨terminal.from T.base⟩ T.space.2 T.spaceOverIntegers.2
    (fun _ _ g hg hM hN => T.surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite g hg hM hN)

/-- `X` viewed over `Spec ℤ` is quasi-compact. -/
theorem isQuasiCompactSpace_spaceOverIntegers :
    IsQuasiCompactSpace T.site (⊤_ Scheme.{u}) T.containsTerminal T.spaceOverIntegers.1 :=
  isQuasiCompactSpace_relocalize T.site T.base T.containsBase T.containsTerminal
    ⟨terminal.from T.base⟩ T.quasiCompact

/-- The canonical morphism `X ⟶ Spec A` induces a bijection on global functions. -/
theorem bijective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers :
    Function.Bijective (pullbackToGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.spaceOverIntegers V (toSpecGlobalFunctionsOverIntegers T V e)) := by
  rw [pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers]
  exact T.spaceOverIntegersGlobalFunctionsEquiv.symm.bijective.comp e.bijective

/-- **Clause (2) of Stacks 07V0.** Let `X` be as in Stacks 07UY, let `A = Γ(X, 𝒪_X)`, and let `A'`
be an `A`-algebra, presented by a morphism `q : W ⟶ V` of affine objects of the site over the
presentation `V` of `Spec A`.  Then the projection `X' = X ×_{Spec A} Spec A' ⟶ X` is affine and
the canonical map `A' = Γ(W, 𝒪_W) ⟶ Γ(X', 𝒪_{X'})` is a bijection. -/
@[stacks 07V0 "part (2); `Spec A'` is an affine object `W` of the site over the presentation \
`V` of `Spec A`"]
theorem isAffineHom_and_bijective_of_isPullback_toSpecGlobalFunctionsOverIntegers
    {W : BigFppfOver T.site (⊤_ Scheme.{u}) T.containsTerminal}
    [IsAffine ((BigFppfOver.toScheme T.site (⊤_ Scheme.{u}) T.containsTerminal).obj W)]
    (q : W ⟶ V) {X' : AlgebraicSpaces T.site (⊤_ Scheme.{u}) T.containsTerminal}
    {pr : X' ⟶ T.spaceOverIntegers} {pr' : X' ⟶ _root_.AlgebraicGeometry.schemeSpace W}
    (sq : IsPullback pr' pr (_root_.AlgebraicGeometry.schemeSpaceMap q)
      (toSpecGlobalFunctionsOverIntegers T V e)) :
    IsAffineHom T.site (⊤_ Scheme.{u}) T.containsTerminal pr.hom ∧
      Function.Bijective
        (pullbackToGlobalFunctions T.site (⊤_ Scheme.{u}) T.containsTerminal X' W pr') :=
  ⟨isAffineHom_of_isPullback_toSpecGlobalFunctionsOverIntegers T V e q sq,
    injective_pullbackToGlobalFunctions_of_isPullback T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.surjective_sectionsMap_spaceOverIntegers T.isQuasiCompactSpace_spaceOverIntegers
      (toSpecGlobalFunctionsOverIntegers T V e)
      (T.bijective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers V e)
      q sq,
    surjective_pullbackToGlobalFunctions_of_isPullback T.site (⊤_ Scheme.{u}) T.containsTerminal
      T.surjective_sectionsMap_spaceOverIntegers T.isQuasiCompactSpace_spaceOverIntegers
      (toSpecGlobalFunctionsOverIntegers T V e)
      (surjective_pullbackToGlobalFunctions_toSpecGlobalFunctionsOverIntegers T V e)
      q sq⟩

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
