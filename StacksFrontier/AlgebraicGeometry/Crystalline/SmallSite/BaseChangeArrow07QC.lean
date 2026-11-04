module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisLevelsInputs07QC

/-!
# Arrow 1 of [Stacks, Tag 07N5] is an isomorphism

Let `T` be a Frobenius crystal situation over the affine base `S = Spec(A)` with `A` Noetherian
and `p`-adically complete, `X ⟶ S₀` proper and smooth, and `E` a crystal in finite locally free
modules. Arrow 1 of the proof of [Stacks, Tag 07N5], the base change map
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})` of [Stacks, Tag 07QC], is an
isomorphism, at any choice of models of the derived categories involved.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.crisLevelsInput07QC`: pseudo-coherence of
  `RΓ(CRIS(X/S), N)` and its base change to every level, for all such situations.
* `Crystalline.GlobalCrystallineSituation.SmallSite.isIso_baseChangeArrow07QC`: arrow 1 is an
  isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Standard

attribute [local instance 1100] HasDerivedCategory.standard

/-- **The level input (P1) + (P2) of arrow 1 holds**: for a global crystalline situation with
affine Noetherian `p`-adically complete base and `X ⟶ S₀` proper and smooth, and a crystal `N`
in finite locally free modules, `RΓ(CRIS(X/S), N)` is pseudo-coherent and its base change to
every level `S_{N₀}`, `N₀ > 0`, is `RΓ(CRIS(X/S_{N₀}), N_{N₀})`. -/
theorem crisLevelsInput07QC : CrisLevelsInput07QC.{u} := by
  intro S _ hnoeth hcomplete hproper hsmooth N hN N₀ h₀ hN₀
  have := hnoeth
  have : IsAdicComplete (DividedPowers.pAdicIdeal (A := Γ(S.S.scheme, ⊤)) S.p)
      Γ(S.S.scheme, ⊤) := hcomplete
  have := hsmooth
  exact levels_isPseudoCoherentIn_and_isIso S h₀ hproper hN hN₀

end Standard

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5] is an isomorphism** ([Stacks, Tag 07QC]): for
`A = Γ(S, 𝒪_S)` Noetherian and `p`-adically complete, `X ⟶ S₀` proper and smooth, and `E` a
crystal in finite locally free modules, the base change map
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})` is an isomorphism, at the models
of the derived categories in scope. -/
theorem isIso_baseChangeArrow07QC (hnoeth : IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤))
    (hcomplete : IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
      ↥Γ(T.global.S.scheme, ⊤))
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) : IsIso (baseChangeArrow07QC T E) :=
  isIso_baseChangeArrow07QC_of_crisLevelsInput_models T crisLevelsInput07QC hnoeth hcomplete
    hproper hsmooth E

end Crystalline.GlobalCrystallineSituation.SmallSite

end
