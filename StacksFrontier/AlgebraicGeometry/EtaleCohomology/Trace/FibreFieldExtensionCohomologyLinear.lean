module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSchemeIsoTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationChangeLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientIsogenyLinear

/-!
# The cohomology of a scheme identified with a base change, `E`-linearly

Let `X` be separated of finite type over a finite field `k` with `q` elements, compactified by `j`,
`F` an ℓ-adic sheaf on `X` with coefficients in `O'`, `κ` a finite extension of `k` with
`q ^ (m + 1)` elements and `Y` a scheme over `κ` with an isomorphism `α : Y ≅ X ×_k κ` over `κ`,
compactified arbitrarily. If a sheaf `G` on `Y` with coefficients in `O` is isogenous to
`α⁻¹ pr⁻¹ F`, compatibly with `O` and `O'` (both localizing to `E`), then
`Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` `E`-linearly, carrying the Frobenius of `Y` over `κ` to
`(π_X^*) ^ (m + 1)`
(`LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_fieldExtensionIso`). The steps: the
isogeny (`rationalIsogenyLinearEquiv`), the change of compactification of `Y` to the one induced by
the base change of `j` (`rationalCompactificationLinearEquiv`, after identifying the structure
morphisms), the transport along `α` (`rationalIsoOfIsIsoLinearEquiv`) and the base change of the
field (`rationalFieldExtensionCohomologyLinearEquiv`). This is how a fibre of Laumon's families is
compared with the base change of the curve in
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_structureMap_eq`: equal structure
  morphisms and any two compactifications give `E`-linearly isomorphic cohomology, compatibly with
  the Frobenius.
* `LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_fieldExtensionIso`:
  `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, `E`-linearly, for `Y ≅ X ×_k κ` over `κ`.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **Equal structure morphisms, any two compactifications**: `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through
`j₁` over `f₁` and through `j₂` over `f₂ = f₁` are `E`-linearly isomorphic, compatibly with the
Frobenius. -/
public theorem LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_structureMap_eq
    {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    (f₁ f₂ : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f₁] [QuasiCompact f₁] [IsSeparated f₁]
    [LocallyOfFiniteType f₂] [QuasiCompact f₂] [IsSeparated f₂] (h : f₁ = f₂)
    (j₁ : CompactificationOf (Over.mk f₁)) (j₂ : CompactificationOf (Over.mk f₂))
    (kbar : Type u) [Field kbar] [Algebra k kbar] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (i : ℤ)
    (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) :
    letI := F.rationalCohomologyModule f₁ j₁ kbar i E
    letI := F.rationalCohomologyModule f₂ j₂ kbar i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f₁ j₁ kbar
        F.toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f₂ j₂ kbar F.toLAdicSheaf i,
      ∀ v, e (F.rationalGeometricCompactlySupportedFrobenius f₁ j₁ kbar i E p q hcard v) =
        F.rationalGeometricCompactlySupportedFrobenius f₂ j₂ kbar i E p q hcard (e v) := by
  subst h
  exact ⟨F.rationalCompactificationLinearEquiv B ℓ f₁ kbar i E j₁ j₂,
    F.rationalCompactificationLinearEquiv_frobenius B ℓ f₁ kbar i E p q hcard j₁ j₂⟩

/-- **`Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`, `E`-linearly, for `Y ≅ X ×_k κ` over `κ` and
`G` isogenous to the inverse image of `F`**, carrying the Frobenius of `Y` over `κ`,
`#κ = q ^ (m + 1)`, to `(π_X^*) ^ (m + 1)`. -/
public theorem LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_fieldExtensionIso
    {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
    [Module.Finite k κ] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra κ kbar]
    [IsScalarTower k κ kbar] [IsNoetherian (fieldExtensionScheme B X f κ).1]
    {Y : B.Scheme} [IsNoetherian Y.1] (fY : Y.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType fY]
    [QuasiCompact fY] [IsSeparated fY] (jY : CompactificationOf (Over.mk fY))
    (α : Y ⟶ fieldExtensionScheme B X f κ) [IsIso (B.inclusion.map α)]
    (hα : B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ) = fY)
    {O O' : Type} [CommRing O] [Algebra ℤ_[ℓ] O] [CommRing O'] [Algebra ℤ_[ℓ] O']
    (G : LAdicSheaf.CoefficientSheaf B Y ℓ O) (F : LAdicSheaf.CoefficientSheaf B X ℓ O') (i : ℤ)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E] [Algebra O' E]
    [IsLocalization (Submonoid.powers (ℓ : O)) E] [IsLocalization (Submonoid.powers (ℓ : O')) E]
    (φ : G.toLAdicSheaf ⟶ (LAdicSheaf.CoefficientSheaf.inverseImage α
      (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f κ) F)).toLAdicSheaf)
    (ψ : (LAdicSheaf.CoefficientSheaf.inverseImage α
      (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f κ) F)).toLAdicSheaf ⟶
        G.toLAdicSheaf) (N : ℕ)
    (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hφ : ∀ (o : O) (o' : O'), algebraMap O E o = algebraMap O' E o' →
      φ ≫ ((LAdicSheaf.CoefficientSheaf.inverseImage α
        (LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f κ) F)).act o').asHom =
        (G.act o).asHom ≫ φ)
    (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP κ p] (hcard : Fintype.card k = p ^ q) (m : ℕ)
    (hcard' : Fintype.card κ = p ^ (q * (m + 1))) :
    letI := G.rationalCohomologyModule fY jY kbar i E
    letI := F.rationalCohomologyModule f j kbar i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        G.toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i,
      ∀ v, e (G.rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p (q * (m + 1))
          hcard' v) =
        ((F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard) ^ (m + 1))
          (e v) := by
  let F' := LAdicSheaf.CoefficientSheaf.inverseImage (fieldExtensionProj B X f κ) F
  let G' := LAdicSheaf.CoefficientSheaf.inverseImage α F'
  let j' := compactificationFieldBaseChange f j κ
  let := G.rationalCohomologyModule fY jY kbar i E
  let := G'.rationalCohomologyModule fY jY kbar i E
  let := G'.rationalCohomologyModule (B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ))
    (j'.restrictOpen (B.inclusion.map α)) kbar i E
  let := F'.rationalCohomologyModule (pullback.snd f (specAlgebraMap k κ)) j' kbar i E
  let := F.rationalCohomologyModule f j kbar i E
  let e₁ := LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G G' fY jY kbar i E φ ψ N h₁ h₂
    hφ
  obtain ⟨e₂, he₂⟩ := LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_structureMap_eq B ℓ
    fY (B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ)) hα.symm jY
    (j'.restrictOpen (B.inclusion.map α)) kbar G' i E p (q * (m + 1)) hcard'
  let e₃ := F'.rationalIsoOfIsIsoLinearEquiv B ℓ α (pullback.snd f (specAlgebraMap k κ)) j' kbar i E
  let e₄ := LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv B X ℓ f j κ kbar
    F i E
  refine ⟨e₁.trans (e₂.trans (e₃.trans e₄)), fun v => ?_⟩
  change e₄ (e₃ (e₂ (e₁ _))) = _
  rw [LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G G' fY jY kbar i E φ ψ N h₁
    h₂ hφ p (q * (m + 1)) hcard', he₂,
    LAdicSheaf.CoefficientSheaf.rationalIsoOfIsIsoLinearEquiv_frobenius B ℓ α
      (pullback.snd f (specAlgebraMap k κ)) j' kbar i p (q * (m + 1)) hcard' F' E,
    LAdicSheaf.CoefficientSheaf.rationalFieldExtensionCohomologyLinearEquiv_frobenius]
  rfl

end Stacks.EtaleCohomology

end
