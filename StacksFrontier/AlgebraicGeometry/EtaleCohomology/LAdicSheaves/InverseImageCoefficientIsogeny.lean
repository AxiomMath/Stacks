module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficient

/-!
# The inverse image of an isogeny of sheaves with coefficients

An isogeny `φ : F → G`, `ψ : G → F`, `φ ψ = ℓ^N = ψ φ`, between ℓ-adic sheaves with coefficients
in `O` and `O'`, commuting with the two actions wherever a relation `R` between `O` and `O'`
holds, induces an isogeny `f⁻¹φ`, `f⁻¹ψ` between the inverse images with the same `N` and the
same compatibility.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny`: the inverse
  image of an isogeny compatible with the actions is an isogeny compatible with the actions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

open AlgebraicGeometry AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [IsNoetherian Y.obj] {O O' : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
  [CommRing O'] [Algebra ℤ_[ℓ] O']

/-- **The inverse image of an isogeny compatible with the actions is an isogeny compatible with
the actions.** -/
public theorem exists_inverseImage_isogeny (F : LAdicSheaf.CoefficientSheaf B Y ℓ O)
    (G : LAdicSheaf.CoefficientSheaf B Y ℓ O') (R : O → O' → Prop)
    (φ : F.toLAdicSheaf ⟶ G.toLAdicSheaf) (ψ : G.toLAdicSheaf ⟶ F.toLAdicSheaf) (N : ℕ)
    (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)
    (hφ : ∀ o o', R o o' → φ ≫ (G.act o').asHom = (F.act o).asHom ≫ φ) :
    ∃ (φ' : (inverseImage f F).toLAdicSheaf ⟶ (inverseImage f G).toLAdicSheaf)
      (ψ' : (inverseImage f G).toLAdicSheaf ⟶ (inverseImage f F).toLAdicSheaf),
      φ' ≫ ψ' = (ℓ ^ N) • 𝟙 _ ∧ ψ' ≫ φ' = (ℓ ^ N) • 𝟙 _ ∧
      ∀ o o', R o o' → φ' ≫ ((inverseImage f G).act o').asHom =
        ((inverseImage f F).act o).asHom ≫ φ' := by
  let Φ := AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImageFunctor (ℓ := ℓ) f
  refine ⟨Φ.map φ, Φ.map ψ, ?_, ?_, fun o o' h => ?_⟩
  · change Φ.map φ ≫ Φ.map ψ = (ℓ ^ N) • 𝟙 (Φ.obj F.toLAdicSheaf)
    rw [← Φ.map_comp, h₁, Functor.map_nsmul, Φ.map_id]
  · change Φ.map ψ ≫ Φ.map φ = (ℓ ^ N) • 𝟙 (Φ.obj G.toLAdicSheaf)
    rw [← Φ.map_comp, h₂, Functor.map_nsmul, Φ.map_id]
  · change Φ.map φ ≫ Φ.map (G.act o').asHom = Φ.map (F.act o).asHom ≫ Φ.map φ
    rw [← Φ.map_comp, ← Φ.map_comp, hφ o o' h]

end Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf

end
