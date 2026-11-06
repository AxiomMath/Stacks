module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheafHomMatrix

/-!
# A morphism `ℱ_ρ → ℱ_{ρ'}` is induced by its matrix

Every morphism of ℓ-adic sheaves `θ : ℱ_ρ → ℱ_{ρ'}` between the sheaves of continuous integral
representations of `π₁(X, x̄)` is the morphism `Stacks.EtaleCohomology.representationLAdicSheafMap`
induced by its matrix `Stacks.EtaleCohomology.representationLAdicSheafHomMatrix`
(`Stacks.EtaleCohomology.eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix`): at
each level both are the image under the canonical equivalence of Tag 0DV5 (2) of the same map of
level modules, multiplication by the reduction of the matrix. This lets statements made for the
morphisms induced by intertwiners (such as `Stacks.EtaleCohomology.CurvePointInertiaStalkInput`) be
applied to an arbitrary endomorphism of `ℱ_ρ`, e.g. the action of coefficients transported through
an isogeny, as in the specialization map of Laumon's degeneration
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' r'' : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')
  {ρ'' : EtaleFundamentalGroup X.1 x →* GL (Fin r'') ℤ_[ℓ]} (hρ'' : Continuous ρ'')

/-- **A morphism `θ : ℱ_ρ → ℱ_{ρ'}` is the morphism induced by its matrix.** -/
public theorem eq_representationLAdicSheafMap_representationLAdicSheafHomMatrix
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') :
    θ = representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ'
      (representationLAdicSheafHomMatrix B X x hρ hρ' θ)
      (representationLAdicSheafHomMatrix_mul B X x hρ hρ' θ) := by
  refine LAdicSheaf.Hom.ext B X ℓ fun n => ?_
  have hmod : representationLevelHomModuleMap B X x hρ hρ'
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (θ.app n) =
      levelAbelianMap hρ hρ' (representationLAdicSheafHomMatrix B X x hρ hρ' θ)
        (representationLAdicSheafHomMatrix_mul B X x hρ hρ' θ) (n + 1) := by
    apply finiteContinuousAbelianHom_ext
    ext y
    refine ULift.ext ?_
    obtain ⟨w, hw⟩ : ∃ w : Fin r → ℤ_[ℓ],
        (fun j => PadicInt.toZModPow (n + 1) (w j)) = y.down :=
      ⟨fun j => (ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) (y.down j)).choose,
        funext fun j =>
          (ZMod.ringHom_surjective (PadicInt.toZModPow (n + 1)) (y.down j)).choose_spec⟩
    have hy : y = ULift.up (fun j => PadicInt.toZModPow (n + 1) (w j)) := by
      rw [hw]
      rfl
    subst hy
    funext i
    show representationLevelHomVec B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (θ.app n)
        (fun j => PadicInt.toZModPow (n + 1) (w j)) i =
      (((representationLAdicSheafHomMatrix B X x hρ hρ' θ).map (PadicInt.toZModPow (n + 1))) *ᵥ
        fun j => PadicInt.toZModPow (n + 1) (w j)) i
    rw [← toZModPow_mulVec_representationLAdicSheafHomMatrix]
    exact RingHom.map_mulVec (PadicInt.toZModPow (n + 1))
      (representationLAdicSheafHomMatrix B X x hρ hρ' θ) w i
  have h := forget₂_map_eq_inverse_map_representationLevelHomModuleMap B X x hρ hρ' (n + 1)
    (θ.app n)
  rw [hmod] at h
  ext U y
  exact congrArg (fun g => (g.hom.app U).hom y) h

end LAdic

end Stacks.EtaleCohomology

end
