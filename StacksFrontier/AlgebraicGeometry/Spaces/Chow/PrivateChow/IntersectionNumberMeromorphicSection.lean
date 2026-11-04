module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.TwistedEulerMixedDifference

/-!
# Intersecting with the divisor of a regular meromorphic section

Let `Y` be an integral algebraic space proper over a field, of dimension `d + 1`, let `𝒩` be an
invertible module with a regular meromorphic section `t` and let `M₁, …, M_d` be invertible.
Then

`(𝒩 M₁ ⋯ M_d · Y) = ∑_W ord_W(t) (M₁ ⋯ M_d · W)`,

the sum over the prime divisors `W` of `Y`. With `𝓘` the ideal of denominators of `t` and the two
quotients `𝒬₁ = 𝒪_Y / 𝓘`, `𝒬₂ = 𝒩 / t 𝓘`, the twisted Euler characteristics satisfy
`χ(𝒩 ⊗ M^n) - χ(M^n) = χ(𝒬₂ ⊗ M^n) - χ(𝒬₁ ⊗ M^n)` by the two short exact sequences
`0 → 𝓘 → 𝒪_Y → 𝒬₁ → 0` and `0 → 𝓘 → 𝒩 → 𝒬₂ → 0`; the two quotients are supported in dimension
`≤ d`, so Stacks 0EDE expresses their mixed differences through the lengths at the generic points
of the prime divisors, and the difference of those lengths is `ord_W(t)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A twisting step of the structure sheaf at exponent one is the invertible module. -/
def twistStepOneUnitIso (N : Modules.{u, u} B S hS F hF)
    [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property N] :
    twistStep B S hS F hF N 1 (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ≅ N :=
  @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _
      _ _ _ _ (Iso.refl _)
      (@Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
        (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
        (structurePresheaf B S hS F)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _
        N hN) ≪≫
    @Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).C _ (smallEtaleRingedSite B S hS F hF).J
      (structurePresheaf B S hS F)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property _ _ N

/-- A monomorphism followed by its cokernel is a short exact sequence. -/
theorem shortExact_cokernel_of_mono {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) [Mono φ] :
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ))
    inferInstance inferInstance

variable (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (Y : AlgebraicSpaces B (Spec (.of k)) hk) (f : Y.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)

/-- **The difference of the twisted Euler characteristics of `𝒩` and `𝒪`, through the ideal of
denominators.** For a regular meromorphic section `t` of an invertible `𝒩` on a proper `Y` whose
support has dimension `≤ d + 1`,
`Δ(𝒪_Y; 𝒩, M₁, …, M_d) = Δ(𝒬₂; M) - Δ(𝒬₁; M)`, with `𝒬₁ = 𝒪_Y / 𝓘` and `𝒬₂ = 𝒩 / t 𝓘`. -/
theorem twistedEulerMixedDifference_cons_eq_sub_denominatorQuotients {d : ℕ}
    (hdim : topologicalKrullDim (moduleSupportSet B (Spec (.of k)) hk Y
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O))) ≤ d + 1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B (Spec (.of k)) hk Y,
      localRingDimension B (Spec (.of k)) hk z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B (Spec (.of k)) hk Y.1)
    (N : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    [hN : Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property N]
    (t : MeromorphicSection.{u, u} B (Spec (.of k)) hk Y.1 Y.2 N)
    (ht : IsRegularMeromorphicSection.{u, u} B (Spec (.of k)) hk Y.1 Y.2 N t)
    (M : Fin d → Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk Y.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property (M j)] :
    haveI : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Y.1
        (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
      ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 f hf⟩
    have hL' := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
    have hIc := isCoherent_meromorphicDenominatorIdeal B (Spec (.of k)) hk Y N t hL' hwa hfin
    have hLc : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 N :=
      { __ := isQuasicoherentOnSite_of_isInvertible B (Spec (.of k)) hk Y N hL'
        __ := isCoherentOnSite_of_isInvertible N hN }
    twistedEulerMixedDifference.{u, w} k B hk Y f hf
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O)) inferInstance
        (Fin.cons N M) =
      twistedEulerMixedDifference.{u, w} k B hk Y f hf
          (meromorphicNumeratorQuotient B (Spec (.of k)) hk Y N t hL')
          (isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc hLc _) M -
        twistedEulerMixedDifference.{u, w} k B hk Y f hf
          (meromorphicDenominatorQuotient B (Spec (.of k)) hk Y N t hL')
          (isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc inferInstance _) M := by
  intros
  rename_i hL' hIc hLc
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Y.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 f hf⟩
  have := mono_meromorphicDenominatorMul B (Spec (.of k)) hk Y N t hL' ht
  rw [twistedEulerMixedDifference_cons_eq_sub_twistStep.{u, w} k B hk Y f hf _ inferInstance hdim
    N M]
  rw [twistedEulerMixedDifference_congr.{u, w} k B hk Y f hf M
      (twistStepOneUnitIso B (Spec (.of k)) hk Y.1 Y.2 N) _ hLc,
    twistedEulerMixedDifference_congr.{u, w} k B hk Y f hf M
      (twistStepZeroIso B (Spec (.of k)) hk Y.1 Y.2 N _) _ inferInstance,
    twistedEulerMixedDifference_of_shortExact.{u, w} k B hk Y f hf M
      (shortExact_cokernel_of_mono B (Spec (.of k)) hk Y.1 Y.2
        (meromorphicDenominatorMul B (Spec (.of k)) hk Y N t hL')) hIc hLc
      (isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc hLc _),
    twistedEulerMixedDifference_of_shortExact.{u, w} k B hk Y f hf M
      (shortExact_cokernel_of_mono B (Spec (.of k)) hk Y.1 Y.2
        (meromorphicDenominatorIdeal B (Spec (.of k)) hk Y N t hL').ι) hIc inferInstance
      (isCoherent_cokernel B (Spec (.of k)) hk Y.1 Y.2 hIc inferInstance _)]
  ring

end AlgebraicGeometry.Space

end
