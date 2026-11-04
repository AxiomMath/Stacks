module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.TransferPullHom
public import StacksFrontier.AlgebraicGeometry.Descent.InvariantSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic

/-!
# Invariant quasi-affine neighbourhoods for an ample sheaf with a descent datum

Let `q : V ⟶ W` be a flat morphism of affine schemes, `π : X ⟶ V` a quasi-compact and
quasi-separated scheme over `V`, and `ρ₁ ρ₂ : X₂ ⟶ X` the two projections of
`X₂ = X ×_W V`, with a diagonal and the three maps out of `X₃` of a descent datum along `q`.
Let `L` be an ample invertible `𝒪_X`-module with an isomorphism `κ : ρ₁^* L ≅ ρ₂^* L`
satisfying the cocycle condition. Then every point `x` of `X` has an open neighbourhood `T`
which is a quasi-affine scheme and is stable for the datum: `ρ₁⁻¹ T = ρ₂⁻¹ T`.

The neighbourhood is the nonvanishing locus of a section of a positive power `L^{⊗ d}`
invariant for the transfer of `κ` and not vanishing at `x`
(`Stacks.Descent.InvariantSections.exists_isInvariant_mem_nonvanishingLocus`, applied to the
transfer `AlgebraicGeometry.Scheme.Modules.tensorPowerTransfer` of `κ`, which is again a
cocycle by `AlgebraicGeometry.Scheme.Modules.pullHom_tensorPowerTransfer_cocycle`). It is
quasi-affine because `L` is ample
(`Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple`), and it is stable
because the section is invariant: the nonvanishing locus of a pulled-back section is the preimage
of the nonvanishing locus.

## Main results

* `Stacks.Descent.InvariantSections.exists_isQuasiAffine_preimage_eq_preimage`: invariant
  quasi-affine neighbourhoods exist.

## References

* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat (pullHom)
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)
open Stacks.Ample (nonvanishingLocus)
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Descent.InvariantSections

variable {W V X X₂ X₃ : Scheme.{u}} [IsAffine W] [IsAffine V] (q : V ⟶ W) [Flat q]
  (π : X ⟶ V) [QuasiSeparatedSpace X] [CompactSpace X₂] [QuasiSeparatedSpace X₂]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (ρ₁ ρ₂ : X₂ ⟶ X) (k₁ : X₂ ⟶ V) (sq₂ : IsPullback ρ₂ k₁ (π ≫ q) q)
  (hW : ρ₁ ≫ π ≫ q = ρ₂ ≫ π ≫ q)
  (κ : (Scheme.Modules.pullback ρ₁).obj L ≅ (Scheme.Modules.pullback ρ₂).obj L)

include sq₂ hW in
/-- **Invariant quasi-affine neighbourhoods.** For an ample invertible module `L` on `X` with a
descent datum `κ` along the flat morphism of affines `q`, every point of `X` has an open
neighbourhood which is a quasi-affine scheme and whose two preimages in `X₂` agree. -/
theorem exists_isQuasiAffine_preimage_eq_preimage (hL : Stacks.Ample.IsAmple X L)
    (Δ : X ⟶ X₂) (hΔ₁ : Δ ≫ ρ₁ = 𝟙 X) (hΔ₂ : Δ ≫ ρ₂ = 𝟙 X)
    (σ₁₂ σ₂₃ σ₁₃ : X₃ ⟶ X₂) (k₃ : X₃ ⟶ V) (sq₃ : IsPullback σ₂₃ k₃ (ρ₂ ≫ π ≫ q) q)
    (t₁ t₂ t₃ : X₃ ⟶ X) (h₁₂₁ : σ₁₂ ≫ ρ₁ = t₁) (h₁₂₂ : σ₁₂ ≫ ρ₂ = t₂)
    (h₂₃₁ : σ₂₃ ≫ ρ₁ = t₂) (h₂₃₂ : σ₂₃ ≫ ρ₂ = t₃) (h₁₃₁ : σ₁₃ ≫ ρ₁ = t₁)
    (h₁₃₂ : σ₁₃ ≫ ρ₂ = t₃) (hk₁₂ : σ₁₂ ≫ k₁ = k₃) (hk₁₃ : σ₁₃ ≫ k₁ = k₃)
    (hcoc : pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
        pullHom (F := modulePullbackPseudofunctor) κ.hom σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHom (F := modulePullbackPseudofunctor) κ.hom σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂)
    (x : X) :
    ∃ T : X.Opens, x ∈ T ∧ (T : Scheme.{u}).IsQuasiAffine ∧ ρ₁ ⁻¹ᵁ T = ρ₂ ⁻¹ᵁ T := by
  classical
  have : CompactSpace X := hL.compactSpace
  obtain ⟨-, hpt⟩ := (Stacks.Ample.isAmple_iff_isOpen X L).1 hL
  obtain ⟨d, hd, s, -, hxs, -⟩ := hpt x
  -- the `d`-th power in the spelling of the transfer, and its comparison with the ample family
  let e := Stacks.PowerFamilyBridge.tensorPowerModuleIso X L (d : ℤ)
  have : Stacks.Ample.IsInvertibleModule X
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)) :=
    Stacks.AmpleBridge.isInvertible_tensorPowerModule L (d : ℤ)
  have : (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  -- the transfer of `κ` to the `d`-th power is a descent datum
  let κd : (Scheme.Modules.pullback ρ₁).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)) ≅
      (Scheme.Modules.pullback ρ₂).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)) :=
    Scheme.Modules.tensorPowerTransfer ρ₁ ρ₂ L κ d
  have hcocd : pullHom (F := modulePullbackPseudofunctor) κd.hom σ₁₂ t₁ t₂ h₁₂₁ h₁₂₂ ≫
        pullHom (F := modulePullbackPseudofunctor) κd.hom σ₂₃ t₂ t₃ h₂₃₁ h₂₃₂ =
      pullHom (F := modulePullbackPseudofunctor) κd.hom σ₁₃ t₁ t₃ h₁₃₁ h₁₃₂ :=
    Scheme.Modules.pullHom_tensorPowerTransfer_cocycle κ σ₁₂ σ₂₃ σ₁₃ t₁ t₂ t₃ h₁₂₁ h₁₂₂ h₂₃₁ h₂₃₂
      h₁₃₁ h₁₃₂ hcoc d
  -- an invariant section through `x`
  have hxm : x ∈ nonvanishingLocus (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ))
      (e.symm.hom.app ⊤ s) := by
    rwa [Stacks.Ample.nonvanishingLocus_congr e.symm s]
  obtain ⟨m₀, hxm₀, hinv⟩ := exists_isInvariant_mem_nonvanishingLocus q π
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)) ρ₁ ρ₂ k₁ sq₂ hW κd Δ hΔ₁ hΔ₂
    σ₁₂ σ₂₃ σ₁₃ k₃ sq₃ t₁ t₂ t₃ h₁₂₁ h₁₂₂ h₂₃₁ h₂₃₂ h₁₃₁ h₁₃₂ hk₁₂ hk₁₃ hcocd _ x hxm
  -- its nonvanishing open
  have hloc : nonvanishingLocus (Stacks.Ample.tensorPowModule X L (d : ℤ)) (e.hom.app ⊤ m₀) =
      nonvanishingLocus (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L (d : ℤ)) m₀ :=
    Stacks.Ample.nonvanishingLocus_congr e m₀
  refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.Ample.tensorPowModule X L (d : ℤ))
    (e.hom.app ⊤ m₀), ?_,
    Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple L hL hd _, ?_⟩
  · show x ∈ nonvanishingLocus (Stacks.Ample.tensorPowModule X L (d : ℤ)) (e.hom.app ⊤ m₀)
    rwa [hloc]
  · ext y
    show ρ₁.base y ∈ nonvanishingLocus (Stacks.Ample.tensorPowModule X L (d : ℤ))
        (e.hom.app ⊤ m₀) ↔
      ρ₂.base y ∈ nonvanishingLocus (Stacks.Ample.tensorPowModule X L (d : ℤ)) (e.hom.app ⊤ m₀)
    rw [hloc, ← mem_nonvanishingLocus_pullbackSectionsHom_iff,
      ← mem_nonvanishingLocus_pullbackSectionsHom_iff,
      ← Stacks.Ample.nonvanishingLocus_congr κd, hinv]

end Stacks.Descent.InvariantSections

end
