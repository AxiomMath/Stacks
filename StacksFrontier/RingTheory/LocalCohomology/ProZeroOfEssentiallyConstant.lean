module

public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantFromProZero

/-!
# Pro-zero local cohomology of `{IⁿM}` from essential constancy of `{H^i_T(M/IⁿM)}`

Let `A` be a commutative ring, `T ⊆ Spec(A)`, `I ⊆ A` an ideal and `M` an `A`-module. If the
systems `{H^{i-1}_T(M/IⁿM)}` and `{H^i_T(M/IⁿM)}` are essentially constant with values
`H^{i-1}_T(M)` and `H^i_T(M)` (with respect to the cones of the quotient maps), then the system
`{H^i_T(IⁿM)}` is pro-zero. In degree `i + 1`, essential constancy in degree `i` alone forces the
classes of `H^{i+1}_T(IᵏM)` which die in `H^{i+1}_T(M)` to die in `H^{i+1}_T(IᵐM)` for `k ≫ m`.

This is the first paragraph of the proof of [Stacks, Tag 0EFX] at a prime, in the form in which
the essential constancy is available there: at the closed point of a local ring it follows from
the identification `H^i_𝔪(M) = lim H^i_𝔪(M/IⁿM)` of [Stacks, Tag 0EFR] and the Artinianness of
the terms.

## Main results

In the namespace `Stacks.LocalCohomology`:

* `exists_localCohomology_idealPowerTower_eq_zero_of_isEssentiallyConstantWith`
* `exists_forall_eq_zero_of_inclusion_eq_zero_of_isEssentiallyConstantWith`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) (I : Ideal A)
  (M : ModuleCat.{max u v} A)

/-- An essentially constant system of local cohomology of the adic quotients has eventually
injective projections. -/
theorem injective_π_of_isEssentiallyConstantWith (i : ℤ) {j : ℕᵒᵖ}
    {σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
      (localCohomologyAdicCone.{u, v} A T I i M).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      j σ) {k : ℕ} (hk : j.unop ≤ k) :
    Function.Injective ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op k)).hom := by
  have : IsSplitMono ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op k)) :=
    ⟨⟨⟨_ ≫ σ, by
      rw [← Category.assoc, (localCohomologyAdicCone.{u, v} A T I i M).w (homOfLE hk).op,
        h.retraction]; rfl⟩⟩⟩
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- An essentially constant system of local cohomology of the adic quotients has transition
images eventually inside the images of the projections. -/
theorem exists_range_le_of_isEssentiallyConstantWith (i : ℤ) {j : ℕᵒᵖ}
    {σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
      (localCohomologyAdicCone.{u, v} A T I i M).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      j σ) (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k),
      LinearMap.range ((localCohomologyAdicTower.{u, v} A T I i M).map
          (homOfLE (hmc.trans hck)).op).hom ≤
        LinearMap.range ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op m)).hom := by
  obtain ⟨k₀, σ', τ, hτ⟩ := h.cofinal (op m)
  have hmc : m ≤ k₀.unop := leOfHom τ.unop
  refine ⟨k₀.unop, hmc, fun k hck ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  have hsplit : (localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE (hmc.trans hck)).op =
      (localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE hck).op ≫
        (localCohomologyAdicTower.{u, v} A T I i M).map τ := by
    rw [← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  refine ⟨σ.hom (((localCohomologyAdicTower.{u, v} A T I i M).map σ').hom
    (((localCohomologyAdicTower.{u, v} A T I i M).map (homOfLE hck).op).hom x)), ?_⟩
  rw [hsplit, hτ]
  rfl


/-- **The kernel condition from essential constancy one degree lower.** If `{H^{i-1}_T(M/IⁿM)}`
is essentially constant with value `H^{i-1}_T(M)`, then for every `m` there is `c ≥ m` such that
every class of `H^i_T(IᵏM)`, `k ≥ c`, which dies in `H^i_T(M)` already dies in `H^i_T(IᵐM)`.

Such a class is `δ(z)` for some `z ∈ H^{i-1}_T(M/IᵏM)`; its image in `H^i_T(IᵐM)` is `δ` of the
image of `z` in `H^{i-1}_T(M/IᵐM)`, which for `k` large comes from `H^{i-1}_T(M)` and is
therefore killed by `δ`. -/
theorem exists_forall_eq_zero_of_inclusion_eq_zero_of_isEssentiallyConstantWith (i : ℤ)
    {j : ℕᵒᵖ} {σ : (localCohomologyAdicTower.{u, v} A T I (i - 1) M).obj j ⟶
      (localCohomologyAdicCone.{u, v} A T I (i - 1) M).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I (i - 1) M)
      (localCohomologyAdicCone.{u, v} A T I (i - 1) M) j σ) (m : ℕ) :
    ∃ c : ℕ, ∃ hmc : m ≤ c, ∀ (k : ℕ) (hck : c ≤ k)
      (ξ : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj
        ((idealPowerTower.{u, v} I M).obj (op k))),
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        (idealPowerInclusion.{u, v} I M k)).hom ξ = 0 →
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerTower.{u, v} I M).map (homOfLE (hmc.trans hck)).op)).hom ξ = 0 := by
  obtain ⟨c, hmc, hc⟩ := exists_range_le_of_isEssentiallyConstantWith T I M (i - 1) h m
  refine ⟨c, hmc, fun k hck ξ hξ ↦ ?_⟩
  have hi : i - 1 + 1 = i := by omega
  have hSk := idealPowerShortComplex_shortExact.{u, v} I M k
  have hSm := idealPowerShortComplex_shortExact.{u, v} I M m
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (localCohomology_exact₁.{u, v} T hSk (i - 1) i hi) ξ hξ
  have hnat := localCohomologyδ_naturality.{u, v} T hSk hSm
    (idealPowerShortComplexMap.{u, v} I M (hmc.trans hck)) (i - 1) i hi
  obtain ⟨w, hw⟩ := hc k hck ⟨z, rfl⟩
  have hzero := localCohomologyMap_comp_localCohomologyδ.{u, v} T hSm (i - 1) i hi
  rw [← hz]
  have h1 := congrArg (fun f ↦ f.hom z) hnat
  change (localCohomologyδ.{u, v} T hSm (i - 1) i hi).hom
      ((localCohomologyMap.{u, v} A T (i - 1)
        (idealPowerShortComplexMap.{u, v} I M (hmc.trans hck)).τ₃).hom z) =
    (localCohomologyMap.{u, v} A T i
        (idealPowerShortComplexMap.{u, v} I M (hmc.trans hck)).τ₁).hom
      ((localCohomologyδ.{u, v} T hSk (i - 1) i hi).hom z) at h1
  change (localCohomologyMap.{u, v} A T i
      (idealPowerShortComplexMap.{u, v} I M (hmc.trans hck)).τ₁).hom
    ((localCohomologyδ.{u, v} T hSk (i - 1) i hi).hom z) = 0
  rw [← h1]
  change (localCohomologyδ.{u, v} T hSm (i - 1) i hi).hom
      (((localCohomologyAdicTower.{u, v} A T I (i - 1) M).map
        (homOfLE (hmc.trans hck)).op).hom z) = 0
  rw [← hw]
  exact congrArg (fun f ↦ f.hom w) hzero

/-- **Pro-zero local cohomology of `{IⁿM}` from essential constancy.** If `{H^{i-1}_T(M/IⁿM)}`
and `{H^i_T(M/IⁿM)}` are essentially constant with values `H^{i-1}_T(M)` and `H^i_T(M)`, then
for every `m` some transition map `H^i_T(IᵏM) → H^i_T(IᵐM)` vanishes.

The kernel condition one degree lower kills the classes dying in `H^i_T(M)`, and every class of
`H^i_T(IᵏM)` dies there for `k` large because `H^i_T(M) → H^i_T(M/IᵏM)` is then injective. -/
theorem exists_localCohomology_idealPowerTower_eq_zero_of_isEssentiallyConstantWith (i : ℤ)
    {j₁ : ℕᵒᵖ} {σ₁ : (localCohomologyAdicTower.{u, v} A T I (i - 1) M).obj j₁ ⟶
      (localCohomologyAdicCone.{u, v} A T I (i - 1) M).pt}
    (h₁ : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I (i - 1) M)
      (localCohomologyAdicCone.{u, v} A T I (i - 1) M) j₁ σ₁)
    {j : ℕᵒᵖ} {σ : (localCohomologyAdicTower.{u, v} A T I i M).obj j ⟶
      (localCohomologyAdicCone.{u, v} A T I i M).pt}
    (h : EssentiallyConstantPro.IsEssentiallyConstantWith
      (localCohomologyAdicTower.{u, v} A T I i M) (localCohomologyAdicCone.{u, v} A T I i M)
      j σ) (m : ℕ) :
    ∃ k : ℕ, ∃ hmk : m ≤ k,
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map
        ((idealPowerTower.{u, v} I M).map (homOfLE hmk).op) = 0 := by
  obtain ⟨c, hmc, hc⟩ :=
    exists_forall_eq_zero_of_inclusion_eq_zero_of_isEssentiallyConstantWith T I M i h₁ m
  refine ⟨max c j.unop, hmc.trans (le_max_left _ _), ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ξ
  have hk : j.unop ≤ max c j.unop := le_max_right _ _
  refine hc (max c j.unop) (le_max_left _ _) ξ ?_
  apply injective_π_of_isEssentiallyConstantWith T I M i h hk
  have hS := idealPowerShortComplex_shortExact.{u, v} I M (max c j.unop)
  have h0 := localCohomologyMap_comp_localCohomologyMap.{u, v} T hS i
  exact (congrArg (fun f ↦ f.hom ξ) h0).trans
    (map_zero ((localCohomologyAdicCone.{u, v} A T I i M).π.app (op (max c j.unop))).hom).symm

end Stacks.LocalCohomology
