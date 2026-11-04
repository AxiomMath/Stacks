module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Factorization
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStable
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ComapBaseChange
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# Lifting a section to the kernel of an invertible quotient on a hyperplane

Let `ℰ` be finite locally free of rank `r + 2` on a scheme `Y`, `τ : ℰ ⟶ ℒ` an epimorphism onto
an invertible module, `σ ∈ Γ(Y, ℰ)` and `t = τ(σ) ∈ Γ(Y, ℒ)`, with zero scheme
`j : Z(t) ⟶ Y`. On `Z(t)` the section `j^* σ` is killed by `j^* τ`, so it comes from a unique
section `σ'` of the kernel `ℰ' = ker(j^* τ)`, finite locally free of rank `r + 1`. Its zero scheme
is the inverse image of the zero scheme of `σ`:

  `Z(σ') = j⁻¹(Z(σ))`  as closed subschemes of `Z(t)`.

This is the step of [Stacks, Tag 0FA9]'s proof where `π^* s` restricted to `Z(t)` "comes from a
unique element `s'` of `Γ(Z(t), ℰ'|_{Z(t)})`" with `Z(s') = Z(π^* s)`.

## Main definitions

* `Stacks.Chow.SectionZeroScheme.liftModule` — the module `ℰ' = ker(j^* τ)` on `Z(t)`.
* `Stacks.Chow.SectionZeroScheme.liftSection` — the section `σ'` of `ℰ'`.

## Main results

* `Stacks.Chow.SectionZeroScheme.kernel_ι_app_liftSection` — `σ'` maps to `j^* σ`.
* `Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_liftSection` — `Z(σ') = j⁻¹(Z(σ))`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

/-- A monomorphism of modules is injective on sections. -/
alias app_injective_of_mono := Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono

variable {Y : Scheme.{u}} {E L : Y.Modules} (τ : E ⟶ L) [hτ : Epi τ]
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
  (σ : Γ(E, ⊤))

/-- The zero scheme `Z(t)` of `t = τ(σ)`. -/
abbrev hyperplane : Y.IdealSheafData :=
  Stacks.Divisors.zeroScheme Y L (τ.app ⊤ σ)

/-- **The module `ℰ' = ker(j^* τ)` on `Z(t)`.** -/
abbrev liftModule : (hyperplane τ σ).subscheme.Modules :=
  kernel ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).map τ)

/-- The pullback `j^* τ` of `τ` to `Z(t)` is an epimorphism. -/
instance epi_pullback_map_τ :
    Epi ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).map τ) :=
  inferInstance

omit hτ in
/-- The pullback of `ℒ` to `Z(t)` is invertible. -/
theorem isInvertible_pullback_L :
    AlgebraicGeometry.SheafOfModules.IsInvertible (hyperplane τ σ).subscheme.presheaf
      (hyperplane τ σ).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).obj L) :=
  Stacks.Divisors.pullback_isInvertible (hyperplane τ σ).subschemeι L

/-- **`ℰ'` is finite locally free of rank `r + 1`.** -/
theorem isFiniteLocallyFreeOfRank_liftModule (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 2)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (liftModule τ σ) (r + 1) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible _
    (epi_pullback_map_τ τ σ) (isInvertible_pullback_L τ σ) r
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ E (r + 2))

omit hτ in
/-- On `Z(t)` the section `j^* σ` is killed by `j^* τ`. -/
theorem pullback_τ_app_pullbackGlobalSections :
    ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).map τ).app ⊤
        (pullbackGlobalSections (hyperplane τ σ).subschemeι E σ) = 0 := by
  rw [pullback_map_app_pullbackGlobalSections]
  exact (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme Y L _
    (hyperplane τ σ).subschemeι).2 ⟨𝟙 _, by simp⟩

omit hτ in
/-- There is a section of `ℰ'` whose image in `j^* ℰ` is `j^* σ`. -/
theorem exists_liftSection :
    ∃ s' : Γ(liftModule τ σ, ⊤),
      (kernel.ι ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).map τ)).app ⊤ s' =
        pullbackGlobalSections (hyperplane τ σ).subschemeι E σ :=
  Stacks.SheafOfModules.exists_kernel_section _ (Opposite.op ⊤) _
    (pullback_τ_app_pullbackGlobalSections τ σ)

/-- **The section `σ'` of `ℰ'`** lifting `j^* σ`. -/
def liftSection : Γ(liftModule τ σ, ⊤) := (exists_liftSection τ σ).choose

omit hτ in
/-- The section `σ'` maps to `j^* σ` under the inclusion `ℰ' ⟶ j^* ℰ`. -/
theorem kernel_ι_app_liftSection :
    (kernel.ι ((Scheme.Modules.pullback (hyperplane τ σ).subschemeι).map τ)).app ⊤
        (liftSection τ σ) =
      pullbackGlobalSections (hyperplane τ σ).subschemeι E σ :=
  (exists_liftSection τ σ).choose_spec

/-- If `K.subscheme` factors through `I.subscheme`, then `I ≤ K`. -/
private theorem le_of_subschemeι_factorsThrough {X : Scheme.{u}} {I K : X.IdealSheafData}
    (h : ∃ g : K.subscheme ⟶ I.subscheme, g ≫ I.subschemeι = K.subschemeι) : I ≤ K := by
  have := (_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker _ _).1 h
  rwa [Scheme.IdealSheafData.ker_subschemeι] at this

/-- For `f : T ⟶ Z(t)`, `f^* σ'` vanishes exactly when `(f ≫ j)^* σ` does. -/
theorem pullbackGlobalSections_liftSection_eq_zero_iff {T : Scheme.{u}}
    (f : T ⟶ (hyperplane τ σ).subscheme) :
    pullbackGlobalSections f (liftModule τ σ) (liftSection τ σ) = 0 ↔
      pullbackGlobalSections (f ≫ (hyperplane τ σ).subschemeι) E σ = 0 := by
  set j := (hyperplane τ σ).subschemeι
  set ι := kernel.ι ((Scheme.Modules.pullback j).map τ)
  have hmono : Mono ((Scheme.Modules.pullback f).map ι) :=
    Stacks.Divisors.mono_pullback_map_kernel_ι f _
      ⟨_, isInvertible_pullback_L τ σ, (Scheme.Modules.pullback j).map τ,
        epi_pullback_map_τ τ σ⟩
  have hnat := pullback_map_app_pullbackGlobalSections f ι (liftSection τ σ)
  rw [kernel_ι_app_liftSection] at hnat
  rw [Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff, ← hnat]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => app_injective_of_mono _ ⊤ (h.trans (map_zero _).symm)⟩

/-- **`Z(σ') = j⁻¹(Z(σ))`.** -/
theorem zeroSchemeOfSection_liftSection (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 2)] :
    zeroSchemeOfSection _ (liftModule τ σ) (liftSection τ σ) =
      (zeroSchemeOfSection Y E σ).comap (hyperplane τ σ).subschemeι := by
  have := isFiniteLocallyFreeOfRank_liftModule τ σ r
  set j := (hyperplane τ σ).subschemeι
  set I := zeroSchemeOfSection Y E σ
  set I' := zeroSchemeOfSection _ (liftModule τ σ) (liftSection τ σ)
  apply le_antisymm
  · refine le_of_subschemeι_factorsThrough ?_
    refine (pullbackGlobalSections_eq_zero_iff_factorsThrough (liftModule τ σ) (r + 1)
      (liftSection τ σ) _).1 ?_
    refine (pullbackGlobalSections_liftSection_eq_zero_iff τ σ _).2 ?_
    refine (pullbackGlobalSections_eq_zero_iff_factorsThrough E (r + 2) σ _).2 ?_
    exact ⟨Stacks.Chow.comapSubschemeMap I j, Stacks.Chow.comapSubschemeMap_comp_subschemeι I j⟩
  · have h : I ≤ (I'.subschemeι ≫ j).ker := by
      refine (_root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker I _).1 ?_
      refine (pullbackGlobalSections_eq_zero_iff_factorsThrough E (r + 2) σ _).1 ?_
      exact (pullbackGlobalSections_liftSection_eq_zero_iff τ σ _).1
        (pullbackGlobalSections_subschemeι_eq_zero (liftModule τ σ) (r + 1) (liftSection τ σ))
    rw [← Scheme.IdealSheafData.map_ker] at h
    have h' := Scheme.IdealSheafData.le_map_iff_comap_le.1 h
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h'

omit hτ in
/-- **`Z(σ) ⊆ Z(t)`**: the ideal of the hyperplane `Z(τ σ)` is contained in that of `Z(σ)`. -/
theorem hyperplane_le_zeroSchemeOfSection (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    hyperplane τ σ ≤ zeroSchemeOfSection Y E σ := by
  refine le_of_subschemeι_factorsThrough ?_
  refine (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme Y L _ _).1 ?_
  rw [← pullback_map_app_pullbackGlobalSections,
    pullbackGlobalSections_subschemeι_eq_zero E r σ, map_zero]

end Stacks.Chow.SectionZeroScheme

end
