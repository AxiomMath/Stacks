module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.ChartSections

/-!
# The theorem of the cube: existence and uniqueness of normalized sections on a chart

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator Stacks.FlatComplexNakayama

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  {N : (P A).Modules}
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  {V : A.left.Opens} {hV : IsAffineOpen V} {ι : Type u} [Fintype ι] [DecidableEq ι]
  {U : ι → A.left.Opens} {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)

attribute [local instance] faceModule

omit [Fintype ι] [DecidableEq ι] in
/-- **Uniqueness of normalized sections.** -/
theorem normSec_unique (h : ChartHyp hV U N)
    (hcone : LinearMap.ker (coneD₀ (d₀ hV U N) (phi₀ hV U ha₀ N hg₁ hg₂)) = ⊥)
    (s s' : Γ(N, (PV V).ι ''ᵁ ⊤)) (hs : NormSec N (g₁ := g₁) (g₂ := g₂) _ s)
    (hs' : NormSec N (g₁ := g₁) (g₂ := g₂) _ s') : s = s' := by
  have hc : secCochain N hV U (s - s') = 0 := by
    have hmem : secCochain N hV U (s - s') ∈
        LinearMap.ker (coneD₀ (d₀ hV U N) (phi₀ hV U ha₀ N hg₁ hg₂)) := by
      rw [LinearMap.mem_ker]
      refine Prod.ext (d₀_secCochain hV U (s - s')) ?_
      show phi₀ hV U ha₀ N hg₁ hg₂ (secCochain N hV U (s - s')) = 0
      refine (congrArg (phi₀ hV U ha₀ N hg₁ hg₂) (secCochain_sub hV U s s')).trans ?_
      rw [map_sub, phi₀_secCochain (hg₁ := hg₁) (hg₂ := hg₂) (hV := hV) (U := U) (ha₀ := ha₀) s hs,
        phi₀_secCochain (hg₁ := hg₁) (hg₂ := hg₂) (hV := hV) (U := U) (ha₀ := ha₀) s' hs',
        sub_self]
    rwa [hcone, Submodule.mem_bot] at hmem
  rw [← sub_eq_zero]
  have hcov' : (⊤ : (PV V).toScheme.Opens) ≤
      ⨆ j : Fin 1 → ι × ι, CechCochains.inter (chartCover U V) j := by
    rw [h.cov]
    exact iSup_le fun i => le_iSup_of_le (fun _ => i) (le_iInf fun _ => le_rfl)
  exact sec_ext (chartModule N V) (fun j : Fin 1 → ι × ι => CechCochains.inter (chartCover U V) j)
    ⊤ (fun _ => le_top) hcov' _ 0 fun j =>
      (congrArg (fun c : CX hV U N 0 => c.1 j) hc).trans (map_zero _).symm

variable [IsAlgClosed k] [LocallyOfFiniteType A.hom] [Smooth A.hom]

include ha₀ hg₁ hg₂ in
/-- **Existence of a normalized section** over a chart all of whose fibres are trivial. -/
theorem exists_normSec (h : ChartHyp hV U N)
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
    (hBc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ (A ⊗ A).hom.appTop))
    (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))
    (hall : ∀ (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) (hzV : z ⁻¹ᵁ V = ⊤),
      ∃ σ₀ : Γ(fibreModule z hzk hzV N, ⊤), IsGen _ σ₀) :
    ∃ s : Γ(N, (PV V).ι ''ᵁ ⊤), NormSec N (g₁ := g₁) (g₂ := g₂) _ s := by
  let I : Ideal (chartRing V) :=
    { carrier := {a | ∃ y : CX hV U N 0, d₀ hV U N y = 0 ∧ phi₀ hV U ha₀ N hg₁ hg₂ y = a • w₁ U}
      add_mem' := fun {a b} ⟨y, hy, hφ⟩ ⟨y', hy', hφ'⟩ =>
        ⟨y + y', by rw [map_add, hy, hy', add_zero], by rw [map_add, hφ, hφ', add_smul]⟩
      zero_mem' := ⟨0, map_zero _, by rw [map_zero, zero_smul]⟩
      smul_mem' := fun c a ⟨y, hy, hφ⟩ =>
        ⟨c • y, by rw [map_smul, hy, smul_zero], by rw [map_smul, hφ, smul_smul, smul_eq_mul]⟩ }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨z, hzk, hzV, rfl⟩ := exists_point_of_isMaximal hV m
    obtain ⟨σ₀, hσ₀⟩ := hall z hzk hzV
    obtain ⟨a, ha, y, hy0, hy⟩ := exists_lift_at ha₀ hg₁ hg₂ hU hUcov hAc hBc h hnorm z hzk hzV hσ₀
    exact ha (RingHom.mem_ker.mp (hIm ⟨y, hy0, hy⟩))
  obtain ⟨y, hy0, hy⟩ : (1 : chartRing V) ∈ I := hI ▸ Submodule.mem_top
  rw [one_smul] at hy
  obtain ⟨s, hs, -⟩ := normSec_of_cocycle hg₁ hg₂ hV ha₀ h hUcov y hy0 hy
  exact ⟨s, hs⟩

end Stacks.Cube

end
