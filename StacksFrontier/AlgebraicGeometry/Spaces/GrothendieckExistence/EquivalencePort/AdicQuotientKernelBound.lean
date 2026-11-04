module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AdicQuotientCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport

namespace Submodule.C1573
end Submodule.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Kernel and cokernel of a morphism reduced modulo a power of an ideal

Let `φ : M ⟶ N` be a morphism of `𝒪_F`-modules whose kernel and cokernel are annihilated by
`𝓚 ^ t`.  Then for any sheaf of ideals `𝓛` and any `b`, the reduction
`φ mod 𝓛^b : M / 𝓛^b M ⟶ N / 𝓛^b N` has cokernel annihilated by `𝓚 ^ t` and, for `M`, `N`,
`𝓛` cartesian on affine charts, kernel annihilated by `𝓚 ^ (2t)`.  This is the bound the source
leaves as "details omitted" in the proof of Stacks 08BC (citing Stacks 0888).

The algebra (`Submodule.C1573.smul_mem_of_map_mem_smul_top`): if `r` kills `ker φ` and `r'` maps
`N` into the image of `φ`, and `φ m ∈ J N`, then `r' • φ m ∈ φ (J M)`, so `r' m - w ∈ ker φ` for
some `w ∈ J M`, whence `r r' m ∈ J M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace Submodule

open _root_.Submodule.C1573
variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- **The algebraic core of the bound.** -/
theorem C1573.smul_mem_of_map_mem_smul_top (φ : M →ₗ[R] N) (K J : Ideal R)
    (hker : ∀ r ∈ K, ∀ m, φ m = 0 → r • m = 0) (hcok : ∀ r ∈ K, ∀ y, ∃ m, φ m = r • y)
    {r : R} (hr : r ∈ K * K) {m : M} (hm : φ m ∈ J • (⊤ : Submodule R N)) :
    r • m ∈ J • (⊤ : Submodule R M) := by
  have himg : ∀ r' ∈ K, ∀ y ∈ J • (⊤ : Submodule R N),
      ∃ w ∈ J • (⊤ : Submodule R M), φ w = r' • y := by
    intro r' hr' y hy
    refine Submodule.smul_induction_on hy (fun j hj n _ => ?_) (fun y y' hy hy' => ?_)
    · obtain ⟨z, hz⟩ := hcok r' hr' n
      exact ⟨j • z, Submodule.smul_mem_smul hj Submodule.mem_top, by
        rw [map_smul, hz, smul_comm]⟩
    · obtain ⟨w, hw, hw'⟩ := hy
      obtain ⟨w', hw2, hw2'⟩ := hy'
      exact ⟨w + w', Submodule.add_mem _ hw hw2, by rw [map_add, hw', hw2', smul_add]⟩
  refine Submodule.mul_induction_on hr (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · obtain ⟨w, hw, hw'⟩ := himg b hb _ hm
    have hk : φ (b • m - w) = 0 := by rw [map_sub, map_smul, hw', sub_self]
    have h2 := hker a ha _ hk
    rw [smul_sub, sub_eq_zero] at h2
    rw [mul_smul, h2]
    exact Submodule.smul_mem _ a hw
  · rw [add_smul]; exact Submodule.add_mem _ hx hy

end Submodule

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓚 𝓛 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **The cokernel of `φ mod 𝓛^b` is a quotient of the cokernel of `φ`.** -/
theorem C1573.isPowAnnihilated_cokernel_mapOfHom (t b : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) (h : IsPowAnnihilated B S hS F hF 𝓚 t (cokernel φ)) :
    IsPowAnnihilated B S hS F hF 𝓚 t
      (cokernel (smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓛 b φ)) := by
  let q : cokernel φ ⟶ cokernel (smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓛 b φ) :=
    cokernel.desc _ (smallEtaleAdicQuotientProjection B S hS F hF 𝓛 b N ≫ cokernel.π _) (by
      rw [← Category.assoc, ← smallEtaleAdicQuotientProjection_mapOfHom, Category.assoc,
        cokernel.condition, comp_zero])
  have : Epi q := by
    have : Epi (cokernel.π φ ≫ q) := by
      rw [cokernel.π_desc]; exact epi_comp _ _
    exact epi_of_epi (cokernel.π φ) q
  exact isPowAnnihilated_of_epi B S hS F hF 𝓚 t q h

/-- **The kernel of `φ mod 𝓛^b` is annihilated by `𝓚^(2t)`** when the kernel and the cokernel
of `φ` are annihilated by `𝓚^t`, for `M`, `N` and `𝓛` cartesian on affine charts. -/
theorem C1573.isPowAnnihilated_kernel_mapOfHom (t b : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) (hL : IsCartesianOnAffineCharts 𝓛.toSheafOfModules)
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N)
    (hk : IsPowAnnihilated B S hS F hF 𝓚 t (kernel φ))
    (hc : IsPowAnnihilated B S hS F hF 𝓚 t (cokernel φ)) :
    IsPowAnnihilated B S hS F hF 𝓚 (2 * t)
      (kernel (smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓛 b φ)) := by
  refine isPowAnnihilated_kernel_of_isAffine B S hS F hF 𝓚 _ _ fun U hU r hr x hx => ?_
  obtain ⟨m, rfl⟩ := surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓛 hL M hM b hU x
  have hφm : φ.val.app (op U) m ∈ chartSectionIdeal B S hS F hF 𝓛 U ^ b •
      (⊤ : Submodule (chartRing B S hS F hF U) (N.val.obj (op U))) := by
    rw [← ker_val_app_idealPowerQuotient_π B S hS F hF 𝓛 hL N hN b hU, LinearMap.mem_ker]
    have h1 := congrArg (fun q => q.val.app (op U) m)
      (smallEtaleAdicQuotientProjection_mapOfHom B S hS F hF 𝓛 b φ)
    exact h1.symm.trans hx
  have hr' : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t * chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t := by
    rw [← pow_add, ← two_mul]; exact hr
  have key := Submodule.C1573.smul_mem_of_map_mem_smul_top (φ.val.app (op U)).hom
    (chartIdeal B S hS ⟨F, hF⟩ 𝓚 U ^ t) (chartSectionIdeal B S hS F hF 𝓛 U ^ b)
    (fun r' hr' m' hm' => smul_eq_zero_of_isPowAnnihilated_kernel B S hS F hF 𝓚 hk U hr' hm')
    (fun r' hr' y => by
      have hy : r' • y ∈ LinearMap.range (φ.val.app (op U)).hom := by
        rw [← ker_val_app_cokernel_π_of_cartesian B S hS F hF φ hM hN hU, LinearMap.mem_ker,
          map_smul]
        exact hc U r' hr' _
      exact hy) hr' hφm
  rw [← ker_val_app_idealPowerQuotient_π B S hS F hF 𝓛 hL M hM b hU, LinearMap.mem_ker] at key
  exact (((smallEtaleAdicQuotientProjection B S hS F hF 𝓛 b M).val.app (op U)).hom.map_smul
    r m).symm.trans key

end AlgebraicGeometry.Space

end
