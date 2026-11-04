module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelImageStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAffineChartCokernelSections

/-!
# Annihilation by a power of a sheaf of ideals, checked on affine charts

Annihilation of an `𝒪_F`-module by `𝓘 ^ k` (`AlgebraicGeometry.Space.IsPowAnnihilated`) can be
checked over the affine étale charts; for the kernel and the cokernel of a morphism of modules
cartesian on affine charts it is a condition on the map of sections over affine charts.
-/

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **Annihilation by `𝓘 ^ k` is checked on affine charts.** -/
theorem C1573.isPowAnnihilated_of_isAffine (k : ℕ) (M : Modules.{u, u} B S hS F hF)
    (h : ∀ U : SmallEtale B S hS F, IsAffine (chartScheme U) → ∀ r : chartRing B S hS F hF U,
      r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k → ∀ x : M.val.obj (op U), r • x = 0) :
    IsPowAnnihilated B S hS F hF 𝓘 k M := by
  intro U r hr x
  have key : ∀ (V : (smallEtaleRingedSite B S hS F hF).C) (g : V ⟶ U), IsAffine (chartScheme V) →
      M.val.map g.op (r • x) = M.val.map g.op 0 := fun V g hV => by
    rw [map_zero]
    refine (PresheafOfModules.map_smul M.val g.op r x).trans ?_
    exact h V hV _ (chartRestrict_mem_chartIdeal_pow B S hS F hF 𝓘 g k hr) _
  exact SmallEtale.C1573.eq_of_forall_isAffine B S hS F hF
    (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget M) fun V g hV => key V g hV

/-- If `𝓘 ^ k` annihilates `M`, then over every chart every element of `𝓘 ^ k` annihilates the
sections of `M`. -/
theorem C1573.smul_eq_zero_of_isPowAnnihilated {k : ℕ} {M : Modules.{u, u} B S hS F hF}
    (h : IsPowAnnihilated B S hS F hF 𝓘 k M) (U : SmallEtale B S hS F)
    {r : chartRing B S hS F hF U} (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k)
    (x : M.val.obj (op U)) : r • x = 0 :=
  h U r hr x

/-- **The kernel of a morphism is annihilated by `𝓘 ^ k`** as soon as, over every affine chart,
`𝓘 ^ k` annihilates the kernel of the map of sections. -/
theorem C1573.isPowAnnihilated_kernel_of_isAffine (k : ℕ) {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N)
    (h : ∀ U : SmallEtale B S hS F, IsAffine (chartScheme U) → ∀ r : chartRing B S hS F hF U,
      r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k → ∀ m : M.val.obj (op U),
        φ.val.app (op U) m = 0 → r • m = 0) :
    IsPowAnnihilated B S hS F hF 𝓘 k (kernel φ) := by
  refine isPowAnnihilated_of_isAffine B S hS F hF 𝓘 k _ fun U hU r hr x => ?_
  have hinj : Function.Injective ((kernel.ι φ).val.app (op U)) :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstanceAs (Mono ((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (op (U : (smallEtaleRingedSite B S hS F hF).C))).map (kernel.ι φ))))
  refine hinj ?_
  rw [map_zero]
  exact (((kernel.ι φ).val.app (op U)).hom.map_smul r x).trans
    (h U hU r hr _ (congrArg (fun q => q.val.app (op U) x) (kernel.condition φ)))

/-- If `𝓘 ^ k` annihilates the kernel of `φ`, then over every chart it annihilates the kernel of
the map of sections. -/
theorem C1573.smul_eq_zero_of_isPowAnnihilated_kernel {k : ℕ} {M N : Modules.{u, u} B S hS F hF}
    {φ : M ⟶ N} (h : IsPowAnnihilated B S hS F hF 𝓘 k (kernel φ)) (U : SmallEtale B S hS F)
    {r : chartRing B S hS F hF U} (hr : r ∈ chartIdeal B S hS ⟨F, hF⟩ 𝓘 U ^ k)
    {m : M.val.obj (op U)} (hm : φ.val.app (op U) m = 0) : r • m = 0 := by
  have hm' : m ∈ LinearMap.ker (φ.val.app (op U)).hom := hm
  rw [← range_val_app_kernel_ι] at hm'
  obtain ⟨x, rfl⟩ := hm'
  refine (((kernel.ι φ).val.app (op U)).hom.map_smul r x).symm.trans ?_
  rw [h U r hr x, map_zero]

end AlgebraicGeometry.Space

end
