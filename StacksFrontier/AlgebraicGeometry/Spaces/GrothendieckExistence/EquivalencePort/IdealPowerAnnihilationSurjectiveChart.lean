module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBijectivePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentCompletionExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Annihilation by a power of an ideal, checked on one surjective affine chart

Let `𝓘` be a sheaf of ideals and `M` a module on an algebraic space `F`, both cartesian on affine
charts, and let `U` be an affine étale chart of `F` which is surjective.  If `𝓘(U) ^ k` kills
`M(U)` then `𝓘 ^ k M = 0`
(`AlgebraicGeometry.Space.C1573.idealPowerMultiple_eq_bot_of_surjective_affineChart`): the
projection `M ⟶ M / 𝓘 ^ k M` is bijective on the sections over `U`, hence over every affine chart
above `U`, hence an isomorphism because `U` covers `F`.

For a morphism `φ : M ⟶ N` of modules cartesian on affine charts, the kernel and the cokernel are
cartesian on affine charts, and their sections over the affine chart `U` are the kernel and the
cokernel of `φ(U)`; so annihilation of `Ker(φ)` and `Coker(φ)` is read off the map of sections
over `U`
(`AlgebraicGeometry.Space.C1573.idealPowerMultiple_kernel_eq_bot_of_surjective_affineChart`,
`AlgebraicGeometry.Space.C1573.idealPowerMultiple_cokernel_eq_bot_of_surjective_affineChart`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **Annihilation by `𝓘 ^ k` of a module cartesian on affine charts is checked on one surjective
affine chart.** -/
theorem C1573.idealPowerMultiple_eq_bot_of_surjective_affineChart
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hUsurj : IsSurjective B S hS U.1.hom)
    (h : ∀ r ∈ chartSectionIdeal B S hS F hF 𝓘 U ^ k, ∀ x : M.val.obj (op U), r • x = 0) :
    idealPowerMultiple B S hS F hF 𝓘 k M = ⊥ := by
  have hbijU : Function.Bijective
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op U)) := by
    refine ⟨?_, surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hU⟩
    rw [← LinearMap.ker_eq_bot, ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k
      hU, eq_bot_iff]
    exact Submodule.smul_le.2 fun r hr x _ => (h r hr x).symm ▸ Submodule.zero_mem _
  have hQcart := isCartesianOnAffineCharts_idealPowerQuotient B S hS F hF 𝓘 hIcart M hMcart k
  have hiso : IsIso (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι) := by
    refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map
      (SmallEtale.coversTop_of_isSurjective B S hS F hF U hUsurj) _ fun _ => ?_
    refine SmallEtale.isIso_of_bijective_app_of_isAffine B S hS F hF U _ fun Z hZaff => ?_
    exact bijective_val_app_of_bijective_of_cartesian B S hS F hF _ hMcart hQcart hU hZaff Z.hom
      hbijU
  refine (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).2 fun V r hr x => ?_
  have hmem := le_idealPowerMultiple_obj B S hS F hF 𝓘 k M V
    (Submodule.smul_mem_smul hr (Submodule.mem_top : x ∈ ⊤))
  have h0 := (cokernel_π_app_eq_zero_iff B S hS F hF _ (op V) (r • x)).2 hmem
  have hbij := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op V)).map
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι))
  exact hbij.1 (h0.trans
    ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op V)).hom.map_zero.symm)

/-- **Annihilation of a kernel by `𝓘 ^ k`, checked on one surjective affine chart**: it suffices
that `𝓘(U) ^ k` kills the kernel of the map of sections over `U`. -/
theorem C1573.idealPowerMultiple_kernel_eq_bot_of_surjective_affineChart
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) (hM : IsCartesianOnAffineCharts M)
    (hN : IsCartesianOnAffineCharts N) (k : ℕ)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hUsurj : IsSurjective B S hS U.1.hom)
    (h : ∀ r ∈ chartSectionIdeal B S hS F hF 𝓘 U ^ k, ∀ x : M.val.obj (op U),
      φ.val.app (op U) x = 0 → r • x = 0) :
    idealPowerMultiple B S hS F hF 𝓘 k (kernel φ) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_surjective_affineChart B S hS F hF 𝓘 hIcart _
    (isCartesianOnAffineCharts_kernel φ hM hN) k U hU hUsurj fun r hr x => ?_
  have hinj : Function.Injective ((kernel.ι φ).val.app (op U)) :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstanceAs (Mono ((SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
        (op (U : (smallEtaleRingedSite B S hS F hF).C))).map (kernel.ι φ))))
  refine hinj ?_
  rw [map_zero]
  refine ((kernel.ι φ).val.app (op U)).hom.map_smul r x |>.trans ?_
  refine h r hr _ ?_
  exact congrArg (fun q => q.val.app (op U) x) (kernel.condition φ)

/-- **Annihilation of a cokernel by `𝓘 ^ k`, checked on one surjective affine chart**: it
suffices that `𝓘(U) ^ k` pushes every section of the target over `U` into the image of the map of
sections. -/
theorem C1573.idealPowerMultiple_cokernel_eq_bot_of_surjective_affineChart
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N) (hM : IsCartesianOnAffineCharts M)
    (hN : IsCartesianOnAffineCharts N) (k : ℕ)
    (U : SmallEtale B S hS F) (hU : IsAffine (chartScheme U))
    (hUsurj : IsSurjective B S hS U.1.hom)
    (h : ∀ r ∈ chartSectionIdeal B S hS F hF 𝓘 U ^ k, ∀ y : N.val.obj (op U),
      ∃ x : M.val.obj (op U), φ.val.app (op U) x = r • y) :
    idealPowerMultiple B S hS F hF 𝓘 k (cokernel φ) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_surjective_affineChart B S hS F hF 𝓘 hIcart _
    (isCartesianOnAffineCharts_cokernel_of_cartesian φ hM hN) k U hU hUsurj fun r hr z => ?_
  obtain ⟨y, rfl⟩ := surjective_val_app_cokernel_π_of_cartesian φ hM hN U hU z
  obtain ⟨x, hx⟩ := h r hr y
  refine (((cokernel.π φ).val.app (op U)).hom.map_smul r y).symm.trans ?_
  rw [← hx]
  exact congrArg (fun q => q.val.app (op U) x) (cokernel.condition φ)

end AlgebraicGeometry.Space

end
