module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration
import all StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GlobalSectionsGeneration

/-!
# Global sections generating a zero-dimensional quotient: the coherent-submodule form

`AlgebraicGeometry.CohenMacaulayCurveSituation.epi_globalSectionsHom_comp` (Tag 0B5F) asks that
*no* nonzero submodule of `F` map injectively to `Q`. This file states the result with that
hypothesis asked of coherent submodules only, as in the source, whose exact sequence is one of
coherent modules.

## Main results

* `CohenMacaulayCurveSituation.isZero_firstCohomology_of_mono_of_supp_dim_le_zero_of_isCoherent`:
  `H¹` of a coherent submodule `F'` of `F` through which `α` factors vanishes.
* `CohenMacaulayCurveSituation.epi_globalSectionsHom_comp_of_isCoherent`: global sections of `F`
  surject onto `Q`, given the hypothesis on coherent submodules only.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-- Variant of `isZero_firstCohomology_of_mono_of_supp_dim_le_zero` in which the last hypothesis
is asked only of coherent submodules of `F`: if `F'` is a coherent submodule of `F` through which
`α` factors, `ι ≫ β ≠ 0`, `Q` has zero-dimensional support, and no nonzero coherent submodule of
`F` maps injectively to `Q`, then `H¹(X, F')` vanishes. -/
public theorem isZero_firstCohomology_of_mono_of_supp_dim_le_zero_of_isCoherent
    {ω F F' Q : S.X.Modules}
    (hωq : ω.IsQuasicoherent) (hF'c : F'.IsCoherent)
    (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (α : ω ⟶ F) (β : F ⟶ Q) (hαβ : α ≫ β = 0) (hex : (ShortComplex.mk α β hαβ).Exact)
    (ι : F' ⟶ F) [Mono ι] (α' : ω ⟶ F') (hα'ι : α' ≫ ι = α) (hne : ι ≫ β ≠ 0)
    (hQdim : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0)
    (hnosub : ∀ (M : S.X.Modules) (u : M ⟶ F), M.IsCoherent → Mono u → Mono (u ≫ β) →
      IsZero M) :
    IsZero (cohomologyOverField S.k S.f F' 1) := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := hωq
  have := hF'c
  have hF'q : F'.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F').1
  have := hF'q
  have hα'β : α' ≫ (ι ≫ β) = 0 := by rw [← Category.assoc, hα'ι, hαβ]
  have hjmono : Mono (cokernel.desc α' (ι ≫ β) hα'β) :=
    mono_cokernel_desc_of_exact α β hαβ hex ι α' hα'ι hα'β
  have hπj : cokernel.π α' ≫ cokernel.desc α' (ι ≫ β) hα'β = ι ≫ β := cokernel.π_desc _ _ _
  have hCc : (cokernel α').IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent hF'c
      (cokernel.π α')
  have hCdim : topologicalKrullDim (SheafOfModules.supp (cokernel α')) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_mono (cokernel.desc α' (ι ≫ β) hα'β) hjmono hQdim
  rcases isZero_firstCohomology_or_iso_biprod hωq hF'q hdual S.secondCohomologyVanishing hone α'
    (cokernel.π α') (cokernel.condition α') (ShortComplex.cokernelSequence_exact α')
    (isZero_firstCohomology_of_supp_dim_le_zero hCc hCdim) with h | ⟨e, he1, he2⟩
  · exact h
  · exfalso
    have hu : (biprod.inr ≫ e.inv) ≫ cokernel.π α' = 𝟙 (cokernel α') := by
      rw [← he2]; simp
    have heq : (biprod.inr ≫ e.inv ≫ ι) ≫ β = cokernel.desc α' (ι ≫ β) hα'β := by
      have h1 : (biprod.inr ≫ e.inv ≫ ι) ≫ β = (biprod.inr ≫ e.inv) ≫ (ι ≫ β) := by simp
      rw [h1]
      conv_lhs => rw [← hπj]
      rw [← Category.assoc, hu, Category.id_comp]
    have hmono1 : Mono ((biprod.inr ≫ e.inv ≫ ι) ≫ β) := by rw [heq]; exact hjmono
    have hmono2 : Mono (biprod.inr ≫ e.inv ≫ ι) :=
      have := hmono1
      mono_of_mono _ β
    have hzQ : IsZero (cokernel α') :=
      hnosub (cokernel α') (biprod.inr ≫ e.inv ≫ ι) hCc hmono2 hmono1
    refine hne ?_
    rw [← hπj, hzQ.eq_of_tgt (cokernel.π α') 0, zero_comp]

/-- Variant of `epi_globalSectionsHom_comp` in which the last hypothesis is asked only of coherent
submodules of `F`: the composite `globalSectionsHom F ≫ β` is an epimorphism. -/
public theorem epi_globalSectionsHom_comp_of_isCoherent {ω F Q : S.X.Modules}
    (hωq : ω.IsQuasicoherent) (hFq : F.IsQuasicoherent) (hFft : F.IsFiniteType)
    (hQq : Q.IsQuasicoherent) (hdual : S.FirstCohomologyDuality ω)
    (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
    (α : ω ⟶ F) (β : F ⟶ Q) (hαβ : α ≫ β = 0)
    (hex : (ShortComplex.mk α β hαβ).Exact) [Epi β]
    (hQdim : topologicalKrullDim (SheafOfModules.supp Q) ≤ 0)
    (htwo : 2 ≤ Module.finrank S.k (cohomologyOverField S.k S.f Q 0))
    (hnosub : ∀ (M : S.X.Modules) (u : M ⟶ F), M.IsCoherent → Mono u → Mono (u ≫ β) →
      IsZero M) :
    Epi (globalSectionsHom F ≫ β) := by
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have := hFq
  have := hFft
  have := hQq
  have hFc : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType F
  have hQc : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent hFc β
  have hγ0 : globalSectionsHom F ≫ (β ≫ cokernel.π (globalSectionsHom F ≫ β)) = 0 := by
    rw [← Category.assoc]; exact cokernel.condition _
  have hα0 : α ≫ (β ≫ cokernel.π (globalSectionsHom F ≫ β)) = 0 := by
    rw [← Category.assoc, hαβ, zero_comp]
  have hepiδ : Epi (β ≫ cokernel.π (globalSectionsHom F ≫ β)) := epi_comp _ _
  have hev : kernel.lift (β ≫ cokernel.π (globalSectionsHom F ≫ β)) (globalSectionsHom F) hγ0 ≫
      kernel.ι (β ≫ cokernel.π (globalSectionsHom F ≫ β)) = globalSectionsHom F :=
    kernel.lift_ι _ _ _
  have hα'ι : kernel.lift (β ≫ cokernel.π (globalSectionsHom F ≫ β)) α hα0 ≫
      kernel.ι (β ≫ cokernel.π (globalSectionsHom F ≫ β)) = α := kernel.lift_ι _ _ _
  have hne : kernel.ι (β ≫ cokernel.π (globalSectionsHom F ≫ β)) ≫ β ≠ 0 := by
    intro h
    refine globalSectionsHom_comp_ne_zero S.secondCohomologyVanishing hone α β hαβ hex htwo ?_
    rw [← hev, Category.assoc, h, comp_zero]
  have hCc : (cokernel (globalSectionsHom F ≫ β)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_epi_of_isQuasicoherent hQc
      (cokernel.π (globalSectionsHom F ≫ β))
  have hF'c : (kernel (β ≫ cokernel.π (globalSectionsHom F ≫ β))).IsCoherent :=
    have := hCc
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_mono_of_isQuasicoherent hFc
      (kernel.ι (β ≫ cokernel.π (globalSectionsHom F ≫ β)))
  have hF'1 : IsZero (cohomologyOverField S.k S.f
      (kernel (β ≫ cokernel.π (globalSectionsHom F ≫ β))) 1) :=
    isZero_firstCohomology_of_mono_of_supp_dim_le_zero_of_isCoherent hωq hF'c hdual hone α β hαβ hex
      (kernel.ι _) (kernel.lift _ α hα0) hα'ι hne hQdim hnosub
  have hsurj0 : Function.Surjective (cohomologyOverFieldMap S.k S.f
      (β ≫ cokernel.π (globalSectionsHom F ≫ β)) 0) :=
    surjective_cohomologyOverFieldMap_g_of_isZero
      (T := ShortComplex.mk (kernel.ι (β ≫ cokernel.π (globalSectionsHom F ≫ β)))
        (β ≫ cokernel.π (globalSectionsHom F ≫ β)) (kernel.condition _))
      (ShortComplex.shortExact_mk_kernel_ι _) 0 hF'1
  have hzero0 : ∀ a, cohomologyOverFieldMap S.k S.f
      (β ≫ cokernel.π (globalSectionsHom F ≫ β)) 0 a = 0 := fun a =>
    cohomologyOverFieldMap_zero_eq_zero_of_globalSectionsHom_comp S.f _ hγ0 a
  have hC0 : IsZero (cohomologyOverField S.k S.f (cokernel (globalSectionsHom F ≫ β)) 0) := by
    refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj0 a
    obtain ⟨b', rfl⟩ := hsurj0 b
    rw [hzero0, hzero0]
  have hπepi : Epi (cokernel.π (globalSectionsHom F ≫ β)) := inferInstance
  have hCdim : topologicalKrullDim
      (SheafOfModules.supp (cokernel (globalSectionsHom F ≫ β))) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_epi (cokernel.π (globalSectionsHom F ≫ β)) hπepi hQdim
  exact epi_of_isZero_cokernel _
    (isZero_of_supp_dim_le_zero_of_isZero_sections hCc hCdim hC0)


end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
