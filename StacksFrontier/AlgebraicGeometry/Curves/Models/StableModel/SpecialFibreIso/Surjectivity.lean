module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.FibreCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SurjectivityAfterBaseChange

/-!
# Surjectivity of `𝒪_{Y_k} ⟶ c_{k*}𝒪_{X_k}`

In the situation of
`Stacks.Models.RegularProperModelSituation.isZero_firstCohomologyStructureSheaf_fiber`, the
contraction `c : X ⟶ Y` is proper with `𝒪_Y = c_*𝒪_X`, and all of its fibres have dimension at
most one and vanishing `H¹` of the structure sheaf. By [Stacks, Tag 0E7I] surjectivity of
`𝒪_Y ⟶ c_*𝒪_X` survives the base change to the special fibre `Y_k ⟶ Y`, and that base change is
`c_k : X_k ⟶ Y_k` up to an isomorphism of the source.

## Main results

* `Stacks.Models.RegularProperModelSituation.epi_unitToPushforwardUnit_specialFiberMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange Stacks.Models.SpecialFibreIso

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)}
  {c₀ : S.specialFiber ⟶ Y₀}

/-- **`𝒪_{Y_k} ⟶ c_{k*}𝒪_{X_k}` is surjective** ([Stacks, Tag 0E7I] for `Y_k ⟶ Y`). -/
theorem epi_unitToPushforwardUnit_specialFiberMap
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R)) (c : S.X ⟶ Y)
    (hc : c ≫ pY = S.X_to_R) [IsProper c]
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (h : Y₀ ⟶ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) [IsFinite h]
    (hh : c₀ ≫ h = S.specialFiberMap pY c hc)
    (hgen : IsIso (S.genericFiberMap pY c hc)) :
    Epi (Scheme.Modules.unitToPushforwardUnit (S.specialFiberMap pY c hc)) := by
  have sq : IsPullback S.specialFiberι (S.specialFiberMap pY c hc) c
      (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) :=
    isPullback_pullbackMap _ _ _ hc _ (by rw [Category.comp_id, hc]) (by simp)
  have : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit c) := hO
  have hepi := epi_unitToPushforwardUnit_of_baseChange c
    (S.topologicalKrullDim_fiber_le_one pY c hc)
    (S.isZero_firstCohomologyStructureSheaf_fiber hc₀ pY c hc h hh hgen) inferInstance
    (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
  have heq : S.specialFiberMap pY c hc = sq.isoPullback.hom ≫ pullback.snd c
      (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) :=
    sq.isoPullback_hom_snd.symm
  rw [heq]
  exact epi_unitToPushforwardUnit_iso_comp _ _ hepi

end Stacks.Models.RegularProperModelSituation

end
