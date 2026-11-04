module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.FibreMaps
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.Injectivity
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.Surjectivity
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SplittingStep
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel

/-!
# The special fibre of the contraction is the stable model of the special fibre

In the situation of [Stacks, Tag 0C61] let `c : X ⟶ Y` be a proper surjective morphism over
`Spec R` with `𝒪_Y = c_*𝒪_X`, an isomorphism on generic fibres, and suppose that on special fibres
`c_k = h ∘ c₀` with `c₀ : X_k ⟶ Y₀` a stable contraction ([Stacks, Tag 0E7Q]) and `h` finite. Then
`h` is an isomorphism `Y₀ ≅ Y_k`.

The fibres of `c` have dimension at most one and `H¹(X_y, 𝒪) = 0`
(`Stacks.Models.RegularProperModelSituation.isZero_firstCohomologyStructureSheaf_fiber`): by
[Stacks, Tag 0E7F] part (2) it suffices that `R¹` of the structure sheaf vanishes along the base
change of `c` to the fibre of `Y` containing `y`, which is `c_K`, an isomorphism, or
`c_k = c₀ ≫ h`, where `R¹(c₀ ≫ h)_*𝒪 ≅ R¹h_*𝒪_{Y₀} = 0` since `c₀` is acyclic and `h` is affine.
So by [Stacks, Tag 0E7I] the map `𝒪_{Y_k} ⟶ c_{k*}𝒪_{X_k}` is surjective
(`…epi_unitToPushforwardUnit_specialFiberMap`); it is injective because a function on an open of
`X` vanishing on `X_k` is divisible by the uniformizer, `X` being flat over `R`
(`…mono_unitToPushforwardUnit_specialFiberMap`). Hence `𝒪_{Y_k} = c_{k*}𝒪_{X_k}`, so
`𝒪_{Y_k} = h_*𝒪_{Y₀}` as `𝒪_{Y₀} = c₀_*𝒪_{X_k}`, and the affine morphism `h` is an isomorphism.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_iso_comp_eq_specialFiberMap`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The special fibre of the contraction is the stable model of the special fibre.** -/
theorem exists_iso_comp_eq_specialFiberMap
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R)) [IsProper pY] (c : S.X ⟶ Y)
    (hc : c ≫ pY = S.X_to_R) [IsProper c] (_hsurj : Function.Surjective c)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (h : Y₀ ⟶ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) [IsFinite h]
    (hh : c₀ ≫ h = S.specialFiberMap pY c hc)
    (hgen : IsIso (S.genericFiberMap pY c hc)) :
    ∃ e : Y₀ ≅ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))),
      c₀ ≫ e.hom = S.specialFiberMap pY c hc := by
  have hepi := S.epi_unitToPushforwardUnit_specialFiberMap hc₀ pY c hc hO h hh hgen
  have hmono := S.mono_unitToPushforwardUnit_specialFiberMap pY c hc hO
  have hk : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (S.specialFiberMap pY c hc).toRingCatSheafHom) :=
    isIso_of_mono_of_epi (C := Scheme.Modules _)
      (Scheme.Modules.unitToPushforwardUnit (S.specialFiberMap pY c hc))
  rw [← hh] at hk
  have hhO := Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_of_comp c₀ h
    hc₀.isIso_unitToPushforwardObjUnit hk
  have : IsIso (h ∣_ ⊤) := Stacks.GlueSquishFactor.isIso_of_isAffineHom_of_isIso_app h
    fun V _ _ => Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit h hhO V
  have : IsIso h :=
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := h) (fun _ : Unit => ⊤) (by simp)).mpr fun _ => inferInstance
  exact ⟨asIso h, hh⟩

end Stacks.Models.RegularProperModelSituation

end
