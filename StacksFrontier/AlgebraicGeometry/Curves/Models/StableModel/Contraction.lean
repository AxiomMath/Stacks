module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SteinModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreMorphism
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.GenericFibreIso
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso
public import StacksFrontier.AlgebraicGeometry.Models.Basic

/-!
# Contracting a regular proper model onto the stable model of its special fibre

In the situation of [Stacks, Tag 0C61] let `c₀ : X_k ⟶ Y₀` be a stable contraction of the special
fibre ([Stacks, Tag 0E7Q]) and `ℒ₀` an ample invertible module on `Y₀`, and let `φ : X ⟶ P` be a
morphism over `R` to a proper locally Noetherian `R`-scheme with an ample invertible `A` such that
`c₀^*ℒ₀ ≅ (φ^*A)|_{X_k}`. Then the first factor `c : X ⟶ Y` of the Stein factorization of `φ`
is an isomorphism on generic fibres, so `Y` is a proper model of the curve, and on special fibres
it is `c₀` followed by an isomorphism `Y₀ ≅ Y_k`.

## Main results

* `Stacks.Models.RegularProperModelSituation.exists_model_of_isStableContraction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **A proper model of the curve whose special fibre is the stable model of `X_k`.** -/
theorem exists_model_of_isStableContraction
    {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    (L₀ : Y₀.Modules) [SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    (hL₀ : Scheme.Modules.IsAmple Y₀ L₀)
    {P : Scheme.{u}} (q : P ⟶ Spec (.of S.R)) [IsProper q] [IsLocallyNoetherian P]
    (φ : S.X ⟶ P) (hφ : φ ≫ q = S.X_to_R)
    (A : P.Modules) [SheafOfModules.IsInvertible P.toRingedSpace.presheaf
      (structureSheafRing P.toRingedSpace).property A]
    (hA : Scheme.Modules.IsAmple P A)
    (α : (Scheme.Modules.pullback c₀).obj L₀ ≅
      (Scheme.Modules.pullback S.specialFiberι).obj ((Scheme.Modules.pullback φ).obj A)) :
    ∃ (Y : Scheme.{u}) (pY : Y ⟶ Spec (.of S.R))
      (eK : S.C ≅ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))),
      IsModel S.C_to_K pY eK ∧ IsProper pY ∧
        ∃ e₀ : pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) ≅ Y₀,
          e₀.hom ≫ g₀ = pullback.snd _ _ := by
  obtain ⟨Y, c, π, hcπ, hcp, hπ, hsurj, hO, -, hflat⟩ :=
    S.exists_steinFactorization_model q φ hφ
  have hc : c ≫ π ≫ q = S.X_to_R := by rw [← Category.assoc, hcπ, hφ]
  obtain ⟨h, hfin, hh⟩ :=
    S.exists_isFinite_comp_eq_specialFiberMap hc₀ L₀ hL₀ q φ hφ A hA α c π hcπ hsurj hO
  have hgen := S.isIso_genericFiberMap hc₀ (π ≫ q) c hc hO h hh
  obtain ⟨e, he⟩ := S.exists_iso_comp_eq_specialFiberMap hc₀ (π ≫ q) c hc hsurj hO h hh hgen
  refine ⟨Y, π ≫ q, S.genericFiberIso ≪≫ asIso (S.genericFiberMap (π ≫ q) c hc), ⟨hflat,
    inferInstance, inferInstance, ?_⟩, inferInstance, e.symm, ?_⟩
  · simp only [Iso.trans_hom, asIso_hom, Category.assoc, genericFiberMap_snd]
    exact S.genericFiberIso_over_K
  · have : IsProper g₀ := hc₀.isProper
    rw [Iso.symm_hom, Iso.inv_comp_eq]
    refine hc₀.ext (gY' := 𝟙 (Spec (.of S.k))) ?_
    rw [reassoc_of% he, specialFiberMap_snd, hc₀.comp_eq]

end Stacks.Models.RegularProperModelSituation

end
