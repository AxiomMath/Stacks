module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected

/-!
# The fibre maps of a morphism of models

Let `S` be the situation of a regular proper model `X ⟶ Spec R` and let `c : X ⟶ Y` be a morphism
to a scheme `Y` over `Spec R`, compatible with the structure morphisms. This file names the
induced morphisms of special fibres `X_k ⟶ Y_k` and of generic fibres `X_K ⟶ Y_K`, as the
morphisms of fibre products induced by `c`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.specialFiberMap`: `c_k : X_k ⟶ Y_k`.
* `Stacks.Models.RegularProperModelSituation.genericFiberMap`: `c_K : X_K ⟶ Y_K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u}) {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R))
  (c : S.X ⟶ Y) (hc : c ≫ pY = S.X_to_R)

/-- The morphism of special fibres `X_k ⟶ Y_k` induced by `c : X ⟶ Y` over `Spec R`. -/
def specialFiberMap :
    S.specialFiber ⟶ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) :=
  pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hc]) (by simp)

/-- The morphism of generic fibres `X_K ⟶ Y_K` induced by `c : X ⟶ Y` over `Spec R`. -/
def genericFiberMap :
    pullback S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) ⟶
      pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) :=
  pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hc]) (by simp)

/-- The special fibre map `c_k` followed by the projection `Y_k ⟶ Y` equals the inclusion `X_k ⟶ X`
followed by `c`. -/
@[reassoc (attr := simp)]
theorem specialFiberMap_fst :
    S.specialFiberMap pY c hc ≫ pullback.fst _ _ = S.specialFiberι ≫ c :=
  pullback.lift_fst _ _ _

/-- The special fibre map `c_k` is compatible with the structure morphisms to `Spec k`. -/
@[reassoc (attr := simp)]
theorem specialFiberMap_snd :
    S.specialFiberMap pY c hc ≫ pullback.snd _ _ = S.specialFiberToSpec :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The generic fibre map `c_K` followed by the projection `Y_K ⟶ Y` equals the projection
`X_K ⟶ X` followed by `c`. -/
@[reassoc (attr := simp)]
theorem genericFiberMap_fst :
    S.genericFiberMap pY c hc ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c :=
  pullback.lift_fst _ _ _

/-- The generic fibre map `c_K` is compatible with the structure morphisms to `Spec K`. -/
@[reassoc (attr := simp)]
theorem genericFiberMap_snd :
    S.genericFiberMap pY c hc ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end Stacks.Models.RegularProperModelSituation

end
