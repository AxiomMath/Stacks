module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation

/-!
# Cohomology commuting with base change descends along a proper surjection

[Stacks, Tag 0A4C](https://stacks.math.columbia.edu/tag/0A4C): let `f : X ⟶ Y` and `g : Y ⟶ Z` be
proper with `f` surjective. If cohomology commutes with base change for `f` and for `g ∘ f`, then
it does so for `g`.

The proof proceeds by dimension shifting along embeddings `A ⟶ f_* J` of sheaves `A` killed by
`ℓ > 0`, with `J` the underlying sheaf of an injective sheaf of `ℤ/ℓℤ`-modules on `X_étale`
(`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_embedding`). This replaces the
source's direct summand argument and its use of condition (2) of [Stacks, Tag 0A4B], and needs
neither [Stacks, Tag 0A3U] nor injectivity of the summand.

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_comp_of_surjective` — cohomology
  commuting with base change descends along a proper surjection ([Stacks, Tag 0A4C]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- An additive functor preserves the vanishing of `ℓ • 𝟙 A`. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A : C} {ℓ : ℕ} (h : ℓ • 𝟙 A = 0) :
    ℓ • 𝟙 (F.obj A) = 0 := by
  rw [← F.map_id, ← F.map_nsmul, h, F.map_zero]

/-- The base change map of `g` at `f_* J`, for the underlying sheaf `J` of an injective sheaf of
`ℤ/ℓℤ`-modules, is invertible when cohomology commutes with base change for `f` and `g ∘ f`. -/
theorem isIso_etaleAbelianSheafDerivedBaseChange_directImage_of_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : CohomologyCommutesWithBaseChange.{u, 0} f)
    (hgf : CohomologyCommutesWithBaseChange.{u, 0} (f ≫ g)) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (J : SheafOfModules.{u + 1} (zmodRingSheaf.{u + 1} X.smallEtaleTopology ℓ)) [Injective J]
    {Y' Z' : Scheme.{u}} (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (sq : IsPullback d g' g c) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} g c d g' sq.w
      ((etaleAbelianDirectImage.{u, 0} f).obj ((SheafOfModules.toSheaf _).obj J))) := by
  set G := (SheafOfModules.toSheaf _).obj J
  set e := pullback.fst f d
  set f' := pullback.snd f d
  have upper : IsPullback e f' f d := IsPullback.of_hasPullback f d
  have outer : IsPullback e (f' ≫ g') (f ≫ g) c := upper.paste_vert sq
  set K :=
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj G
  have D := etaleAbelianDerivedBaseChange_compDirectImage_app.{u, 0} f g (f ≫ g) rfl c d g' e f'
    (f' ≫ g') rfl sq.w upper.w outer.w K
  have hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G :=
    torsionSheafProperty_toSheaf_zmod.{u, 0} hℓ J
  have hout : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} (f ≫ g) c e (f' ≫ g') outer.w).app K) :=
    hgf c e (f' ≫ g') outer G hG
  have h₂ : IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f d e f' upper.w).app K) :=
    hf d e f' upper G hG
  rw [D] at hout
  have h3 := (isIso_comp_left_iff _ _).1 hout
  rw [← Category.assoc] at h3
  have h4 := (isIso_comp_right_iff _ _).1 h3
  have h5 := (isIso_comp_right_iff _ _).1 h4
  exact (NatTrans.isIso_app_iff_of_iso _
    (etaleAbelianDerivedDirectImageSingleIsoOfInjective f ℓ J)).2 h5

/-- **[Stacks, Tag 0A4C].** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be proper morphisms of schemes with
`f` surjective. If cohomology commutes with base change for `f` and for `g ∘ f`, then it does so
for `g`. -/
public theorem cohomologyCommutesWithBaseChange_of_comp_of_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] [Surjective f]
    (hf : CohomologyCommutesWithBaseChange.{u, 0} f)
    (hgf : CohomologyCommutesWithBaseChange.{u, 0} (f ≫ g)) :
    CohomologyCommutesWithBaseChange.{u, 0} g := by
  refine cohomologyCommutesWithBaseChange_of_embedding fun ℓ hℓ Y' Z' c d g' sq A hA ↦ ?_
  obtain ⟨J, hJ, i, hi⟩ :=
    exists_mono_toSheaf_injective ℓ _ (nsmul_id_obj_eq_zero (etaleAbelianInverseImage.{u, 0} f) hA)
  have : Injective J := hJ
  have hmono := mono_etaleAbelianUnit_of_surjective f A
  refine ⟨(etaleAbelianDirectImage.{u, 0} f).obj ((SheafOfModules.toSheaf _).obj J),
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app A ≫
      (etaleAbelianDirectImage.{u, 0} f).map i, inferInstance, ?_,
    isIso_etaleAbelianSheafDerivedBaseChange_directImage_of_comp f g hf hgf ℓ hℓ.pos J c d g' sq⟩
  exact nsmul_id_obj_eq_zero _ (nsmul_id_toSheaf_eq_zero.{u, 0} ℓ J)

end Stacks.EtaleCohomology

end
