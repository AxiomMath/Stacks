module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFilteredColimit

/-!
# The four lemma for restriction on étale cohomology

Let `i : Y ⟶ X` be a morphism of schemes and `0 → F₁ → F₂ → F₃ → 0` a short exact sequence of
abelian sheaves on `X_étale`. Restriction along `i` maps the long exact cohomology sequence over
`X` to the one over `Y`. The two halves of the five lemma, in the precise degrees in which the
proof of Gabber's theorem ([Stacks, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)) uses
them, are recorded here, together with the passage of injectivity of restriction to filtered
colimits.

## Main results

* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_X₁_of_shortExact`.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₁_of_injective_X₃`.
* `Stacks.EtaleCohomology.injective_etaleCohomologyRestrictionMap_of_isColimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.Abelian

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

section FourLemma

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
include hS

/-- **Injectivity on the subsheaf.** If restriction is injective in degree `q + 1` and surjective
in degree `q` on the middle term, and injective in degree `q` on the quotient, then it is
injective in degree `q + 1` on the subsheaf. -/
theorem injective_etaleCohomologyRestrictionMap_X₁_of_shortExact (q : ℕ)
    (h₂inj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₂ (q + 1)))
    (h₂surj : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₂ q))
    (h₃inj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₁ (q + 1)) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, 0} i)
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  have h1 : etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₂ (q + 1)
      (ξ.comp (Ext.mk₀ S.f) (add_zero _)) = 0 := by
    rw [etaleCohomologyRestrictionMap_comp_mk₀, hξ, Ext.zero_comp]
  obtain ⟨ζ, hζ⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (h₂inj (h1.trans (map_zero _).symm)) rfl
  have h3 : (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ q ζ).comp hS'.extClass rfl = 0 := by
    rw [← etaleCohomologyRestrictionMap_comp_extClass i hS, hζ, hξ]
  obtain ⟨η, hη⟩ := Ext.covariant_sequence_exact₃ _ hS'
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ q ζ) rfl h3
  obtain ⟨η', hη'⟩ := h₂surj η
  have hlift : η'.comp (Ext.mk₀ S.g) (add_zero q) = ζ :=
    h₃inj (by rwa [etaleCohomologyRestrictionMap_comp_mk₀, hη'])
  rw [← hζ, ← hlift, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- **Surjectivity on the subsheaf.** If restriction is surjective in degree `q + 1` on the
middle term, injective in degree `q + 1` and surjective in degree `q` on the quotient, then it is
surjective in degree `q + 1` on the subsheaf. -/
theorem surjective_etaleCohomologyRestrictionMap_X₁_of_injective_X₃ (q : ℕ)
    (h₂surj : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₂ (q + 1)))
    (h₃inj : Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ (q + 1)))
    (h₃surj : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₁ (q + 1)) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, 0} i)
  intro ξ
  obtain ⟨θ, hθ⟩ := h₂surj (ξ.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map S.f))
    (add_zero _))
  have hg : etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₃ (q + 1)
      (θ.comp (Ext.mk₀ S.g) (add_zero _)) = 0 := by
    rw [etaleCohomologyRestrictionMap_comp_mk₀, hθ, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, ← Functor.map_comp, S.zero, Functor.map_zero, Ext.mk₀_zero,
      Ext.comp_zero]
  obtain ⟨ξ₀, hξ₀⟩ := Ext.covariant_sequence_exact₂ _ hS θ (h₃inj (hg.trans (map_zero _).symm))
  have hdiff : (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₁ (q + 1) ξ₀ - ξ).comp
      (Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map S.f)) (add_zero _) = 0 := by
    change ((Ext.mk₀ ((etaleAbelianInverseImage.{u, 0} i).map S.f)).postcomp _ (add_zero _))
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₁ (q + 1) ξ₀ - ξ) = 0
    rw [map_sub]
    change (etaleCohomologyRestrictionMap.{u, 0, u + 1} i S.X₁ (q + 1) ξ₀).comp _ (add_zero _) -
      ξ.comp _ (add_zero _) = 0
    rw [← etaleCohomologyRestrictionMap_comp_mk₀, hξ₀, hθ, sub_self]
  obtain ⟨κ, hκ⟩ := Ext.covariant_sequence_exact₁ _ hS' _ hdiff rfl
  obtain ⟨κ', hκ'⟩ := h₃surj κ
  refine ⟨ξ₀ - κ'.comp hS.extClass rfl, ?_⟩
  rw [map_sub, etaleCohomologyRestrictionMap_comp_extClass i hS, hκ', hκ, sub_sub_cancel]

end FourLemma

section Colimit

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {I : Type (u + 1)}
  [SmallCategory I] [IsFiltered I] {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {c : Cocone D} (hc : IsColimit c)

include hc

/-- **Injectivity of restriction passes to filtered colimits.** -/
theorem injective_etaleCohomologyRestrictionMap_of_isColimit {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (i : Y ⟶ X) (q : ℕ)
    (h : ∀ j, Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i (D.obj j) q)) :
    Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i c.pt q) := by
  have := preservesColimitsOfShape_functorH_smallEtale X q I
  have := preservesColimitsOfShape_functorH_smallEtale Y q I
  have : PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, 0} i) :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  let α := etaleCohomologyRestrictionNatTrans i q
  have hH := isColimitOfPreserves (smallEtaleFunctorH X q) hc
  have hG := isColimitOfPreserves (etaleAbelianInverseImage.{u, 0} i ⋙ smallEtaleFunctorH Y q) hc
  have hmono : ∀ j, Mono ((Functor.whiskerLeft D α).app j) := fun j =>
    (AddCommGrpCat.mono_iff_injective _).2 (h j)
  have : Mono (Functor.whiskerLeft D α) := NatTrans.mono_of_mono_app _
  have : Mono (colimMap (Functor.whiskerLeft D α)) := colim.map_mono _
  have key : α.app c.pt =
      (hH.coconePointUniqueUpToIso (colimit.isColimit (D ⋙ smallEtaleFunctorH X q))).hom ≫
      colimMap (Functor.whiskerLeft D α) ≫
        (hG.coconePointUniqueUpToIso (colimit.isColimit
          (D ⋙ etaleAbelianInverseImage.{u, 0} i ⋙ smallEtaleFunctorH Y q))).inv := by
    refine hH.hom_ext fun j => ?_
    have h2 := IsColimit.comp_coconePointUniqueUpToIso_inv hG (colimit.isColimit
      (D ⋙ etaleAbelianInverseImage.{u, 0} i ⋙ smallEtaleFunctorH Y q)) j
    rw [colimit.cocone_ι] at h2
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, colimit.cocone_ι, ι_colimMap_assoc, h2]
    simp only [Functor.mapCocone_ι_app, Functor.whiskerLeft_app]
    exact α.naturality (c.ι.app j)
  have : Mono (α.app c.pt) := by
    rw [key]
    infer_instance
  exact (AddCommGrpCat.mono_iff_injective _).1 this

end Colimit

end Stacks.EtaleCohomology
