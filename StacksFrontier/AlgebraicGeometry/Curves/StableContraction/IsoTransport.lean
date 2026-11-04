module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre

/-!
# The conditions of Stacks 0E7Q are invariant under isomorphism of the target

Let `X` be proper over a field `k` with `H⁰(X, 𝒪_X) = k` and `c : X ⟶ Y` a morphism over `k`
satisfying the three conditions of [Stacks, Tag 0E7Q]
(`Stacks.Curves.StableModel.IsStableContraction`), and let `e : Y' ≅ Y` be an isomorphism of
schemes. Then `c' : X ⟶ Y'` with `c' ≫ e = c` satisfies them as well, `Y'` being over `k` through
`e`.

## Main results

* `Stacks.Curves.StableModel.IsStableContraction.of_iso`: the conditions of [Stacks, Tag 0E7Q]
  transport along an isomorphism `e : Y' ≅ Y` of the target.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X Y Y' : Scheme.{u}}

open Stacks.AlgebraicGeometry.FlatBaseChangeDerived in
/-- **The conditions of [Stacks, Tag 0E7Q] are invariant under isomorphism of the target.** If
`c : X ⟶ Y` satisfies them over `k` and `e : Y' ≅ Y` is an isomorphism, then `c' : X ⟶ Y'` with
`c' ≫ e = c` satisfies them for `Y'` over `k` through `e`. -/
theorem IsStableContraction.of_iso {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (h : IsStableContraction f gY c) (e : Y' ≅ Y) (c' : X ⟶ Y')
    (hc : c' ≫ e.hom = c) : IsStableContraction f (e.hom ≫ gY) c' := by
  have : IsProper gY := h.isProper
  have : IsProper c := by
    have : IsProper (c ≫ gY) := by rw [h.comp_eq]; infer_instance
    exact IsProper.of_comp c gY
  have hsq : IsPullback (𝟙 X) c' c e.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hc]⟩
  have hk : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have hYsq : IsPullback e.hom (e.hom ≫ gY) gY (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hk]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
  have hdim : topologicalKrullDim Y' = 1 :=
    ((Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq).trans h.topologicalKrullDim_eq
  let : Y.Over (Spec (.of k)) := ⟨gY⟩
  have : LocallyOfFiniteType gY := inferInstance
  have hnodal : let : Y'.Over (Spec (.of k)) := ⟨e.hom ≫ gY⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y' :=
    Stacks.Curves.hasAtWorstNodalSingularities_of_isIso gY (e.hom ≫ gY) h.topologicalKrullDim_eq
      e.hom (𝟙 _) (by rw [Spec.map_id, Category.comp_id]) h.hasAtWorstNodalSingularities
  have hunit := c.isIso_unitToPushforwardObjUnit_of_isPullback hsq h.isIso_unitToPushforwardObjUnit
  have hcomp : c' ≫ e.hom ≫ gY = f := by rw [← Category.assoc, hc, h.comp_eq]
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ gY).appTop) := by
    have hcTop : IsIso c'.appTop :=
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c' hunit ⊤
    have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ gY).appTop) ≫ c'.appTop) := by
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ c'.appTop
  refine
    { comp_eq := hcomp
      isProper := inferInstance
      topologicalKrullDim_eq := hdim
      hasAtWorstNodalSingularities := hnodal
      isIso_unitToPushforwardObjUnit := hunit
      isZero_rightDerived_one :=
        isZero_rightDerived_pushforward_unit_of_isPullback hsq 1 h.isZero_rightDerived_one
      isAmple := ?_ }
  obtain ⟨hωY, hωYample⟩ := h.isAmple
  let eY : (Scheme.Modules.pullback e.hom).obj (Stacks.Duality.dualizingSheafOverField gY) ≅
      Stacks.Duality.dualizingSheafOverField (e.hom ≫ gY) :=
    Stacks.Duality.dualizingSheafOverFieldBaseChangeIso gY e.hom (e.hom ≫ gY) hYsq
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2
      ((Scheme.Modules.pullback e.hom).obj (Stacks.Duality.dualizingSheafOverField gY)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have hωY' : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField (e.hom ≫ gY)) := by
    let : Y'.Over (Spec (.of k)) := ⟨e.hom ≫ gY⟩
    have : IsProper (Y' ↘ Spec (.of k)) := inferInstanceAs (IsProper (e.hom ≫ gY))
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y' ↘ Spec (.of k)).appTop) :=
      inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (e.hom ≫ gY).appTop))
    have : ConnectedSpace Y' := connectedSpace_of_isIso_globalSections k (Y' ↘ Spec (.of k))
    exact isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y' hdim hnodal
  exact ⟨hωY', Scheme.Modules.isAmple_of_iso eY
    (Scheme.Modules.isAmple_pullback_of_isIso e.hom _ hωYample)⟩

end Stacks.Curves.StableModel

end
