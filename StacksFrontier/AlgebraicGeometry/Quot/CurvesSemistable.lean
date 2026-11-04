module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.SemistableCurveFamilies

/-!
# The substack of semistable curves

A family of curves `f : X → S` is semistable (Stacks 0E6Z) when it is prestable and every fibre
has genus at least one and no rational tail. This file shows that the condition cuts a strictly
full subcategory `Curves^{semistable}` out of the category of families of curves: it is inherited
by every family mapping to a semistable family, that is, by every base change of a semistable
family, and in particular it is invariant under isomorphism of families.

Base change is checked on the two halves of the definition. Prestability is the conjunction of
an at-worst-nodal condition, stable under base change by Stacks 0DSF, and of the universal form
of `f_*𝒪_X = 𝒪_S`, which passes to a base change because a base change of the base change is a
base change of the original family. The fibre condition passes because the fibre of a base
change at a field-valued point is the fibre of the original family at the composite point.

## Main definitions

* `AlgebraicGeometry.CurvesSemistable`: the strictly full subcategory of semistable families of
  curves.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsMap_bijective_of_iso`: pullback of global regular
  functions along an isomorphism of algebraic spaces is bijective.
* `AlgebraicGeometry.CurveFamily.isSemistableCurveFamily_of_hom`: a family of curves mapping to
  a semistable family is semistable.
* `AlgebraicGeometry.curvesSemistable_isClosedUnderIsomorphisms`: semistability is invariant
  under isomorphism of families of curves.

## References

* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Pullback of global regular functions along an isomorphism of algebraic spaces is bijective:
pullback along the inverse is a two-sided inverse. -/
theorem Space.globalFunctionsMap_bijective_of_iso {S : Scheme.{u}} {hS : B.Contains S}
    {U V : AlgebraicSpaces B S hS} (e : V ≅ U) :
    Function.Bijective (Space.globalFunctionsMap B S hS e.hom) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Space.globalFunctionsMap B S hS e.inv, fun s => ?_, fun s => ?_⟩ <;>
  rw [← RingHom.comp_apply, ← Space.globalFunctionsMap_comp] <;>
  simp only [Iso.inv_hom_id, Iso.hom_inv_id, Space.globalFunctionsMap_id, RingHom.id_apply]

/-- A family of curves mapping to a semistable family of curves is semistable: it is prestable
as a base change of a prestable family, and its fibre at a field-valued point of its base is the
fibre of the target family at the image point, by pasting cartesian squares. -/
theorem CurveFamily.isSemistableCurveFamily_of_hom {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsSemistableCurveFamily B hZ Y) : IsSemistableCurveFamily B hZ X := by
  refine ⟨CurveFamily.isPrestableCurveFamily_of_hom φ hY.1, fun p => ?_⟩
  obtain ⟨V, v, q, hpb, hV⟩ :=
    hY.2 (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p)
  have hval : yonedaEquiv.symm
      (Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap φ.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap φ.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  rw [hval] at hpb
  have hc := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  let q' : yoneda.obj V ⟶ X.total.obj :=
    hc.lift q (yoneda.map v ≫ yonedaEquiv.symm p.value) (by rw [hpb.w, Category.assoc]; rfl)
  refine ⟨V, v, q', ?_, hV⟩
  exact IsPullback.of_right (h₁₂ := φ.totalMap.hom) (h₂₂ := (schemeSpaceMap φ.baseMap).hom)
    (v₁₃ := Y.toBase.hom) (by rwa [hc.lift_fst]) (hc.lift_snd _ _ _) hc

/-- Semistability is invariant under isomorphism of families of curves, so the semistable
families form a strictly full subcategory of the category of families of curves. -/
theorem curvesSemistable_isClosedUnderIsomorphisms :
    (show ObjectProperty (CurveFamily B hZ) from
      IsSemistableCurveFamily B hZ).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => CurveFamily.isSemistableCurveFamily_of_hom B hZ e.inv hX⟩

/-- The strictly full subcategory `Curves^{semistable}` of semistable families of curves. -/
abbrev CurvesSemistable :=
  (show ObjectProperty (CurveFamily B hZ) from IsSemistableCurveFamily B hZ).FullSubcategory

end AlgebraicGeometry

end
