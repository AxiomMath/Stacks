module

public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple

/-!
# Ampleness on a fibre of a module identified there with the dualizing sheaf

Let `X` be a family of curves, `s` a point of its base and `V` a scheme of the site, proper over
`Spec κ(s)`, with a morphism `q : V ⟶ Y` to an algebraic space `Y` carrying an invertible
module `ω` whose restriction to `V` is the dualizing sheaf `ω_V` (Stacks 0BS2). The pullback of
`ω` to `V` is ample over `Spec κ(s)` in the sense of algebraic spaces exactly when `ω_V` is
invertible and ample.

## Main results

* `AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff_of_iso`: the criterion.

## Implementation notes

**Unregistered helper** (for Stacks 0E74). This is
`AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff` with the identification of the
restriction of `ω` given directly, so that `ω` may live on any algebraic space through which the
fibre maps, such as the preimage `f⁻¹(U)` of an open `U ∋ s` of the base: the relative dualizing
sheaf is constructed over affine opens of the base.

## References

* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Ampleness on a fibre.** Let `ω` be an invertible module on an algebraic space `Y`, and let
`V` be a scheme of the site over `Spec κ(s)`, `s` a point of the base of a family of curves `X`,
proper over `κ(s)`, with a morphism `q : V ⟶ Y` along which `ω` restricts to the dualizing sheaf
`ω_V`. Then the pullback of `ω` to `V` is ample over `Spec κ(s)` in the sense of algebraic spaces
exactly when `ω_V` is invertible and ample.

This is `AlgebraicGeometry.CurveFamily.isRelativelyAmple_fibre_iff` with the identification of
the restriction of `ω` given directly, for `ω` on any algebraic space through which the fibre
maps. -/
theorem isRelativelyAmple_fibre_iff_of_iso {X : CurveFamily B hZ}
    {Y : AlgebraicSpaces B integerBase hZ}
    {ω : Space.Modules.{u, u} B integerBase hZ Y.obj Y.property}
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Y.1 Y.2).O)).property ω)
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ residuePoint B hZ X s} [IsProper (fibreMap B hZ X s v)]
    (q : yoneda.obj V ⟶ Y.obj)
    (e : Space.baseChangeModule B integerBase hZ ω V q ≅
      Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) :
    Space.IsRelativelyAmple B integerBase hZ (schemeSpaceMap v)
        ((Space.modulePullback B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj ω) ↔
      ∃ _ : SheafOfModules.IsInvertible
          ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace.presheaf
          (structureSheafRing
            ((BigFppfOver.toScheme B integerBase hZ).obj V).toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)),
        Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj V)
          (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) := by
  let L' := (Space.modulePullback B integerBase hZ
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj ω
  let E : Space.baseChangeModule B integerBase hZ L' V (𝟙 _) ≅
      Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v) :=
    (Space.baseChangeModuleCompIso B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ Y) ω V (𝟙 _)).symm ≪≫
      eqToIso (congrArg (Space.baseChangeModule B integerBase hZ ω V) (Category.id_comp q)) ≪≫ e
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (residuePoint B hZ X s)) :=
    inferInstanceAs (IsAffine (Spec _))
  constructor
  · intro hamp
    obtain ⟨hL, hrel⟩ := hamp.2 (residuePoint B hZ X s) V (𝟙 _) (𝟙 _) v
      (IsPullback.id_horiz (yoneda.map v))
    have : Stacks.Ample.IsInvertibleModule _
        (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E
    have hrel' := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mp hrel
    have hst := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      (fibreMap B hZ X s v) _).mp hrel'
    exact ⟨this, (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp hst⟩
  · rintro ⟨hinv, hamp⟩
    have hL'inv : Stacks.SheafOfModules.IsInvertible
        (Space.structurePresheaf B integerBase hZ (schemeSpace V).1)
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace V).1
            (schemeSpace V).2).O)).property L' :=
      Stacks.SheafOfModules.isInvertible_pullbackModules_obj
        (f := Space.smallEtaleRingedToposModulesHom B integerBase hZ
          (ObjectProperty.homMk q : schemeSpace V ⟶ Y)) (L := ω) (hL := hωinv)
    have : Stacks.Ample.IsInvertibleModule _
        (Stacks.Duality.dualizingSheafOverField (fibreMap B hZ X s v)) := hinv
    have hVinv : Stacks.Ample.IsInvertibleModule _ _ :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ E.symm
    refine Space.isRelativelyAmple_of_exists_scheme _ L' hL'inv (residuePoint B hZ X s)
      (Iso.refl _) ⟨V, Iso.refl _, hVinv, ?_⟩
    have h1 := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple
      (fibreMap B hZ X s v) _).mpr ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hamp)
    have h2 := (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mpr h1
    convert h2 using 2
    · rfl
    · refine (fun (m : V ⟶ residuePoint B hZ X s) (hm : m = v) =>
        (hm ▸ HEq.rfl : HEq ((BigFppfOver.toScheme B integerBase hZ).map m)
          (fibreMap B hZ X s v))) _ ?_
      apply yoneda.map_injective
      simp only [Functor.map_preimage, Iso.refl_hom, schemeSpaceMap_hom]
      exact (Category.id_comp _).trans (Category.comp_id _)
    · rfl

end CurveFamily

end AlgebraicGeometry

end
