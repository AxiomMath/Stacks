module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# The two descents of a base change comparison to `D⁺` are invertible together

Let `τ : F ⋙ G ⟶ G' ⋙ F'` be a comparison of additive functors between abelian categories with
enough injectives, `G` and `G'` exact. It descends to bounded below derived categories in two ways:

* `Stacks.Cohomology.BaseChange.derived`, a transformation `RF ⋙ RG ⟶ RG' ⋙ RF'` between
  composites of right derived functors;
* `Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus`, a transformation
  `RF ⋙ G ⟶ G' ⋙ RF'` in which the exact functors act degreewise.

At a bounded below complex of injectives both are the localized degreewise comparison followed by
the unit of `RF'`; so at every object of `D⁺` **one is invertible exactly when the other is**
(`isIso_derived_app_iff_isIso_derivedBaseChangePlus_app`).

## References

* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

-- `Stacks.Cohomology.BaseChange.derived`
-- (`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean:204`) is
-- built under the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')

/-- **The two descents of `τ` to `D⁺` are invertible together**: at every bounded below object
`K`, `Stacks.Cohomology.BaseChange.derived` of `τ` is invertible exactly when
`Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus` of `τ` is. At a bounded below
complex of injectives both are, up to isomorphisms, the localized degreewise `τ` followed by the
unit of `RF'`. -/
theorem isIso_derived_app_iff_isIso_derivedBaseChangePlus_app (K : DerivedCategory.Plus A) :
    letI : IsIso G.rightDerivedFunctorPlusUnith := exactUnit_isIso G
    IsIso ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app K) ↔
      IsIso
        ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' τ).app K) := by
  let : IsIso G.rightDerivedFunctorPlusUnith := exactUnit_isIso G
  let : IsIso G'.rightDerivedFunctorPlusUnith := exactUnit_isIso G'
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff K n).1 hn
  obtain ⟨L, _, ⟨i⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := (InjectiveObject.ι A).mapCochainComplexPlus.obj L
  let Kh := (HomotopyCategory.Plus.quotient A).obj I
  let j : DerivedCategory.Plus.Qh.obj Kh ≅ K :=
    (ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso A).app I.obj) :
      DerivedCategory.Plus.Qh.obj Kh ≅ DerivedCategory.Plus.Q.obj I) ≪≫ i
  rw [← NatTrans.isIso_app_iff_of_iso _ j, ← NatTrans.isIso_app_iff_of_iso _ j]
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app Kh) := inferInstance
  rw [isIso_derived_app_Qh_iff F F' G G' τ _ Kh hF inferInstance]
  have hfac := Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_fac F F' G G' τ Kh
  rw [Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusAux_app] at hfac
  have hc : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (G' ⋙ F'))).inv.app Kh) = 𝟙 _ := by
    have hc' : (Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F'))
        (ComplexShape.up ℤ)).inv.app I.obj = 𝟙 _ := by
      ext m
      simp [Functor.mapHomologicalComplexCompIso]
    have e : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app Kh = 𝟙 _ := by
      ext
      show (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (G' ⋙ F'))
          (ComplexShape.up ℤ)).inv.app I.obj) = _
      rw [hc', CategoryTheory.Functor.map_id]
      rfl
    rw [e]
    exact CategoryTheory.Functor.map_id _ _
  have hcomp : DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans τ).app Kh) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (G' ⋙ F'))).inv.app Kh) ≫
      F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj Kh) =
      DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj Kh) := by
    rw [hc]
    exact congrArg (fun t => _ ≫ t) (Category.id_comp _)
  have h₂ : IsIso ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' τ).app
      (DerivedCategory.Plus.Qh.obj Kh)) ↔
      IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj Kh)) := by
    rw [← isIso_comp_left_iff (G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app Kh))
      ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus F F' G G' τ).app
        (DerivedCategory.Plus.Qh.obj Kh)), hfac, isIso_comp_left_iff, isIso_comp_left_iff,
      ← hcomp, ← Category.assoc, ← Category.assoc, isIso_comp_right_iff, Category.assoc]
  exact h₂.symm

end Stacks.Cohomology.BaseChange

end
