module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleModuleAbelianBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusOfDerived

/-!
# Proper base change for the base change map of sheaves of `Λ`-modules read on abelian sheaves

Sheaves of `Λ`-modules on the small étale sites carry two base change maps on `D⁺` for a
commutative square `h ≫ f' = e ≫ g`:

* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`, of [Stacks, Tag 0DDE], for which proper
  base change is proved (`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`);
* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeMatePlus`, which forgetting the module
  structure carries to the abelian base change map
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`.

This file shows that **the underived maps they descend are the same**
(`etaleModuleBaseChangeMate_eq_etaleModuleBaseChange`), so that the two are invertible together
(`isIso_etaleModuleDerivedBaseChangeMatePlus_app_iff`), and reads proper base change on the second
and on the abelian base change map
(`isIso_smallEtaleDerivedBaseChangeAb_app_of_isProper`): for a proper `g`, a cartesian square
and a bounded below complex of sheaves of `Λ`-modules with torsion cohomology sheaves, the abelian
base change map is invertible at its underlying complex of abelian sheaves.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeMatePlus` and
-- `Stacks.EtaleCohomology.etaleModuleDerivedBaseChange` are built for the standard model of the
-- derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- The composition isomorphism of direct images of sheaves of `Λ`-modules, followed by the
identification along `c = a ≫ b`, is the composition isomorphism with the composite named. -/
theorem etaleModuleDirectImageCompIso_trans_eqToIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ Z) (hc : c = a ≫ b) :
    etaleModuleDirectImageCompIso Λ a b ≪≫
        eqToIso (congrArg (fun m => etaleModuleDirectImage.{u, 0} Λ m) hc.symm) =
      etaleModuleDirectImageComp.{u, 0} Λ a b c hc := by
  subst hc
  simp only [etaleModuleDirectImageCompIso, etaleModuleDirectImageComp, smallEtalePushforwardComp',
    smallEtaleBaseChangeComp', eqToIso_refl, Iso.refl_trans, Iso.trans_refl]

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The two underived base change maps of sheaves of `Λ`-modules agree**: the mate of the
identification of the composite direct images (`etaleModuleBaseChangeMate`) is the mate of the
identification of the composite inverse images (`etaleModuleBaseChange`). -/
theorem etaleModuleBaseChangeMate_eq_etaleModuleBaseChange :
    etaleModuleBaseChangeMate Λ f' g h e w = etaleModuleBaseChange Λ g h f' e w := by
  rw [etaleModuleBaseChange_eq_mateEquiv_symm, etaleModuleBaseChangeMate,
    Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm]
  congr 3
  rw [etaleModuleDirectImageSquareIso, ← etaleModuleDirectImageCompIso_trans_eqToIso Λ e g _ w,
    ← etaleModuleDirectImageCompIso_trans_eqToIso Λ h f' _ rfl]
  simp

/-- **The two base change maps of sheaves of `Λ`-modules on `D⁺` are invertible together.** -/
theorem isIso_etaleModuleDerivedBaseChangeMatePlus_app_iff
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ T)) :
    IsIso ((etaleModuleDerivedBaseChangeMatePlus Λ f' g h e w).app K) ↔
      IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ g h f' e w).app K) := by
  have h₁ := Stacks.Cohomology.BaseChange.isIso_derived_app_iff_isIso_derivedBaseChangePlus_app
    (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleDirectImage.{u, 0} Λ h)
    (etaleModuleInverseImage.{u, 0} Λ f') (etaleModuleInverseImage.{u, 0} Λ e)
    (etaleModuleBaseChangeMate Λ f' g h e w) K
  rw [etaleModuleBaseChangeMate_eq_etaleModuleBaseChange] at h₁
  unfold etaleModuleDerivedBaseChangeMatePlus
  rw [etaleModuleBaseChangeMate_eq_etaleModuleBaseChange]
  exact h₁

/-- **Proper base change for the abelian base change map at a complex of sheaves of
`Λ`-modules** ([Stacks, Tag 0DDE] read on abelian sheaves). Let `g` be proper and the square
`h ≫ f' = e ≫ g` cartesian. For a bounded below complex `K` of sheaves of `Λ`-modules with torsion
cohomology sheaves, `smallEtaleDerivedBaseChangeAb` is invertible at the underlying complex of
abelian sheaves of `K`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_of_isProper [IsProper g]
    (sq : IsPullback e h g f') (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ T))
    (hK : isTorsionPlus.{u, 0} Λ T K) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e sq.w.symm).app
      ((etaleModuleForgetAb.{u, 0} Λ T).mapDerivedCategoryPlus.obj K)) := by
  rw [isIso_smallEtaleDerivedBaseChangeAb_app_iff,
    isIso_etaleModuleDerivedBaseChangeMatePlus_app_iff]
  exact isIso_etaleModuleDerivedBaseChange_of_isProper Λ g sq K hK

end Stacks.EtaleCohomology

end
