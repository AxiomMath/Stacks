module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleModuleMatePlusProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleModulesZModTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsOpenImmersionBaseChange

/-!
# Proper base change on `D(-_étale, ℤ/m)` at the structure sheaf

For a cartesian square
```
Y  --h-->  X'
|e         |f'
T  --g-->  S
```
with `g` proper and `m ≥ 1`, the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` of `D(-_étale, ℤ/m)`
(`Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap`) is an isomorphism at the structure
sheaf `ℤ/m[0]` of `T` (`isIso_baseChangeMap_app_unit_of_isProper`). This is proper base change
([Stacks, Tag 0DDE], `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`) read
across to `D(-_étale, ℤ/m)`: by `isIso_baseChangeMap_app_iff` the map is the abelian base change
map at the underlying sheaf of `ℤ/m`, which is the underlying sheaf of a sheaf of
`ℤ/m`-modules on the small étale site (`etaleModuleForgetAb_zmod_essImage_iff`), at which
`Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_of_isProper` applies.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap` and
-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BaseChangeCondition.lean:220`)
-- are built for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

/-- Every sheaf of `ℤ/m`-modules on the small étale site is a torsion sheaf. -/
theorem isTorsionEtaleModule_of_zmodModule (m : ℕ) [NeZero m] {X : Scheme.{u}}
    (F : EtaleModules.{u, 0} (ZMod m) X) : IsTorsionEtaleModule.{u, 0} (ZMod m) X F := by
  intro V x
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun _ _ _ => ⟨m, NeZero.pos m, ?_⟩⟩
  rw [← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul]

/-- **Proper base change on `D(-_étale, ℤ/m)` at the structure sheaf.** For a cartesian square
`h ≫ f' = e ≫ g` with `g` proper and `m ≥ 1`, the base change map
`(f')⁻¹Rg_*(ℤ/m) ⟶ Rh_*e⁻¹(ℤ/m)` of `D(-_étale, ℤ/m)` is an isomorphism. -/
theorem EtaleCoefficients.isIso_baseChangeMap_app_unit_of_isProper (m : ℕ) [NeZero m]
    {X' S T Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) [IsProper g]
    (sq : IsPullback e h g f') :
    IsIso ((EtaleCoefficients.baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e sq.w.symm).app
      (EtaleCoefficients.unit (ULift.{u + 1} (ZMod m)) T)) := by
  refine EtaleCoefficients.isIso_baseChangeMap_app_unit_of_isIso_single m f' g h e sq.w.symm ?_
  -- the underlying abelian sheaf of `ℤ/m` is the one of a sheaf of `ℤ/m`-modules
  let F₀ := (EtaleCoefficients.etaleToSheaf (ULift.{u + 1} (ZMod m)) T).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (EtaleCoefficients.ringedTopos (ULift.{u + 1} (ZMod m)) T).O))
  obtain ⟨F₁, ⟨e₁⟩⟩ := (etaleModuleForgetAb_zmod_essImage_iff m T F₀).2
    ((EtaleCoefficients.mem_essImage_etaleToSheaf_iff m T F₀).1 ⟨_, ⟨Iso.refl _⟩⟩)
  let K₁ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod m) T) 0).obj F₁
  have j : (etaleModuleForgetAb.{u, 0} (ZMod m) T).mapDerivedCategoryPlus.obj K₁ ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F₀ :=
    EtaleCoefficients.mapDerivedCategoryPlusSingleFunctorObjIso _ F₁ ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e₁
  rw [← NatTrans.isIso_app_iff_of_iso _ j]
  exact isIso_smallEtaleDerivedBaseChangeAb_app_of_isProper (ZMod m) f' g h e sq K₁
    fun _ => isTorsionEtaleModule_of_zmodModule m _

end Stacks.EtaleCohomology

end
