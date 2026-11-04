module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RelativeCurveTopSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RightDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMapShift
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleCohomology
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `R² f_*` of the constant sheaf of `ℤ/n`-modules, as an abelian sheaf

For `f : X ⟶ S`, a field `k` with a primitive `n`-th root of unity `ζ` and `X` over `k`, the
underlying abelian sheaf of `R² f_* (ℤ/n)`, computed in sheaves of `ℤ/n`-modules on bounded below
derived categories, is `H⁰(Rf_*(μ_n[2]))` computed in abelian sheaves on unbounded derived
categories (`Stacks.EtaleCohomology.nonempty_forget_singleHomology_two_iso_relativeTopSheaf`):
both are the classical right derived functor `R² f_*` (of the module, resp. of its underlying
abelian sheaf, `Stacks.EtaleCohomology.etaleModuleForgetRightDerivedDirectImageIso`), and
`m ↦ ζ^m` identifies the underlying abelian sheaf of `ℤ/n` with `μ_n`.

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] {S X : Scheme.{u}} (f : X ⟶ S) (p : X ⟶ Spec (.of k)) {n : ℕ}
  {ζ : k} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)

include hζ hn p in
/-- **The underlying abelian sheaf of `R² f_* (ℤ/n)` is `H⁰(Rf_*(μ_n[2]))`.** -/
theorem nonempty_forget_singleHomology_two_iso_relativeTopSheaf :
    Nonempty ((etaleModuleForgetAb.{u, 0} (ZMod n) S).obj
      ((singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod n) f) 2).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n) X.smallEtaleTopology)) ≅
      relativeTopSheaf f n) := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod n) X
  let := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  let G := Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod n) X.smallEtaleTopology
  -- the module side: `R² f_*` of the module
  let e₁ : (singleHomology (etaleModuleDerivedDirectImage.{u, 0} (ZMod n) f) 2).obj G ≅
      ((etaleModuleDirectImage.{u, 0} (ZMod n) f).rightDerived 2).obj G :=
    (DerivedCategory.Plus.homologyFunctor _ 2).mapIso
        ((etaleModuleDerivedDirectImage.{u, 0} (ZMod n) f).mapIso
          ((StacksDraft.DerivedSectionsComparison.singlePlusQIso _).app G)) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, 0} (ZMod n) f) 2).app
        G).symm
  -- forgetting the module structure
  let e₂ := (etaleModuleForgetAb.{u, 0} (ZMod n) S).mapIso e₁ ≪≫
    etaleModuleForgetRightDerivedDirectImageIso (ZMod n) f G 2
  -- the abelian side, unbounded
  let e₃ := (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
      (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
      (fun K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ =>
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)
      ((etaleModuleForgetAb.{u, 0} (ZMod n) X).obj G) 2).symm
  -- `ℤ/n ≅ μ_n` and the shift
  let e₄ := (DerivedCategory.homologyFunctor _ (2 : ℤ)).mapIso
    ((etaleAbelianDerivedDirectImage.{u, 0} f).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (Stacks.Kummer.etaleModuleConstantUnderlyingIso p hζ hn)))
  let e₅ := (((DerivedCategory.homologyFunctor _ 0).shiftIso 2 0 2 (by omega)).app
      ((etaleAbelianDerivedDirectImage.{u, 0} f).obj ((DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X n)))).symm ≪≫
    ((DerivedCategory.homologyFunctor _ 0).isoShiftZero ℤ).app _ ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      (((etaleAbelianDerivedDirectImage.{u, 0} f).commShiftIso (2 : ℤ)).app _).symm
  exact ⟨e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅⟩

end Stacks.EtaleCohomology

end
