module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.AbelianULiftIntConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierProperCurves.AbelianAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ExactnessUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurveTorsionStatementsClopen
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero along an open immersion and finite direct image preserve constructibility

For abelian sheaves on Mathlib's small étale sites, this file proves that extension by zero along
a quasi-compact open immersion of quasi-compact quasi-separated schemes ([Stacks, Tag 03S8], for an
open immersion and a sheaf killed by a positive integer) and direct image along a finite morphism
of finite presentation ([Stacks, Tag 095R], for an arbitrary constructible sheaf) carry
constructible sheaves to constructible sheaves.

Both are read off the corresponding statements for sheaves of modules over `ULift ℤ`, through the
equivalence `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence` between abelian sheaves and
sheaves of `ULift ℤ`-modules: a constructible abelian sheaf is a constructible sheaf of
`ULift ℤ`-modules, the two functors commute with forgetting the module structure, and a
constructible torsion sheaf of `ULift ℤ`-modules has constructible underlying abelian sheaf
(`Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt`). For
extension by zero, being killed by an integer is what makes the image torsion; for a finite direct
image, torsion of the image is Tag 0DDD (1) in degree zero.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_extensionByZero`: `j_! F` is
  constructible.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleAbelianDirectImage_of_isFinite`:
  `f_* F` is constructible, `f` finite of finite presentation.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

/-- A sheaf of `ULift ℤ`-modules whose underlying abelian sheaf is isomorphic to one killed by a
positive integer is torsion. -/
private theorem isTorsionEtaleModule_of_iso_of_zsmul {X : Scheme.{u}}
    (G : EtaleModules.{u, u + 1} (ULift.{u + 1} ℤ) X)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1}
      (ULift.{u + 1} ℤ) X).obj G ≅ F) {n : ℕ} (hn : 0 < n)
    (hF : (n : ℤ) • 𝟙 F = 0) : IsTorsionEtaleModule (ULift.{u + 1} ℤ) X G := by
  have h : (n : ℤ) • 𝟙 ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1}
      (ULift.{u + 1} ℤ) X).obj G) = 0 := by
    rw [← cancel_mono e.hom, Preadditive.zsmul_comp, Category.id_comp, ← Category.comp_id e.hom,
      ← Preadditive.comp_zsmul, hF, Limits.comp_zero, Limits.zero_comp]
  exact torsionSheafProperty_of_zsmul_id_eq_zero_general hn h

/-- **[Stacks, Tag 03S8], for an open immersion and a sheaf killed by an integer.** Let
`j : U ⟶ X` be an open immersion of quasi-compact quasi-separated schemes and `F` a constructible
abelian sheaf on `U_étale` killed by a positive integer. Then `j_! F` is constructible. -/
theorem isConstructibleEtaleAbelianSheaf_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [CompactSpace U] [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F)
    {n : ℕ} (hn : 0 < n)
    (hFn : (n : ℤ) • 𝟙 F = 0) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      ((extensionByZero.{u, 0} j).obj F) := by
  let E := etaleModuleULiftIntEquivalence.{0} U
  let G := E.inverse.obj F
  have hG' := isConstructibleEtaleModule_etaleModuleExtensionByZero (ULift.{u + 1} ℤ) j G
    (isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj F hF)
  let e : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) X).obj
      ((etaleModuleExtensionByZero.{u, u + 1} (ULift.{u + 1} ℤ) j).obj G) ≅
      (extensionByZero.{u, 0} j).obj F :=
    ((asIso (etaleModuleExtensionByZeroForget.{u, u + 1} (ULift.{u + 1} ℤ) j)).app
      G).symm ≪≫ (extensionByZero.{u, 0} j).mapIso (E.counitIso.app F)
  have hkill : (n : ℤ) • 𝟙 ((extensionByZero.{u, 0} j).obj F) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, hFn, Functor.map_zero]
  exact isConstructibleEtaleAbelianSheaf_of_iso e
    (isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt _ hG'
      (isTorsionEtaleModule_of_iso_of_zsmul _ e hn hkill))

/-- **[Stacks, Tag 095R], for sheaves of abelian groups.** Let `f : X ⟶ Y` be a finite morphism
of finite presentation and `F` a constructible abelian sheaf on `X_étale`. Then `f_* F` is
constructible.

As a sheaf of `ULift ℤ`-modules, `F` is constructible, so `f_* F` is a constructible sheaf of
`ULift ℤ`-modules by the module case of the tag
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite`). It is
moreover torsion: `F` is torsion, being constructible
(`Stacks.EtaleCohomology.torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf`), and the
direct image along the quasi-compact quasi-separated `f` of a torsion sheaf is torsion
(`Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb`, Tag 0DDD (1) in degree
zero). A constructible torsion sheaf of `ULift ℤ`-modules has constructible underlying abelian
sheaf. No torsion hypothesis is imposed on `F`. -/
@[stacks 095R "sheaves of abelian groups"]
theorem isConstructibleEtaleAbelianSheaf_etaleAbelianDirectImage_of_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (hfp : FinitePresentation f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      ((etaleAbelianDirectImage.{u, 0} f).obj F) := by
  let E := etaleModuleULiftIntEquivalence.{0} X
  let G := E.inverse.obj F
  have hG' := isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite (ULift.{u + 1} ℤ) f
    hfp G (isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj F hF)
  let e : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) Y).obj
      ((etaleModuleDirectImage.{u, u + 1} (ULift.{u + 1} ℤ) f).obj G) ≅
      (etaleAbelianDirectImage.{u, 0} f).obj F :=
    ((etaleModuleDirectImageCompForgetIso.{u, u + 1} (ULift.{u + 1} ℤ) f).app G).symm ≪≫
      (etaleAbelianDirectImage.{u, 0} f).mapIso (E.counitIso.app F)
  have hT' : IsTorsionEtaleModule (ULift.{u + 1} ℤ) Y
      ((etaleModuleDirectImage.{u, u + 1} (ULift.{u + 1} ℤ) f).obj G) :=
    Stacks.Torsion.torsionSheafProperty_of_iso Y.smallEtaleTopology e.symm
      (torsionSheafProperty_smallEtaleDirectImageAb.{0} f F
        (torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf F hF))
  exact isConstructibleEtaleAbelianSheaf_of_iso e
    (isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt _ hG' hT')

end Stacks.EtaleCohomology

end
