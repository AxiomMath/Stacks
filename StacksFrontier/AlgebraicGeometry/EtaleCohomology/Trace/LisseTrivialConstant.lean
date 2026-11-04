module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PermutationModuleCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.ConstantSheafModuleDictionaryEtaleSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The lisse sheaf of the trivial module is the constant sheaf

For a connected scheme `X` of a big étale site with a geometric point `x̄`, the lisse sheaf
(Stacks 0DV5 (3)) of `ℤ/m` with the trivial action of `π₁(X, x̄)` is the constant sheaf `ℤ/m` on
`X_étale`, as sheaves of `ℤ/m`-modules.

## Main definitions

* `Stacks.EtaleCohomology.etaleStalkConstantSheafIso`: the stalk of a constant sheaf of modules on
  a small étale site is its value.

## Main results

* `Stacks.EtaleCohomology.nonempty_lisseEtaleSheaf_trivialContinuousModule_iso`: the lisse sheaf
  of `ℤ/m` with the trivial action is the constant sheaf `ℤ/m`.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology


section Stalk

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (Λ : Type) [Ring Λ] (M : ModuleCat.{u + 1} Λ)

/-- **The stalk of the constant sheaf of modules is its value**: the stalk at `s` of the constant
sheaf of modules with value `M` on the small étale site of `S` is `M`. -/
def etaleStalkConstantSheafIso :
    etaleStalk B S hS s ((constantSheaf (SmallEtale.topology B S hS)
      (ModuleCat.{u + 1} Λ)).obj M).obj ≅ M :=
  let Φ := geometricPointSitePoint B S hS s
  let P := (Functor.const (SmallEtale B S hS)ᵒᵖ).obj M
  (asIso (Φ.presheafFiber.map (CategoryTheory.toSheafify (SmallEtale.topology B S hS) P))).symm ≪≫
    HasColimit.isoOfNatIso (Iso.refl ((Functor.const Φ.fiber.Elementsᵒᵖ).obj M)) ≪≫
    colimit.isoColimitCocone ⟨_, isColimitConstCocone Φ.fiber.Elementsᵒᵖ M⟩

end Stalk

section Lisse

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (m : ℕ) [NeZero m]

/-- **The lisse sheaf of `ℤ/m` with the trivial action is the constant sheaf `ℤ/m`**, as sheaves of
`ℤ/m`-modules on Mathlib's small étale site. -/
theorem nonempty_lisseEtaleSheaf_trivialContinuousModule_iso :
    Nonempty ((lisseEtaleSheaf B X x (ZMod m)).obj (trivialContinuousModule m) ≅
      etaleModuleConstantSheaf (ZMod m) (ModuleCat.of (ZMod m) (ULift.{u + 1} (ZMod m))) X.1) := by
  let Λ := ZMod m
  let M : ModuleCat.{u + 1} Λ := ModuleCat.of Λ (ULift.{u + 1} Λ)
  have : Finite (ToType M) := inferInstanceAs (Finite (ULift.{u + 1} Λ))
  let E := finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ
  let c := constantSheafFiniteTypeLocallyConstantModule B X Λ M
  let Qc := E.functor.obj c
  let Ac := ((Stacks.ConstantSheaf.finiteLocallyConstantModuleSheafScalarActionEquivalence
    (SmallEtale.topology B X.1 X.2) Λ).functor.obj
      ((finiteTypeLocallyConstantModuleSheafBridge B X Λ).inverse.obj c)).obj.obj (SingleObj.star Λ)
  let e₀ := (finiteLocallyConstantAbelianStalkIso B X (Iso.refl (finiteEtaleFiberFunctor x))).app Ac
  let e₁ := etaleStalkForget₂Iso B X.1 X.2 x Λ c.obj
  let e₂ := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
    (etaleStalkConstantSheafIso B X.1 X.2 x Λ M)
  let eab := e₀.symm ≪≫ e₁.symm ≪≫ e₂
  let fadd : Qc.obj.obj.obj.V ≃+ ULift.{u + 1} Λ := eab.addCommGroupIsoToAddEquiv
  let f : Qc.obj.obj.obj.V ≃ₗ[Λ] ULift.{u + 1} Λ :=
    { fadd with map_smul' := fun a v => ZMod.map_smul fadd a v }
  let i : trivialContinuousModule m ≅ Qc := finiteTypeContinuousModuleIsoMk m f.symm fun g v => by
    rw [rho_eq_one_finiteTypeLocallyConstantModuleSheafEquivalence_constantSheaf B X Λ x M g]
    rfl
  refine ⟨(lisseEtaleSheaf B X x Λ).mapIso i ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).functor.mapIso
      ((ObjectProperty.ι _).mapIso (E.unitIso.app c).symm ≪≫
        (sheafEquivInverseConstantSheafModuleIso B X Λ M).symm) ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} Λ)).counitIso.app _⟩

end Lisse

end Stacks.EtaleCohomology
