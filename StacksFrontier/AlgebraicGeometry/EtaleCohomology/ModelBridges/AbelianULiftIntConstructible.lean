module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeZariskiLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralBaseChangeReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteTorsionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian étale sheaves as étale sheaves of `ULift ℤ`-modules, and constructibility

An abelian group is the same thing as a module over `ULift ℤ`, the integers lifted into the
universe of the group, and so an abelian sheaf on Mathlib's small étale site of a scheme `X` is
the same thing as a sheaf of `ULift ℤ`-modules there. This file records that equivalence in the
model `Stacks.EtaleCohomology.EtaleModules`, and how it interacts with constructibility
([Stacks, Tag 03RW], parts (2) and (3)). The point of passing through `ULift.{u + 1} ℤ` rather
than `ℤ` is that `ULift.{u + 1} ℤ` is a Noetherian ring in `Type (u + 1)`, the universe to which
the library's theory of constructible sheaves of modules on Mathlib's small étale sites is pinned
(for instance Tag 09YU, clause (3),
`Stacks.EtaleCohomology.exists_isConstructibleEtaleModule_etaleModuleInverseImage_iso`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence`: the equivalence between étale sheaves
  of `ULift ℤ`-modules and abelian étale sheaves. Its functor is, on the nose, the functor
  `_root_.Stacks.EtaleCohomology.etaleModuleForgetAb` forgetting the module structure
  (`Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence_functor`).
* `Stacks.EtaleCohomology.etaleModuleForgetBiproductDirectImageConstantSheafIso`: forgetting the
  module structure carries `⨁ⱼ fⱼ_* M̲ⱼ` to `⨁ⱼ fⱼ_* M̲ⱼ` (for any commutative ring).

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj`:
  a constructible abelian sheaf is a constructible sheaf of `ULift ℤ`-modules.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt`: a
  constructible *torsion* sheaf of `ULift ℤ`-modules is a constructible abelian sheaf.
* `Stacks.EtaleCohomology.torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf`: a
  constructible abelian sheaf is torsion.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt_iff`: the
  underlying abelian sheaf of a sheaf `G` of `ULift ℤ`-modules is constructible if and only if `G`
  is constructible and torsion.

## Constructibility is not simply preserved and reflected

The two notions of Tag 03RW differ in the local values on the strata: finite abelian groups in
part (2), finitely generated modules in part (3). So the equivalence carries constructible abelian
sheaves to constructible sheaves of `ULift ℤ`-modules, but not conversely: the constant sheaf
`ℤ̲` on the spectrum of a separably closed field is a constructible sheaf of `ULift ℤ`-modules
(its value `ULift ℤ` is a finitely generated module), its underlying abelian sheaf has stalk `ℤ`
and is not torsion, while every constructible abelian sheaf is torsion. The correct statement is
therefore the one with the torsion condition,
`Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt_iff`.

## Compatibility with the functors of Tag 09Z7

Because the functor of the equivalence is `_root_.Stacks.EtaleCohomology.etaleModuleForgetAb`, its
compatibilities with the étale functors are the existing ones for forgetting the module
structure: with inverse image, the isomorphism
`Stacks.EtaleCohomology.etaleModuleInverseImageForget` (an isomorphism by
`Stacks.EtaleCohomology.isIso_etaleModuleInverseImageForget`); with direct image, the identity
`Stacks.EtaleCohomology.etaleModuleDirectImageForget`; with constant sheaves,
`Stacks.EtaleCohomology.etaleModuleForgetConstantSheafIsoGeneral`. The functor is additive and
exact, so it preserves finite direct sums and monomorphisms; the isomorphism for the target
`⨁ⱼ fⱼ_* M̲ⱼ` of Tag 09Z7 is assembled once here.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u r

namespace Stacks.EtaleCohomology

variable (X : Scheme.{u})

/-- **Abelian étale sheaves are étale sheaves of `ULift ℤ`-modules.** The change of coefficients
along `AddCommGrpCat.uliftIntForgetEquivalence`, whose functor is the forgetful functor
`ModuleCat (ULift ℤ) ⥤ AddCommGrpCat`, so that the functor of this equivalence is
`_root_.Stacks.EtaleCohomology.etaleModuleForgetAb` on the nose. -/
def etaleModuleULiftIntEquivalence :
    EtaleModules.{u, max (u + 1) v} (ULift.{max (u + 1) v} ℤ) X ≌
      Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Sheaf.coefficientEquivalence X.smallEtaleTopology
    AddCommGrpCat.uliftIntForgetEquivalence.{max (u + 1) v}

/-- The functor of `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence` is the functor
forgetting the module structure. -/
theorem etaleModuleULiftIntEquivalence_functor :
    (etaleModuleULiftIntEquivalence.{v} X).functor =
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, max (u + 1) v}
        (ULift.{max (u + 1) v} ℤ) X :=
  rfl

variable {X}

/-- **A constructible abelian sheaf is a constructible sheaf of `ULift ℤ`-modules** ([Stacks,
Tag 03RW], parts (2) and (3)). Both notions are read on the small étale site of Tag 021B, where
the change of coefficients commutes with the transport on the nose, and there this is
`AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntEquivalence`: a finite abelian group is a
finitely generated `ULift ℤ`-module. -/
@[sga "4 IX 2.3.1" "Forward implication"]
theorem isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    IsConstructibleEtaleModule (ULift.{u + 1} ℤ)
      ((etaleModuleULiftIntEquivalence.{0} X).inverse.obj F) :=
  isConstructibleModuleSheaf_uliftIntEquivalence _ _ _ hF

/-- A sheaf of `ULift ℤ`-modules is constructible iff its image under the equivalence with abelian
sheaves and back is. -/
private theorem isConstructibleEtaleModule_inverse_obj_functor_obj_iff
    (G : EtaleModules.{u, u + 1} (ULift.{u + 1} ℤ) X) :
    IsConstructibleEtaleModule (ULift.{u + 1} ℤ)
      ((etaleModuleULiftIntEquivalence.{0} X).inverse.obj
        ((etaleModuleULiftIntEquivalence.{0} X).functor.obj G)) ↔
      IsConstructibleEtaleModule (ULift.{u + 1} ℤ) G :=
  (IsConstructibleEtaleModule (ULift.{u + 1} ℤ)).prop_iff_of_iso
    ((etaleModuleULiftIntEquivalence.{0} X).unitIso.app G).symm

/-- **A constructible torsion sheaf of `ULift ℤ`-modules is a constructible abelian sheaf**
([Stacks, Tag 03RW], parts (3) and (2)). On the small étale site of Tag 021B, a constructible
sheaf of `ULift ℤ`-modules descends to a constructible sheaf of `ℤ`-modules
(`AlgebraicGeometry.isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars`), and a torsion
abelian sheaf whose sheaf of `ℤ`-modules is constructible is constructible
(`AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general`):
torsion improves the finitely generated local values to finite ones. Torsion cannot be dropped;
see the module docstring. -/
theorem isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt
    (G : EtaleModules.{u, u + 1} (ULift.{u + 1} ℤ) X)
    (hG : IsConstructibleEtaleModule (ULift.{u + 1} ℤ) G)
    (hT : IsTorsionEtaleModule (ULift.{u + 1} ℤ) X G) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) X).obj
        G) := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  have : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
          (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f ↦
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B ℤ f
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{u + 1} ℤ) := fun T V ↦
    SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B ℤ T V
  exact isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int_general B (B.obj X hX) _
    (isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars B (B.obj X hX) _
      ((isConstructibleEtaleModule_inverse_obj_functor_obj_iff G).2 hG))
    (SmallEtale.torsionSheafProperty_sheafEquiv_inverse_obj B (B.obj X hX) _ hT)

/-- **A constructible abelian sheaf is torsion**, on Mathlib's small étale site: its transport to
the small étale site of Tag 021B is torsion
(`AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf`, by the stalk
criterion), and torsion is carried back along the comparison of the two sites. -/
theorem torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0} F) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  exact (Stacks.Torsion.torsionSheafProperty _).prop_of_iso (e.counitIso.app F)
    (SmallEtale.torsionSheafProperty_sheafEquiv_functor_obj B (B.obj X hX) _
      (torsionSheafProperty_of_isConstructibleAbelianSheaf B (B.obj X hX) _ hF))

/-- **Constructibility across `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence`.** The
underlying abelian sheaf of a sheaf `G` of `ULift ℤ`-modules on `X_étale` is constructible
([Stacks, Tag 03RW] (2)) if and only if `G` is constructible ([Stacks, Tag 03RW] (3)) and torsion.
-/
theorem isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt_iff
    (G : EtaleModules.{u, u + 1} (ULift.{u + 1} ℤ) X) :
    _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
        ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} (ULift.{u + 1} ℤ) X).obj G) ↔
      IsConstructibleEtaleModule (ULift.{u + 1} ℤ) G ∧
        IsTorsionEtaleModule (ULift.{u + 1} ℤ) X G :=
  ⟨fun h => ⟨(isConstructibleEtaleModule_inverse_obj_functor_obj_iff G).1
      (isConstructibleEtaleModule_etaleModuleULiftIntEquivalence_inverse_obj _ h),
    torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf _ h⟩,
   fun h => isConstructibleEtaleAbelianSheaf_etaleModuleForget_uliftInt G h.1 h.2⟩

section Biproducts

attribute [local instance] Abelian.hasFiniteBiproducts

variable (Λ : Type r) [CommRing Λ]

/-- **Forgetting the module structure carries `⨁ⱼ fⱼ_* M̲ⱼ` to `⨁ⱼ fⱼ_* M̲ⱼ`**, the target of
the embeddings of [Stacks, Tag 09Z7] (and of Tag 09Z6): the forgetful functor is additive, so it
commutes with finite direct sums, it commutes with direct images on the nose
(`Stacks.EtaleCohomology.etaleModuleDirectImageForget`), and it carries constant sheaves to
constant sheaves (`Stacks.EtaleCohomology.etaleModuleForgetConstantSheafIsoGeneral`). At
`Λ = ULift ℤ` this is the compatibility of `Stacks.EtaleCohomology.etaleModuleULiftIntEquivalence`
with that target, and a monomorphism into the left side gives one into the right side. -/
def etaleModuleForgetBiproductDirectImageConstantSheafIso {X : Scheme.{u}} {J : Type}
    [Finite J] {Y : J → Scheme.{u}} (f : ∀ j, Y j ⟶ X) (M : J → ModuleCat.{max (u + 1) r} Λ) :
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj
      (⨁ fun j => (etaleModuleDirectImage.{u, r} Λ (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj (M j))) ≅
      ⨁ fun j => (etaleAbelianDirectImage.{u, r} (f j)).obj
        ((constantSheaf (Y j).smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
          ((forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).obj (M j))) :=
  (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).mapBiproduct _ ≪≫
    biproduct.mapIso fun j => by
      exact (etaleAbelianDirectImage.{u, r} (f j)).mapIso
        ((etaleModuleForgetConstantSheafIsoGeneral.{u, r} Λ (Y j)).app (M j))

end Biproducts

end Stacks.EtaleCohomology

end
