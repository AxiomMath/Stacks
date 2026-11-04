module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso

/-!
# The inverse image along the identity on `D(X_étale, ℤ/mℤ)`

The inverse image `f⁻¹ : D(Y_étale, ℤ/mℤ) ⥤ D(X_étale, ℤ/mℤ)` is defined on the small models of
the étale sites, through base change of étale schemes along `f`, which for `f = 𝟙 X` is only
isomorphic to the identity. This file proves that `(𝟙 X)⁻¹` is isomorphic to the identity
functor, so that statements made at `p⁻¹E` for a projection `p` apply at `E` itself when `p` is
the identity.

## The argument

On sheaves of `ℤ/mℤ̲`-modules, the underlying abelian sheaf carries `(𝟙 X)⁻¹` to the abelian
inverse image along `𝟙 X` (`pullbackEtaleToSheafIso`), which is the identity
(`Stacks.EtaleCohomology.smallEtalePullbackAbIdOf`); the underlying abelian sheaf is fully
faithful for `ℤ/mℤ`-coefficients (`etaleToSheafZModFullyFaithful`), so `(𝟙 X)⁻¹` is the identity
already on sheaves of modules. The derived inverse image is the inverse image applied degreewise,
it being exact (`Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived`).

## Main definitions

* `Stacks.EtaleCohomology.EtaleCoefficients.pullbackToposIdIso` — `(𝟙 X)⁻¹ ≅ 𝟭` on sheaves of
  `ℤ/mℤ̲`-modules.
* `Stacks.EtaleCohomology.EtaleCoefficients.pullbackIdIso` — `(𝟙 X)⁻¹ ≅ 𝟭` on
  `D(X_étale, ℤ/mℤ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- forced by `Stacks.EtaleCohomology.EtaleCoefficients.pullback`
-- (Kunneth/EtaleKunnethMap.lean:199), the derived inverse image `derivedPullback`, stated for the
-- standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (m : ℕ) (X : Scheme.{u})

/-- **The inverse image of sheaves of `ℤ/mℤ̲`-modules along the identity is the identity**: the
underlying abelian sheaf, which is fully faithful, carries it to the abelian inverse image along
`𝟙 X`, which is the identity. -/
def pullbackToposIdIso :
    (ringedToposHom (ULift.{u + 1} (ZMod m)) (𝟙 X)).pullbackTopos ≅
      𝟭 (SheafOfModules.{u + 1} (etaleRing (ULift.{u + 1} (ZMod m)) X)) :=
  ((etaleToSheafZModFullyFaithful m X).whiskeringRight _).preimageIso
    (pullbackEtaleToSheafIso m (𝟙 X) ≪≫
      Functor.isoWhiskerLeft _ (smallEtalePullbackAbIdOf (𝟙 X) rfl) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- **The inverse image `(𝟙 X)⁻¹` on `D(X_étale, ℤ/mℤ)` is the identity**: it is the inverse image
of sheaves of modules applied degreewise, which is the identity (`pullbackToposIdIso`). -/
def pullbackIdIso :
    pullback (ULift.{u + 1} (ZMod m)) (𝟙 X) ≅ 𝟭 (DerivedModules (ULift.{u + 1} (ZMod m)) X) :=
  haveI : PreservesColimitsOfSize.{0, 0}
      (ringedToposHom (ULift.{u + 1} (ZMod m)) (𝟙 X)).pullbackTopos :=
    Adjunction.leftAdjoint_preservesColimits
      (ringedToposHom (ULift.{u + 1} (ZMod m)) (𝟙 X)).pullbackPushforwardAdjunctionTopos
  haveI : PreservesFiniteColimits (ringedToposHom (ULift.{u + 1} (ZMod m)) (𝟙 X)).pullbackTopos :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived
      (ringedToposHom (ULift.{u + 1} (ZMod m)) (𝟙 X)) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ (pullbackToposIdIso m X) ≪≫
    StacksDraft.DerivedRingIso.mapDerivedCategoryIdIso

end Stacks.EtaleCohomology.EtaleCoefficients

end
