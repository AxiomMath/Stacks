module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite

/-!
# The inverse image of a lisse sheaf is the lisse sheaf of the restricted module

Let `f : Y ⟶ X` be a morphism of connected schemes of a big étale site and `ȳ` a geometric point of
`Y`. For a finite `Λ`-module `P` with a continuous action of `π₁(X, f(ȳ))`, the inverse image along
`f` of the lisse sheaf `ℱ_P` (`Stacks.EtaleCohomology.lisseEtaleSheaf`) is the lisse sheaf of `P`
with the action restricted along `π₁(Y, ȳ) → π₁(X, f(ȳ))`. This is [Stacks, Tag 0DV6] for sheaves
of `Λ`-modules, which is
`AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso`
for the inverse image on Mathlib's small étale site; that inverse image is isomorphic to
`Stacks.EtaleCohomology.etaleModuleInverseImage`, both being left adjoint to the same direct image.

## Main definitions

* `Stacks.EtaleCohomology.etaleSiteSheafPullbackModuleIso`: the isomorphism between the two
  inverse images.

## Main results

* `Stacks.EtaleCohomology.nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso`:
  `f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace Y.1]
  (f : Y ⟶ X) (y : GeometricPoint Y.1) (Λ : Type) [CommRing Λ] [Finite Λ]

/-- The inverse image on Mathlib's small étale site, used by Tag 0DV6, is isomorphic to
`etaleModuleInverseImage`: both are left adjoint to the direct image. -/
def etaleSiteSheafPullbackModuleIso :
    etaleSiteSheafPullbackModule B f Λ ≅ etaleModuleInverseImage.{u, 0} Λ f.hom :=
  (etaleSiteSheafPullbackModuleAdjunction B f Λ).leftAdjointUniq
    (etaleModuleInverseImageAdj.{u, 0} Λ f.hom)

/-- **Tag 0DV6 for lisse sheaves**: `f⁻¹ ℱ_P ≅ ℱ_{P|_{π₁(Y, ȳ)}}`. -/
theorem nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (y.map f.hom))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ f.hom).obj
        ((lisseEtaleSheaf B X (y.map f.hom) Λ).obj P) ≅
      (lisseEtaleSheaf B Y y Λ).obj
        ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).obj P)) := by
  obtain ⟨α⟩ :=
    nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso B f Λ y
  let EX := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X (y.map f.hom) Λ
  let EY := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ
  let G := EX.inverse.obj P
  let pull := etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ
  let β : EY.functor.obj (pull.obj G) ≅
      (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).obj P :=
    (α.app G).symm ≪≫
      (finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).mapIso
        (EX.counitIso.app P)
  let γ : pull.obj G ≅ EY.inverse.obj
      ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y)).obj P) :=
    EY.unitIso.app (pull.obj G) ≪≫ EY.inverse.mapIso β
  exact ⟨(etaleSiteSheafPullbackModuleIso B f Λ).symm.app _ ≪≫ (ObjectProperty.ι _).mapIso γ⟩

end Stacks.EtaleCohomology

end
