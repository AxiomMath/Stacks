module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The derived direct image along an integral morphism of a single sheaf

For `π : Z ⟶ X` integral, direct image of abelian sheaves on the small étale sites is exact
([Stacks, Tag 04C2]), so `Rπ_*F[0] = (π_*F)[0]` on `D(-_étale, ℤ/m)`
(`Stacks.EtaleCohomology.EtaleCoefficients.nonempty_singleFunctor_pushforwardTopos_iso`). The
last paragraph of the proof of [Stacks, Tag 0F1J] uses this as "`Rπ_{i,*} = π_{i,*}`": it is what
identifies a sheaf `⨁ πᵢ_*𝔽_ℓ` placed in degree zero with `⨁ Rπᵢ_*𝔽_ℓ`.

## The proof

The underlying complex of abelian sheaves of `Rπ_*F[0]` is `R⁺π_*` of the underlying abelian
sheaf of `F` (`pushforwardForgetPlusIso`), which is `π_*` of it placed in degree zero, `π_*`
being exact. So `Rπ_*F[0]` has cohomology in degree zero only, and is that cohomology placed in
degree zero; the cohomology sheaf is `π_*F` because forgetting the module structure is fully
faithful for `ℤ/mℤ`-coefficients (`etaleToSheafZModFullyFaithful`).

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (m : ℕ) {Z X : Scheme.{u}}

/-- **The derived direct image along an integral morphism of a sheaf placed in degree zero is the
direct image placed in degree zero**, on `D(-_étale, ℤ/m)`: the underlying complex of abelian
sheaves of `Rπ_*F[0]` is `R⁺π_*` of the underlying abelian sheaf, which is `π_*` of it because
direct image along an integral morphism is exact
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`, Stacks 04C2). -/
theorem nonempty_singleFunctor_pushforwardTopos_iso (π : Z ⟶ X) [IsIntegralHom π]
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (ringedTopos (ULift.{u + 1} (ZMod m)) Z).O)) :
    Nonempty ((DerivedCategory.singleFunctor _ 0).obj
        ((ringedToposHom (ULift.{u + 1} (ZMod m)) π).pushforwardTopos.obj F) ≅
      (pushforward (ULift.{u + 1} (ZMod m)) π).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let Λ := ULift.{u + 1} (ZMod m)
  have hex := (exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)
  have : PreservesFiniteLimits (smallEtalePushforwardAb π) := hex.1
  have : PreservesFiniteColimits (smallEtalePushforwardAb π) := hex.2
  have : (smallEtalePushforwardAb π).Additive := Functor.additive_of_preserves_binary_products _
  let G := (etaleToSheaf Λ Z).obj F
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let Xd := (pushforward Λ π).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  -- the underlying complex of abelian sheaves of `Xd`
  let e₁ : (forgetDerived Λ X).obj Xd ≅
      DerivedCategory.Plus.ι.obj ((smallEtalePushforwardAb π).rightDerivedFunctorPlus.obj
        ((forgetDerivedPlus Λ Z).obj K)) :=
    (forgetDerived Λ X).mapIso ((pushforward Λ π).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app F).symm) ≪≫
      (pushforwardForgetPlusIso Λ π).app K
  let e₂ : DerivedCategory.Plus.ι.obj ((smallEtalePushforwardAb π).rightDerivedFunctorPlus.obj
        ((forgetDerivedPlus Λ Z).obj K)) ≅
      (smallEtalePushforwardAb π).mapDerivedCategory.obj
        ((forgetDerived Λ Z).obj (DerivedCategory.Plus.ι.obj K)) :=
    DerivedCategory.Plus.ι.mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (smallEtalePushforwardAb π)).app
        ((forgetDerivedPlus Λ Z).obj K)).symm
  let e₃ : (smallEtalePushforwardAb π).mapDerivedCategory.obj
        ((forgetDerived Λ Z).obj (DerivedCategory.Plus.ι.obj K)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((smallEtalePushforwardAb π).obj G) :=
    (smallEtalePushforwardAb π).mapDerivedCategory.mapIso ((forgetDerived Λ Z).mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app F) ≪≫
      ((etaleToSheaf Λ Z).mapDerivedCategorySingleFunctor 0).app F) ≪≫
      ((smallEtalePushforwardAb π).mapDerivedCategorySingleFunctor 0).app G
  let e₄ : (smallEtalePushforwardAb π).obj G ≅
      (etaleToSheaf Λ X).obj ((ringedToposHom Λ π).pushforwardTopos.obj F) :=
    ((pushforwardEtaleToSheafIso Λ π).app F).symm
  let E : (forgetDerived Λ X).obj Xd ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((etaleToSheaf Λ X).obj ((ringedToposHom Λ π).pushforwardTopos.obj F)) :=
    e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₄
  -- cohomology of `Xd` through the underlying abelian sheaves
  let hH : ∀ q : ℤ, (etaleToSheaf Λ X).obj ((DerivedCategory.homologyFunctor _ q).obj Xd) ≅
      (DerivedCategory.homologyFunctor _ q).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((etaleToSheaf Λ X).obj ((ringedToposHom Λ π).pushforwardTopos.obj F))) := fun q =>
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (etaleToSheaf Λ X) q).app
      Xd).symm ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso E
  have hGE : Xd.IsGE 0 := isGE_pushforward_obj Λ π _ 0 inferInstance
  have hLE : Xd.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_of_isZero_etaleToSheaf_obj Λ
      ((DerivedCategory.isZero_of_isLE _ 0 i hi).of_iso (hH i))
  obtain ⟨A, ⟨eA⟩⟩ := Xd.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let eA' : (etaleToSheaf Λ X).obj A ≅
      (etaleToSheaf Λ X).obj ((ringedToposHom Λ π).pushforwardTopos.obj F) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso
        (((etaleToSheaf Λ X).mapDerivedCategorySingleFunctor 0).app A).symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (etaleToSheaf Λ X)
        0).app _ ≪≫
      (etaleToSheaf Λ X).mapIso ((DerivedCategory.homologyFunctor _ 0).mapIso eA.symm) ≪≫
      hH 0 ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _
  exact ⟨(DerivedCategory.singleFunctor _ 0).mapIso
    ((etaleToSheafZModFullyFaithful m X).preimageIso eA').symm ≪≫ eA.symm⟩

end Stacks.EtaleCohomology.EtaleCoefficients

end
