module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.HigherDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AcyclicSheavesFilteredColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ExtendScalarsCofan

/-!
# `R^n f_* (Λ/ℓΛ)̲` is the extension of scalars of `R^n f_* (ℤ/ℓ)̲`

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, `ℓ` a prime and `Λ` a
ring (in the coefficient universe of `X`). This file proves

`R^n f_* (Λ/ℓΛ)̲ ≅ R^n f_* (ℤ/ℓ)̲ ⊗_ℤ Λ̲`

as sheaves of `Λ`-modules on `S_étale`. This is the step of [Stacks, Tag 0GKW] that the source
takes from the projection formula ([Stacks, Tag 0F0G]); here it is deduced from the fact that
higher direct images along a quasi-compact quasi-separated morphism commute with direct sums
([Stacks, Tag 09Z1], `preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`): as
abelian sheaves both sides are direct sums of copies of `R^n f_* (ℤ/ℓ)̲` indexed by an `𝔽_ℓ`-basis
of `Λ/ℓΛ`.

## Main definitions

* `Stacks.EtaleCohomology.FiniteCoefficients.constantDirectImage`: `M ↦ R^n f_* M̲` on
  `Λ`-modules.
* `Stacks.EtaleCohomology.FiniteCoefficients.constantDirectImageForgetIso`: its underlying
  abelian sheaf only depends on the underlying abelian group of `M`.
* `Stacks.EtaleCohomology.FiniteCoefficients.quotientDirectImageIso`: the isomorphism above.

## References

* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.FiniteCoefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- `M ↦ R^n f_* M̲`, for `Λ`-modules `M`. -/
abbrev constantDirectImage (Λ : Type r) [CommRing Λ] :
    ModuleCat.{max (u + 1) r} Λ ⥤ EtaleModules.{u, r} Λ S :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
    (etaleModuleDirectImage.{u, r} Λ f).rightDerived n

/-- `A ↦ R^n f_* A̲`, for abelian groups `A`. -/
abbrev constantDirectImageAb :
    AddCommGrpCat.{u + 1} ⥤ Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (etaleAbelianDirectImage.{u, 0} f).rightDerived n

/-- **The underlying abelian sheaf of `R^n f_* M̲` only depends on the underlying abelian group of
`M`**: it is `R^n f_*` of the constant abelian sheaf on it ([Stacks, Tag 0D6J] (3)). -/
def constantDirectImageForgetIso (Λ : Type r) [CommRing Λ] :
    constantDirectImage f n Λ ⋙ _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ S ≅
      forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ⋙
        constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} ⋙
          (etaleAbelianDirectImage.{u, r} f).rightDerived n :=
  Functor.isoWhiskerLeft (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
      (etaleModuleRightDerivedDirectImageForgetIso.{u, r} Λ f n) ≪≫
    Functor.isoWhiskerRight (etaleModuleForgetConstantSheafIsoGeneral.{u, r} Λ X)
      ((etaleAbelianDirectImage.{u, r} f).rightDerived n)

/-- `M ↦ R^n f_* M̲` is `Λ`-linear. -/
instance constantDirectImage_linear (Λ : Type r) [CommRing Λ] :
    Functor.Linear Λ (constantDirectImage f n Λ) :=
  haveI : Functor.Linear Λ
      (constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :=
    inferInstanceAs (Functor.Linear Λ (Functor.const X.Etaleᵒᵖ ⋙
      presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)))
  inferInstance

section Quotient

variable (Λ : Type (u + 1)) [CommRing Λ] (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] quotientZModModule

/-- `Λ/ℓΛ` as a `Λ`-module. -/
abbrev quotientModule : ModuleCat.{u + 1} Λ :=
  ModuleCat.of Λ (Λ ⧸ Ideal.span {(ℓ : Λ)})

/-- `R^n f_* (ℤ/ℓ)̲`, a sheaf of `ℤ/ℓ`-modules on `S_étale`. -/
abbrev zmodDirectImage : EtaleModules.{u, 0} (ZMod ℓ) S :=
  (constantDirectImage f n (ZMod ℓ)).obj (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- The unit `ℤ/ℓ ⟶ Λ/ℓΛ`, `k ↦ k · 1`, of underlying abelian groups. -/
def zmodToQuotient : AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ⟶
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj (quotientModule Λ ℓ) :=
  AddCommGrpCat.ofHom
    { toFun := fun k ↦ k.down.val • (1 : Λ ⧸ Ideal.span {(ℓ : Λ)})
      map_zero' := by simp
      map_add' := fun k k' ↦ val_add_nsmul ℓ (nsmul_quotient_span Λ ℓ 1) _ _ }

/-- For a basis element `bᵢ` of `Λ/ℓΛ` with lift `λᵢ ∈ Λ`, the unit `ℤ/ℓ ⟶ Λ/ℓΛ` followed by
multiplication by `λᵢ` is the map `k ↦ k · bᵢ`, the `i`-th inclusion of the cofan. -/
theorem zmodToQuotient_comp_smul (i : quotientBasisIndex Λ ℓ) :
    zmodToQuotient Λ ℓ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (quotientBasisLift Λ ℓ i • 𝟙 (quotientModule Λ ℓ)) =
      (zmodBasisCofan (quotientBasis Λ ℓ)).inj i := by
  ext k
  change quotientBasisLift Λ ℓ i • (k.down.val • (1 : Λ ⧸ Ideal.span {(ℓ : Λ)})) =
    k.down.val • quotientBasis Λ ℓ i
  rw [smul_comm (quotientBasisLift Λ ℓ i) k.down.val]
  congr 1
  rw [← mk_quotientBasisLift, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]

/-- The additive map `R^n f_* (ℤ/ℓ)̲ ⟶ R^n f_* (Λ/ℓΛ)̲` induced by the unit `ℤ/ℓ ⟶ Λ/ℓΛ`, of
underlying abelian sheaves. -/
def zmodDirectImageToQuotient :
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, 0} (ZMod ℓ) S).obj
        (zmodDirectImage f n ℓ) ⟶
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).obj
        ((constantDirectImage f n Λ).obj (quotientModule Λ ℓ)) :=
  (constantDirectImageForgetIso f n (ZMod ℓ)).hom.app _ ≫
    (constantDirectImageAb f n).map (zmodToQuotient Λ ℓ) ≫
      (constantDirectImageForgetIso f n Λ).inv.app (quotientModule Λ ℓ)

variable [QuasiCompact f] [QuasiSeparated f]

/-- **`R^n f_* (Λ/ℓΛ)̲` is, as an abelian sheaf, the direct sum of copies of `R^n f_* (ℤ/ℓ)̲`
indexed by an `𝔽_ℓ`-basis of `Λ/ℓΛ`.** `R^n f_*` commutes with direct sums ([Stacks, Tag 09Z1]). -/
def isColimitQuotientDirectImageCofan :
    IsColimit (Cofan.mk ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).obj
        ((constantDirectImage f n Λ).obj (quotientModule Λ ℓ))) fun i ↦
      zmodDirectImageToQuotient f n Λ ℓ ≫
        (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).map
          (quotientBasisLift Λ ℓ i •
            𝟙 ((constantDirectImage f n Λ).obj (quotientModule Λ ℓ)))) := by
  haveI : PreservesColimitsOfShape (Discrete (quotientBasisIndex Λ ℓ))
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (etaleSiteTerminalIsTerminal X)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  haveI := preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{0} f n
    (quotientBasisIndex Λ ℓ)
  have hΨ := isColimitCofanMkObjOfIsColimit (constantDirectImageAb f n) _ _
    (isColimitZModBasisCofan (quotientBasis Λ ℓ))
  refine isColimit_cofan_of_iso hΨ ((constantDirectImageForgetIso f n (ZMod ℓ)).app _)
    ((constantDirectImageForgetIso f n Λ).app (quotientModule Λ ℓ)).symm _ fun i ↦ ?_
  have hlin : (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).map
      (quotientBasisLift Λ ℓ i •
        𝟙 ((constantDirectImage f n Λ).obj (quotientModule Λ ℓ))) =
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).map
        ((constantDirectImage f n Λ).map
          (quotientBasisLift Λ ℓ i • 𝟙 (quotientModule Λ ℓ))) := by
    congr 1
    rw [Functor.map_smul (constantDirectImage f n Λ), CategoryTheory.Functor.map_id]
  have hnat : (constantDirectImageForgetIso f n Λ).inv.app (quotientModule Λ ℓ) ≫
      (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, u + 1} Λ S).map
        ((constantDirectImage f n Λ).map
          (quotientBasisLift Λ ℓ i • 𝟙 (quotientModule Λ ℓ))) =
      (constantDirectImageAb f n).map ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (quotientBasisLift Λ ℓ i • 𝟙 (quotientModule Λ ℓ))) ≫
        (constantDirectImageForgetIso f n Λ).inv.app (quotientModule Λ ℓ) :=
    ((constantDirectImageForgetIso f n Λ).inv.naturality
      (quotientBasisLift Λ ℓ i • 𝟙 (quotientModule Λ ℓ))).symm
  rw [hlin, zmodDirectImageToQuotient, Category.assoc, Category.assoc, hnat,
    ← Functor.map_comp_assoc, zmodToQuotient_comp_smul]
  rfl

attribute [local instance] preservesSheafification_forget₂_moduleCat_smallEtale in
/-- **`R^n f_* (ℤ/ℓ)̲ ⊗_ℤ Λ̲ ⟶ R^n f_* (Λ/ℓΛ)̲` is an isomorphism**: the `Λ`-linear map adjoint to
the map induced by the unit `ℤ/ℓ ⟶ Λ/ℓΛ`. Both sides are, as abelian sheaves, direct sums of
copies of `R^n f_* (ℤ/ℓ)̲` along an `𝔽_ℓ`-basis of `Λ/ℓΛ`. -/
theorem isIso_zmodExtendScalarsDesc_zmodDirectImageToQuotient :
    IsIso (zmodExtendScalarsDesc S.smallEtaleTopology Λ ℓ (zmodDirectImage f n ℓ)
      (zmodDirectImageToQuotient f n Λ ℓ)) :=
  isIso_zmodExtendScalarsDesc S.smallEtaleTopology (zmodDirectImage f n ℓ)
    (zmodDirectImageToQuotient f n Λ ℓ) (quotientBasisLift Λ ℓ) (quotientCoord Λ ℓ)
    (exists_eq_sum_quotientBasisLift Λ ℓ) (quotientCoord_quotientBasisLift Λ ℓ)
    (isColimitQuotientDirectImageCofan f n Λ ℓ)

end Quotient

end Stacks.EtaleCohomology.FiniteCoefficients

end
