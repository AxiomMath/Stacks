module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSectionsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionPulledBackIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceTangentClass
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveExtensionOfClass

/-!
# The thickening realizing an extension of the structure sheaf of an algebraic space over `k`

In the situation of Stacks 0E3Z, let `X` be an algebraic space over the field `k`, `f : X ⟶ Spec k`
its structure morphism, and `P` an extension of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by
`𝒪_X ⊗_k k`. Its ideal is `𝒪_X ≅ f^*𝒪_{Spec k}`, quasi-coherent and pulled back from the affine
scheme `Spec k` with sections of size below the cutoff of the site, so `P` is the data of
Stacks 05ZT and is realized on the given site by the thickened quotient `X ⊂ X' = U'/R'` over
`Spec k` of a presentation `X = U/R`
(`AlgebraicGeometry.Space.SquareZeroExtension.thickeningQuotient`).

## Main definitions

* `Deformation.Examples.spaceRankOneCoefficient`: the module `𝒪_X ⊗_k k`.
* `Deformation.Examples.spaceSurjExtension`: the 05ZT data of `P`.
* `Deformation.Examples.spaceSurjAmbient`: the thickening `X'`.
* `Deformation.Examples.spaceSurjImmersion`, `Deformation.Examples.spaceSurjToBase`: `X ⟶ X'` and
  `X' ⟶ Spec k`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Deformation.AlgebraExtension

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The module `𝒪_X ⊗_k k`.** -/
abbrev spaceRankOneCoefficient :=
  (baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
    ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k))

/-- `𝒪_X ⊗_k k ≅ 𝒪_X`. -/
abbrev spaceRankOneCoefficientIso :
    spaceRankOneCoefficient B hΛ hSpec X hX toK ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of Λ)) hΛ X hX).O) :=
  baseRingTensorModuleSelfIso B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)

/-- `𝒪_X ⊗_k k` is quasi-coherent. -/
theorem isQuasicoherentOnSite_spaceRankOneCoefficient :
    (spaceRankOneCoefficient B hΛ hSpec X hX toK).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_baseRingTensorModule_self B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)

variable (P : AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
  (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
  (spaceRankOneCoefficient B hΛ hSpec X hX toK))

/-- **The 05ZT data of an extension by `𝒪_X ⊗_k k`**, relative to `X ⟶ Spec k`. -/
def spaceSurjExtension :
    SquareZeroExtension B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK) :=
  SquareZeroExtension.ofAlgebraExtension _ P
    (isQuasicoherentOnSite_spaceRankOneCoefficient B hΛ hSpec X hX toK)

/-- The ideal `𝒪_X ⊗_k k` of the extension is the pullback of `𝒪_{Spec k}` along `X ⟶ Spec k`. -/
abbrev spaceSurjIdealIso :
    (spaceSurjExtension B hΛ hSpec X hX toK P).I ≅
      (modulePullback B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)).obj
        (SheafOfModules.unit _) :=
  spaceRankOneCoefficientIso B hΛ hSpec X hX toK ≪≫
    (modulePullbackUnitIso B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)).symm

/-- The presentation of `X` over the chosen presentation of `Spec k`. -/
def spaceSurjPresentation : Presentation B (Spec (.of Λ)) hΛ X hX :=
  presentationOverChart (spaceStructureMap B hΛ hSpec X hX toK).hom
    (presentationOfIsAlgebraicSpace B (Spec (.of Λ)) hΛ X hX)
    (presentationOfIsAlgebraicSpace B (Spec (.of Λ)) hΛ _
      (isAlgebraicSpace_yoneda B (Spec (.of Λ)) hΛ
        (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))))

/-- The site contains the thickening of each chart `U` realizing the extension. -/
theorem contains_spaceSurj_chartRealizedScheme (U : SmallEtale B (Spec (.of Λ)) hΛ X) :
    B.Contains ((spaceSurjExtension B hΛ hSpec X hX toK P).chartRealizedScheme U) :=
  (spaceSurjExtension B hΛ hSpec X hX toK P).contains_chartRealizedScheme_of_iso_modulePullback
    (isAffine_toScheme_spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))
    (spaceStructureMap B hΛ hSpec X hX toK) (SheafOfModules.unit _)
    (SheafOfModules.isQuasicoherentOnSite_unit _)
    (mk_sections_structureRingSheaf_lt_cutoff B (Spec (.of Λ)) hΛ _ _)
    (spaceSurjIdealIso B hΛ hSpec X hX toK P) U

/-- **The thickening `X' = U'/R'` realizing the extension.** -/
abbrev spaceSurjAmbient : AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
  (spaceSurjExtension B hΛ hSpec X hX toK P).thickeningQuotient hΛ
    (spaceSurjPresentation B hΛ hSpec X hX toK)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)

/-- **The closed immersion `X ⟶ X'`.** -/
abbrev spaceSurjImmersion : spaceOf B hΛ X hX ⟶ spaceSurjAmbient B hΛ hSpec X hX toK P :=
  (spaceSurjExtension B hΛ hSpec X hX toK P).thickeningImmersion
    (spaceSurjPresentation B hΛ hSpec X hX toK)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)

/-- **The morphism `X' ⟶ Spec k` extending the structure morphism of `X`.** -/
abbrev spaceSurjToBase :
    spaceSurjAmbient B hΛ hSpec X hX toK P ⟶
      schemeSpace (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) :=
  (spaceSurjExtension B hΛ hSpec X hX toK P).thickeningQuotientToBase
    (spaceSurjPresentation B hΛ hSpec X hX toK) _ _
    (presentationOverChart_comm _ _ _) _
    (presentationOverChartRelHom_target _ _ _) (presentationOverChartRelHom_source _ _ _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)

/-- `X ⟶ X' ⟶ Spec k` is the structure morphism of `X`. -/
theorem spaceSurjImmersion_comp_toBase :
    spaceSurjImmersion B hΛ hSpec X hX toK P ≫ spaceSurjToBase B hΛ hSpec X hX toK P =
      spaceStructureMap B hΛ hSpec X hX toK :=
  (spaceSurjExtension B hΛ hSpec X hX toK P).thickeningImmersion_comp_thickeningQuotientToBase
    (spaceSurjPresentation B hΛ hSpec X hX toK) _ _
    (presentationOverChart_comm _ _ _) _
    (presentationOverChartRelHom_target _ _ _) (presentationOverChartRelHom_source _ _ _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)
    (contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _)

end Deformation.Examples

end
