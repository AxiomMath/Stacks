module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeGeometryModel
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeCotangent

/-!
# The obstruction groups of the deformations of a point of `Spaces'_{fp, flat, proper}`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over a field and let
`x = (X ⟶ Spec A)` be a deformation of `x₀` over an object `A` of `𝒞_Λ`. For an `A`-module `I`
killed by `𝔪_A`, the obstruction group `T²_{X/A}(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of
[Stacks, Remark 0D1P] is `T²_{X₀/k}(I) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀} ⊗_k I)`:

* `T²_{X/A}(I) = Hom(Lj^* L_{X/A}, (𝒪_{X₀} ⊗_k I)[2])` along the closed immersion
  `j : X₀ ⟶ X`, whose direct image of étale sheaves is an equivalence
  (`AlgebraicGeometry.ProperFlatSpaceDeformation.cotangentExtTwoSpecialFibreAddEquiv`);
* `Lj^* L_{X/A} ≅ L_{X₀/k}`, flat base change of the cotangent complex ([Stacks, Tag 08QQ],
  [Stacks, Tag 09DL]; `AlgebraicGeometry.ProperFlatSpaceDeformation.specialFibreCotangentIso`).

Hence the obstruction groups of all deformations of `x₀` vanish as soon as
`T²_{X₀/k}(k) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀})` does.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceDeformation.cotangentExtTwoSpecialFibreEquiv`:
  `T²_{X/A}(I) ≃ T²_{X₀/k}(I)`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.obstructionGroupsEmbedInSpecialFibre`
* `AlgebraicGeometry.ProperFlatSpaceDeformation.deformationObstructionGroupsVanish_of_subsingleton`

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 09DL](https://stacks.math.columbia.edu/tag/09DL)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (a : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀)
  (I : ModuleCat.{u} a.algebra) (hI : ∀ r ∈ IsLocalRing.maximalIdeal a.algebra, ∀ i : I, r • i = 0)

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`T²_{X/A}(I) ≃ T²_{X₀/k}(I)`** for a deformation `x = (X ⟶ Spec A)` of `x₀` and an
`A`-module `I` killed by `𝔪_A`, read as a `k`-vector space: the adjunction along the closed
immersion `X₀ ⟶ X` (`cotangentExtTwoSpecialFibreAddEquiv`) followed by flat base change of the
cotangent complex (`specialFibreCotangentIso`). -/
def cotangentExtTwoSpecialFibreEquiv :
    (Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap a.point a.obj_eq)
        (Space.ProperFlatLift.chartBaseRingHom a.point a.obj_eq)).obj I ≃
      (Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
          (residueModule I hI) :=
  (cotangentExtTwoSpecialFibreAddEquiv a I hI).toEquiv.trans
    (((Iso.refl _ ≪≫ specialFibreCotangentIso a ≪≫ Iso.refl _).homCongr (Iso.refl _)).trans
      (Space.cotangentExtFunctorObjEquiv
        (Space.ProperFlatLift.chartStructureMap x₀ (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀)) 2
        (residueModule I hI)).symm.toEquiv)

variable (x₀ hx₀) in
/-- The obstruction groups of the deformations of `x₀` embed in those of `x₀`. -/
theorem obstructionGroupsEmbedInSpecialFibre : ObstructionGroupsEmbedInSpecialFibre x₀ hx₀ :=
  fun a I hI => ⟨cotangentExtTwoSpecialFibreEquiv a I hI,
    (cotangentExtTwoSpecialFibreEquiv a I hI).injective⟩

/-- **The obstruction groups of all deformations of `x₀` vanish when `T²_{X₀/k}(k) = 0`.** If
`Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀}) = 0`, then for every deformation `x = (X ⟶ Spec A)` of `x₀` over
an object `A` of `𝒞_Λ` and every `A`-module `I` killed by `𝔪_A`,
`T²_{X/A}(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I) = 0` ([Stacks, Remark 0D1P]). -/
theorem deformationObstructionGroupsVanish_of_subsingleton
    (hT2 : Subsingleton
      ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
          (ModuleCat.of k k))) :
    DeformationObstructionGroupsVanish (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀) :=
  deformationObstructionGroupsVanish_of_embed_of_subsingleton (iΛ := iΛ) (x₀ := x₀) (hx₀ := hx₀)
    (obstructionGroupsEmbedInSpecialFibre x₀ hx₀) hT2

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
