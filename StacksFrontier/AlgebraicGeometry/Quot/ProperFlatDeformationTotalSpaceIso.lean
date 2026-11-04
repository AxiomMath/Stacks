module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.IsoOfInverseImageStructureSheafIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickeningAdditions

/-!
# Isomorphic extensions give isomorphic total spaces

For two deformations `X'₁ ⟶ Spec k[V]` and `X'₂ ⟶ Spec k[V]` of the same object
`x₀ = (X₀ ⟶ Spec k)` of `Spaces'_{fp, flat, proper}` over `Spec ℤ`, an isomorphism of their
extensions (`AlgebraicGeometry.Space.deformationTangentExtension`) is in particular an
isomorphism, over `𝒪_{X₀}`, of the structure sheaves of `X'₁` and `X'₂` read on `X₀`. By
Stacks 05ZM and 05YZ it gives an isomorphism `f : X'₁ ≅ X'₂` under `X₀`. This is the first step
of the injectivity over `k[ε]` of the classes of the proof of Stacks 0D1K.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_pushforward_deformationThickeningIso_hom_comp`: the
  closed fibre of a deformation is a thickening of its total space, so the direct image along
  `X₀ ≅ Z ⊂ X'` is an equivalence of étale topoi.
* `AlgebraicGeometry.Space.exists_iso_deformationArrow_comp_eq_of_iso`

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

universe u

namespace Deformation.AlgebraExtension

universe v w

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {A O : Sheaf J CommRingCat.{u}}
  {a : A ⟶ O}
  {M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  {P Q : AlgebraExtension a M}

/-- The isomorphism of middle terms underlying an isomorphism of extensions. -/
def extensionRingIso (e : P ≅ Q) : P.extension ≅ Q.extension where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by rw [← comp_hom', e.hom_inv_id, id_hom]
  inv_hom_id := by rw [← comp_hom', e.inv_hom_id, id_hom]

/-- The isomorphism of middle terms of an isomorphism of extensions lies over `𝒪`. -/
theorem extensionRingIso_hom_comp_reduction (e : P ≅ Q) :
    (extensionRingIso e).hom ≫ Q.reduction = P.reduction :=
  e.hom.reduction_comm

end Deformation.AlgebraExtension

namespace AlgebraicGeometry.Space

section Thickening

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- **The direct image along `X₀ ≅ Z ⊂ X'` is an equivalence of étale topoi**, `Z` the closed
fibre of a deformation `X'`: the composite is a closed immersion, surjective on points because
`Z ⊂ X'` is a thickening (Stacks 0D16, 05ZM). -/
theorem isEquivalence_pushforward_deformationThickeningIso_hom_comp :
    (smallEtaleRingedToposHom B S hS ((deformationThickeningIso B S hS x hsq).hom ≫
      subspaceInclusion B S hS _
        (deformationThickening B S hS x hsq))).toToposHom.pushforward.IsEquivalence := by
  obtain ⟨hG, -⟩ := isFirstOrderThickening_deformationThickening B S hS x hsq
  have : IsIso (deformationThickeningIso B S hS x hsq).hom.hom :=
    (ObjectProperty.ι _).map_isIso (deformationThickeningIso B S hS x hsq).hom
  have hci : IsClosedImmersion B S hS ((deformationThickeningIso B S hS x hsq).hom ≫
      subspaceInclusion B S hS _ (deformationThickening B S hS x hsq)).hom :=
    isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
      (isClosedImmersion_inclusion_of_isThickening B S hS hG)
  refine isEquivalence_pushforward_smallEtaleRingedToposHom B S hS _ hci
    ((surjective_iff_pointsMap_surjective B S hS y₀.obj.obj.left.2 (deformationSpace B S hS x).2
      _ hci.rep).2 ?_)
  rw [show ((deformationThickeningIso B S hS x hsq).hom ≫
      subspaceInclusion B S hS _ (deformationThickening B S hS x hsq)).hom =
        (deformationThickeningIso B S hS x hsq).hom.hom ≫
          (subspaceInclusion B S hS _ (deformationThickening B S hS x hsq)).hom from rfl,
    pointsMap_comp]
  exact hG.2.comp (pointsMap_surjective_of_isIso B S hS _)

end Thickening

section Iso

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {iΛ : Spec (.of Λ) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))}
  {y₀ : CartesianProperFlatSpaces B _ hZ}
  {hy₀ : (cartesianProperFlatProjection B _ hZ ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (V : FGModuleCat.{u} k)

/-- The category of extensions of `f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}` by `𝒪_{X₀} ⊗_k V`, with its
universes named (instance search does not find them here). -/
local instance deformationTangentExtensionCategory :
    Category.{u + 1, u + 1} (AlgebraExtension (J := SmallEtale.topology B _ hZ y₀.obj.obj.left.1)
      (inverseImageBaseMap B _ hZ (baseStructureMap B _ hZ (y₀ := y₀)))
      ((baseRingTensorModule B _ hZ y₀.obj.obj.left (baseFieldHom B _ hZ (hy₀ := hy₀))).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V))) :=
  AlgebraExtension.instCategory.{u, u + 1, u}

variable {x x' : DeformationObject iΛ (cartesianProperFlatProjection B _ hZ ⋙ Over.post B.inclusion)
    y₀ hy₀}
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (e : deformationTangentExtension B _ hZ V x hx ≅
    deformationTangentExtension B _ hZ V x' hx')

/-- **The isomorphism of structure sheaves underlying an isomorphism of extensions**: the
structure sheaves of the two total spaces, read on `X₀` through the closed fibres. -/
def deformationTangentExtensionRingIso :
    etaleRestrictedInverseImageStructureSheaf B hZ
        (deformationThickeningIso B _ hZ x (ker_residueMap_sq_of_eq B _ hZ V x hx))
        (subspaceInclusion B _ hZ _
          (deformationThickening B _ hZ x (ker_residueMap_sq_of_eq B _ hZ V x hx))) ≅
      etaleRestrictedInverseImageStructureSheaf B hZ
        (deformationThickeningIso B _ hZ x' (ker_residueMap_sq_of_eq B _ hZ V x' hx'))
        (subspaceInclusion B _ hZ _
          (deformationThickening B _ hZ x' (ker_residueMap_sq_of_eq B _ hZ V x' hx'))) :=
  AlgebraExtension.extensionRingIso.{u, u + 1, u} e

/-- **The isomorphism of small étale ringed topoi of the two total spaces** determined by an
isomorphism of the extensions of two deformations over `k[V]`
(`AlgebraicGeometry.RingedToposHom.transferOfInverseImageIso`). -/
def deformationTransfer :
    RingedToposHom (smallEtaleRingedTopos B _ hZ (deformationSpace B _ hZ x))
      (smallEtaleRingedTopos B _ hZ (deformationSpace B _ hZ x')) :=
  haveI := isEquivalence_pushforward_deformationThickeningIso_hom_comp B _ hZ x
    (ker_residueMap_sq_of_eq B _ hZ V x hx)
  haveI := isEquivalence_pushforward_deformationThickeningIso_hom_comp B _ hZ x'
    (ker_residueMap_sq_of_eq B _ hZ V x' hx')
  RingedToposHom.transferOfInverseImageIso (X := smallEtaleRingedTopos B _ hZ y₀.obj.obj.left)
    (Y₁ := smallEtaleRingedTopos B _ hZ (deformationSpace B _ hZ x))
    (Y₂ := smallEtaleRingedTopos B _ hZ (deformationSpace B _ hZ x'))
    (smallEtaleRingedToposHom B _ hZ
      ((deformationThickeningIso B _ hZ x (ker_residueMap_sq_of_eq B _ hZ V x hx)).hom ≫
        subspaceInclusion B _ hZ _
          (deformationThickening B _ hZ x (ker_residueMap_sq_of_eq B _ hZ V x hx))))
    (smallEtaleRingedToposHom B _ hZ
      ((deformationThickeningIso B _ hZ x' (ker_residueMap_sq_of_eq B _ hZ V x' hx')).hom ≫
        subspaceInclusion B _ hZ _
          (deformationThickening B _ hZ x' (ker_residueMap_sq_of_eq B _ hZ V x' hx'))))
    (etaleRestrictedInverseImageStructureSheafIso B hZ _ _ ≪≫
      deformationTangentExtensionRingIso B hZ V hx hx' e ≪≫
      (etaleRestrictedInverseImageStructureSheafIso B hZ _ _).symm)

/-- **Isomorphic extensions give isomorphic total spaces under `X₀`.** An isomorphism of the
extensions of two deformations `X'₁, X'₂` over `k[V]` of `x₀ = (X₀ ⟶ Spec k)` gives an
isomorphism `f : X'₁ ≅ X'₂` commuting with the two arrows `X₀ ⟶ X'_j`, inducing the isomorphism
of small étale ringed topoi `AlgebraicGeometry.Space.deformationTransfer`. -/
theorem exists_iso_deformationArrow_comp_eq_of_iso :
    ∃ f : deformationSpace B _ hZ x ≅ deformationSpace B _ hZ x',
      (deformationArrow B _ hZ x).left ≫ f.hom = (deformationArrow B _ hZ x').left ∧
        InducesSmallEtaleRingedToposHom B _ hZ f.hom (deformationTransfer B hZ V hx hx' e) := by
  have := isEquivalence_pushforward_deformationThickeningIso_hom_comp B _ hZ x
    (ker_residueMap_sq_of_eq B _ hZ V x hx)
  have := isEquivalence_pushforward_deformationThickeningIso_hom_comp B _ hZ x'
    (ker_residueMap_sq_of_eq B _ hZ V x' hx')
  obtain ⟨f, hf, hind⟩ := exists_iso_comp_eq_of_etaleRestrictionIso B hZ _ _ _ _
    (deformationTangentExtensionRingIso B hZ V hx hx' e)
    (AlgebraExtension.extensionRingIso_hom_comp_reduction.{u, u + 1, u} e)
  refine ⟨f, ?_, hind⟩
  rw [← deformationThickeningIso_hom_comp_subspaceInclusion B _ hZ x
      (ker_residueMap_sq_of_eq B _ hZ V x hx),
    ← deformationThickeningIso_hom_comp_subspaceInclusion B _ hZ x'
      (ker_residueMap_sq_of_eq B _ hZ V x' hx')]
  exact hf

end Iso

end AlgebraicGeometry.Space

end
