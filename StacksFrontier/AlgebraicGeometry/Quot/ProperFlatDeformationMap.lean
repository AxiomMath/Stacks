module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationClass
public import StacksFrontier.Deformation.AlgebraExtension.InducedKernelMap

/-!
# The map of extensions induced by a morphism of deformations

Let `φ : x ⟶ x'` be a morphism of deformations of `x₀ = (X₀ ⟶ Spec k)` in
`Spaces'_{fp, flat, proper}`, lying over `A ⟶ A'` in `𝒞_Λ`, with reversed arrow
`h : X'_{x'} ⟶ X'_x` of total spaces. The extension of `x` read on `X₀`
(`AlgebraicGeometry.Space.deformationTensorBaseExtension`) has middle term the restriction of
`i⁻¹𝒪_{X'}` to `X₀`, which is `u⁻¹𝒪_{X'}` for the map `u : X₀ ⟶ X'` of the deformation
(Stacks 03G8, 03LQ). The inverse image of `h^♯` along `u'` is a homomorphism
`u⁻¹𝒪_{X'_x} = (u' ≫ h)⁻¹𝒪_{X'_x} ⟶ u'⁻¹𝒪_{X'_{x'}}` of middle terms, over `𝒪_{X₀}` and, when the
retractions onto `Spec k` are compatible, under `f₀⁻¹𝒪_{Spec k}`: a morphism of extensions along
the map of ideals it induces. This is the functoriality of the deformation class in the proof of
[Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.deformationMorphismSpaceMap`: the map `h` of total spaces.
* `AlgebraicGeometry.Space.deformationMiddleMap`: the homomorphism of middle terms.
* `AlgebraicGeometry.Space.deformationBaseMapAlong`,
  `AlgebraicGeometry.Space.deformationTangentMapAlong`: the morphisms of extensions.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.AlgebraExtension Deformation.Artin

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  {x x' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀}
  (φ : DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    y₀ hy₀ x x')

/-- The map of total spaces `X'_{x'} ⟶ X'_x` of a morphism of deformations `x ⟶ x'`. -/
abbrev deformationMorphismSpaceMap : deformationSpace B S hS x' ⟶ deformationSpace B S hS x :=
  φ.arrow.1.hom.left

/-- The map of total spaces of a morphism of deformations commutes with the maps from `X₀`. -/
theorem deformationArrow_comp_deformationMorphismSpaceMap :
    (deformationArrow B S hS x').left ≫ deformationMorphismSpaceMap B S hS φ =
      (deformationArrow B S hS x).left :=
  congrArg (fun t => t.1.hom.left) φ.triangle

/-- The map of total spaces of a morphism of deformations lies over the map of bases. -/
theorem deformationMorphismSpaceMap_comp_structureMap :
    deformationMorphismSpaceMap B S hS φ ≫ deformationStructureMap B S hS x =
      deformationStructureMap B S hS x' ≫
        (schemeSpaceFunctor B S hS).map ((cartesianProperFlatProjection B S hS).map φ.arrow) := by
  apply ObjectProperty.hom_ext
  exact φ.arrow.1.hom.w

/-- **Retractions along a morphism of deformations.** The retraction attached to a section
`σ : k ⟶ A` pulls back along a morphism of deformations over `ρ : A ⟶ A'` to the retraction
attached to `ρ ∘ σ`. -/
theorem map_arrow_comp_baseRetraction (σ : k →+* x.algebra)
    (hσ : σ.comp (algebraMap Λ k) = algebraMap Λ x.algebra) (σ' : k →+* x'.algebra)
    (hσ' : σ'.comp (algebraMap Λ k) = algebraMap Λ x'.algebra)
    (hρ : φ.ringHom.hom.toRingHom.comp σ = σ') :
    (cartesianProperFlatProjection B S hS).map φ.arrow ≫
        baseRetraction (cartesianProperFlatProjection B S hS) x σ hσ =
      baseRetraction (cartesianProperFlatProjection B S hS) x' σ' hσ' := by
  have key : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).map φ.arrow ≫
      eqToHom x.base = eqToHom x'.base ≫
        Over.homMk (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ x.algebra)) ≫ iΛ))
          (Spec.map (CommRingCat.ofHom φ.ringHom.hom.toRingHom)) (by
            change Spec.map _ ≫ Spec.map _ ≫ iΛ = Spec.map _ ≫ iΛ
            rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
            exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ iΛ)
              φ.ringHom.hom.comp_algebraMap) := by
    ext1
    have hb := φ.arrow_base
    simp only [Over.comp_left, Over.homMk_left]
    rw [← hb, Over.eqToHom_left, Over.eqToHom_left]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp]
  unfold baseRetraction
  rw [Functor.map_preimage, Functor.map_preimage]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) key).trans ?_
  ext1
  simp only [Over.comp_left, Over.homMk_left, Category.assoc]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hρ]

/-- Retracted structure maps along a morphism of deformations, for compatible retractions. -/
theorem deformationMorphismSpaceMap_comp_retractedStructureMap
    (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
      (cartesianProperFlatProjection B S hS).obj y₀)
    (r' : (cartesianProperFlatProjection B S hS).obj x'.point ⟶
      (cartesianProperFlatProjection B S hS).obj y₀)
    (hrr : (cartesianProperFlatProjection B S hS).map φ.arrow ≫ r = r') :
    deformationMorphismSpaceMap B S hS φ ≫ deformationRetractedStructureMap B S hS r =
      deformationRetractedStructureMap B S hS r' := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [deformationMorphismSpaceMap_comp_structureMap, Category.assoc, ← Functor.map_comp, hrr]

variable (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)
  (hsq' : RingHom.ker (residueMap x'.algebra) ^ 2 = ⊥)

/-- The map of total spaces of a morphism of deformations commutes with the identifications of
`X₀` with the closed subspaces of the total spaces cut out by the ideals of the bases. -/
theorem deformationThickeningIso_comp_deformationMorphismSpaceMap :
    ((deformationThickeningIso B S hS x' hsq').hom ≫
        subspaceInclusion B S hS _ (deformationThickening B S hS x' hsq')) ≫
        deformationMorphismSpaceMap B S hS φ =
      (deformationThickeningIso B S hS x hsq).hom ≫
        subspaceInclusion B S hS _ (deformationThickening B S hS x hsq) := by
  rw [deformationThickeningIso_hom_comp_subspaceInclusion,
    deformationThickeningIso_hom_comp_subspaceInclusion,
    deformationArrow_comp_deformationMorphismSpaceMap]

/-- **The homomorphism of middle terms of the extensions of a morphism of deformations**: the
inverse image along `u' : X₀ ⟶ X'_{x'}` of `h^♯`, read on the restrictions of the inverse images
of the structure sheaves to `X₀`. -/
def deformationMiddleMap :=
  etaleRestrictionInverseImageMap B S hS _ (isEtale_hom_of_iso B S hS _) _ _
    (isEtale_hom_of_iso B S hS _) _ (deformationMorphismSpaceMap B S hS φ)
    (deformationThickeningIso_comp_deformationMorphismSpaceMap B S hS φ hsq hsq')

variable {hsq} (r : (cartesianProperFlatProjection B S hS).obj x.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr : (cartesianProperFlatProjection B S hS).map x.arrow ≫ r = 𝟙 _)

variable (r' : (cartesianProperFlatProjection B S hS).obj x'.point ⟶
    (cartesianProperFlatProjection B S hS).obj y₀)
  (hr' : (cartesianProperFlatProjection B S hS).map x'.arrow ≫ r' = 𝟙 _)

/-- The homomorphism of middle terms of a morphism of deformations is over `𝒪_{X₀}`. -/
theorem deformationMiddleMap_comp_reduction :
    deformationMiddleMap B S hS φ hsq hsq' ≫
        (deformationTensorBaseExtension B S hS hsq' r' hr').reduction =
      (deformationTensorBaseExtension B S hS hsq r hr).reduction :=
  etaleRestrictionInverseImageMap_comp_reduction B S hS _ _ _ _ _ _ _ _

variable (hg : deformationMorphismSpaceMap B S hS φ ≫ deformationRetractedStructureMap B S hS r =
  deformationRetractedStructureMap B S hS r')

include hg in
/-- The homomorphism of middle terms of a morphism of deformations is under
`f₀⁻¹𝒪_{Spec k}` when the retractions onto `Spec k` are compatible. -/
theorem algebraMap_comp_deformationMiddleMap :
    (deformationTensorBaseExtension B S hS hsq r hr).algebraMap ≫
        deformationMiddleMap B S hS φ hsq hsq' =
      (deformationTensorBaseExtension B S hS hsq' r' hr').algebraMap := by
  have L := etaleRestrictionInverseImageMap_algebraMap B S hS _ (isEtale_hom_of_iso B S hS _) _ _
    (isEtale_hom_of_iso B S hS _) _ _
    (deformationThickeningIso_comp_deformationMorphismSpaceMap B S hS φ hsq hsq') _ _ hg
      ((deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq r hr).trans
        (deformationThickeningIso_hom_comp_retractedStructureMap B S hS hsq' r' hr').symm)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans L)).trans ?_
  refine (eqToHom_trans_assoc _ _ _).trans ?_
  rfl

/-- **The morphism of extensions of a morphism of deformations**, along the map of ideals induced
by `AlgebraicGeometry.Space.deformationMiddleMap`. -/
def deformationBaseMapAlong :
    MapAlong.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
        (deformationTensorBaseExtension B S hS hsq r hr)
        (deformationTensorBaseExtension B S hS hsq' r' hr') (deformationMiddleMap B S hS φ hsq hsq')
        (deformationMiddleMap_comp_reduction B S hS φ hsq' r hr r' hr'))
      (deformationTensorBaseExtension B S hS hsq r hr)
      (deformationTensorBaseExtension B S hS hsq' r' hr') :=
  mapAlongInducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
    _ _ _ _ (algebraMap_comp_deformationMiddleMap B S hS φ hsq' r hr r' hr' hg)

/-! ### Over `k[V]` -/

section Tangent

variable (V V' : FGModuleCat.{u} k)
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V')
  (hgt : deformationMorphismSpaceMap B S hS φ ≫
      deformationRetractedStructureMap B S hS (tangentRetraction B S hS V x hx) =
    deformationRetractedStructureMap B S hS (tangentRetraction B S hS V' x' hx'))

/-- The middle term of the extension of a deformation over `k[V]` is that of its extension read
on `X₀` for the retraction of the constants. -/
theorem deformationTangentExtension_extension :
    (deformationTangentExtension B S hS V x hx).extension =
      (deformationTensorBaseExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
        (tangentRetraction B S hS V x hx)
        (map_arrow_comp_tangentRetraction B S hS V x hx)).extension :=
  rfl

/-- The reduction of the extension of a deformation over `k[V]` is that of its extension read on
`X₀` for the retraction of the constants. -/
theorem deformationTangentExtension_reduction :
    (deformationTangentExtension B S hS V x hx).reduction =
      (deformationTensorBaseExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
        (tangentRetraction B S hS V x hx)
        (map_arrow_comp_tangentRetraction B S hS V x hx)).reduction :=
  rfl

/-- The algebra map of the extension of a deformation over `k[V]` is that of its extension read
on `X₀` for the retraction of the constants. -/
theorem deformationTangentExtension_algebraMap :
    (deformationTangentExtension B S hS V x hx).algebraMap =
      (deformationTensorBaseExtension B S hS (ker_residueMap_sq_of_eq B S hS V x hx)
        (tangentRetraction B S hS V x hx)
        (map_arrow_comp_tangentRetraction B S hS V x hx)).algebraMap :=
  rfl

/-- The homomorphism of middle terms of a morphism of deformations over `k[V] ⟶ k[V']`, as a map
of the middle terms of the extensions with ideals `𝒪_{X₀} ⊗_k V` and `𝒪_{X₀} ⊗_k V'`. -/
def deformationTangentMiddleMap :
    (deformationTangentExtension B S hS V x hx).extension ⟶
      (deformationTangentExtension B S hS V' x' hx').extension :=
  deformationMiddleMap B S hS φ (ker_residueMap_sq_of_eq B S hS V x hx)
    (ker_residueMap_sq_of_eq B S hS V' x' hx')

/-- The homomorphism of middle terms of a morphism of deformations over `k[V] ⟶ k[V']` is over
`𝒪_{X₀}`. -/
theorem deformationTangentMiddleMap_comp_reduction :
    deformationTangentMiddleMap B S hS φ V V' hx hx' ≫
        (deformationTangentExtension B S hS V' x' hx').reduction =
      (deformationTangentExtension B S hS V x hx).reduction := by
  rw [deformationTangentExtension_reduction, deformationTangentExtension_reduction]
  exact deformationMiddleMap_comp_reduction B S hS φ _ _ _ _ _

include hgt in
/-- The homomorphism of middle terms of a morphism of deformations over `k[V] ⟶ k[V']` is under
`f₀⁻¹𝒪_{Spec k}` when the retractions of the constants are compatible. -/
theorem algebraMap_comp_deformationTangentMiddleMap :
    (deformationTangentExtension B S hS V x hx).algebraMap ≫
        deformationTangentMiddleMap B S hS φ V V' hx hx' =
      (deformationTangentExtension B S hS V' x' hx').algebraMap := by
  rw [deformationTangentExtension_algebraMap, deformationTangentExtension_algebraMap]
  exact algebraMap_comp_deformationMiddleMap B S hS φ _ _ _ _ _ hgt

/-- The map of ideals `𝒪_{X₀} ⊗_k V ⟶ 𝒪_{X₀} ⊗_k V'` induced by a morphism of deformations. -/
def deformationTangentKernelMap :=
  inducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
    (deformationTangentExtension B S hS V x hx) (deformationTangentExtension B S hS V' x' hx')
    (deformationTangentMiddleMap B S hS φ V V' hx hx')
    (deformationTangentMiddleMap_comp_reduction B S hS φ V V' hx hx')

/-- **The morphism of extensions over `k[V] ⟶ k[V']` of a morphism of deformations**, between
the extensions with ideals `𝒪_{X₀} ⊗_k V` and `𝒪_{X₀} ⊗_k V'`, along the induced map of
ideals. -/
def deformationTangentMapAlong :
    MapAlong.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
      (deformationTangentKernelMap B S hS φ V V' hx hx')
      (deformationTangentExtension B S hS V x hx) (deformationTangentExtension B S hS V' x' hx') :=
  mapAlongInducedKernelMap.{u, u + 1, u} (J := SmallEtale.topology B S hS y₀.obj.obj.left.1)
    _ _ _ _ (algebraMap_comp_deformationTangentMiddleMap B S hS φ V V' hx hx' hgt)

/-- A `k`-module is a `kᵐᵒᵖ`-module through `MulOpposite.unop`. -/
local instance (W : FGModuleCat.{u} k) : Module kᵐᵒᵖ W :=
  Module.oppositeOfCommSemiring k W

/-- The `k`- and `kᵐᵒᵖ`-actions on a `k`-module agree. -/
local instance (W : FGModuleCat.{u} k) : IsCentralScalar k W :=
  Module.isCentralScalar_oppositeOfCommSemiring k W

/-- A homomorphism `k[V] ⟶ k[V']` given by `k[f]` carries the section `k ⟶ k[V]` of the constants
to the section `k ⟶ k[V']`. -/
theorem eqToHom_squareZeroSection_comp_map {A A' : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (h' : A' = (artinianSquareZeroExtensionFunctor Λ k).obj V') (f : V ⟶ V') (ρ : A ⟶ A')
    (hρ : ρ = eqToHom h ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫ eqToHom h'.symm) :
    ρ.hom.toRingHom.comp ((eqToHom h.symm).hom.toRingHom.comp (squareZeroSection Λ k V)) =
      (eqToHom h'.symm).hom.toRingHom.comp (squareZeroSection Λ k V') := by
  subst h h' hρ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext a
  change ((artinianSquareZeroExtensionFunctor Λ k).map f).hom (TrivSqZeroExt.inl a) =
    TrivSqZeroExt.inl a
  exact TrivSqZeroExt.map_inl (f := f.hom.hom) a

/-- **Compatible retractions over `k[f]`.** For a morphism of deformations lying over
`k[f] : k[V] ⟶ k[V']`, the retractions of the constants are compatible, so the morphism of
extensions `AlgebraicGeometry.Space.deformationTangentMapAlong` exists. -/
theorem deformationMorphismSpaceMap_comp_tangentRetraction (f : V ⟶ V')
    (hρ : φ.ringHom = eqToHom hx ≫ (artinianSquareZeroExtensionFunctor Λ k).map f ≫
      eqToHom hx'.symm) :
    deformationMorphismSpaceMap B S hS φ ≫
        deformationRetractedStructureMap B S hS (tangentRetraction B S hS V x hx) =
      deformationRetractedStructureMap B S hS (tangentRetraction B S hS V' x' hx') :=
  deformationMorphismSpaceMap_comp_retractedStructureMap B S hS φ _ _
    (map_arrow_comp_baseRetraction B S hS φ _ _ _ _
      (eqToHom_squareZeroSection_comp_map V V' hx hx' f φ.ringHom hρ))

end Tangent

end AlgebraicGeometry.Space

end
