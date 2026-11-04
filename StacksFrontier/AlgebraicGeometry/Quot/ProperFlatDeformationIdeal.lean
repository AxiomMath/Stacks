module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback

/-!
# The ideal of the extension of a deformation is `𝒪_{X₀} ⊗ I/I²`

Let `j : T ⟶ T'` be a closed immersion of objects of the big fppf site with `T'` affine,
`R' = Γ(T', 𝒪_{T'})`, `R = Γ(T, 𝒪_T)` and `I = Ker(R' → R)`. The conormal module of `T ⊆ T'` is
`𝒪_T ⊗_{R'} I` (`AlgebraicGeometry.Space.conormalModuleRangeIso`), and changing the base ring
along `R' → R` it is `𝒪_T ⊗_R (R ⊗_{R'} I)`, the module attached to `R ⊗_{R'} I = I/I²`. Pulled
back along any `q : X ⟶ T` it becomes `𝒪_X ⊗_R (R ⊗_{R'} I)`
(`AlgebraicGeometry.Space.conormalModuleRangePullbackIso`).

For a deformation `X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra with square-zero
residue kernel, the ideal of the extension `AlgebraicGeometry.Space.deformationBaseExtension` of
`𝒪_{X₀}` is the restriction to `X₀` of the pullback of the conormal module of `Spec k ⊆ Spec A`.
Étale restriction being pullback (Stacks 03LW), this ideal is the pullback of that conormal module
along `X₀ ⟶ Spec k`, hence `𝒪_{X₀} ⊗_k (k ⊗_A I)` with `I = 𝔪_A`
(`AlgebraicGeometry.Space.deformationBaseExtensionIdealIso`). For `A = k[V]` this is the module
`𝒪_{X₀} ⊗_k V` of [Stacks Project, Tag 0D1K].

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleRangePullbackIso`: `q^*𝒞_{T/T'} ≅ 𝒪_X ⊗_R (R ⊗_{R'} I)`.
* `AlgebraicGeometry.Space.deformationBaseExtensionIdealIso`: the ideal of the extension of a
  deformation is `𝒪_{X₀} ⊗_R (R ⊗_{R'} I)`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Range

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) {X : AlgebraicSpaces B S hS}
  (q : X ⟶ schemeSpace T)

/-- The `Γ(T, 𝒪_T)`-module `Γ(T, 𝒪_T) ⊗_{R'} I` attached to a closed immersion `j : T ⟶ T'`,
`I = Ker(R' → Γ(T, 𝒪_T))`: the module `I/I²`. -/
abbrev rangeConormalBaseModule : ModuleCat.{u} (baseRing B S hS T) :=
  (ModuleCat.extendScalars.{u, u, u}
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj
    (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)))

/-- The base-ring datum of `j : T ⟶ T'` on `T` is the identity datum of `T` precomposed with
pullback of functions along `j`. -/
theorem baseRingHomOfMap_schemeSpaceMap :
    baseRingHomOfMap (schemeSpaceMap j) =
      (baseRingHomOfMap (𝟙 (schemeSpace T))).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom := by
  rw [← baseRingHomOfMap_comp]
  exact congrArg baseRingHomOfMap (Category.id_comp _).symm

/-- **The conormal module of `T ⊆ T'`, pulled back along `q : X ⟶ T`, is
`𝒪_X ⊗_R (R ⊗_{R'} I)`**, `R = Γ(T, 𝒪_T)`, `R' = Γ(T', 𝒪_{T'})`, `I = Ker(R' → R)`, for `T'`
affine. -/
def conormalModuleRangePullbackIso :
    (modulePullback B S hS (q ≫ (rangeSpaceIso B S hS j hj).hom)).obj
        (conormalModule B S hS (schemeSpace T') (rangeSubspace B S hS j hj)) ≅
      (baseRingTensorModule B S hS X (baseRingHomOfMap q)).obj
        (rangeConormalBaseModule B S hS j hj) :=
  ((modulePullbackCompIso B S hS q (rangeSpaceIso B S hS j hj).hom).app _).symm ≪≫
    (modulePullback B S hS q).mapIso
      (conormalModuleRangeIso B S hS j hj hT' ≪≫
        eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS (schemeSpace T) φ).obj
          (ModuleCat.of (baseRing B S hS T')
            (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))))
          (baseRingHomOfMap_schemeSpaceMap B S hS j)) ≪≫
        ((baseRingTensorModuleCompIso B S hS (schemeSpace T)
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom
          (baseRingHomOfMap (𝟙 (schemeSpace T)))).app _).symm) ≪≫
    (baseRingTensorModulePullbackIso B S hS q).app _

end Range

section Deformation

open Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}
  {hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)
  (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- The base `Spec A` of a deformation is affine. -/
theorem isAffine_deformationBase :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((cartesianProperFlatProjection B S hS).obj
      x.point)) :=
  let e : (BigFppfOver.toScheme B S hS).obj ((cartesianProperFlatProjection B S hS).obj x.point) ≅
      Spec (.of x.algebra) := eqToIso (congrArg Over.left x.base)
  IsAffine.of_isIso e.hom

/-- The closed immersion `Spec k ⟶ Spec A` under the arrow of a deformation. -/
abbrev deformationBaseImmersion :
    (cartesianProperFlatProjection B S hS).obj y₀ ⟶
      (cartesianProperFlatProjection B S hS).obj x.point :=
  (cartesianProperFlatProjection B S hS).map x.arrow

include hsq in
/-- The base immersion of a deformation with square-zero residue kernel is a closed immersion. -/
theorem isClosedImmersion_deformationBaseImmersion :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (deformationBaseImmersion B S hS x)) :=
  (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq).1

/-- The projection `X' ×_{Spec A} Spec k ⟶ Spec k` of the closed fibre of a deformation, onto
the closed subspace `Spec k ⊆ Spec A`. -/
abbrev deformationFibreProjection :=
  preimageProjection B S hS (deformationStructureMap B S hS x)
    (squareZeroSubspace B S hS _
      (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq))

/-- The conormal module of the closed subspace `Spec k ⊆ Spec A` cut out by the arrow of a
deformation. -/
abbrev deformationBaseConormal :=
  conormalModule B S hS _ (squareZeroSubspace B S hS _
    (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq))

/-- **Through the closed fibre, `X₀ ⟶ Spec k` is the projection of the closed fibre.** The
identification of `X₀` with the closed fibre, followed by the projection of the closed fibre to
`Spec k ⊆ Spec A` read on `Spec k`, is the structure morphism of `x₀`. -/
theorem deformationThickeningIso_hom_comp_preimageProjection :
    (deformationThickeningIso B S hS x hsq).hom ≫
        preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x hsq)) ≫
        (rangeSpaceIso B S hS _ (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).inv =
      baseStructureMap B S hS (y₀ := y₀) :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- The identification of `X₀` with the closed fibre, followed by the projection to
`Spec k ⊆ Spec A`, is the structure morphism of `x₀` read on that subspace. -/
theorem deformationThickeningIso_hom_comp_fibreProjection :
    (deformationThickeningIso B S hS x hsq).hom ≫ deformationFibreProjection B S hS x hsq =
      baseStructureMap B S hS (y₀ := y₀) ≫
        (rangeSpaceIso B S hS _ (isClosedImmersion_deformationBaseImmersion B S hS x hsq)).hom :=
  (Iso.comp_inv_eq _).1 ((Category.assoc _ _ _).trans
    (deformationThickeningIso_hom_comp_preimageProjection B S hS x hsq))

/-- The conormal module of `Spec k ⊆ Spec A`, pulled back to a space over `Spec k`, read on the
closed subspace cut out by `Spec k ⟶ Spec A` as the range of its image. -/
def deformationBaseConormalCast {W : AlgebraicSpaces B S hS}
    (m : W ⟶ closedSubspaceRangeSpace B S hS _
      (isClosedImmersion_deformationBaseImmersion B S hS x hsq)) :
    (modulePullback B S hS (Y := ⟨_, (squareZeroSubspace B S hS _
        (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
          hsq)).2.1⟩) m).obj (deformationBaseConormal B S hS x hsq) ≅
      (modulePullback B S hS m).obj (conormalModule B S hS
        (schemeSpace ((cartesianProperFlatProjection B S hS).obj x.point))
        (rangeSubspace B S hS _ (isClosedImmersion_deformationBaseImmersion B S hS x hsq))) :=
  Iso.refl _

/-- **The ideal of the extension of a deformation is `𝒪_{X₀} ⊗_R (R ⊗_{R'} I)`.** For a
deformation `X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra with square-zero residue
kernel and a retraction `r` of `Spec k ⟶ Spec A`, the ideal of
`AlgebraicGeometry.Space.deformationBaseExtension` is `𝒪_{X₀} ⊗_R (R ⊗_{R'} I)`, where
`R' = Γ(Spec A)`, `R = Γ(Spec k)`, `I = Ker(R' → R)`, the base ring acting through the structure
morphism of `x₀`. -/
def deformationBaseExtensionIdealIso :
    (etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((modulePullback B S hS (preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
              hsq)))).obj
        (conormalModule B S hS _ (squareZeroSubspace B S hS _
          (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
            hsq)))) ≅
      (baseRingTensorModule B S hS y₀.obj.obj.left
        (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))).obj
        (rangeConormalBaseModule B S hS (deformationBaseImmersion B S hS x)
          (isClosedImmersion_deformationBaseImmersion B S hS x hsq)) :=
  ((modulePullbackIsoEtaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
      (isEtale_hom_of_iso B S hS _)).app
        ((modulePullback B S hS (deformationFibreProjection B S hS x hsq)).obj
          (deformationBaseConormal B S hS x hsq))).symm ≪≫
    (modulePullbackCompIso B S hS (deformationThickeningIso B S hS x hsq).hom
      (deformationFibreProjection B S hS x hsq)).app (deformationBaseConormal B S hS x hsq) ≪≫
    (eqToIso (congrArg (modulePullback B S hS)
      (deformationThickeningIso_hom_comp_fibreProjection B S hS x hsq))).app
        (deformationBaseConormal B S hS x hsq) ≪≫
    deformationBaseConormalCast B S hS x hsq _ ≪≫
    conormalModuleRangePullbackIso B S hS (deformationBaseImmersion B S hS x)
      (isClosedImmersion_deformationBaseImmersion B S hS x hsq) (isAffine_deformationBase B S hS x)
      (baseStructureMap B S hS (y₀ := y₀))

end Deformation

end AlgebraicGeometry.Space

end
