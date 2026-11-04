module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleChangeOfRings
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor
public import StacksFrontier.Deformation.RingThickening.SquareZeroKernelModule

/-!
# The conormal module of `X ×_{T'} T ⊆ X` for flat `X ⟶ T'`

Let `T'` be an affine object of the big fppf site, `R' = Γ(T', 𝒪_{T'})`, `Z ⊆ T'` a closed
subspace with ideal `I ⊆ R'`, and `g : W ⟶ T'` a flat morphism of algebraic spaces. This file
identifies the conormal module of [Stacks Project, Tag 04CN] of the closed subspace
`g⁻¹(Z) = W ×_{T'} Z` of `W`, read on `g⁻¹(Z)`, with the base-ring tensor product
`𝒪_{g⁻¹(Z)} ⊗_{R'} I` of [Stacks Project, Tag 0D3F].

When `Z` is cut out by a closed immersion `j : T ⟶ T'` and `I² = 0`, the `R'`-module `I` is a
module over `R₁ = Γ(T, 𝒪_T) = R'/I`, and the conormal module is `𝒪_{g⁻¹(Z)} ⊗_{R₁} I`, the base
ring `R₁` acting through the projection `g⁻¹(Z) ⟶ T`. In the body of
[Stacks Project, Tag 0D3X], for the flat family `Xₙ ⟶ Spec(Rₙ)` and
`X₁ = Xₙ ×_{Spec(Rₙ)} Spec(R₁)`, this is the kernel `𝒪_{X₁} ⊗_{R₁} Iₙ` of
`𝒪_{Xₙ} ⟶ 𝒪_{X₁}`, `Iₙ = Ker(Rₙ → R₁)`.

## Main definitions

* `AlgebraicGeometry.Space.baseRingTensorModulePullbackCompIso`: for `i : Z ⟶ W` and
  `g : W ⟶ T`, `i^*(𝒪_W ⊗_R M) ≅ 𝒪_Z ⊗_R M`, the base ring acting on `Z` through `i ≫ g`.
* `AlgebraicGeometry.Space.conormalModulePreimageIso`: the conormal module of `g⁻¹(Z) ⊆ W` is
  `𝒪_{g⁻¹(Z)} ⊗_{R'} I` for flat `g` and affine `T'`.
* `AlgebraicGeometry.Space.conormalModulePreimageRangeIso`: for `Z` the range of a closed
  immersion `j : T ⟶ T'` and an `R₁`-module `N` whose restriction to `R'` is `I`, the conormal
  module is `𝒪_{g⁻¹(Z)} ⊗_{R₁} N`.
* `AlgebraicGeometry.Space.conormalModulePreimageSquareZeroIso`: when `I² = 0`, the conormal
  module is `𝒪_{g⁻¹(T)} ⊗_{R₁} I`, `I` read as an `R₁`-module (`RingHom.squareZeroKer`).

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pullback

variable {Z W : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **`𝒪_W ⊗_R -` commutes with pullback along any `i : Z ⟶ W`** over `g : W ⟶ T`,
`R = Γ(T, 𝒪_T)`: `i^*(𝒪_W ⊗_R M) ≅ 𝒪_Z ⊗_R M`, naturally in the `R`-module `M`, the base ring
acting on `Z` through `i ≫ g`. Both sides are `(i ≫ g)^*(𝒪_T ⊗_R M)`, by
`AlgebraicGeometry.Space.baseRingTensorModulePullbackIso` for `g` and for `i ≫ g`. -/
def baseRingTensorModulePullbackCompIso (i : Z ⟶ W) (g : W ⟶ schemeSpace T) :
    baseRingTensorModule B S hS W (baseRingHomOfMap g) ⋙ modulePullback B S hS i ≅
      baseRingTensorModule B S hS Z (baseRingHomOfMap (i ≫ g)) :=
  Functor.isoWhiskerRight (baseRingTensorModulePullbackIso B S hS g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (modulePullbackCompIso B S hS i g) ≪≫
    baseRingTensorModulePullbackIso B S hS (i ≫ g)

end Pullback

section Conormal

variable {W : AlgebraicSpaces B S hS} {T' : BigFppfOver B S hS} (g : W ⟶ schemeSpace T')
  (Z : ClosedSubspaces B S hS (schemeSpace T').1)

/-- **The conormal module of `g⁻¹(Z) ⊆ W` is `𝒪_{g⁻¹(Z)} ⊗_{R'} I`** for a flat morphism
`g : W ⟶ T'` to an affine object `T'` of the site, `R' = Γ(T', 𝒪_{T'})` and `I ⊆ R'` the ideal
of the closed subspace `Z` (`AlgebraicGeometry.Space.closedSubspaceBaseIdeal`); the base ring
acts on `g⁻¹(Z)` through its inclusion into `W` followed by `g`. -/
def conormalModulePreimageIso (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    conormalModule B S hS W (preimageSubspace B S hS g Z) ≅
      (baseRingTensorModule B S hS _
          (baseRingHomOfMap (subspaceInclusion B S hS W (preimageSubspace B S hS g Z) ≫ g))).obj
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) :=
  (modulePullback B S hS (subspaceInclusion B S hS W (preimageSubspace B S hS g Z))).mapIso
      (definingIdealSheafPreimageIso B S hS g Z hg hT').symm ≪≫
    (baseRingTensorModulePullbackCompIso B S hS
      (subspaceInclusion B S hS W (preimageSubspace B S hS g Z)) g).app _

variable {T : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **The projection `g⁻¹(T) ⟶ T`** of the inverse image of the closed subscheme cut out by a
closed immersion `j : T ⟶ T'`: the projection onto the range of `j`, read on `T`. -/
def preimageRangeProjection :
    (⟨(preimageSubspace B S hS g (rangeSubspace B S hS j hj)).1.toFunctor,
        (preimageSubspace B S hS g (rangeSubspace B S hS j hj)).2.1⟩ : AlgebraicSpaces B S hS) ⟶
      schemeSpace T :=
  preimageProjection B S hS g (rangeSubspace B S hS j hj) ≫ (rangeSpaceIso B S hS j hj).inv

/-- The projection `g⁻¹(T) ⟶ T` followed by `j` is the inclusion `g⁻¹(T) ⊆ W` followed by
`g`. -/
theorem preimageRangeProjection_comp :
    preimageRangeProjection B S hS g j hj ≫ schemeSpaceMap j =
      subspaceInclusion B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)) ≫ g := by
  have h : (rangeSpaceIso B S hS j hj).inv ≫ schemeSpaceMap j =
      subspaceInclusion B S hS (schemeSpace T') (rangeSubspace B S hS j hj) :=
    (Iso.inv_comp_eq _).2 (rangeSpaceIso_hom_comp_subspaceInclusion B S hS j hj).symm
  refine (Category.assoc _ _ _).trans ((congrArg (preimageProjection B S hS g
    (rangeSubspace B S hS j hj) ≫ ·) h).trans ?_)
  exact ObjectProperty.hom_ext _
    (Subfunctor.isPullback_preimage g.hom (rangeSubspace B S hS j hj).1).w.symm

/-- **The conormal module of `g⁻¹(T) ⊆ W` is `𝒪_{g⁻¹(T)} ⊗_{R₁} N`.** Let `g : W ⟶ T'` be flat
with `T'` affine, `j : T ⟶ T'` a closed immersion, `R' = Γ(T', 𝒪_{T'})`, `R₁ = Γ(T, 𝒪_T)`,
`ψ : R' ⟶ R₁` pullback of functions along `j` (surjective, `T'` being affine) and
`I = Ker(ψ)` (`AlgebraicGeometry.Space.closedSubspaceBaseIdeal_rangeSubspace`). For an
`R₁`-module `N` whose restriction to `R'` is `I` (for instance `I` itself when `I² = 0`), the
conormal module of `g⁻¹(T) ⊆ W` is `𝒪_{g⁻¹(T)} ⊗_{R₁} N`, the base ring `R₁` acting through the
projection `g⁻¹(T) ⟶ T`. -/
def conormalModulePreimageRangeIso (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} (baseRing B S hS T))
    (e : (ModuleCat.restrictScalars.{u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) :
    conormalModule B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)) ≅
      (baseRingTensorModule B S hS _ (baseRingHomOfMap (preimageRangeProjection B S hS g j hj))).obj
        N := by
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'
  have hψ : Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map j)).2
  have hdat : baseRingHomOfMap (subspaceInclusion B S hS W
        (preimageSubspace B S hS g (rangeSubspace B S hS j hj)) ≫ g) =
      (baseRingHomOfMap (preimageRangeProjection B S hS g j hj)).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom := by
    rw [← preimageRangeProjection_comp]
    exact baseRingHomOfMap_comp B S hS _ j
  exact conormalModulePreimageIso B S hS g _ hg hT' ≪≫
    (baseRingTensorModule B S hS _ _).mapIso e.symm ≪≫
    eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS _ φ).obj
      ((ModuleCat.restrictScalars.{u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj N)) hdat) ≪≫
    (baseRingTensorModuleRestrictScalarsIso B S hS _ _ _ hψ).app N

/-- **The conormal module of `g⁻¹(T) ⊆ W` is `𝒪_{g⁻¹(T)} ⊗_{R₁} I` when `I² = 0`.** Let
`g : W ⟶ T'` be flat with `T'` affine and `j : T ⟶ T'` a closed immersion whose ideal
`I = Ker(Γ(T', 𝒪) → Γ(T, 𝒪))` has square zero. Then `I` is a module over `R₁ = Γ(T, 𝒪_T)`
(`RingHom.squareZeroKer`) and the conormal module of `g⁻¹(T) ⊆ W` is `𝒪_{g⁻¹(T)} ⊗_{R₁} I`, the
base ring acting through the projection `g⁻¹(T) ⟶ T`. In the body of
[Stacks Project, Tag 0D3X] this is the kernel `𝒪_{X₁} ⊗_{R₁} Iₙ` of `𝒪_{Xₙ} ⟶ 𝒪_{X₁}`. -/
def conormalModulePreimageSquareZeroIso (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hsq : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom ^ 2 = ⊥) :
    conormalModule B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)) ≅
      (baseRingTensorModule B S hS _ (baseRingHomOfMap (preimageRangeProjection B S hS g j hj))).obj
        (RingHom.squareZeroKer _
          (haveI := hT'
          (IsClosedImmersion.isAffine_surjective_of_isAffine
            ((BigFppfOver.toScheme B S hS).map j)).2) hsq) :=
  conormalModulePreimageRangeIso B S hS g j hj hg hT' _
    (RingHom.restrictScalarsSquareZeroKerIso _ _ hsq ≪≫
      eqToIso (congrArg (fun I : Ideal (baseRing B S hS T') => ModuleCat.of _ I)
        (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj).symm))

end Conormal

end AlgebraicGeometry.Space

end
