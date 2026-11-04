module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffineIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.HasFiniteTorDimension

/-!
# Base change for the right adjoint of `Rf_*` along a morphism of finite Tor dimension

Let `g : Y' ⟶ Y` be a morphism of affine schemes of finite Tor dimension with `Y` Noetherian, and
let `f : X ⟶ Y` be proper, with `X` and `Y'` Tor independent over `Y`. Then the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an isomorphism for every `K ∈ D^+_QCoh(𝒪_Y)`
(case (3) of Stacks 0E5I).

## Main results

* `hasFiniteTorDimensionRingHom_of_hasFiniteTorDimension_representedSpaceMap`: a morphism of
  affine schemes of finite Tor dimension has a ring map of finite Tor dimension.
* `isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_hasFiniteTorDimension`: the base
  change map `L(g')^* a(K) ⟶ a'(Lg^*K)` is an isomorphism when `g` has finite Tor dimension.

## References

* [Stacks Project, Tag 0E5I](https://stacks.math.columbia.edu/tag/0E5I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of affine schemes of finite Tor dimension has a ring map of finite Tor
dimension**: for `g : U' ⟶ U` with `U`, `U'` affine, read the étale-local condition of
`AlgebraicGeometry.Space.HasFiniteTorDimension` on the square of identity charts. -/
theorem hasFiniteTorDimensionRingHom_of_hasFiniteTorDimension_representedSpaceMap
    {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)
    (hg : AlgebraicGeometry.Space.HasFiniteTorDimension (representedSpaceMap B S hS g₀)) :
    HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g₀).hom :=
  hg.hasFiniteTorDimensionRingHom U U' (𝟙 _) (𝟙 _) g₀
    (isEtale_of_isIso B S hS (𝟙 (yoneda.obj U)))
    (isEtale_of_isIso B S hS (𝟙 (yoneda.obj U')))
    (by rw [Category.comp_id, Category.id_comp])

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0E5I (3).** Let `g : U' ⟶ U` be a morphism of affine schemes of finite Tor dimension,
with `U` Noetherian, and consider a cartesian square
```
X' --g'--> X
|f'        |f
U' --g---> U
```
with `f` proper and `X`, `U'` Tor independent over `U`. Then the base change map
`L(g')^* a(K) ⟶ a'(Lg^*K)` of Stacks 0E5D is an isomorphism for every `K ∈ D^+_QCoh(𝒪_U)`. -/
@[stacks 0E5I "(3)"]
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_hasFiniteTorDimension
    {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)
    {X X' : AlgebraicSpaces B S hS} {f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩}
    {f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g₀)) (hf : IsProper B S hS f.hom)
    (hY : IsNoetherian B S hS hZ (yoneda.obj U))
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g₀).hom)
    (hg : AlgebraicGeometry.Space.HasFiniteTorDimension (representedSpaceMap B S hS g₀))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hf.2.1.2
        (isAffineSpace_yoneda B S hS U inferInstance))
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f
        (isQuasiSeparated_of_isSeparated B S hS hf.1) (isAffineSpace_yoneda B S hS U inferInstance))
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS U inferInstance))
      (isAffineSpace_yoneda B S hS U' inferInstance).isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS U' inferInstance)) hTor).app K) :=
  isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_hasFiniteTorDimensionRingHom hZ g₀
    sq hf hY hTor (hasFiniteTorDimensionRingHom_of_hasFiniteTorDimension_representedSpaceMap g₀ hg)
    K hK

end AlgebraicGeometry.Space

end
