module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.AffineTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompAssembly
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompTransport
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentDerivedPullbackOpenImmersion

/-!
# The base-change composition at a total tensor complex, from the affine charts

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, `P` a K-flat
complex of `𝒪_X`-modules with quasi-coherent cohomology and `G` a complex of quasi-coherent
`𝒪_X`-modules. If on every Cartesian affine-open chart `U ⊆ X` over `V ⊆ S` the complex
`Γ(U, G)` is K-flat over `𝒪_S(V)`, then the composition
`Lg^*Rf_*Tot(P ⊗ G) ⟶ Rf'_*(g')^*Tot(P ⊗ G)` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_chart_totalTensor`: on one Cartesian affine-open chart of the square,
  the composition at `Tot(P ⊗ G)` is an isomorphism.
* `AlgebraicGeometry.isIso_derivedBaseChangeComp_totalTensor_of_charts`: if `Γ(U, G)` is K-flat
  over `𝒪_S(V)` on every Cartesian affine-open chart, the composition
  `Lg^*Rf_*Tot(P ⊗ G) ⟶ Rf'_*(g')^*Tot(P ⊗ G)` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex
  pullbackTensorComplexNatIso)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- On one Cartesian affine-open chart of the square, on which the complex of sections of `G`
is K-flat over the ring of the chart of `S`, the base-change composition at the total tensor
complex `Tot(P ⊗ G)` is an isomorphism. -/
theorem isIso_chart_totalTensor (hsq : IsPullback g' f' f g) (ch : BaseChangeChart f g f' g')
    (P G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    (hPq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj P)).IsQuasicoherent)
    (hG : ∀ n, ((show CochainComplex X.Modules ℤ from G).X n).IsQuasicoherent)
    (hflat : ((CochainComplex.restrictScalars ch.a.hom).obj
      (sectionsComplex (show CochainComplex (Spec ch.A).Modules ℤ from
        (pullbackComplex ch.incU.toLRSHom.toShHom).obj G))).KFlat) :
    IsIso (derivedBaseChangeMap (Spec.map ch.c).toLRSHom.toShHom (Spec.map ch.d).toLRSHom.toShHom
        (Spec.map ch.a).toLRSHom.toShHom (Spec.map ch.b).toLRSHom.toShHom
        (comp_toShHom_of_comm (isPullback_SpecMap_of_isPushout _ _ _ _ ch.isPushout).w)
        ((derivedPullback ch.incU.toLRSHom.toShHom).obj (DerivedCategory.Q.obj
          (HomologicalComplex.mapBifunctor P G
            (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
            (ComplexShape.up ℤ)))) ≫
      (derivedPushforward (Spec.map ch.d).toLRSHom.toShHom).map
        (Stacks.Cohomology.BaseChangeCover.pullDatum (Spec.map ch.c).toLRSHom.toShHom
          ch.incU'.toLRSHom.toShHom ch.incU.toLRSHom.toShHom g'.toLRSHom.toShHom
          (comp_toShHom_of_comm ch.wU'U.symm)
          (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
            (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ)))
          (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj
            (HomologicalComplex.mapBifunctor P G
              (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
              (ComplexShape.up ℤ))))
          ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
            (HomologicalComplex.mapBifunctor P G
              (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
              (ComplexShape.up ℤ))))) := by
  have := ch.isOpenImmersion_incU
  have := BaseChangeChart.isOpenImmersion_incU' hsq ch
  set W := HomologicalComplex.mapBifunctor P G
    (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ)
  have hj : ∀ K, IsIso ((derivedPullbackNatTrans ch.incU.toLRSHom.toShHom).app K) := fun K ↦
    Stacks.Cohomology.BaseChangeCover.isIso_derivedPullbackNatTrans_app_of_isOpenImmersion _ K
  have hj' := Stacks.Cohomology.BaseChangeCover.isIso_derivedPullbackNatTrans_app_of_isOpenImmersion
    ch.incU'.toLRSHom.toShHom ((pullbackComplex g'.toLRSHom.toShHom).obj W)
  refine (Stacks.Cohomology.BaseChangeCover.isIso_bc_pullDatum_comparison_iff _ _ _ _ _ _ _ _ _ W
    (hj W) hj').2 ?_
  refine (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso _ _ _ _ _
    (Stacks.Cohomology.BaseChangeCover.pullbackMapBifunctorIso ch.incU.toLRSHom.toShHom P G)).2 ?_
  have hPU := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
    ch.incU.toLRSHom.toShHom P hP
  have hPUq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec ch.A).toRingedSpace)) n).obj
      (DerivedCategory.Q.obj ((pullbackComplex ch.incU.toLRSHom.toShHom).obj P))).IsQuasicoherent :=
    fun n ↦ (SheafOfModules.isQuasicoherent
        (structureSheafRing (Spec ch.A).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        (@asIso _ _ _ _ _ (hj P)))
      (isQuasicoherent_homology_derivedPullback_of_isOpenImmersion ch.incU
        (DerivedCategory.Q.obj P) hPq n)
  have hGU : ∀ n, ((show CochainComplex (Spec ch.A).Modules ℤ from
      (pullbackComplex ch.incU.toLRSHom.toShHom).obj G).X n).IsQuasicoherent := fun n ↦
    @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _ ch.incU (G.X n) (hG n)
  exact isIso_derivedBaseChangeComp_specMap_tensor ch.isPushout _ _ hPU hPUq hGU hflat

/-- Let `f` be quasi-compact and quasi-separated, `P` a K-flat complex of `𝒪_X`-modules with
quasi-coherent cohomology and `G` a complex of quasi-coherent `𝒪_X`-modules. If on every Cartesian
affine-open chart `U ⊆ X` over `V ⊆ S` the complex `Γ(U, G)` is K-flat over `𝒪_S(V)`, then the
base-change composition `Lg^*Rf_*Tot(P ⊗ G) ⟶ Rf'_*(g')^*Tot(P ⊗ G)` is an isomorphism. -/
theorem isIso_derivedBaseChangeComp_totalTensor_of_charts (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f]
    (P G : CochainComplex (RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat X.toRingedSpace P)
    (hPq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj P)).IsQuasicoherent)
    (hG : ∀ n, ((show CochainComplex X.Modules ℤ from G).X n).IsQuasicoherent)
    (hflat : ∀ (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U), IsAffineOpen V →
      ∀ hUV : U ≤ f ⁻¹ᵁ V,
      ((CochainComplex.restrictScalars (f.appLE V U hUV).hom).obj
        (sectionsComplex (show CochainComplex (Spec Γ(X, U)).Modules ℤ from
          (pullbackComplex hU.fromSpec.toLRSHom.toShHom).obj G))).KFlat) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w)
        (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
          (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) (ComplexShape.up ℤ))) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app
          (HomologicalComplex.mapBifunctor P G
            (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)
            (ComplexShape.up ℤ)))) :=
  Stacks.Cohomology.BaseChangeCover.isIso_comp_of_affineOpens hsq _ _ _
    fun V V' hV hV' hle U hU hUV ↦
      Stacks.Cohomology.BaseChangeCover.repGood_of_chart hsq V V' hV hV' hle U hU hUV _ _ _
        (isIso_chart_totalTensor hsq _ P G hP hPq hG (hflat U V hU hV hUV))

end AlgebraicGeometry
