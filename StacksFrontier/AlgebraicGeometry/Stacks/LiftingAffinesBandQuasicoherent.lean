module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandChartReadingLinear

/-!
# The band of the gerbe of smooth lifts is a quasi-coherent module (Stacks 0CKG (2))

Let `p : 𝒞 ⟶ W_{spaces,étale}` be the gerbe of smooth lifts of Stacks 0CJP along a first order
thickening `𝒳 ⊂ 𝒳'` and `𝒢` its band (Stacks 0CJY). The band module
`AlgebraicGeometry.Stack.EtaleSmoothLift.bandModule` is a sheaf of `𝒪_W`-modules on `W_étale`
whose underlying abelian sheaf is the restriction of `𝒢`. Over the base `U` of an object `ξ` of
`𝒞` it is identified, chart by chart, with the internal Hom
`𝓗om(Δ^*Ω_{I/U'}, 𝒞_{U/U'})` (the reading of
`StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandChartReadingLinear`); the source is of
finite presentation (`I ⟶ U'` is smooth, Stacks 0CK5) and the target quasi-coherent (Stacks 04CN),
so the internal Hom is quasi-coherent (Stacks 03M1). As `𝒞` is locally nonempty, the band module
is quasi-coherent: Stacks 0CKG (2).

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isQuasicoherentOnSite_etaleModulePullback_bandModule`:
  the band module, pulled back to the base of any object `ξ`, is quasi-coherent.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_band_isQuasicoherent`: **Stacks 0CKG (2)**.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CJY](https://stacks.math.columbia.edu/tag/0CJY)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local instance] isFibered_proj

section Inputs

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

/-- The isomorphism `zs : U ⟶ i(U)` is étale. -/
theorem isEtale_zSection (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    Space.IsEtale B S hS (zSection hι₁ ξ).hom :=
  @Space.isEtale_of_isIso B S hS _ _ _ ⟨⟨(zProjection hι₁ ξ).hom,
    congrArg (fun t => t.hom) (zSection_comp_zProjection hι₁ ξ),
    congrArg (fun t => t.hom) (zProjection_comp_zSection hι₁ ξ)⟩⟩

/-- **`Ω_{I/U'}` is of finite presentation** on `I` when `p' : I' ⟶ U'` is smooth (Stacks 0CK5
after the cartesian identification `Ω_{I/U'} = Ω_{I/U}`). -/
theorem isFinitePresentationOnSite_liftsDifferentials (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (hp : Space.IsSmooth B S hS ξ.selfIntersection.fst.hom) :
    (liftsDifferentials hι₁ ξ).IsFinitePresentationOnSite := by
  have hsq := Subfunctor.isPullback_preimage ξ.selfIntersection.fst.hom (baseSubspace hι₁ ξ).1
  have hsm : Space.IsSmooth B S hS
      (Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).hom :=
    Space.isSmooth_of_isPullback hsq
      (Space.isClosedSubspace_preimage B S hS _ _ ξ.ambient.2 ξ.selfIntersection.pt.2
        (baseSubspace hι₁ ξ).2).1 ξ.selfIntersection.pt.2 (baseSubspace hι₁ ξ).2.1 ξ.ambient.2 hp
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite (liftsDifferentials hι₁ ξ) :=
    SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (Space.cartesianDifferentialsIso B S hS (baseSubspace hι₁ ξ) ξ.selfIntersection.fst
        (isFirstOrderThickening_preimage_fst hι₁ ξ).1).symm
      (Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth B S hS _ hsm)
  exact SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hfree

/-- **The scalars on a chart.** A function `r` on an étale chart `T` of the base of `ξ`, read
on the frame `ξ_T` and pulled back to `T` along `zs`, is `r` as a global function on `T`. -/
theorem frameScalar_chartScalar (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (T : Space.SmallEtale B S hS ξ.base.obj.left.1)
    (r : (Space.structureRingSheaf B S hS ξ.base.obj.left).obj.obj (op T)) :
    Space.globalFunctionsMap B S hS
        (U := (⟨(liftsZ hι₁ (frameFiber ξ T).1).1.toFunctor, (liftsZ hι₁ (frameFiber ξ T).1).2.1⟩ :
          AlgebraicSpaces B S hS)) (V := Space.chartSpace B S hS ξ.base.obj.left T)
        (zSection hι₁ (frameAt ξ T))
        (liftsScalar hι₁ (frameFiber ξ T).1 (frameScalar (frameFiber ξ T)
          (chartScalar B S hS W
            ((Space.smallEtalePostcomp B S hS ξ.base.obj.hom ξ.base.property).obj T) r))) =
      Space.chartRingMap B S hS T r :=
  (RingHom.congr_fun (Space.globalFunctionsMap_comp B S hS (zSection hι₁ (frameAt ξ T))
      (zProjection hι₁ (frameAt ξ T))) _).symm.trans
    ((congrArg (fun g => Space.globalFunctionsMap B S hS g _)
      (zSection_comp_zProjection hι₁ (frameAt ξ T))).trans
      ((RingHom.congr_fun (Space.globalFunctionsMap_id B S hS _) _).trans
        ((frameScalar_mk (frameAt ξ T) _).trans (chartScalar_postcomp ξ T r))))

end Inputs

section Band

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
    (Space.SpacesEtale.topology B S hS W))
  (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
    (Space.SpacesEtale.topology B S hS W))
  (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
        uliftFunctor.{u + 1, u + 1})
  (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)
  (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ξ ⟶ ζ) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ).hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ξ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
  (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).hom)

/-- **The band module, pulled back to the base `U` of an object `ξ`, is quasi-coherent**
(Stacks 0CKG (2), the local statement): read on the étale charts `T` of `U` through the frames
`ξ_T` and the datum of Stacks 0CK6, it is the internal Hom `𝓗om(Δ^*Ω_{I/U'}, 𝒞_{U/U'})`
(Stacks 03M1 (6)). -/
theorem isQuasicoherentOnSite_etaleModulePullback_bandModule
    (ξ : EtaleSmoothLift B S hS ι hι W x hx) :
    ((Space.etaleModulePullback B S hS ξ.base.obj.hom ξ.base.property).obj
      (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃)).IsQuasicoherentOnSite := by
  have : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
    isFiberedInGroupoids_proj.fiber_isGroupoid
  have hp : Space.IsSmooth B S hS ξ.selfIntersection.fst.hom :=
    isSmooth_fst_of_isTwoFibreProduct ξ.selfIntersection.isTwoFibreProduct.some
      ξ.isSmooth_ambientMap
  have hfp := Space.isFinitePresentationOnSite_modulePullback B S hS (diagonalRestriction hι₁ ξ) _
    (isFinitePresentationOnSite_liftsDifferentials hι₁ ξ hp)
  refine Space.isQuasicoherentOnSite_of_chartReading_comp B S hS (frameInclusion hι₁ ξ)
      ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
        (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (Space.conormalModule B S hS ξ.ambient (baseSubspace hι₁ ξ))
    inferInstance hfp (Space.isQuasicoherentOnSite_conormalModule B S hS _ _) _
    (fun T => (exists_readEquiv hι₁ ξ 𝒢 θ h₁ (frameFiber ξ T) (frameHom ξ T)
        (Y' := Space.chartSpace B S hS ξ.base.obj.left T) (zSection hι₁ (frameAt ξ T))
        (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ)
        (frameChart_comp hι₁ ξ T)
        (zProjection hι₁ (frameAt ξ T)) (zSection_comp_zProjection hι₁ (frameAt ξ T))
        (zProjection_comp_zSection hι₁ (frameAt ξ T))).choose)
    (fun {T' T} f s => ?_) (fun T r s => ?_)
  · have := isHomLift_frameTransition ξ f
    exact readEquiv_naturality hι₁ ξ 𝒢 θ h₁ (frameFiber ξ T) (frameHom ξ T)
      (Y' := Space.chartSpace B S hS ξ.base.obj.left T) (zSection hι₁ (frameAt ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ) (frameChart_comp hι₁ ξ T)
      (zProjection hι₁ (frameAt ξ T)) (zSection_comp_zProjection hι₁ (frameAt ξ T))
      (zProjection_comp_zSection hι₁ (frameAt ξ T)) (frameFiber ξ T') (frameHom ξ T')
      (frameTransition ξ f) (frameTransition_comp ξ f)
      (Y'' := Space.chartSpace B S hS ξ.base.obj.left T') (zSection hι₁ (frameAt ξ T'))
      (Space.chartToSpace B S hS ξ.base.obj.left T' ≫ frameInclusion hι₁ ξ)
      (frameChart_comp hι₁ ξ T')
      (zProjection hι₁ (frameAt ξ T')) (zSection_comp_zProjection hι₁ (frameAt ξ T'))
      (zProjection_comp_zSection hι₁ (frameAt ξ T')) (Space.chartMap B S hS ξ.base.obj.left f)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ frameInclusion hι₁ ξ)
        (Space.chartMap_comp_chartToSpace B S hS _ f)))
      (zSection_comp_liftsZRestriction hι₁ ξ f)
      (((Space.etaleModulePullback B S hS ξ.base.obj.hom ξ.base.property).obj
        (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃)).val.map f.op s) s
      (Functor.fiberInclusion_bandFrame_comp_of_isHomLift θ h₂ h₃ (frameChartMap ξ f)
        (frameFiber ξ T) (frameFiber ξ T') (frameTransition ξ f) (Additive.toMul s))
  · refine (readEquiv_bandSmul hι₁ ξ hne hlc 𝒢 θ h₁ h₂ h₃ (frameFiber ξ T) (frameHom ξ T)
      (Y' := Space.chartSpace B S hS ξ.base.obj.left T) (zSection hι₁ (frameAt ξ T))
      (Space.chartToSpace B S hS ξ.base.obj.left T ≫ frameInclusion hι₁ ξ) (frameChart_comp hι₁ ξ T)
      (zProjection hι₁ (frameAt ξ T)) (zSection_comp_zProjection hι₁ (frameAt ξ T))
      (zProjection_comp_zSection hι₁ (frameAt ξ T)) (isEtale_zSection hι₁ (frameAt ξ T))
      (chartScalar B S hS W
        ((Space.smallEtalePostcomp B S hS ξ.base.obj.hom ξ.base.property).obj T) r)
      (Additive.toMul (α := 𝒢.obj.obj (op (frameChartBase ξ T))) s)).trans ?_
    exact congrArg (fun v => _ ≫ Space.globalFunctionsSmul B S hS v _)
      (frameScalar_chartScalar hι₁ ξ T r)

end Band

section Registration

/-- **The band module is quasi-coherent over every étale chart carrying an object of the gerbe**
(the hypothesis `hloc` of
`AlgebraicGeometry.Stack.EtaleSmoothLift.isQuasicoherentOnSite_bandModule_of_frames`). -/
theorem isQuasicoherentOnSite_bandModule_over
    (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
    (Space.SpacesEtale.topology B S hS W))
  (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
    (Space.SpacesEtale.topology B S hS W))
  (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
        uliftFunctor.{u + 1, u + 1})
  (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)
  (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ξ ⟶ ζ) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ).hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ξ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
  (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).hom)
    (V : Space.SmallEtale B S hS W.1)
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
      ((Space.comparisonFunctor B S hS W).obj V)) :
    ((bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃).over V).IsQuasicoherentOnSite := by
  obtain ⟨ξ, hξ⟩ := ζ
  refine Space.isQuasicoherentOnSite_over_of_etaleModulePullback_chartToSpace B S hS W
    (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃) V ?_
  have key : ∀ U₁ : Space.SpacesEtale B S hS W, U₁ = (Space.comparisonFunctor B S hS W).obj V →
      ((Space.etaleModulePullback B S hS U₁.obj.hom U₁.property).obj
        (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃)).IsQuasicoherentOnSite →
      ((Space.etaleModulePullback B S hS (Space.chartToSpace B S hS W V)
        (Space.isEtale_chartToSpace B S hS W V)).obj
        (bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃)).IsQuasicoherentOnSite := by
    rintro _ rfl h
    exact h
  exact key ξ.base hξ
    (isQuasicoherentOnSite_etaleModulePullback_bandModule hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ ξ)

/-- **Stacks 0CKG (2).** In Situation 0CJP, let `𝒳 ⊂ 𝒳'` be a first order thickening. Then the
sheaf of groups `𝒢` of Stacks 0CJY — the band of the gerbe `p : 𝒞 ⟶ W_{spaces,étale}` of smooth
lifts, with its banding `θ` and the three clauses of 0CJY — is a quasi-coherent `𝒪_W`-module: its
restriction to `W_étale` (Stacks 03G1) underlies a quasi-coherent `𝒪_W`-module `M`.

The gerbe inputs are proved (Stacks 0CJU, 0CJX) and so is the commutativity of the automorphism
groups (part (1)); nothing is assumed beyond Situation 0CJP and the first order thickening. -/
@[stacks 0CKG "part (2): the sheaf of groups `𝒢` of Stacks 0CJY is a quasi-coherent `𝒪_W`-module"]
theorem exists_band_isQuasicoherent (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι) :
               haveI : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibered :=
        isFiberedInGroupoids_proj.isFibered
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ∃ (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
        (θ : ∀ (U : Space.SpacesEtale B S hS W)
          (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
          (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf y y ⋙
              uliftFunctor.{u + 1, u + 1}),
        (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a b : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) (a * b)).down =
              ((θ U y).hom.app (op g) a).down ≫ ((θ U y).hom.app (op g) b).down) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
              (y z : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : y ⟶ z)
              (g : Over U) (a : 𝒢.obj.obj (op g.left)),
            ((θ U z).hom.app (op g) a).down =
              Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
                ((θ U y).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom) ∧
          (∀ (U : Space.SpacesEtale B S hS W)
            (y : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
            (a : 𝒢.obj.obj (op g.left)),
            ((θ U y).hom.app (op g) a).down =
              (Functor.pullbackFiberIdIso
                  ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y g.hom)).inv ≫
                ((θ g.left ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                    g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
                  (Functor.pullbackFiberIdIso
                    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).pullbackFiber y
                      g.hom)).hom) ∧
          ∃ M : SheafOfModules.{u + 1} (Space.structureRingSheaf B S hS W),
            M.IsQuasicoherentOnSite ∧
              Nonempty ((Space.spacesEtaleAbelianRestriction B S hS W).obj
                ((sheafCompose _ commGroupAddCommGroupEquivalence.{u + 1}.functor).obj 𝒢) ≅
                (SheafOfModules.toSheaf _).obj M)
 := by
  have : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
    isFiberedInGroupoids_proj.fiber_isGroupoid
  obtain ⟨𝒢, θ, h₁, h₂, h₃⟩ := Gerbe.exists_sheaf_iso_morPresheaf_self_uliftFunctor_base
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) (Space.SpacesEtale.topology B S hS W)
    isFiberedInGroupoids_proj isStack_proj locallyNonempty_proj locallyConnected_proj
    (fiber_endomorphisms_comm hι₁)
  exact ⟨𝒢, θ, h₁, h₂, h₃, bandModule hι₁ locallyNonempty_proj locallyConnected_proj 𝒢 θ h₁ h₂ h₃,
    isQuasicoherentOnSite_bandModule_of_frames hι₁ locallyNonempty_proj locallyConnected_proj 𝒢 θ
      h₁ h₂ h₃ (fun V ζ => isQuasicoherentOnSite_bandModule_over hι₁ locallyNonempty_proj
        locallyConnected_proj 𝒢 θ h₁ h₂ h₃ V ζ),
    ⟨bandModuleIso hι₁ locallyNonempty_proj locallyConnected_proj 𝒢 θ h₁ h₂ h₃⟩⟩

end Registration

end AlgebraicGeometry.Stack.EtaleSmoothLift
