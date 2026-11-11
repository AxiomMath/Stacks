module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceTensorSectionsLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceBoundedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsHocolim
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorSupportClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowersPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryIsZero

/-!
# The derived existence theorem: `K` vanishes against perfect objects living off `X₀`

In the situation of `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)` be the object of the existence theorem. For every perfect `E ∈ D(𝒪_X)` whose
derived pullbacks `Ljₙ^* E` to the `Xₙ` all vanish, `RΓ(X, E ⊗^L K) = 0`. This is because
`RΓ(X, E ⊗^L K)` is the derived limit of the `RΓ(Xₙ, Ljₙ^* E ⊗^L Kₙ)` (Stacks 0DIM), which
vanish. Consequently, if `E` is perfect and supported on a closed `Q ⊆ |X|` disjoint from the
images of the `|Xₙ|`, then `E ⊗^L K = 0`.

This is the part of the support clause of Stacks 0DIR that holds for every separated `X`. Every
`K` with `Ljₙ^* K ≅ Kₙ` differs from `K = DQ_X(R lim Kₙ)` only away from `X₀`, and this file shows
that `K = DQ_X(R lim Kₙ)` has nothing there that a perfect object supported off `X₀` can see.
The object `K ⊕ 𝒪/(px − 1)` on `𝔸¹_{ℤ_p}` (errata entry 0DIR(support of K)) satisfies
`Ljₙ^*(K ⊕ 𝒪/(px − 1)) ≅ Kₙ`, but not this vanishing, at `E` the Koszul complex on `px − 1`.

## Main results

* `AlgebraicGeometry.Space.isZero_smallEtaleDerivedModulePullback_of_disjoint`: the derived
  pullback of an object supported on `Q` along a morphism whose image misses `Q` is zero.
* `AlgebraicGeometry.Space.isZero_of_forall_isAffineChart_isZero_derivedSections`: an object of
  `D_QCoh(𝒪_X)` with zero derived sections over every affine étale chart is zero.
* `…SeparatedDerivedExistenceSystem.isZero_limitTensorSections_quasicoherentLimit_of_isZero`:
  `RΓ(X, E ⊗^L K) = 0` for perfect `E` with `Ljₙ^* E = 0` for all `n`.
* `…SeparatedDerivedExistenceSystem.isZero_smallEtaleDerivedTensor_quasicoherentLimit_of_…`:
  `E ⊗^L K = 0` for perfect `E` supported on a closed subset disjoint from every `|Xₙ|`.

## References

* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

section PullbackVanishing

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

/-- **The derived pullback of an object supported on `Q` along a morphism missing `Q` vanishes.**
`Lg^*E` is supported on `|g|⁻¹(Q) = ∅`
(`AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedModulePullback`), and a sheaf
with empty support is zero. -/
theorem isZero_smallEtaleDerivedModulePullback_of_disjoint {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X' X : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (Q : Set (points B S hS X.1)) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2 Q E)
    (hdisj : Disjoint (Set.range (pointsMap B S hS X'.1 g.hom)) Q) :
    IsZero ((smallEtaleDerivedModulePullback B S hS g).obj E) := by
  have h := cohomologySupportedOn_smallEtaleDerivedModulePullback g E hE
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro i
  exact (supportOfSheaf_eq_empty_iff_isZero B S hS X' _).1
    (Set.eq_empty_of_forall_notMem fun x hx =>
      Set.disjoint_left.1 hdisj (Set.mem_range_self x) (h i hx))

end PullbackVanishing

section ChartSections

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] hasRightDerivedFunctor_chartSections

/-- **An object of `D_QCoh(𝒪_X)` whose derived sections over every affine étale chart vanish is
zero**: on an affine chart `U`, `Hᵠ(RΓ(U, M)) = Γ(U, Hᵠ(M))`
(`AlgebraicGeometry.Space.chartDerivedSectionsHomologyIso`), and a module whose sections over
the affine charts vanish is zero, the affine charts covering. -/
theorem isZero_of_forall_isAffineChart_isZero_derivedSections {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)
    (M : spaceDerivedCategory B S hS X) (hM : spaceQuasicoherentProp B S hS X M)
    (h : ∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U →
      IsZero ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U).obj
          M)) :
    IsZero M := by
  refine (@DerivedCategory.isZero_iff_forall_isZero_homology _ _
    (modulesAbelianSmallEtale B S hS X.1 X.2) (spaceHasDerivedCategory B S hS X) M).2 fun q => ?_
  let N := (spaceDerivedHomology B S hS X q).obj M
  let K := (HomologicalComplex.single (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ) 0).obj N
  have hK : K.ExactAt 0 := by
    refine exactAt_of_forall_isAffineChart B S hS X.1 X.2 K 0 fun A hA => ?_
    let F := Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS X.1 X.2) A
    have hz0 : IsZero (N.val.obj (Opposite.op A)) :=
      (Functor.map_isZero (DerivedCategory.homologyFunctor _ q) (h A hA)).of_iso
        (chartDerivedSectionsHomologyIso B S hS X M hM A hA q)
    have hz : IsZero (F.obj N) := Functor.map_isZero (forget₂ _ AddCommGrpCat) hz0
    refine HomologicalComplex.ExactAt.of_iso ?_
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app N).symm
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hz.of_iso (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj N))
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hK
  exact hK.of_iso (HomologicalComplex.singleObjHomologySelfIso _ 0 N).symm

/-- **An object of `D_QCoh(𝒪_X)` with vanishing derived sections over the affine étale charts, read
over an affine base, is zero.** For `h : X ⟶ h_T` with `T` affine, if for every affine chart `U`
of `X` with chart morphism `u` the object `RΓ_T(h_U, R(u ≫ h)_* Lu^*M)` vanishes, then `M = 0`:
it is `RΓ(U, M)` with scalars restricted
(`AlgebraicGeometry.Space.chartDerivedSectionsPushforwardIso`). -/
theorem isZero_of_forall_isAffineChart_isZero_representedChartSections {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (M : spaceDerivedCategory B S hS X) (hM : spaceQuasicoherentProp B S hS X M)
    (hz : ∀ U : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 U →
      IsZero ((representedAffineDerivedSections B S hS T).obj
        ((derivedModulePushforward B S hS (representedChartToSpace X U ≫ h)).obj
          ((smallEtaleDerivedModulePullback B S hS (representedChartToSpace X U)).obj M)))) :
    IsZero M := by
  refine isZero_of_forall_isAffineChart_isZero_derivedSections X M hM fun U hU => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :=
    hU
  let g : (SmallEtale.toOver B S hS X.1).obj U ⟶ T :=
    yoneda.preimage (representedChartToSpace X U ≫ h).hom
  have w : representedChartToSpace X U ≫ h = representedSpaceMap B S hS g := by
    ext1
    exact (Functor.map_preimage yoneda _).symm
  refine StacksDraft.DerivedCategoryHomology.isZero_of_isZero_mapDerivedCategory_obj
    (ModuleCat.restrictScalars (representedAffineCommRingCatHom B S hS g).hom) ?_
  exact (hz U hU).of_iso ((chartDerivedSectionsPushforwardIso X U h g w).app M)

end ChartSections

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian
attribute [local instance] pointTopology

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **`RΓ(X, E ⊗^L K) = 0` when every `Ljₙ^* E` vanishes.** For `K = DQ_X(R lim Kₙ)` and `E`
perfect with `Ljₙ^* E = 0` for all `n`, `RΓ(X, E ⊗^L K)` is the derived limit of the
`RΓ(Xₙ, Ljₙ^* E ⊗^L Kₙ) = 0` (Stacks 0DIM), hence zero. -/
theorem isZero_limitTensorSections_quasicoherentLimit_of_isZero
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (h : ∀ n : ℕ, IsZero ((D.stageDerivedPullback n).obj E)) :
    IsZero ((D.limitTensorSections E).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        D.quasicoherentLimit)) := by
  obtain ⟨hp, hK⟩ := D.isDerivedLimit_quasicoherentLimit
  let hT : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj
      E).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).commShift_right E
  have hTtri : ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      D.X.left).obj E).IsTriangulated :=
    (smallEtaleDerivedTensorProduct D.B (limitBase D.system) D.containsLimitBase
      D.X.left).exact_right E
  let hι : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).ι.CommShift ℤ := inferInstance
  let hRf : (derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
      D.X.hom).CommShift ℤ := inferInstance
  let hRΓ : (representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).CommShift ℤ := inferInstance
  let h₁ : D.limitSectionsFunctor.CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase D.system)
        D.containsLimitBase D.X.hom) (representedAffineDerivedSections D.B (limitBase D.system)
        D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) ℤ _ _ _ _ hRf hRΓ
  have : D.limitSectionsFunctor.IsTriangulated := ⟨fun Tr hTr ↦ isomorphic_distinguished _
    ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).map_distinguished _
          ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          D.X.hom).map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ (derivedModulePushforward D.B (limitBase
          D.system) D.containsLimitBase D.X.hom) hRf (representedAffineDerivedSections D.B
          (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)) hRΓ).app Tr)⟩
  let h₂ : (D.limitTensorSections E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase D.system)
        D.containsLimitBase D.X.left).obj E) D.limitSectionsFunctor ℤ _ _ _ _ hT h₁
  have : (D.limitTensorSections E).IsTriangulated := ⟨fun Tr hTr ↦ isomorphic_distinguished _
    (D.limitSectionsFunctor.map_distinguished _ (hTtri.map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ ((smallEtaleDerivedTensor D.B (limitBase
          D.system) D.containsLimitBase D.X.left).obj E) hT D.limitSectionsFunctor h₁).app Tr)⟩
  let : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (spaceQuasicoherentProp D.B (limitBase D.system)
        D.containsLimitBase D.X.left).ι (D.limitTensorSections E) ℤ _ _ _ _ hι h₂
  have : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).IsTriangulated := ⟨fun Tr hTr ↦
    isomorphic_distinguished _
      ((D.limitTensorSections E).map_distinguished _ ((spaceQuasicoherentProp D.B (limitBase
          D.system) D.containsLimitBase D.X.left).ι.map_distinguished Tr hTr)) _
      ((@Functor.mapTriangleCompIso _ _ _ _ _ _ _ _ _ (spaceQuasicoherentProp D.B (limitBase
          D.system) D.containsLimitBase D.X.left).ι hι (D.limitTensorSections E) h₂).app Tr)⟩
  have : ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E).IsRightAdjoint := (Adjunction.liftLeftAdjoint
    (P := spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (D.limitTensorSectionsAdjunction E hE)
    (D.qcohDerived_limitTensorSections_leftAdjoint_obj E hE)).isRightAdjoint
  obtain ⟨hprod, p, δ, hTr⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
      D.limitTensorSections E)
    D.quasicoherentTower D.quasicoherentLimit hK
  have hq := qcohDerived_of_isPerfect _ _ _ _ _ hE
  -- each term of the tower is `res Mₙ = 0`
  have hzero : ∀ n : ℕ, IsZero ((D.quasicoherentTower ⋙
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
        D.limitTensorSections E)).obj ⟨n⟩) := by
    intro n
    have hM : IsZero (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
        (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).obj
              E)).obj (D.K n)) :=
      Functor.map_isZero ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
        (spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n)).flip.obj (D.K n))
        (h n)
    have hadj := affineBaseDerivedSectionsAdjunction D.B (limitBase D.system) D.containsLimitBase
      (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    have : (affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
        (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
          n)).IsRightAdjoint :=
      hadj.isRightAdjoint
    have : (affineBaseToposSections D.B (limitBase D.system) D.containsLimitBase
        (spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
          n)).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isRightAdjoint _
    exact (Functor.map_isZero _ (Functor.map_isZero _ hM)).of_iso
      (@asIso _ _ _ _ (D.towerTensorSectionsHom E n) (D.isIso_towerTensorSectionsHom E hq n))
  have hP : IsZero (∏ᶜ fun n : ℕ => (D.quasicoherentTower ⋙
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⋙
        D.limitTensorSections E)).obj ⟨n⟩) := by
    rw [IsZero.iff_id_eq_zero]
    exact Pi.hom_ext _ _ fun n => (hzero n).eq_of_tgt _ _
  exact Triangle.isZero₁_of_isZero₂₃ _ hTr hP hP

/-- **`RΓ(X, P ⊗^L E ⊗^L K) = 0` for `E` perfect and supported off the `Xₙ`.** Let `Q ⊆ |X|` be
closed, disjoint from the image of every `|Xₙ|`, and `E` perfect supported on `Q`. For every
perfect `P`, `P ⊗^L E` is perfect and supported on `Q`, so all its pullbacks to the `Xₙ` vanish
and `isZero_limitTensorSections_quasicoherentLimit_of_isZero` applies to it. -/
theorem isZero_limitTensorSections_smallEtaleDerivedTensor_quasicoherentLimit
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (Q : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hQ : IsClosed Q)
    (hEQ : CohomologySupportedOn D.B (limitBase D.system) D.containsLimitBase D.X.left.1
      D.X.left.2 Q E)
    (hdisj : ∀ n : ℕ, Disjoint (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase
      _ (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom)) Q)
    (P : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hP : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left P) :
    IsZero ((D.limitTensorSections P).obj
      (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase D.X.left).obj E).obj
        ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          D.quasicoherentLimit))) := by
  let P' := ((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
    D.X.left).obj P).obj E
  have hP' : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left P' :=
    isPerfect_derivedTensorProductFunctor_obj_obj P E hP hE
  have hP'Q : CohomologySupportedOn D.B (limitBase D.system) D.containsLimitBase D.X.left.1
      D.X.left.2 Q P' :=
    cohomologySupportedOn_smallEtaleDerivedTensor_of_right Q hQ P E hEQ
  have h0 := D.isZero_limitTensorSections_quasicoherentLimit_of_isZero P' hP' fun n =>
    isZero_smallEtaleDerivedModulePullback_of_disjoint _ Q P' hP'Q (hdisj n)
  exact h0.of_iso (D.limitSectionsFunctor.mapIso (smallEtaleDerivedTensorAssociator D.X.left P E
    ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
      D.quasicoherentLimit))).symm

/-- **`E ⊗^L K` has no derived sections over any étale `U ⟶ X`, for `E` perfect and supported off
the `Xₙ`.** For `Q ⊆ |X|` closed, disjoint from the image of every `|Xₙ|`, `E` perfect supported
on `Q`, and `j : U ⟶ X` étale with `U` quasi-compact and quasi-separated,
`RΓ(U, (E ⊗^L K)|_U) = 0`: by
`isZero_limitTensorSections_smallEtaleDerivedTensor_quasicoherentLimit`, every
`RΓ(X, P ⊗^L E ⊗^L K)` with `P` perfect vanishes. -/
theorem isZero_etaleSections_smallEtaleDerivedTensor_quasicoherentLimit
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (Q : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hQ : IsClosed Q)
    (hEQ : CohomologySupportedOn D.B (limitBase D.system) D.containsLimitBase D.X.left.1
      D.X.left.2 Q E)
    (hdisj : ∀ n : ℕ, Disjoint (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase
      _ (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom)) Q)
    {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (j : U ⟶ D.X.left)
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase
      D.B.contains_terminal U.1) :
    IsZero ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (j ≫ D.X.hom)).obj
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase j).obj
            (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
              D.X.left).obj E).obj
              ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
                D.X.left).ι.obj D.quasicoherentLimit))))) :=
  isZero_etaleSections_of_forall_isPerfect (D := D) hj hUqc hUqs _
    (qcohDerived_smallEtaleDerivedTensor _ _ _ (qcohDerived_of_isPerfect _ _ _ _ _ hE)
      D.quasicoherentLimit.property)
    fun P hP => D.isZero_limitTensorSections_smallEtaleDerivedTensor_quasicoherentLimit E hE Q hQ
      hEQ hdisj P hP

/-- **`E ⊗^L K = 0` for `E` perfect and supported off the `Xₙ`.** Let `Q ⊆ |X|` be closed,
disjoint from the image of every `|Xₙ|`, and `E` perfect supported on `Q`. Then
`E ⊗^L K = 0` for `K = DQ_X(R lim Kₙ)`: its derived sections over every affine étale chart
vanish (`isZero_etaleSections_smallEtaleDerivedTensor_quasicoherentLimit`). -/
theorem isZero_smallEtaleDerivedTensor_quasicoherentLimit_of_cohomologySupportedOn
    (E : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B (limitBase D.system) D.containsLimitBase D.X.left E)
    (Q : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hQ : IsClosed Q)
    (hEQ : CohomologySupportedOn D.B (limitBase D.system) D.containsLimitBase D.X.left.1
      D.X.left.2 Q E)
    (hdisj : ∀ n : ℕ, Disjoint (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase
      _ (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom)) Q) :
    IsZero (((smallEtaleDerivedTensor D.B (limitBase D.system) D.containsLimitBase
      D.X.left).obj E).obj
        ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
          D.quasicoherentLimit)) := by
  refine isZero_of_forall_isAffineChart_isZero_representedChartSections D.X.left D.X.hom _
    (qcohDerived_smallEtaleDerivedTensor _ _ _ (qcohDerived_of_isPerfect _ _ _ _ _ hE)
      D.quasicoherentLimit.property) fun U hU => ?_
  have hT : IsAffine ((BigFppfOver.toScheme D.B (limitBase D.system) D.containsLimitBase).obj
      ((SmallEtale.toOver D.B (limitBase D.system) D.containsLimitBase D.X.left.1).obj U)) := hU
  exact D.isZero_etaleSections_smallEtaleDerivedTensor_quasicoherentLimit E hE Q hQ hEQ hdisj
    (representedChartToSpace D.X.left U) (isEtale_representedChartToSpace D.X.left U)
    (isQuasiCompactSpace_yoneda_of_isAffine _ _ _ _ hT)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace _ _ _ _ (isAffineSpace_yoneda _ _ _ _ hT))

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
