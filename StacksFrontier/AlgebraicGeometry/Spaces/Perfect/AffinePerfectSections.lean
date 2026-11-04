module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartSlicePerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.Homology.Perfect.FiniteFlatCoverDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceAndTorAmplitudeGeneral
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# The sections of a perfect object on an affine algebraic space are perfect

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring of
global functions `R`, and let `E` be a perfect object of `D(𝒪_{yoneda.obj U})` (Stacks 08G5).
Then `RΓ(E)` is a perfect object of `D(R)`.

The object `E` lies in `D_QCoh` (Stacks 08JL), so `E = Φ(K)` with `K = RΓ(E)` and `Φ` the derived
associated-module functor.  There is a finite family of affine étale charts `U_i = Spec R_i`
covering `U` on which `E` has strictly perfect models.  The pullback of `Φ(K)` to `U_i` is
`Φ_{R_i}` of the termwise base change `K ⊗_R R_i`, the ring map being flat, and a strictly
perfect object on an affine has perfect derived sections, so every `K ⊗_R R_i` is perfect.  As
`R → ∏ R_i` is faithfully flat, `K` is perfect (Stacks 068T).

## Main results

* `AlgebraicGeometry.Space.representedAffineAssociatedModulePullbackIso`: along a morphism
  `g : U' ⟶ U` of affine representables, `g^*(M^~) ≅ (Γ(U') ⊗_{Γ(U)} M)^~` naturally in `M`.
* `AlgebraicGeometry.Space.exists_isStrictlyPerfect_iso_of_hasStrictlyPerfectQuasiIso`: a
  strictly perfect local model on the slice at an étale chart is a strictly perfect model of the
  pullback to the chart.
* `AlgebraicGeometry.Space.qcohDerived_of_isPerfect`: a perfect object lies in `D_QCoh`.
* `AlgebraicGeometry.Space.isPerfect_representedAffineDerivedSections_obj`: the statement above.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 068T](https://stacks.math.columbia.edu/tag/068T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.AffineTilde in
/-- **The associated module commutes with pullback along a morphism of affine representables.**
For `g : U' ⟶ U` with affine underlying schemes, `g^*(M^~) ≅ (Γ(U') ⊗_{Γ(U)} M)^~`, naturally in
the `Γ(U)`-module `M`. -/
def representedAffineAssociatedModulePullbackIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U' U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U' ⟶ U) :
    representedAffineAssociated B S hS U ⋙ modulePullback B S hS (representedSpaceMap B S hS g) ≅
      ModuleCat.extendScalars.{u, u, u} (Scheme.Hom.appTop (B.inclusion.map g.left)).hom ⋙
        representedAffineAssociated B S hS U' :=
  Functor.associator (tildeOf ((BigFppfOver.toScheme B S hS).obj U))
      (representedAssociatedModuleFunctor B S hS U) _ ≪≫
    Functor.isoWhiskerLeft (tildeOf ((BigFppfOver.toScheme B S hS).obj U))
      (representedAssociatedModulePullbackNatIso B S hS g
        (relativelyRepresentable_yoneda_map B S hS g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@tildeOfPullbackIso _ _ ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U')›
        ‹IsAffine ((BigFppfOver.toScheme B S hS).obj U)› (B.inclusion.map g.left))
      (representedAssociatedModuleFunctor B S hS U') ≪≫
    Functor.associator _ _ _

/-! ### Strictly perfect models on étale charts -/

section Model

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The étale pullback of the structure sheaf is the structure sheaf: étale pullback is
restriction of sections along the identity map of structure sheaves. -/
def etaleModulePullbackUnitIso {X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O) :=
  Iso.refl _

/-- The comparison equivalence of Stacks 04M0 carries the unit of the slice of `X_étale` at a
chart `W` to the structure sheaf of the algebraic space represented by `W`. -/
def chartLocalizationModuleEquivalenceUnitIso (W : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (chartLocalizationModuleEquivalence B S hS X W).functor.obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).over W)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).O) :=
  ((etaleModulePullbackChartToSpaceNatIso B S hS X W).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))).symm ≪≫
    etaleModulePullbackUnitIso B S hS X (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W)

/-- **A strictly perfect local model over a chart is a strictly perfect model of the pullback to
the chart.**  If the restriction of the complex `K` to the slice at `W` receives a
quasi-isomorphism from a strictly perfect complex, then the pullback of `K` to the algebraic
space represented by `W` is isomorphic in the derived category to a strictly perfect complex: the
comparison equivalence of Stacks 04M0 carries the one to the other. -/
theorem exists_isStrictlyPerfect_iso_of_hasStrictlyPerfectQuasiIso
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (h : (smallEtaleRingedSite B S hS X.1 X.2).HasStrictlyPerfectQuasiIso K W) :
    ∃ P : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS X W).1
        (chartSpace B S hS X W).2) ℤ,
      IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).O) P ∧
      Nonempty ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
          DerivedCategory.Q.obj P) := by
  obtain ⟨P, hP, q, hq⟩ := h
  let G := (chartLocalizationModuleEquivalence B S hS X W).functor
  let L := etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
    (isEtale_chartToSpace B S hS X W)
  refine ⟨_, SheafOfModules.isStrictlyPerfect_map G
    (chartLocalizationModuleEquivalenceUnitIso B S hS X W) hP, ⟨?_⟩⟩
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := inferInstance
  let e₁ : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K W) :=
    (NatIso.mapHomologicalComplex (etaleModulePullbackChartToSpaceNatIso B S hS X W)
        (ComplexShape.up ℤ)).app K ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) W ⋙ G)) (ComplexShape.up ℤ)).app K).symm
  exact (L.mapDerivedCategoryFactors.app K) ≪≫ DerivedCategory.Q.mapIso e₁ ≪≫
    (asIso (DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q))).symm

end Model

/-! ### The sections of a perfect object on an affine represented space -/

section Sections

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **A perfect object of `D(𝒪_{yoneda.obj U})` lies in `D_QCoh`**, being pseudo-coherent
(Stacks 08JL). -/
theorem qcohDerived_of_isPerfect (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) : QcohDerived B S hS X E :=
  derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E
    (RingedSite.isPseudoCoherent_of_isPerfect_general _ hE)

/-- **The derived sections of a perfect object on an affine represented algebraic space are
perfect.**  If `E` is a perfect object of `D(𝒪_{yoneda.obj U})` and `U` has affine underlying
scheme with ring of global functions `R`, then `RΓ(E)` is a perfect object of `D(R)`.

`E` lies in `D_QCoh`, so `E = Φ(K)` with `K = RΓ(E)`.  On a finite family of affine étale charts
`U_i = Spec R_i` covering `U` the pullbacks of `E` have strictly perfect models; the pullback of
`Φ(K)` to `U_i` is `Φ_{R_i}` of the termwise base change `K ⊗_R R_i`, so `K ⊗_R R_i` is perfect,
and `R → ∏ R_i` is faithfully flat, so `K` is perfect (Stacks 068T). -/
theorem isPerfect_representedAffineDerivedSections_obj
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).IsPerfect E) :
    StacksDraft.Perfect.IsPerfect ((representedAffineDerivedSections B S hS U).obj E) := by
  classical
  let Z : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E
    (qcohDerived_of_isPerfect B S hS Z E hE)
  set K := (representedAffineDerivedSections B S hS U).obj E
  let ε : (representedAffineDerivedAssociated B S hS U).obj K ≅ E :=
    asIso ((representedAffineDerivedAdjunction B S hS U).counit.app E)
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨E₀, hE₀, ⟨e₀⟩⟩ := hE
  let T := representedAffineFinalChart B S hS U
  obtain ⟨Sv, hSv, hmod⟩ := hE₀ T
  let Sm : Sieve T :=
    { arrows := fun V _ => (smallEtaleRingedSite B S hS Z.1 Z.2).HasStrictlyPerfectQuasiIso E₀ V
      downward_closed := fun h g =>
        RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ E₀ g h }
  have hSm : Sm ∈ SmallEtale.topology B S hS (yoneda.obj U) T := by
    refine (SmallEtale.topology B S hS (yoneda.obj U)).superset_covering ?_ hSv
    rintro V f ⟨W, a, b, hb, rfl⟩
    exact RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ E₀ a (hmod b hb)
  obtain ⟨n, V, φ, haff, hmemSm, -, hpre⟩ := SmallEtale.exists_finite_affine_etale_ofArrows_le
    B S hS (yoneda.obj U) (isAffineChart_representedAffineFinalChart B S hS U) hSm
  let Ui : Fin n → BigFppfOver B S hS := fun i => (SmallEtale.toOver B S hS _).obj (V i)
  have hUi : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ui i)) := haff
  let g : ∀ i, Ui i ⟶ U := fun i => (SmallEtale.toOver B S hS _).map (φ i)
  let f : ∀ i, Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj (Ui i), ⊤) := fun i =>
    (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map (g i))).hom
  have hloc : ∀ i, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₀)) := by
    intro i
    have := hUi i
    obtain ⟨P, hP, ⟨eP⟩⟩ :=
      exists_isStrictlyPerfect_iso_of_hasStrictlyPerfectQuasiIso B S hS Z (V i) E₀ (hmemSm i)
    have hchart : chartToSpace B S hS Z (V i) = representedSpaceMap B S hS (g i) :=
      ObjectProperty.hom_ext _ ((CostructuredArrow.w (φ i).hom).symm.trans (Category.comp_id _))
    have het : IsEtale B S hS (representedSpaceMap B S hS (g i)).hom :=
      hchart ▸ isEtale_chartToSpace B S hS Z (V i)
    let L : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
        Modules.{u, u} B S hS (yoneda.obj (Ui i)) (isAlgebraicSpace_yoneda B S hS (Ui i)) :=
      etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Z (V i))
        (isEtale_chartToSpace B S hS Z (V i))
    let Φ₀ := representedAffineAssociated B S hS U
    let Φᵢ := representedAffineAssociated B S hS (Ui i)
    let ext := ModuleCat.extendScalars.{u, u, u} (f i)
    have hflat : (f i).Flat :=
      flat_chartRestrict_of_isAffine (hF := isAlgebraicSpace_yoneda B S hS U)
        (φ i) (isAffineChart_representedAffineFinalChart B S hS U) (haff i)
    have : ext.Additive := extendScalars_additive.{u, u} _
    have : PreservesFiniteLimits ext := extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ hflat
    have : PreservesFiniteColimits ext :=
      StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars.{u, u, u} (f i)
    have : L.Additive := etaleModulePullback_additive B S hS _ _
    have : PreservesFiniteLimits L := preservesFiniteLimits_etaleModulePullback B S hS _ _
    have : PreservesFiniteColimits L := preservesFiniteColimits_etaleModulePullback B S hS _ _
    have : Φᵢ.Additive := additive_representedAffineAssociated B S hS (Ui i)
    have : Φ₀.Additive := additive_representedAffineAssociated B S hS U
    have : (ext ⋙ Φᵢ).Additive := inferInstance
    have : (Φ₀ ⋙ L).Additive := inferInstance
    have hL : L = etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS (g i)) het :=
      etaleModulePullback_congr B S hS _ _ hchart
    let bc : Φ₀ ⋙ L ≅ ext ⋙ Φᵢ :=
      eqToIso (by rw [hL]) ≪≫
        Functor.isoWhiskerLeft Φ₀ (modulePullbackIsoEtaleModulePullback B S hS
          (representedSpaceMap B S hS (g i)) het).symm ≪≫
        representedAffineAssociatedModulePullbackIso B S hS (g i)
    let a₁ : (representedAffineDerivedAssociated B S hS (Ui i)).obj
        (DerivedCategory.Q.obj ((ext.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≅
        DerivedCategory.Q.obj (((ext ⋙ Φᵢ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :=
      (Φᵢ.mapDerivedCategoryFactors.app _) ≪≫ DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (ext ⋙ Φᵢ))
          (ComplexShape.up ℤ)).app K₀)
    let a₂ : DerivedCategory.Q.obj (((ext ⋙ Φᵢ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
        DerivedCategory.Q.obj (((Φ₀ ⋙ L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) :=
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex bc (ComplexShape.up ℤ)).symm.app K₀)
    let a₃ : DerivedCategory.Q.obj (((Φ₀ ⋙ L).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
        L.mapDerivedCategory.obj ((representedAffineDerivedAssociated B S hS U).obj
          (DerivedCategory.Q.obj K₀)) :=
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (Φ₀ ⋙ L))
          (ComplexShape.up ℤ)).app K₀).symm ≪≫
        (L.mapDerivedCategoryFactors.app _).symm ≪≫
        L.mapDerivedCategory.mapIso (Φ₀.mapDerivedCategoryFactors.app K₀).symm
    let a₄ : L.mapDerivedCategory.obj ((representedAffineDerivedAssociated B S hS U).obj
          (DerivedCategory.Q.obj K₀)) ≅ L.mapDerivedCategory.obj (DerivedCategory.Q.obj E₀) :=
      L.mapDerivedCategory.mapIso
        ((representedAffineDerivedAssociated B S hS U).mapIso eK ≪≫ ε ≪≫ e₀.symm)
    let P' : CochainComplex (Modules.{u, u} B S hS (yoneda.obj (Ui i))
        (isAlgebraicSpace_yoneda B S hS (Ui i))) ℤ := P
    let a₅ : L.mapDerivedCategory.obj (DerivedCategory.Q.obj E₀) ≅ DerivedCategory.Q.obj P' := eP
    let e₁ := a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅
    have h3 := isPerfect_representedAffineDerivedSections_obj_of_isStrictlyPerfect
      (B := B) (S := S) (hS := hS) (U := Ui i) _ P' hP e₁
    exact StacksDraft.Perfect.isPerfect_of_iso ((asIso (representedAffineDerivedAdjunction
      B S hS (Ui i)).unit).app _) h3
  -- the product of the `R_i` is faithfully flat over `R`
  have hφ : (RingHom.pi f).FaithfullyFlat :=
    faithfullyFlat_pi_chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (isAffineChart_representedAffineFinalChart B S hS U) φ haff hpre
  let S' : ULift.{u} (Fin n) → Type u := fun j =>
    Γ((BigFppfOver.toScheme B S hS).obj (Ui j.down), ⊤)
  let f' : ∀ j, Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+* S' j := fun j => f j.down
  let ψ : (∀ i, Γ((BigFppfOver.toScheme B S hS).obj (Ui i), ⊤)) →+* ∀ j, S' j :=
    RingHom.pi fun j => Pi.evalRingHom _ j.down
  have hψ : Function.Bijective ψ :=
    ⟨fun x y h => funext fun i => congrFun h ⟨i⟩, fun y => ⟨fun i => y ⟨i⟩, rfl⟩⟩
  have hφ' : (RingHom.pi f').FaithfullyFlat := by
    rw [show RingHom.pi f' = ψ.comp (RingHom.pi f) from rfl]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hφ
      (RingHom.FaithfullyFlat.of_bijective hψ)
  exact StacksDraft.Perfect.isPerfect_of_iso eK.symm
    (StacksDraft.Perfect.isPerfect_of_extendScalars_of_faithfullyFlat_pi f' hφ' K₀
      fun j => hloc j.down)

end Sections

end AlgebraicGeometry.Space

end
