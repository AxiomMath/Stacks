module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSchemeCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq
public import StacksFrontier.Homology.Tor.DerivedFibreBoundedBelow

/-!
# Étale charts of the fibres of a morphism to a scheme

Let `f : X ⟶ T` be a morphism from an algebraic space to (the algebraic space represented by)
a scheme `T`, and let `s ∈ T`. The fibre `X_s = X ×_T Spec κ(s)` comes with a representable
morphism `j : X_s ⟶ X`, so an étale scheme chart `U` of `X` pulls back to an étale scheme chart
`U_s = U ×_X X_s` of `X_s`, and `U_s = U ×_T Spec κ(s)` as schemes. When `U` maps into an affine
open `O` of `T` containing `s` and `U` is affine, `U_s = U ×_O Spec κ(s)` is affine with ring of
functions `Γ(U) ⊗_{Γ(O)} κ(s)`, and the derived pullback of `E ∈ D_QCoh(𝒪_X)` to `U_s` is bounded
below exactly when the derived fibre `RΓ(U, E) ⊗^L_{Γ(O)} κ(p)` is, `p` the prime of `s`.

## Main definitions

* `AlgebraicGeometry.Space.residueFibre`, `AlgebraicGeometry.Space.residueFibreι`: the fibre
  `X_s` and its morphism to `X`.
* `AlgebraicGeometry.Space.residueFibreChart`: the chart `U ×_X X_s` of `X_s`.
* `AlgebraicGeometry.Space.OpenAffineChartSquare`: an affine chart of `X` over an affine open of
  `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ representedSpace T)
  (s : (BigFppfOver.toScheme B S hS).obj T)

/-- The fibre `X_s = X ×_T Spec κ(s)` of a morphism from an algebraic space to a scheme. -/
abbrev residueFibre : AlgebraicSpaces B S hS :=
  ⟨fieldFibre B S hS f.hom (residueFieldValuedPoint B S hS T s),
    isAlgebraicSpace_fieldFibre X.2 (isAlgebraicSpace_yoneda B S hS T) f.hom _⟩

/-- The morphism `X_s ⟶ X`. -/
abbrev residueFibreι : residueFibre f s ⟶ X :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The section of the residue field point, read through Yoneda. -/
theorem yonedaEquiv_symm_residueFieldValuedPoint_value :
    yonedaEquiv.symm (residueFieldValuedPoint B S hS T s).value =
      yoneda.map (residueFieldValuedPoint B S hS T s).value :=
  (Equiv.symm_apply_eq _).2 (yonedaEquiv_yoneda_map _).symm

/-- The morphism of schemes underlying the residue field point is `Spec κ(s) ⟶ T`. -/
theorem toScheme_map_residueFieldValuedPoint_value :
    (BigFppfOver.toScheme B S hS).map (residueFieldValuedPoint B S hS T s).value =
      ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField s :=
  B.inclusion.map_preimage _

/-- The morphism `X_s ⟶ X` is representable, being a base change of a morphism of schemes. -/
theorem relativelyRepresentable_residueFibreι :
    yoneda.relativelyRepresentable (residueFibreι f s).hom := by
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hv : yoneda.relativelyRepresentable
      (yonedaEquiv.symm (residueFieldValuedPoint B S hS T s).value) := by
    rw [yonedaEquiv_symm_residueFieldValuedPoint_value]
    exact Functor.relativelyRepresentable.map yoneda _
  exact (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (IsPullback.of_hasPullback f.hom _).flip hv

/-- **The chart `U ×_X X_s` of the fibre** attached to an étale chart `U` of `X`. -/
abbrev residueFibreChart (U : SmallEtale B S hS X.1) : SmallEtale B S hS (residueFibre f s).1 :=
  (smallBaseChange B S hS (residueFibreι f s) (relativelyRepresentable_residueFibreι f s)).obj U

/-- The projection `U ×_X X_s ⟶ U`. -/
abbrev residueFibreChartFst (U : SmallEtale B S hS X.1) :
    (residueFibreChart f s U).1.left ⟶ U.1.left :=
  (relativelyRepresentable_residueFibreι f s).snd U.1.hom

/-- The projection `U ×_X X_s ⟶ Spec κ(s)`. -/
def residueFibreChartSnd (U : SmallEtale B S hS X.1) :
    (residueFibreChart f s U).1.left ⟶
      (residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T) :=
  yoneda.preimage ((relativelyRepresentable_residueFibreι f s).fst U.1.hom ≫ pullback.snd _ _)

/-- The chart of the fibre lies over the chart of `X`. -/
theorem chartToSpace_residueFibreChart_comp (U : SmallEtale B S hS X.1) :
    chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U) ≫ residueFibreι f s =
      representedSpaceMap B S hS (residueFibreChartFst f s U) ≫ chartToSpace B S hS X U :=
  ObjectProperty.hom_ext _ ((relativelyRepresentable_residueFibreι f s).w U.1.hom)

/-- **The chart of the fibre is `U ×_T Spec κ(s)`**, in the big fppf site. -/
theorem isPullback_residueFibreChart (U : SmallEtale B S hS X.1) :
    IsPullback (residueFibreChartFst f s U) (residueFibreChartSnd f s U)
      (yoneda.preimage (U.1.hom ≫ f.hom)) (residueFieldValuedPoint B S hS T s).value := by
  have h := ((relativelyRepresentable_residueFibreι f s).isPullback U.1.hom).flip.paste_vert
    (IsPullback.of_hasPullback f.hom (yonedaEquiv.symm (residueFieldValuedPoint B S hS T s).value))
  exact IsPullback.of_map_of_faithful yoneda (IsPullback.of_eq h rfl (Functor.map_preimage _ _).symm
    (Functor.map_preimage _ _).symm (yonedaEquiv_symm_residueFieldValuedPoint_value s))

/-- **The chart of the fibre is `U ×_T Spec κ(s)`**, as schemes. -/
theorem isPullback_toScheme_residueFibreChart (U : SmallEtale B S hS X.1) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s U))
      ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s U))
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.1.hom ≫ f.hom)))
      (((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField s) := by
  rw [← toScheme_map_residueFieldValuedPoint_value]
  exact (isPullback_residueFibreChart f s U).map (BigFppfOver.toScheme B S hS)

/-! ### Charts over an affine open of the base -/

/-- **An affine étale chart of `X` over an affine open of `T`**: an affine chart `U` of `X` whose
composite to `T` factors through an affine open `O` of `T`. -/
structure OpenAffineChartSquare where
  /-- The affine open of the base. -/
  O : ((BigFppfOver.toScheme B S hS).obj T).Opens
  isAffineOpen_O : IsAffineOpen O
  /-- The chart of `X`. -/
  U : SmallEtale B S hS X.1
  isAffine_U : IsAffine (chartScheme U)
  /-- The factorization through `O`. -/
  g : (SmallEtale.toOver B S hS X.1).obj U ⟶ chartOpenOver B S hS (idEtaleChart B S hS T) O
  comm : U.1.hom ≫ f.hom = yoneda.map (g ≫ chartOpenOverι B S hS (idEtaleChart B S hS T) O)

namespace OpenAffineChartSquare

variable {f} (c : OpenAffineChartSquare f)

/-- The square of étale charts over `f` of an affine chart over an affine open. -/
def toChartDiagram : ChartDiagram B S hS X.1 (yoneda.obj T) f.hom where
  U := c.U
  V := (chartOpens B S hS (idEtaleChart B S hS T)).obj c.O
  g := c.g
  comm := by
    rw [c.comm, Functor.map_comp]
    exact (Category.comp_id _).symm.trans (Category.assoc _ _ _)

/-- The chart `U` of the square is affine. -/
instance isAffine_chartScheme_U : IsAffine (chartScheme c.toChartDiagram.U) := c.isAffine_U

/-- The chart `O` of the base in the square is affine. -/
instance isAffine_chartScheme_V : IsAffine (chartScheme c.toChartDiagram.V) := c.isAffineOpen_O

/-- The composite `U ⟶ T` is the factorization through `O` followed by the inclusion. -/
theorem preimage_comp_eq : yoneda.preimage (c.U.1.hom ≫ f.hom) =
    c.g ≫ chartOpenOverι B S hS (idEtaleChart B S hS T) c.O :=
  yoneda.map_injective ((Functor.map_preimage _ _).trans c.comm)

/-- The point `Spec κ(s) ⟶ T` of a point of `O`, factored through `O`. -/
def residueLift (hs : s ∈ c.O) :
    (BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)) ⟶ c.O.toScheme :=
  IsOpenImmersion.lift c.O.ι (((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField s)
    (fun _ ⟨_, hx⟩ => ⟨⟨s, hs⟩, (hx.symm.trans (Scheme.fromSpecResidueField_apply _ _)).symm⟩)

/-- The lift `Spec κ(s) ⟶ O` composed with the inclusion `O ⟶ T` is `Spec κ(s) ⟶ T`. -/
theorem residueLift_fac (hs : s ∈ c.O) :
    c.residueLift s hs ≫ c.O.ι = ((BigFppfOver.toScheme B S hS).obj T).fromSpecResidueField s :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The chart of the fibre over an affine open is `U ×_O Spec κ(s)`.** -/
theorem isPullback_residueFibreChart (hs : s ∈ c.O) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U))
      ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U))
      ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g) (c.residueLift s hs) := by
  have hm : Mono c.O.ι := inferInstance
  refine @IsPullback.of_comp_mono' _ _ _ _ _ _ _ _ _ _ _ c.O.ι hm ?_
  refine IsPullback.of_eq (isPullback_toScheme_residueFibreChart f s c.U) rfl rfl ?_
    (c.residueLift_fac s hs).symm
  rw [c.preimage_comp_eq]
  exact Functor.map_comp _ _ _

/-- The scheme `Spec κ(s)` underlying the residue field point is affine. -/
instance isAffine_toScheme_siteObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T))) :=
  (inferInstance : IsAffine (Spec (.of (((BigFppfOver.toScheme B S hS).obj T).residueField s))))

/-- The ring of functions on `Spec κ(s)` is a field. -/
theorem isField_siteObject :
    IsField Γ((BigFppfOver.toScheme B S hS).obj
      ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤) :=
  MulEquiv.isField (Field.toIsField (((BigFppfOver.toScheme B S hS).obj T).residueField s))
    (Scheme.ΓSpecIso (.of
      (((BigFppfOver.toScheme B S hS).obj T).residueField s))).commRingCatIsoToRingEquiv.toMulEquiv

/-- The chart `U ×_O Spec κ(s)` of the fibre is affine. -/
theorem isAffine_residueFibreChart
    (hs : s ∈ c.O) :
    IsAffine (chartScheme (residueFibreChart f s c.U)) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.U.obj.left) := c.isAffine_U
  have : IsAffine c.O.toScheme := c.isAffineOpen_O
  have := isAffineHom_isStableUnderBaseChange.of_isPullback
    (c.isPullback_residueFibreChart s hs).flip
    (inferInstance : AlgebraicGeometry.IsAffineHom (c.residueLift s hs))
  exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U))

end OpenAffineChartSquare



/-- **Boundedness below on the chart of the fibre.** For an étale chart `U` of `X` with affine
scheme, whose chart `U ×_X X_s` of the fibre is affine, and `E ∈ D_QCoh(𝒪_X)`, the cohomology
sheaves of `E` pulled back to `U ×_X X_s` vanish below `a` exactly when the base change
`RΓ(U, E) ⊗^L_{Γ(U)} Γ(U ×_X X_s)` is bounded below by `a`. -/
theorem forall_isZero_homology_residueFibreChart_iff (U : SmallEtale B S hS X.1)
    [hU : IsAffine (chartScheme U)] [hW : IsAffine (chartScheme (residueFibreChart f s U))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) (a : ℤ) :
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFibreChart f s U).1.left) := hW
    (∀ i < a, IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).1
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).2) i).obj
        ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U))).obj
          ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E)))) ↔
      ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj
        ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E))).IsGE a := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFibreChart f s U).1.left) := hW
  let F := (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E
  have hF : QcohDerived B S hS (chartSpace B S hS X U) F :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X U) E hE
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS
    ((SmallEtale.toOver B S hS X.1).obj U) F hF
  let K := (representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj F
  let e : (smallEtaleDerivedModulePullback B S hS
        (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U))).obj
        ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E) ≅
      (representedAffineDerivedAssociated B S hS (residueFibreChart f s U).1.left).obj
        ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj K) :=
    (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (chartToSpace_residueFibreChart_comp f s U)).app E ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app E).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS
        (representedSpaceMap B S hS (residueFibreChartFst f s U))).mapIso
        (asIso ((representedAffineDerivedAdjunction B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).counit.app F)).symm ≪≫
      (representedAffineDerivedBaseChangeIso B S hS (residueFibreChartFst f s U)).app K
  rw [DerivedCategory.isGE_iff]
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  refine ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).1
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).2) i).mapIso
    e).isZero_iff.trans ?_
  exact (((representedAffineAssociated B S hS
    (residueFibreChart f s U).1.left).mapDerivedCategoryHomologyIso i).app
      ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj
        K)).isZero_iff.trans (isZero_representedAffineAssociated_obj_iff B S hS _ _)

namespace OpenAffineChartSquare

variable {f} (c : OpenAffineChartSquare f)

/-- The point `Spec κ(s) ⟶ O`, with its target read as the chart of `T`. -/
abbrev residuePoint (hs : s ∈ c.O) :
    (BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)) ⟶
      chartScheme c.toChartDiagram.V :=
  c.residueLift s hs

/-- **Boundedness below on the chart of the fibre, read on rings.** For an affine chart `U` over
an affine open `O ∋ s` and `K ∈ D(Γ(U))`, the base change `K ⊗^L_{Γ(U)} Γ(U ×_O Spec κ(s))` is
bounded below exactly when the derived fibre `K ⊗^L_{Γ(O)} κ(p)` is, `p` the prime of `s`. -/
theorem isGE_representedAffineDerivedExtension_residueFibreChartFst_iff
    (hfl : IsFlat B S hS f.hom) (hs : s ∈ c.O)
    (K : DerivedCategory (ModuleCat.{u} Γ(chartScheme c.toChartDiagram.U, ⊤))) (a : ℤ) :
    haveI := c.isAffine_residueFibreChart s hs
    haveI := (isField_siteObject s).isDomain
    haveI := RingHom.ker_isPrime (c.residuePoint s hs).appTop.hom
    ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s c.U)).functor.obj
        K).IsGE a ↔
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap Γ(chartScheme c.toChartDiagram.V, ⊤)
            (RingHom.ker (c.residuePoint s hs).appTop.hom).ResidueField)).functor.obj
        ((ModuleCat.restrictScalars.{u}
          ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom).mapDerivedCategory.obj
            K)).IsGE a := by
  have := c.isAffine_residueFibreChart s hs
  have := (isField_siteObject s).isDomain
  have := RingHom.ker_isPrime (c.residuePoint s hs).appTop.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.U.obj.left) := c.isAffine_U
  have hsq := c.isPullback_residueFibreChart s hs
  let gR := ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom
  let ℓR := (c.residuePoint s hs).appTop.hom
  let qR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U)).appTop.hom
  let rR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U)).appTop.hom
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤) :=
    gR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤) :=
    ℓR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := qR.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := rR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := (qR.comp gR).toAlgebra
  have hw : qR.comp gR = rR.comp ℓR := congrArg (·.appTop.hom) hsq.w
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq (RingHom.congr_fun hw)
  have : Algebra.IsPushout Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    (CommRingCat.isPushout_iff_isPushout).1 (isPushout_appTop_of_isPullback hsq)
  have : Module.Flat Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) _ (flat_chartDiagram_g f hfl c.toChartDiagram)
  exact (CochainComplex.DerivedExtensionScalars.isGE_totalDerivedExtensionScalars_iff_of_isPushout
    (R := Γ(chartScheme c.toChartDiagram.V, ⊤)) (A := Γ(chartScheme c.toChartDiagram.U, ⊤))
    (R' := Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤))
    (A' := Γ(chartScheme (residueFibreChart f s c.U), ⊤)) K a).trans
    (CochainComplex.DerivedExtensionScalars.isGE_totalDerivedExtensionScalars_iff_residueField
      (isField_siteObject s) ℓR ((ModuleCat.restrictScalars.{u} gR).mapDerivedCategory.obj K) a)

end OpenAffineChartSquare


/-- **The points of the fibre lie over `s`.** -/
theorem pointsToScheme_pointsMap_residueFibreι (x : points B S hS (residueFibre f s).1) :
    pointsToScheme B S hS T (pointsMap B S hS _ f.hom
      (pointsMap B S hS _ (residueFibreι f s).hom x)) = s := by
  have h : (residueFibreι f s).hom ≫ f.hom =
      pullback.snd _ _ ≫ yoneda.map (residueFieldValuedPoint B S hS T s).value := by
    rw [← yonedaEquiv_symm_residueFieldValuedPoint_value]
    exact pullback.condition
  have h2 := congrFun (pointsMap_comp B S hS _ (residueFibreι f s).hom f.hom) x
  rw [Function.comp_apply] at h2
  rw [← h2, h, pointsMap_comp, Function.comp_apply, pointsToScheme_pointsMap_yoneda,
    toScheme_map_residueFieldValuedPoint_value]
  exact Scheme.fromSpecResidueField_apply _ _

/-- A point of the fibre lies on the chart `U ×_X X_s` as soon as its image in `X` lies on `U`. -/
theorem mem_range_residueFibreChart (U : SmallEtale B S hS X.1)
    (x : points B S hS (residueFibre f s).1)
    (hx : pointsMap B S hS _ (residueFibreι f s).hom x ∈
      Set.range (pointsMap B S hS _ (chartToSpace B S hS X U).hom)) :
    x ∈ Set.range (pointsMap B S hS _
      (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U)).hom) := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS
    ((relativelyRepresentable_residueFibreι f s).isPullback U.1.hom) x u hu.symm
  exact ⟨w, hw⟩

namespace OpenAffineChartSquare

variable {f}

/-- **Affine charts over an affine open pass through every point over it.** -/
theorem exists_of_mem (x : points B S hS X.1) (O : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hO : IsAffineOpen O) (hx : pointsToScheme B S hS T (pointsMap B S hS _ f.hom x) ∈ O) :
    ∃ c : OpenAffineChartSquare f, c.O = O ∧
      x ∈ Set.range (pointsMap B S hS _ (chartToSpace B S hS X c.U).hom) := by
  obtain ⟨U₀, a, ha_surj, ha_et⟩ := X.2.exists_atlas
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U₀ a).1 ha_surj x
  let C₀ : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk a, ha_et⟩
  let uT : U₀ ⟶ T := yoneda.preimage (a ≫ f.hom)
  set g₀ := (BigFppfOver.toScheme B S hS).map uT
  set u₀ := pointsToScheme B S hS U₀ u
  have hu₀ : g₀ u₀ ∈ O := by
    rw [← pointsToScheme_pointsMap_yoneda, Functor.map_preimage, pointsMap_comp,
      Function.comp_apply, hu]
    exact hx
  obtain ⟨U', hU', huU', hU'le'⟩ := exists_isAffineOpen_mem_and_subset (x := u₀)
    (U := g₀ ⁻¹ᵁ O) hu₀
  have hU'le : U' ≤ g₀ ⁻¹ᵁ O := hU'le'
  let g' : chartOpenOver B S hS C₀ U' ⟶ chartOpenOver B S hS (idEtaleChart B S hS T) O :=
    Over.homMk (ObjectProperty.homMk (g₀.resLE O U' hU'le)) (by
      apply ObjectProperty.hom_ext
      change g₀.resLE O U' hU'le ≫ O.ι ≫ T.hom.hom = U'.ι ≫ U₀.hom.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (U'.ι ≫ ·) (congrArg (fun φ => φ.hom) (Over.w uT)))
  have hg' : g' ≫ chartOpenOverι B S hS (idEtaleChart B S hS T) O =
      chartOpenOverι B S hS C₀ U' ≫ uT :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.Hom.resLE_comp_ι _ _))
  refine ⟨⟨O, hO, (chartOpens B S hS C₀).obj U', hU', g', ?_⟩, rfl, ?_⟩
  · change (yoneda.map (chartOpenOverι B S hS C₀ U') ≫ a) ≫ f.hom = _
    have h1 : yoneda.map (chartOpenOverι B S hS C₀ U' ≫ uT) =
        yoneda.map (chartOpenOverι B S hS C₀ U') ≫ (a ≫ f.hom) :=
      (yoneda.map_comp _ _).trans (congrArg (CategoryStruct.comp _) (Functor.map_preimage _ _))
    exact (Category.assoc _ _ _).trans (h1.symm.trans (congrArg yoneda.map hg'.symm))
  · refine ⟨(pointsEquivScheme B S hS (chartOpenOver B S hS C₀ U')).symm ⟨u₀, huU'⟩, ?_⟩
    change pointsMap B S hS _ (yoneda.map (chartOpenOverι B S hS C₀ U') ≫ a) _ = x
    rw [pointsMap_comp, Function.comp_apply, ← hu]
    congr 1
    apply injective_pointsToScheme B S hS
    rw [pointsToScheme_pointsMap_yoneda]
    have h := (pointsEquivScheme B S hS (chartOpenOver B S hS C₀ U')).apply_symm_apply ⟨u₀, huU'⟩
    change (BigFppfOver.toScheme B S hS).map (chartOpenOverι B S hS C₀ U')
      ((pointsEquivScheme B S hS (chartOpenOver B S hS C₀ U')) _) = u₀
    rw [h]
    rfl

end OpenAffineChartSquare


/-- **The kernel of a map to an affine scheme from an affine scheme with a field of functions** is
the prime of the image point. -/
theorem ker_appTop_eq_asIdeal_isoSpec {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (hY : IsField Γ(Y, ⊤)) (h : Y ⟶ Z) (y : Y) :
    RingHom.ker h.appTop.hom = (Z.isoSpec.hom (h y)).asIdeal := by
  have e := congrArg (fun k : Y ⟶ Spec Γ(Z, ⊤) => k y) (Scheme.isoSpec_hom_naturality h)
  simp only [Scheme.Hom.comp_apply] at e
  rw [← e, Spec.map_apply]
  have := hY.isDomain
  have hbot : (Y.isoSpec.hom y).asIdeal = ⊥ := by
    let := hY.toField
    exact Ideal.eq_bot_of_prime _
  change RingHom.ker h.appTop.hom = Ideal.comap h.appTop.hom (Y.isoSpec.hom y).asIdeal
  rw [hbot, RingHom.ker_eq_comap_bot]


namespace OpenAffineChartSquare

variable {f}

/-- **Every prime of `Γ(O)` is the kernel at a point of `O`.** -/
theorem exists_ker_residuePoint_eq (c : OpenAffineChartSquare f)
    (p : PrimeSpectrum Γ(chartScheme c.toChartDiagram.V, ⊤)) :
    ∃ (s : (BigFppfOver.toScheme B S hS).obj T) (hs : s ∈ c.O),
      RingHom.ker (c.residuePoint s hs).appTop.hom = p.asIdeal := by
  let z : c.O.toScheme := (chartScheme c.toChartDiagram.V).isoSpec.inv p
  have hz : c.O.ι z ∈ c.O := by
    have : c.O.ι z ∈ Set.range c.O.ι := ⟨z, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  refine ⟨c.O.ι z, hz, ?_⟩
  let y : (BigFppfOver.toScheme B S hS).obj ((residueFieldValuedPoint B S hS T (c.O.ι z)).siteObject
      B S hS (yoneda.obj T)) :=
    IsLocalRing.closedPoint (((BigFppfOver.toScheme B S hS).obj T).residueField (c.O.ι z))
  rw [ker_appTop_eq_asIdeal_isoSpec (isField_siteObject (c.O.ι z)) _ y]
  have hy : c.residuePoint (c.O.ι z) hz y = z := by
    apply c.O.ι.isOpenEmbedding.injective
    change (c.residueLift (c.O.ι z) hz ≫ c.O.ι) y = c.O.ι z
    rw [c.residueLift_fac]
    exact Scheme.fromSpecResidueField_apply _ _
  rw [hy]
  change (((chartScheme c.toChartDiagram.V).isoSpec.inv ≫
    (chartScheme c.toChartDiagram.V).isoSpec.hom) p).asIdeal = p.asIdeal
  rw [Iso.inv_hom_id]
  rfl

end OpenAffineChartSquare

end AlgebraicGeometry.Space

end
