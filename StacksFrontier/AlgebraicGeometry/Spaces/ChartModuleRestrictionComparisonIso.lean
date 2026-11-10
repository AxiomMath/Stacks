module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# The chart comparison of a quasi-coherent module is an isomorphism

Let `X` be an algebraic space, `M` a quasi-coherent `𝒪_X`-module and `g : V ⟶ U` a morphism of
étale charts of `X`.  `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is the
canonical morphism `(chartSchemeMap g)^* M|_U ⟶ M|_V` between the Zariski restrictions of `M` to
the two chart schemes.  This file proves that it is an isomorphism.

## Main results

* `Stacks.TensorProduct.bijective_of_tmul_eq`: bijectivity of a map out of a tensor product
  transports along additive identifications of the factors that are semilinear over a ring
  isomorphism.
* `AlgebraicGeometry.Space.chartSectionsToRestrict`: a section of `M` over the étale chart cut
  out by a Zariski open `O` of a chart scheme, read as a section of the chart restriction over
  `O`; `AlgebraicGeometry.Space.bijective_chartSectionsToRestrict` says this is bijective.
* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_chartSectionsToRestrict`
  and `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_pullbackSection`: the two
  forms of the comparison, on sections.
* `AlgebraicGeometry.Space.isIso_restrictToChartSchemePullbackComparison`: **for a
  quasi-coherent module the chart comparison is an isomorphism.**

## Implementation notes

The criterion is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover`:
both sides are quasi-coherent, so it suffices to check bijectivity on the sections over the
affine opens `O'` of the smaller chart scheme lying over an affine open `O` of the larger one.
There the sections of the pullback are `Γ(O') ⊗_{Γ(O)} Γ(M|_U, O)`
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, normalised by its value on `1 ⊗ a`),
the sections of the chart restrictions are the sections of `M` over the corresponding étale charts
(the restricted presheaf is already a Zariski sheaf, so the unit of sheafification is bijective),
and the comparison becomes the base change map of `M` along the morphism of affine charts, which
is bijective by the forward half of Stacks 03DX (2)
(`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite`). The passage
between the rings `Γ(O)` and the rings of the étale site is
`AlgebraicGeometry.Scheme.restrictFunctorΓ`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.TensorProduct

/-- **Transport of bijectivity of a map out of a tensor product.**  Additive identifications of the
two factors which are semilinear over a ring isomorphism identify the two tensor products; a map
out of the first which corresponds, on pure tensors, to a bijective map out of the second is
bijective. -/
theorem bijective_of_tmul_eq {R R' P P' M M' N N' : Type*} [CommRing R] [CommRing R']
    {_ : AddCommMonoid P} {_ : Module R P} {_ : AddCommMonoid P'} {_ : Module R' P'}
    {_ : AddCommMonoid M} {_ : Module R M} {_ : AddCommMonoid M'} {_ : Module R' M'}
    {_ : AddCommMonoid N} {_ : AddCommMonoid N'}
    (eR : R ≃+* R') (eP : P ≃+ P') (eM : M ≃+ M') (eN : N' ≃+ N)
    (hP : ∀ (r : R) (p : P), eP (r • p) = eR r • eP p)
    (hM : ∀ (r : R) (m : M), eM (r • m) = eR r • eM m)
    (L : TensorProduct R P M →+ N) (L' : TensorProduct R' P' M' →+ N')
    (hL : ∀ p m, L (p ⊗ₜ m) = eN (L' (eP p ⊗ₜ eM m))) (h' : Function.Bijective L') :
    Function.Bijective L := by
  let T : TensorProduct R P M →+ TensorProduct R' P' M' :=
    TensorProduct.liftAddHom
      { toFun := fun p => (TensorProduct.mk R' P' M' (eP p)).toAddMonoidHom.comp
          eM.toAddMonoidHom
        map_zero' := by ext m; simp
        map_add' := fun p q => by ext m; simp }
      (fun r p m => by simp [hP, hM])
  let T' : TensorProduct R' P' M' →+ TensorProduct R P M :=
    TensorProduct.liftAddHom
      { toFun := fun p' => (TensorProduct.mk R P M (eP.symm p')).toAddMonoidHom.comp
          eM.symm.toAddMonoidHom
        map_zero' := by ext m; simp
        map_add' := fun p q => by ext m; simp }
      (fun r' p' m' => by
        obtain ⟨r, rfl⟩ := eR.surjective r'
        have h1 : eP.symm (eR r • p') = r • eP.symm p' := by
          apply eP.injective
          simp [hP]
        have h2 : eM.symm (eR r • m') = r • eM.symm m' := by
          apply eM.injective
          simp [hM]
        simp [h1, h2])
  have hTT' : ∀ z, T' (T z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul p m => simp [T, T']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hT'T : ∀ z, T (T' z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul p m => simp [T, T']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hLT : ∀ z, L z = eN (L' (T z)) := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul p m => simp [T, hL]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
  have hT : Function.Bijective T :=
    ⟨Function.LeftInverse.injective hTT', Function.RightInverse.surjective hT'T⟩
  rw [show ⇑L = eN ∘ L' ∘ T from funext hLT]
  exact eN.bijective.comp (h'.comp hT)

open ChangeOfRings in
/-- `Stacks.TensorProduct.bijective_of_tmul_eq` for a map out of an extension of scalars of
modules over commutative rings, with the pure tensors written as in
`ModuleCat.ExtendScalars`. -/
theorem bijective_extendScalars_of_tmul_eq {R S : CommRingCat.{u}} (f : R ⟶ S)
    (Mm : ModuleCat.{u} R) {R' P' M' N N' : Type*} [CommRing R']
    [AddCommGroup P'] [Module R' P'] [AddCommGroup M'] [Module R' M']
    [AddCommGroup N] [AddCommGroup N']
    (eR : R ≃+* R') (eP : S ≃+ P') (eM : Mm ≃+ M') (eN : N' ≃+ N)
    (hP : ∀ (r : R) (s : S), eP (f r * s) = eR r • eP s)
    (hM : ∀ (r : R) (m : Mm), eM (r • m) = eR r • eM m)
    (L : (ModuleCat.extendScalars f.hom).obj Mm →+ N)
    (L' : TensorProduct R' P' M' →+ N')
    (hL : ∀ s m, L (s ⊗ₜ[R,f.hom] m) = eN (L' (eP s ⊗ₜ eM m)))
    (h' : Function.Bijective L') :
    Function.Bijective L :=
  bijective_of_tmul_eq eR eP eM eN hP hM L L' hL h'

end Stacks.TensorProduct

namespace AlgebraicGeometry

/-- Restricting a morphism of schemes to an open `O` of its target and the preimage of that open,
after restricting further to an open `O'` inside that preimage, is, on global sections and read
through `AlgebraicGeometry.Scheme.restrictFunctorΓ`, the map `appLE` between `O` and `O'`. -/
theorem Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_comp_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (O : Y.Opens) (O' : X.Opens) (hle : O' ≤ f ⁻¹ᵁ O)
    (r : Γ(Y, O)) :
    (Scheme.Γ.map (X.homOfLE hle ≫ (f ∣_ O)).op).hom
        (((Scheme.restrictFunctorΓ (X := Y)).inv.app (op O)).hom r) =
      ((Scheme.restrictFunctorΓ (X := X)).inv.app (op O')).hom (f.appLE O O' hle r) := by
  have e1 := congrArg (fun φ => CommRingCat.Hom.hom φ r)
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict f O)
  have e2 := congrArg (fun φ => CommRingCat.Hom.hom φ (f.app O r))
    ((Scheme.restrictFunctorΓ (X := X)).inv.naturality (homOfLE hle).op)
  have e1' : (Scheme.Γ.map (f ∣_ O).op).hom
      (((Scheme.restrictFunctorΓ (X := Y)).inv.app (op O)).hom r) =
      ((Scheme.restrictFunctorΓ (X := X)).inv.app (op (f ⁻¹ᵁ O))).hom (f.app O r) := e1
  rw [op_comp, Functor.map_comp]
  exact (congrArg (Scheme.Γ.map (X.homOfLE hle).op).hom e1').trans e2.symm

/-- A morphism of modules on a scheme commutes with the action of functions on sections, with the
action on the source read through `AlgebraicGeometry.Scheme.Modules` sections and the one on the
target through the underlying sheaf of modules. -/
theorem Scheme.Modules.Hom.app_smul_val {Y : Scheme.{u}} {F G : Y.Modules} (φ : F ⟶ G)
    (V : Y.Opens) (t : Γ(Y, V)) (z : Γ(F, V)) :
    (φ.val.app (op V)).hom (t • z) =
      (show Y.ringCatSheaf.obj.obj (op V) from t) • (φ.val.app (op V)).hom z :=
  (φ.val.app (op V)).hom.map_smul t z

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS X.1 X.2)

/-! ### Sections of the chart restriction -/

/-- A section of `M` over the étale chart cut out by a Zariski open `O` of the chart scheme of
`U`, read as a section of the chart restriction `M|_U` over `O`: the unit of Zariski
sheafification, after the universe lift of the sections. -/
noncomputable def chartSectionsToRestrict (U : SmallEtale B S hS X.1) (O : (chartScheme U).Opens) :
    M.val.obj (op (openChart B S hS X.1 U O)) →+
      (restrictToChartScheme B S hS X.1 X.2 M U).val.obj (op O) := by
  letI : HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  exact (((PresheafOfModules.sheafificationAdjunction (𝟙 (chartScheme U).ringCatSheaf.obj)).unit.app
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)).app
          (op O)).hom.toAddMonoidHom.comp
    (AddEquiv.ulift (α := M.val.obj (op (openChart B S hS X.1 U O)))).symm.toAddMonoidHom

/-- Abelian-group-valued presheaves on the opens of a chart scheme sheafify. -/
private noncomputable instance hasSheafify_chartScheme (U : SmallEtale B S hS X.1) :
    HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of a chart scheme, weak equivalences are the locally bijective maps. -/
private noncomputable instance wEqualsLocallyBijective_chartScheme (U : SmallEtale B S hS X.1) :
    (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {X M} in
/-- `AlgebraicGeometry.Space.chartSectionsToRestrict` is the unit of Zariski sheafification. -/
theorem chartSectionsToRestrict_apply (U : SmallEtale B S hS X.1) (O : (chartScheme U).Opens)
    (x : M.val.obj (op (openChart B S hS X.1 U O))) :
    letI : HasSheafify (Opens.grothendieckTopology (chartScheme U)) AddCommGrpCat.{u} :=
      hasSheafifyEssentiallySmallSite _ _
    letI : (Opens.grothendieckTopology (chartScheme U)).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
    chartSectionsToRestrict X M U O x =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (chartScheme U).ringCatSheaf.obj)).unit.app
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)).app (op O)
        (ULift.up x) :=
  rfl

/-- **The sections of the chart restriction over a Zariski open are the sections of `M` over the
étale chart it cuts out**: the restricted presheaf is already a Zariski sheaf, the index functor
being continuous, so the unit of sheafification is bijective on it. -/
theorem bijective_chartSectionsToRestrict (U : SmallEtale B S hS X.1)
    (O : (chartScheme U).Opens) :
    Function.Bijective (chartSectionsToRestrict X M U O) := by
  have := isContinuous_openChartFunctor B S hS X U
  have hP : Presheaf.IsSheaf (Opens.grothendieckTopology (chartScheme U))
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val).presheaf :=
    ((SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 U)).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M)).isSheaf
  have := isIso_toSheafify _ hP
  have hb := ConcreteCategory.bijective_of_isIso ((toSheafify
      (Opens.grothendieckTopology (chartScheme U))
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val).presheaf).app (op O))
  exact hb.comp (AddEquiv.ulift (α := M.val.obj (op (openChart B S hS X.1 U O)))).symm.bijective

/-- `AlgebraicGeometry.Space.chartSectionsToRestrict` is semilinear along the identification of
the functions on a Zariski open with the functions on the étale chart it cuts out. -/
theorem chartSectionsToRestrict_smul (U : SmallEtale B S hS X.1) (O : (chartScheme U).Opens)
    (r : (chartScheme U).ringCatSheaf.obj.obj (op O))
    (x : M.val.obj (op (openChart B S hS X.1 U O))) :
    chartSectionsToRestrict X M U O
        ((show chartRing B S hS X.1 X.2 (openChart B S hS X.1 U O) from
          ((chartSchemeRestrictionRingHom B S hS X.1 U).app (op O)).hom r) • x) =
      r • chartSectionsToRestrict X M U O x := by
  exact (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (chartScheme U).ringCatSheaf.obj)).unit.app
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)).app
      (op O)).hom.map_smul r (ULift.up x)

/-- `AlgebraicGeometry.Space.chartSectionsToRestrict` is natural in the Zariski open. -/
theorem chartSectionsToRestrict_naturality (U : SmallEtale B S hS X.1)
    {O O' : (chartScheme U).Opens} (i : O' ⟶ O)
    (x : M.val.obj (op (openChart B S hS X.1 U O))) :
    (restrictToChartScheme B S hS X.1 X.2 M U).val.map i.op (chartSectionsToRestrict X M U O x) =
      chartSectionsToRestrict X M U O'
        (M.val.map ((openChartFunctor B S hS X.1 U).map i).op x) := by
  exact (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (chartScheme U).ringCatSheaf.obj)).unit.app
      ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS X.1 U)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val)) i.op (ULift.up x)).symm

/-! ### The comparison on sections -/

/-- **The direct-image form of the comparison on sections**: over a Zariski open `O` of the larger
chart scheme it is restriction of sections of `M` along the morphism of étale charts
`AlgebraicGeometry.Space.openChartRestrict`. -/
theorem restrictToChartSchemePushforwardComparison_chartSectionsToRestrict
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) (O : (chartScheme U).Opens)
    (x : M.val.obj (op (openChart B S hS X.1 U O))) :
    (restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g).val.app (op O)
        (chartSectionsToRestrict X M U O x) =
      chartSectionsToRestrict X M V (chartSchemeMap g ⁻¹ᵁ O)
        (M.val.map (openChartRestrict B S hS X.1 g O).op x) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (chartScheme U).ringCatSheaf.obj)
    (restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g)
  have h2 : PresheafOfModules.sheafificationHomEquiv (𝟙 (chartScheme U).ringCatSheaf.obj)
      (restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g) =
      chartRestrictionPresheafComparison B S hS X.1 g
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u} M).val ≫
        (PresheafOfModules.pushforward (chartSchemeMap g).toRingCatSheafHom.hom).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (chartScheme V).ringCatSheaf.obj)).unit.app _) :=
    Equiv.apply_symm_apply _ _
  rw [h2] at h
  exact (ConcreteCategory.congr_hom (congrArg (NatTrans.app · (op O)) h) (ULift.up x)).symm

/-- **The inverse-image form of the comparison on sections**: on the pullback of a section `a`
over `O` to an open `O'` of the preimage it is the restriction to `O'` of the direct-image form of
the comparison at `a`. -/
theorem restrictToChartSchemePullbackComparison_pullbackSection
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) (O : (chartScheme U).Opens)
    (O' : (chartScheme V).Opens) (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (a : (restrictToChartScheme B S hS X.1 X.2 M U).val.obj (op O)) :
    (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g).val.app (op O')
        (Scheme.Modules.pullbackSection (chartSchemeMap g)
          (restrictToChartScheme B S hS X.1 X.2 M U) O O' hle a) =
      (restrictToChartScheme B S hS X.1 X.2 M V).val.map (homOfLE hle).op
        ((restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g).val.app (op O) a) := by
  have hc : (Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).unit.app
        (restrictToChartScheme B S hS X.1 X.2 M U) ≫
      (Scheme.Modules.pushforward (chartSchemeMap g)).map
        (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g) =
      restrictToChartSchemePushforwardComparison B S hS X.1 X.2 M g :=
    ((Scheme.Modules.pullbackPushforwardAdjunction (chartSchemeMap g)).homEquiv_unit
      _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op O)) hc) a
  delta Scheme.Modules.pullbackSection
  exact (PresheafOfModules.naturality_apply
    (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g).val (homOfLE hle).op _).trans
      (congrArg _ h1)

/-- **The comparison on the pullback of a section of `M`**: the comparison sends the pullback to
`O'` of the section over `O` given by a section `x` of `M` to the section over `O'` given by the
restriction of `x` to the chart cut out by `O'`. -/
theorem restrictToChartSchemePullbackComparison_pullbackSection_chartSectionsToRestrict
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) (O : (chartScheme U).Opens)
    (O' : (chartScheme V).Opens) (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O)
    (x : M.val.obj (op (openChart B S hS X.1 U O))) :
    (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g).val.app (op O')
        (Scheme.Modules.pullbackSection (chartSchemeMap g)
          (restrictToChartScheme B S hS X.1 X.2 M U) O O' hle (chartSectionsToRestrict X M U O x)) =
      chartSectionsToRestrict X M V O'
        (M.val.map ((openChartFunctor B S hS X.1 V).map (homOfLE hle) ≫
          openChartRestrict B S hS X.1 g O).op x) := by
  have hk : M.val.map ((openChartFunctor B S hS X.1 V).map (homOfLE hle) ≫
      openChartRestrict B S hS X.1 g O).op x =
        M.val.map ((openChartFunctor B S hS X.1 V).map (homOfLE hle)).op
          (M.val.map (openChartRestrict B S hS X.1 g O).op x) :=
    ConcreteCategory.congr_hom (M.val.map_comp (openChartRestrict B S hS X.1 g O).op
      ((openChartFunctor B S hS X.1 V).map (homOfLE hle)).op) x
  rw [restrictToChartSchemePullbackComparison_pullbackSection,
    restrictToChartSchemePushforwardComparison_chartSectionsToRestrict, hk]
  exact chartSectionsToRestrict_naturality X M V (homOfLE hle) _

/-! ### The comparison is an isomorphism -/

/-- **The chart comparison is bijective on the sections over an affine open lying over an affine
open.**  The sections of the pullback are a base change of the sections over the affine open of
the larger chart scheme, and under the identification of the sections of the chart restrictions
with sections of `M` the comparison is the base change map of `M` along a morphism of affine étale
charts, which is bijective by Stacks 03DX (2). -/
theorem bijective_restrictToChartSchemePullbackComparison_app (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) {O : (chartScheme U).Opens} (hO : IsAffineOpen O)
    {O' : (chartScheme V).Opens} (hO' : IsAffineOpen O') (hle : O' ≤ chartSchemeMap g ⁻¹ᵁ O) :
    Function.Bijective
      ((restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g).val.app (op O')) := by
  have : (restrictToChartScheme B S hS X.1 X.2 M U).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS X M hM U
  let k : openChart B S hS X.1 V O' ⟶ openChart B S hS X.1 U O :=
    (openChartFunctor B S hS X.1 V).map (homOfLE hle) ≫ openChartRestrict B S hS X.1 g O
  let eR : Γ(chartScheme U, O) ≃+* chartRing B S hS X.1 X.2 (openChart B S hS X.1 U O) :=
    ((Scheme.restrictFunctorΓ (X := chartScheme U)).app (op O)).symm.commRingCatIsoToRingEquiv
  let eS : Γ(chartScheme V, O') ≃+* chartRing B S hS X.1 X.2 (openChart B S hS X.1 V O') :=
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).app (op O')).symm.commRingCatIsoToRingEquiv
  let e₁ := AddEquiv.ofBijective (chartSectionsToRestrict X M U O)
    (bijective_chartSectionsToRestrict X M U O)
  let eN := AddEquiv.ofBijective (chartSectionsToRestrict X M V O')
    (bijective_chartSectionsToRestrict X M V O')
  let L := (ConcreteCategory.hom ((restrictToChartSchemePullbackComparison B S hS X.1 X.2 M
    g).val.app (op O'))).toAddMonoidHom.comp (ConcreteCategory.hom
      (affinePullbackSectionsBaseChangeIso (chartSchemeMap g)
        (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle).hom).toAddMonoidHom
  have hring : ∀ r : Γ(chartScheme U, O),
      eS (chartSchemeMap g |>.appLE O O' hle r) = chartRestrict (hF := X.2) k (eR r) := fun r =>
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_homOfLE_comp_morphismRestrict
      (chartSchemeMap g) O O' hle r).symm
  have hsmulU : ∀ (r : Γ(chartScheme U, O)) (x : M.val.obj (op (openChart B S hS X.1 U O))),
      e₁ (eR r • x) = (show (chartScheme U).ringCatSheaf.obj.obj (op O) from r) • e₁ x :=
    chartSectionsToRestrict_smul X M U O
  have hsmulV : ∀ (r : Γ(chartScheme V, O')) (x : M.val.obj (op (openChart B S hS X.1 V O'))),
      eN (eS r • x) = (show (chartScheme V).ringCatSheaf.obj.obj (op O') from r) • eN x :=
    chartSectionsToRestrict_smul X M V O'
  have he₁ : ∀ x, e₁ x = chartSectionsToRestrict X M U O x := fun _ => rfl
  have heN : ∀ x, eN x = chartSectionsToRestrict X M V O' x := fun _ => rfl
  have hLdef : ∀ z, L z = ((restrictToChartSchemePullbackComparison B S hS X.1 X.2 M
      g).val.app (op O')).hom ((ConcreteCategory.hom (affinePullbackSectionsBaseChangeIso
        (chartSchemeMap g) (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle).hom) z) :=
    fun _ => rfl
  have hLbij : Function.Bijective
      (affinePullbackSectionsBaseChangeIso (chartSchemeMap g)
        (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle).hom :=
    ConcreteCategory.bijective_of_isIso _
  clear_value eR eS e₁ eN L
  let := chartAlgebra (hF := X.2) k
  have hL : Function.Bijective L := by
    let : Module Γ(chartScheme U, O) Γ(restrictToChartScheme B S hS X.1 X.2 M U, O) :=
      ((restrictToChartScheme B S hS X.1 X.2 M U).val.obj (op O)).isModule
    refine Stacks.TensorProduct.bijective_extendScalars_of_tmul_eq
      ((chartSchemeMap g).appLE O O' hle) (ModuleCat.of Γ(chartScheme U, O)
        Γ(restrictToChartScheme B S hS X.1 X.2 M U, O))
      eR eS.toAddEquiv e₁.symm eN ?_ ?_ L (sectionsBaseChange M k).toAddMonoidHom ?_
      (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS X.1 X.2 M hM
        (U := openChart B S hS X.1 U O) (V := openChart B S hS X.1 V O') hO hO' k)
    · intro r p
      exact (map_mul eS _ _).trans (congrArg (· * eS p) (hring r))
    · intro r a
      obtain ⟨x, rfl⟩ := e₁.surjective a
      exact (congrArg e₁.symm (hsmulU r x).symm).trans ((e₁.symm_apply_apply _).trans
        (congrArg (eR r • ·) (e₁.symm_apply_apply x).symm))
    · intro p a
      obtain ⟨x, rfl⟩ := e₁.surjective a
      refine (hLdef _).trans ?_
      have hR : eN ((sectionsBaseChange M k).toAddMonoidHom (eS.toAddEquiv p ⊗ₜ e₁.symm (e₁ x))) =
          (show (chartScheme V).ringCatSheaf.obj.obj (op O') from p) • eN (M.val.map k.op x) := by
        rw [AddEquiv.symm_apply_apply]
        exact hsmulV p _
      have hc : ((restrictToChartSchemePullbackComparison B S hS X.1 X.2 M
          g).val.app (op O')).hom (Scheme.Modules.pullbackSection (chartSchemeMap g)
            (restrictToChartScheme B S hS X.1 X.2 M U) O O' hle (e₁ x)) =
          eN (M.val.map k.op x) := by
        rw [he₁]
        exact (restrictToChartSchemePullbackComparison_pullbackSection_chartSectionsToRestrict
          X M g O O' hle x).trans (heN _).symm
      rw [affinePullbackSectionsBaseChangeIso_tmul (chartSchemeMap g)
          (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle p (e₁ x),
        affinePullbackSectionsBaseChangeIso_one_tmul (chartSchemeMap g)
          (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle (e₁ x)]
      refine (Scheme.Modules.Hom.app_smul_val
        (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g) O' p _).trans ?_
      exact (congrArg (fun y => (show (chartScheme V).ringCatSheaf.obj.obj (op O') from p) • y)
        hc).trans hR.symm
  have hfun : ⇑L = ((restrictToChartSchemePullbackComparison B S hS X.1 X.2 M
      g).val.app (op O')).hom ∘ (ConcreteCategory.hom (affinePullbackSectionsBaseChangeIso
        (chartSchemeMap g) (restrictToChartScheme B S hS X.1 X.2 M U) hO hO' hle).hom) :=
    funext hLdef
  rw [hfun] at hL
  exact (Function.Bijective.of_comp_iff _ hLbij).1 hL

/-- **The chart comparison of a quasi-coherent module is an isomorphism.**  For a quasi-coherent
`𝒪_X`-module `M` and a morphism `g : V ⟶ U` of étale charts of `X`, the canonical morphism
`(chartSchemeMap g)^* M|_U ⟶ M|_V` of
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison` is an isomorphism.

Both sides are quasi-coherent, and the affine opens of the smaller chart scheme lying over an
affine open of the larger one cover it; on each of them the comparison is bijective on sections by
`AlgebraicGeometry.Space.bijective_restrictToChartSchemePullbackComparison_app`. -/
theorem isIso_restrictToChartSchemePullbackComparison (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    IsIso (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g) := by
  have : (restrictToChartScheme B S hS X.1 X.2 M U).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS X M hM U
  have : (restrictToChartScheme B S hS X.1 X.2 M V).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS X M hM V
  have := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback (chartSchemeMap g)
    (restrictToChartScheme B S hS X.1 X.2 M U)
  let I := {p : (chartScheme V).affineOpens × (chartScheme U).affineOpens //
    p.1.1 ≤ chartSchemeMap g ⁻¹ᵁ p.2.1}
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover
    (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g) (fun i : I => i.1.1.1) ?_
    (fun i => i.1.1.2) (fun i => bijective_restrictToChartSchemePullbackComparison_app X M hM g
      i.1.2.2 i.1.1.2 i.2)
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
  obtain ⟨O, hO, hxO, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (chartScheme U).isBasis_affineOpens (TopologicalSpace.Opens.mem_top (chartSchemeMap g x))
  obtain ⟨O', hO', hxO', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1
    (chartScheme V).isBasis_affineOpens (U := chartSchemeMap g ⁻¹ᵁ O) hxO
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨O', hO'⟩, ⟨O, hO⟩), hle⟩, hxO'⟩

/-- **The chart comparison of a quasi-coherent module, as an isomorphism**
`(chartSchemeMap g)^* M|_U ≅ M|_V`. -/
noncomputable def restrictToChartSchemePullbackComparisonIso (hM : M.IsQuasicoherentOnSite)
    {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (Scheme.Modules.pullback (chartSchemeMap g)).obj (restrictToChartScheme B S hS X.1 X.2 M U) ≅
      restrictToChartScheme B S hS X.1 X.2 M V :=
  haveI := isIso_restrictToChartSchemePullbackComparison X M hM g
  asIso (restrictToChartSchemePullbackComparison B S hS X.1 X.2 M g)

end Space

end AlgebraicGeometry

end
