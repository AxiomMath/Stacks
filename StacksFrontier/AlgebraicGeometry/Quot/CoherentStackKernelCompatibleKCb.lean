module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentN1b
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackKernelRetraction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTangentDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ModuleTransposeSets
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.TransposeCompatible

/-!
# The kernel map of the pullback unit is the map of coefficient modules

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}`, `h : T ⟶ T'`, `h₂ : T ⟶ T'₂` split first order
thickenings with retractions `r`, `r₂ = g ≫ r`, and `g : T'₂ ⟶ T'` a morphism under `T`. Given
the ideal-square compatibility of the map `λ` of pulled-back ideals of the relative squares, every
map `τ₁` of kernels making the kernel square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` commute is, read
on `X_T` through the retractions, the map `λ_g` of coefficient modules. At the test thickenings
`Spec A ⊂ Spec A[M]`, `Spec A ⊂ Spec A[N]` this gives the naturality of the difference from the
trivial lift.

## Main results

* `CoherentSituation.thickeningLiftPullbackKernel_eq_of_relativeIdealSquare`:
  the kernel map of the pullback unit, read on `X_T`, is the map of coefficient modules.
* `CoherentSituation.tangentLiftDifferencePullback_of_testRelativeIdealSquareCompatible`:
  the difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`, given the
  ideal-square compatibility at the test maps.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe u

namespace Deformation.ToposThickening.ThickeningTargetMorphism

open AlgebraicGeometry (RingedTopos RingedToposHom)

universe vX uX vY₁ uY₁ vY₂ uY₂ w

variable {X : RingedTopos.{vX, uX, w}} {Y₁ : RingedTopos.{vY₁, uY₁, w}}
  {Y₂ : RingedTopos.{vY₂, uY₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}] in
/-- `D.restrictIdealTensorMapOver` at `θ = E⁻¹_F : i₁_*F ⟶ Ψ₀ i₂_*F` is the restriction along `i₁`
of `I₁ ⊗ E⁻¹_F` followed by `D.idealTensorMap`, composed with the inverse of `D.restrictIso`. -/
theorem restrictIdealTensorMapOver_inv_app_eq
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    D.restrictIdealTensorMapOver hi₁ hi₂ (F₁ := (thickenedModulesFunctor i₁).obj F)
      (F₂ := (thickenedModulesFunctor i₂).obj F) (E.inv.app F) =
    (structureRestrict i₁).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map (E.inv.app F) ≫
            D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F)) ≫
        (D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
          ((thickenedModulesFunctor i₂).obj F)).obj hi₂.I)).inv := rfl

end Deformation.ToposThickening.ThickeningTargetMorphism

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- `G.map f = r` read at other spellings of the functor and of the objects. -/
theorem Functor.map_eq_of_heq {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G G' : C ⥤ D} (hG : G = G') {X Y X' Y' : C} (hX : X = X') (hY : Y = Y') (f : X ⟶ Y)
    (f' : X' ⟶ Y') (hf : HEq f f') (r : G.obj X ⟶ G.obj Y) (r' : G'.obj X' ⟶ G'.obj Y')
    (hr : HEq r r') (h : G.map f = r) : G'.map f' = r' := by
  subst hG hX hY
  cases hf
  cases hr
  exact h

/-- A component of a natural transformation at other spellings of the functors and the object. -/
theorem NatTrans.app_heq_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G F' G' : C ⥤ D} (hF : F = F') (hG : G = G') {α : F ⟶ G} {α' : F' ⟶ G'}
    (hα : HEq α α') {X X' : C} (hX : X = X') : HEq (α.app X) (α'.app X') := by
  subst hF hG hX
  cases hα
  rfl

end CategoryTheory


namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]


section KernelIso

variable {T₀ : SchemesOver D.Y} (k : ξ.T ⟶ T₀) (c : T₀ ⟶ ξ.T) (hkc : k ≫ c = 𝟙 ξ.T)
  (hk : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map k.left))
  (hflk : IsFlat B S hS (D.projection T₀).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left)] in
/-- The kernel identification `I ⊗ i_*𝒢 ≅ i_*(𝒢 ⊗ f^*𝒥)` given by
`thickeningKernelThickenedIso k hk hflk` is `ThickeningTargetMorphism.kernelThickenedIso` for the
relative first order thickening of `k` and the pulled-back ideal of its relative square. -/
theorem thickeningKernelThickenedIso_eq_kernelThickenedIso :
    thickeningKernelThickenedIso k hk hflk =
    Deformation.ToposThickening.ThickeningTargetMorphism.kernelThickenedIso
      (D.relativeSquareSituation.relativeMapFirstOrderThickening k hk) ξ.F
      (basePullbackIdeal.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (D.relativeSquareSituation.relativeSquareThickening k)
        (D.relativeSquareSituation.relativeSquareLeft k)
        (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening k hk))
      (basePullbackIdealIsoIdeal
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap k))
        (D.relativeSquareSituation.relativeSquareThickening k)
        (D.relativeSquareSituation.relativeSquareLeft k)
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T₀)))
        (D.relativeSquareSituation.relativeMapFirstOrderThickening k hk)
        (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening k hk)
        (D.relativeSquareSituation.relativeSquare_comm k)
        (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T₀)
          hflk)
        (D.relativeSquareSituation.isStrict_relativeSquare k hk)) := rfl

end KernelIso

/-- **The kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, read on `X_T`, is `λ_g`**, given the
ideal-square compatibility of `λ` for the relative squares of `h`, `h₂`: any map `τ₁` of kernels
making the kernel square commute is carried by `ρ_*` and `ρ_*(X_g)_* ≅ ρ₂_*` to the coefficient
map, through the identifications `ρ_*(I ⊗ i_*𝒢) ≅ 𝒢 ⊗ f_T^*𝒥` of the kernels. -/
theorem thickeningLiftPullbackKernel_eq_of_relativeIdealSquare
    (H : RelativeIdealSquareCompatible h h₂ g hg hh hh₂ hfl hfl₂
      (relativeSquareIdealMap h h₂ g hg hh hh₂))
    (L : D.ThickeningLift ξ h)
    (τ₁ : (thickeningLiftShortComplex h hh L).X₁ ⟶
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁)
    (hτ : (thickeningLiftShortComplex h hh L).f ≫ thickeningLiftPullbackUnit hh hh₂ g hg L =
      τ₁ ≫ (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).f) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₁ ≫
        (retractionPushforwardCompIso g hgr).hom.app
          (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁ =
      (thickeningLiftKernelIso hr hh hfl L).hom ≫ thickeningCoefficientMap g hg hh hh₂ ≫
        (thickeningLiftKernelIso hr₂ hh₂ hfl₂ (L.pullback g hg)).inv := by
  have := preservesFiniteLimits_retraction_pushforwardModules (D := D) g
  have : Mono (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).f :=
    (yonedaExtension_shortExact (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))).mono_f
  have hτM₀ := (cancel_mono ((smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
      (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).f)).1
    (hτ.symm.trans (thickeningLiftExtension_f_comp_pullbackUnit_eq_comp hh hh₂ g hg L))
  have hτM := hτM₀.trans
    (Deformation.ToposThickening.ThickeningTargetMorphism.restrictIdealTensorMapOver_inv_app_eq
      (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
      (smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)) ξ.F)
  subst hτM
  have hl := sheafTensor_map_relativeSquareIdealMap hh hh₂ g hg
  have key := AlgebraicGeometry.Space.retraction_map_idealTensorMap_comp_eq
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_of_comp_eq g hg)
    (relativeMap_comp_of_eq_comp g hgr) (relativeMap_comp_relativeMap_retraction h r hr)
    (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T') hfl)
    (D.relativeSquareSituation.isStrict_relativeSquare h hh)
    (D.relativeSquareSituation.relativeSquareThickening h₂)
    (D.relativeSquareSituation.relativeSquareLeft h₂)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₂)))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeSquare_comm h₂)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T'₂) hfl₂)
    (D.relativeSquareSituation.isStrict_relativeSquare h₂ hh₂)
    ξ.F (relativeSquareIdealMap h h₂ g hg hh hh₂) H
    (thickeningCoefficientIso h hh).hom (thickeningCoefficientMap g hg hh hh₂)
    (thickeningCoefficientIso h₂ hh₂).inv
    (CategoryTheory.Functor.map_eq_of_heq (by rfl)
      (X := D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh)
      (Y := D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂) (by rfl) (by rfl)
      (relativeSquareIdealMap h h₂ g hg hh hh₂) _ (by exact HEq.rfl) _ _ (by exact HEq.rfl) hl)
  refine eq_of_heq ((?_ : HEq _ _).trans ((heq_of_eq key).trans ?_))
  · refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl)
      (CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl) (by exact HEq.rfl))
      (CategoryTheory.NatTrans.app_heq_app (by rfl) (by rfl) (by exact HEq.rfl) (by rfl))
  · have e₁ := (congrArg Iso.hom (thickeningKernelRetractionIso.eq_1 h r hr hh hfl)).trans
      ((Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·)
        ((Functor.mapIso_hom _ _).trans (congrArg (thickenedRetraction h r).map
          (congrArg Iso.hom (thickeningKernelThickenedIso_eq_kernelThickenedIso h hh hfl))))
        ((Iso.trans_hom _ _).trans (congrArg (· ≫ _) (Iso.app_hom _ _)))))
    have e₂ := (congrArg Iso.inv (thickeningKernelRetractionIso.eq_1 h₂ r₂ hr₂ hh₂ hfl₂)).trans
      ((Iso.trans_inv _ _).trans (congrArg₂ (· ≫ ·)
        ((Iso.trans_inv _ _).trans (congrArg (_ ≫ ·) (Iso.app_inv _ _)))
        ((Functor.mapIso_inv _ _).trans (congrArg (thickenedRetraction h₂ r₂).map
          (congrArg Iso.inv (thickeningKernelThickenedIso_eq_kernelThickenedIso h₂ hh₂ hfl₂))))))
    refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) ?_ ?_
    · refine HEq.trans ?_ ((heq_of_eq e₁).symm.trans (by exact HEq.rfl))
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl)
        (CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl)
          (CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl) (by exact HEq.rfl))) ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl)
        (CategoryTheory.NatTrans.app_heq_app (by rfl) (by rfl) (by exact HEq.rfl) (by rfl)) HEq.rfl
    · refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine HEq.trans ?_ ((heq_of_eq e₂).symm.trans (by exact HEq.rfl))
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) ?_
        (CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl)
          (CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl) (by exact HEq.rfl)))
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl
        (CategoryTheory.NatTrans.app_heq_app (by rfl) (by rfl) (by exact HEq.rfl) (by rfl))

section Test

variable (hY : IsTerminal D.Y) {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] (hflat : IsFlat B S hS D.f.hom)

/-- Given the ideal-square compatibility `hH` at the test maps, the difference from the trivial
lift is natural along `Spec A[N] ⟶ Spec A[M]`. -/
theorem tangentLiftDifferencePullback_of_testRelativeIdealSquareCompatible
    {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
    (hH : D.TestRelativeIdealSquareCompatible hY hflat hx
      (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS) (hA := hA)
        f)) :
    TangentLiftDifferencePullback hY hx hflat f :=
  tangentLiftDifferencePullback_of_thickeningTestKernel hY hx hflat f fun L τ₁ hτ =>
    thickeningLiftPullbackKernel_eq_of_relativeIdealSquare _ _ _ _
      (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
      (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
      (thickeningTestSchemeMap_comp_thickeningTestRetraction hY hx f) _ _ hH L τ₁ hτ

end Test

end AlgebraicGeometry.Space.CoherentSituation

end
