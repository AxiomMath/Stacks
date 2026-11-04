module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeTwistTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Composition

/-!
# Relative ampleness along a composition of morphisms of algebraic spaces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, with `Z`
quasi-compact, let `L` be an invertible `𝒪_X`-module ample relative to `f` and `M` an invertible
`𝒪_Y`-module ample relative to `g`. Then `L ⊗ f^* M^{⊗ a}` is ample relative to `g ∘ f` for every
`a` beyond a single threshold. This is the analogue for algebraic spaces of Stacks 0C4K, which
Stacks Remark 088T invokes.

## Main results

* `AlgebraicGeometry.Space.baseChangeModuleTensorIso` and
  `AlgebraicGeometry.Space.nonempty_baseChangeModule_tensorPow`: the reading on a scheme of a
  tensor product, and of a tensor power, of invertible modules.
* `AlgebraicGeometry.Space.exists_threshold_isRelativelyAmple_comp`: **the analogue of
  Stacks 0C4K for algebraic spaces.**

## The route

Choose an affine scheme `W` with a surjective étale morphism to `Z` (Stacks 03H6). Over `W` the
two morphisms become morphisms of schemes `X_W ⟶ Y_W ⟶ W`, because relatively ample modules
live on representable morphisms, and the readings of `L` and `M` on them are relatively ample.
Stacks 0C4K for schemes, `Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp`,
gives a threshold over the quasi-compact `W`; above it the reading of `L ⊗ f^* M^{⊗ a}` on `X_W`
is ample relative to `X_W ⟶ W`, which is the clause of Stacks 0D36 at `W`
(`AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isPullback_of_isRelativelyAmple`), and Stacks
0D36, clause (4) implies clause (1), spreads this from the one chart `W` to every scheme over
`Z`.

## References

* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 088T](https://stacks.math.columbia.edu/tag/088T)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The reading on a scheme of a tensor product of invertible modules is the tensor product of the
readings. -/
def baseChangeModuleTensorIso {X : AlgebraicSpaces B S hS} (A A' : Modules.{u, u} B S hS X.1 X.2)
    (hA : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property A)
    (hA' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property A')
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    baseChangeModule B S hS (A ⊗ A') U p ≅
      Stacks.RelativeVeryAmple.tensorModules _ (baseChangeModule B S hS A U p)
        (baseChangeModule B S hS A' U p) :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso (modulePullbackTensorIso B S hS
        (ObjectProperty.homMk p :
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X) A A') ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS U _ _
      (isQuasicoherentOnSite_modulePullback_of_isInvertible _ A hA)
      (isQuasicoherentOnSite_modulePullback_of_isInvertible _ A' hA')

/-- The reading on a scheme of the tensor power `L^{⊗ d}` of an invertible module is the `d`-th
tensor power of the reading of `L`. -/
theorem nonempty_baseChangeModule_tensorPow {X : AlgebraicSpaces B S hS}
    (A : Modules.{u, u} B S hS X.1 X.2)
    (hA : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property A)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    ∀ d : ℕ,
      haveI := isInvertibleModule_baseChangeModule A hA U p
      Nonempty (baseChangeModule B S hS (tensorPow B S hS A d) U p ≅
        Stacks.Ample.tensorPowModule _ (baseChangeModule B S hS A U p) (d : ℤ)) := by
  intro d
  have := isInvertibleModule_baseChangeModule A hA U p
  induction d using Nat.twoStepInduction with
  | zero => exact ⟨baseChangeUnitModuleIso X U p ≪≫ (Stacks.Ample.tensorPowModuleZeroIso _ _).symm⟩
  | one => exact ⟨(Stacks.Ample.tensorPowModuleOneIso _ (baseChangeModule B S hS A U p)).symm⟩
  | more d _ ih =>
      obtain ⟨e⟩ := ih
      exact ⟨baseChangeModuleTensorIso (tensorPow B S hS A (d + 1)) A
          (@isInvertible_tensorPow B S hS _ A hA (d + 1)) hA U p ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso _ e
          (Stacks.Ample.tensorPowModuleOneIso _ (baseChangeModule B S hS A U p)).symm ≪≫
        Stacks.Ample.tensorPowModuleAddIso _ (baseChangeModule B S hS A U p) ((d + 1 : ℕ) : ℤ) 1 ≪≫
        eqToIso (congrArg (Stacks.Ample.tensorPowModule _ _) (by push_cast; ring))⟩

/-- **The analogue of Stacks 0C4K for algebraic spaces.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces with `Z` quasi-compact, let `L` be an invertible `𝒪_X`-module ample
relative to `f` and `M` an invertible `𝒪_Y`-module ample relative to `g`. Then there is `n` such
that `L ⊗ f^* M^{⊗ a}` is ample relative to `g ∘ f` for every `a ≥ n`. -/
theorem exists_threshold_isRelativelyAmple_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hZ : IsQuasiCompactSpace B S hS Z.1)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hMinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property M)
    (hL : IsRelativelyAmple B S hS f L) (hM : IsRelativelyAmple B S hS g M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a →
      IsRelativelyAmple B S hS (f ≫ g)
        (L ⊗ (modulePullback B S hS f).obj (tensorPow B S hS M a)) := by
  obtain ⟨W, w, hWaff, hws, hwe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z.1 Z.2).mp hZ
  have hwe' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) w := by
    have h := hwe W _ (idEtaleChart B S hS W).2
    change (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (𝟙 _ ≫ w) at h
    rwa [Category.id_comp] at h
  -- the base changes `Y_W ⟶ W` and `X_W ⟶ Y_W`, both schemes
  set UY := hM.1.pullback w
  set qY : UY ⟶ W := hM.1.snd w
  set pY : yoneda.obj UY ⟶ Y.1 := hM.1.fst w
  have sqY : IsPullback pY (yoneda.map qY) g.hom w := hM.1.isPullback w
  set UX := hL.1.pullback pY
  set qX : UX ⟶ UY := hL.1.snd pY
  set pX : yoneda.obj UX ⟶ X.1 := hL.1.fst pY
  have sqX : IsPullback pX (yoneda.map qX) f.hom pY := hL.1.isPullback pY
  have sq : IsPullback pX (yoneda.map (qX ≫ qY)) (f ≫ g).hom w := by
    rw [Functor.map_comp]; exact sqX.paste_vert sqY
  obtain ⟨hinvX, hampX⟩ := hL.2 UY UX pY pX qX sqX
  obtain ⟨hinvY, hampY⟩ := hM.2 W UY w pY qY sqY
  have := hinvX
  have := hinvY
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp
    ((BigFppfOver.toScheme B S hS).map qX) ((BigFppfOver.toScheme B S hS).map qY)
    (baseChangeModule B S hS L UX pX) (baseChangeModule B S hS M UY pY) hampX hampY
  refine ⟨n, fun a ha => ?_⟩
  have hinvPow := @isInvertible_tensorPow B S hS _ M hMinv a
  have hinvPull := isInvertible_modulePullback B S hS f _ (hL := hinvPow)
  have hinvT := @isInvertible_modulesTensorObj B S hS _ L _ hLinv hinvPull
  have h4 : IsAmpleOnBaseChange B S hS (f ≫ g)
      (L ⊗ (modulePullback B S hS f).obj (tensorPow B S hS M a)) W w := ?_
  · exact (isRelativelyAmple_iff_forall_isAmpleOnBaseChange _ _).2 fun T gT =>
      isAmpleOnBaseChange_of_forall_affine hinvT (fun T' hT' gT' =>
        isAmpleOnBaseChange_of_exists_etaleChart hinvT ⟨W, w, hws, hwe', h4⟩ T' hT' gT') T gT
  obtain ⟨e₁⟩ := nonempty_baseChangeModule_tensorPow M hMinv UY pY a
  obtain ⟨e₂⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible (tensorPow B S hS M a)
    hinvPow UY UX pY qX
  have e₃ : baseChangeModule B S hS ((modulePullback B S hS f).obj (tensorPow B S hS M a)) UX pX ≅
      baseChangeModule B S hS (tensorPow B S hS M a) UX (yoneda.map qX ≫ pY) :=
    (baseChangeModuleCompIso B S hS f (tensorPow B S hS M a) UX pX).symm ≪≫
      eqToIso (congrArg (baseChangeModule B S hS (tensorPow B S hS M a) UX) sqX.w)
  have E : baseChangeModule B S hS (L ⊗ (modulePullback B S hS f).obj (tensorPow B S hS M a))
      UX pX ≅ Stacks.AmplePullbackPart1.tensorPullbackPowModule
        ((BigFppfOver.toScheme B S hS).map qX)
        (baseChangeModule B S hS L UX pX) (baseChangeModule B S hS M UY pY) a :=
    baseChangeModuleTensorIso L _ hLinv hinvPull UX pX ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso _ (Iso.refl _)
        (e₃ ≪≫ e₂ ≪≫ (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map qX).toLRSHom.toShHom).mapIso e₁)
  have := isInvertibleModule_baseChangeModule _ hinvT UX pX
  refine isAmpleOnBaseChange_of_isPullback_of_isRelativelyAmple hinvT sq inferInstance
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ E).mpr ?_)
  rw [Functor.map_comp]
  exact hn a ha

end AlgebraicGeometry.Space

end
