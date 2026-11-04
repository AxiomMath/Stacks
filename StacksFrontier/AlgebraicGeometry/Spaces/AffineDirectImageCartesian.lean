module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# The direct image of a quasi-coherent module along an affine morphism

Let `f : X' ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `M` be an `𝒪_{X'}`-module.  Over an étale chart `V` of `X` the direct
image `f_*M` has sections `M(V ×_X X')`.  If `M` is cartesian on affine charts — its sections
over a smaller affine chart are the base change of its sections over a larger one, the criterion
of Stacks 03DX(2) — then so is `f_*M`: for a morphism `V ⟶ W` of affine charts of `X` the charts
`V ×_X X'` and `W ×_X X'` are affine, `V ×_X X' = V ×_W (W ×_X X')`, and the rings of global
functions turn this fibre product of affine schemes into a tensor product, so

`𝒪(V) ⊗_{𝒪(W)} M(W ×_X X') = 𝒪(V ×_X X') ⊗_{𝒪(W ×_X X')} M(W ×_X X') = M(V ×_X X')`.

Since quasi-coherence on the small étale site is the cartesian criterion
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`), the direct image
of a quasi-coherent module along an affine morphism is quasi-coherent.  This is the
quasi-coherence assertion of Stacks 07U8.

## Main results

* `Algebra.IsPushout.bijective_liftBaseChange_of_bijective`: base change along one side of a
  pushout square of rings can be computed along the other.
* `isCartesianOnAffineCharts_smallBaseChangeModulePushforward_of_isAffineHom`:
  the direct image along an affine morphism of a module cartesian on affine charts is cartesian on
  affine charts.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom`
and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom'`: the direct
  image of a quasi-coherent module along an affine morphism is quasi-coherent, for the direct
  image along base change of charts and for the direct image of Stacks 03LU.

The scheme-target hypothesis `AlgebraicGeometry.Space.SchemeTargetAffinePushforwardQuasicoherent`
of `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isAffineHom` is
`AlgebraicGeometry.Space.schemeTargetAffinePushforwardQuasicoherent`, proved in
`StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional`.

## References

* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

/-- Base change along one side of a pushout square of rings can be computed along the other
side: if `Bb ⊗_A N → N'` is bijective and `R → Sr, R → A, Sr → Bb, A → Bb` is a pushout square,
then so is `Sr ⊗_R N → N'`. -/
theorem Algebra.IsPushout.bijective_liftBaseChange_of_bijective
    {R Sr A Bb N N' : Type*} [CommRing R] [CommRing Sr] [CommRing A] [CommRing Bb]
    [Algebra R Sr] [Algebra R A] [Algebra A Bb] [Algebra Sr Bb] [Algebra R Bb]
    [IsScalarTower R A Bb] [IsScalarTower R Sr Bb] [Algebra.IsPushout R Sr A Bb]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [AddCommGroup N'] [Module R N'] [Module Sr N'] [Module A N'] [Module Bb N']
    [IsScalarTower R Sr N'] [IsScalarTower A Bb N'] [IsScalarTower Sr Bb N']
    (φ : N →ₗ[R] N') (ψ : N →ₗ[A] N') (hφψ : ∀ x, φ x = ψ x)
    (hψ : Function.Bijective (LinearMap.liftBaseChange Bb ψ)) :
    Function.Bijective (LinearMap.liftBaseChange Sr φ) := by
  have h : LinearMap.liftBaseChange Sr φ = ((LinearMap.liftBaseChange Bb ψ).restrictScalars Sr) ∘ₗ
      (Algebra.IsPushout.cancelBaseChange R Sr A Bb N).symm.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun s x => by
      simp [hφψ, algebraMap_smul]
  rw [h]
  exact hψ.comp (Algebra.IsPushout.cancelBaseChange R Sr A Bb N).symm.bijective

/-- A transport form of `Algebra.IsPushout.bijective_liftBaseChange_of_bijective`: the source
and target of the `R`-linear map are identified additively with an `A`-module and a
`Bb`-module, compatibly with the scalar actions. -/
theorem Algebra.IsPushout.bijective_liftBaseChange_of_addEquiv
    {R Sr A Bb : Type*} [CommRing R] [CommRing Sr] [CommRing A] [CommRing Bb]
    [Algebra R Sr] [Algebra R A] [Algebra A Bb] [Algebra Sr Bb] [Algebra R Bb]
    [IsScalarTower R A Bb] [IsScalarTower R Sr Bb] [Algebra.IsPushout R Sr A Bb]
    {N N' P₁ P₂ : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    [Module Bb N'] [IsScalarTower A Bb N']
    [AddCommGroup P₁] [iP₁ : Module R P₁] [AddCommGroup P₂] [iR₂ : Module R P₂]
    [iS₂ : Module Sr P₂] [iT₂ : IsScalarTower R Sr P₂]
    (ψ : N →ₗ[A] N') (hψ : Function.Bijective (LinearMap.liftBaseChange Bb ψ))
    (φ : P₁ →ₗ[R] P₂) (e₁ : P₁ ≃+ N) (e₂ : P₂ ≃+ N')
    (h₁ : ∀ (r : R) (p : P₁), e₁ (r • p) = algebraMap R A r • e₁ p)
    (h₂ : ∀ (s : Sr) (p : P₂), e₂ (s • p) = algebraMap Sr Bb s • e₂ p)
    (hφ : ∀ p, e₂ (φ p) = ψ (e₁ p)) :
    Function.Bijective (LinearMap.liftBaseChange Sr φ) := by
  let : Module R N := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Sr N' := Module.compHom N' (algebraMap Sr Bb)
  have : IsScalarTower Sr Bb N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module R N' := Module.compHom N' (algebraMap R Bb)
  have : IsScalarTower R Sr N' := IsScalarTower.of_algebraMap_smul fun r x => by
    show algebraMap Sr Bb (algebraMap R Sr r) • x = algebraMap R Bb r • x
    rw [IsScalarTower.algebraMap_apply R Sr Bb r]
  have : IsScalarTower R A N' := IsScalarTower.of_algebraMap_smul fun r x => by
    rw [← algebraMap_smul Bb (algebraMap R A r) x, ← IsScalarTower.algebraMap_apply]
    rfl
  let E₁ : P₁ ≃ₗ[R] N := { e₁ with map_smul' := h₁ }
  let E₂ : P₂ ≃ₗ[Sr] N' := { e₂ with map_smul' := h₂ }
  let φ' : N →ₗ[R] N' := ψ.restrictScalars R
  have h := Algebra.IsPushout.bijective_liftBaseChange_of_bijective (R := R) (Sr := Sr) (A := A)
      (Bb := Bb) φ' ψ (fun _ => rfl) hψ
  let C := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Sr Sr) E₁
  have hfun : LinearMap.liftBaseChange Sr φ = E₂.symm.toLinearMap ∘ₗ
      LinearMap.liftBaseChange Sr φ' ∘ₗ C.toLinearMap :=
    TensorProduct.AlgebraTensorModule.ext fun s x => E₂.injective <| by
      simp only [C, LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.apply_symm_apply, map_smul]
      change s • e₂ (φ x) = s • ψ (e₁ x)
      rw [hφ]
  rw [hfun]
  exact E₂.symm.bijective.comp (h.comp C.bijective)

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

/-- **The base change comparison of a direct image along base change of charts.** For a
representable `f : X' ⟶ X` and a morphism `k : V ⟶ W` of affine étale charts of `X` with
`W ×_X X'` affine, the base change comparison of `f_*M` over `k` is bijective as soon as that of
`M` over the base-changed morphism `V ×_X X' ⟶ W ×_X X'` is.

The rings of global functions of the four charts form a pushout square
(`AlgebraicGeometry.Space.isPushout_appTop_representablePullback`), so
`𝒪(V) ⊗_{𝒪(W)} M(W ×_X X') ≅ 𝒪(V ×_X X') ⊗_{𝒪(W ×_X X')} M(W ×_X X')`. -/
theorem bijective_sectionsBaseChange_smallBaseChangeModulePushforward_of_isAffineHom
    (f : X' ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
    (M : Modules.{u, m} B S hS X'.1 X'.2) {V W : SmallEtale B S hS X.1} (k : V ⟶ W)
    (hXW : IsAffine ((BigFppfOver.toScheme B S hS).obj (hf.pullback W.1.hom)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (hM : Function.Bijective (sectionsBaseChange M ((smallBaseChange B S hS f hf).map k))) :
    Function.Bijective (sectionsBaseChange (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) k) := by
  let G := smallBaseChange B S hS f hf
  let sW : chartRing B S hS X.1 X.2 W →+* chartRing B S hS X'.1 X'.2 (G.obj W) :=
    ((smallBaseChangeSharp B S hS f hf).hom.app (op W)).hom
  let sV : chartRing B S hS X.1 X.2 V →+* chartRing B S hS X'.1 X'.2 (G.obj V) :=
    ((smallBaseChangeSharp B S hS f hf).hom.app (op V)).hom
  let : Algebra (chartRing B S hS X.1 X.2 W) (chartRing B S hS X.1 X.2 V) := chartAlgebra k
  let : Algebra (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 (G.obj W)) :=
    sW.toAlgebra
  let : Algebra (chartRing B S hS X'.1 X'.2 (G.obj W)) (chartRing B S hS X'.1 X'.2 (G.obj V)) :=
    chartAlgebra (G.map k)
  let : Algebra (chartRing B S hS X.1 X.2 V) (chartRing B S hS X'.1 X'.2 (G.obj V)) :=
    sV.toAlgebra
  let : Algebra (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 (G.obj V)) :=
    (sV.comp (chartRestrict k)).toAlgebra
  have hsq : (chartRestrict (G.map k)).comp sW = sV.comp (chartRestrict k) :=
    RingHom.ext fun x => ConcreteCategory.congr_hom
      ((smallBaseChangeSharp B S hS f hf).hom.naturality k.op).symm x
  have : IsScalarTower (chartRing B S hS X.1 X.2 W) (chartRing B S hS X'.1 X'.2 (G.obj W))
      (chartRing B S hS X'.1 X'.2 (G.obj V)) :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hsq r).symm
  have : IsScalarTower (chartRing B S hS X.1 X.2 W) (chartRing B S hS X.1 X.2 V)
      (chartRing B S hS X'.1 X'.2 (G.obj V)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsPushout (chartRing B S hS X.1 X.2 W) (chartRing B S hS X.1 X.2 V)
      (chartRing B S hS X'.1 X'.2 (G.obj W)) (chartRing B S hS X'.1 X'.2 (G.obj V)) := by
    refine (CommRingCat.isPushout_iff_isPushout.1 ?_).symm
    exact (isPushout_appTop_representablePullback B S hS f hf k hXW hV hW)
  let : Module (chartRing B S hS X.1 X.2 W)
      (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op W)) :=
    (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op W)).isModule
  let : Module (chartRing B S hS X.1 X.2 V)
      (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op V)) :=
    (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op V)).isModule
  let : Module (chartRing B S hS X.1 X.2 W)
      (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op V)) :=
    chartSectionsModule (F := X.1) (hF := X.2) ((smallBaseChangeModulePushforward B S hS f hf).obj
        M) k
  have : IsScalarTower (chartRing B S hS X.1 X.2 W) (chartRing B S hS X.1 X.2 V)
      (((smallBaseChangeModulePushforward B S hS f hf).obj M).val.obj (op V)) :=
    chartSections_isScalarTower (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) k
  let : Module (chartRing B S hS X'.1 X'.2 (G.obj W)) (M.val.obj (op (G.obj V))) :=
    chartSectionsModule M (G.map k)
  have : IsScalarTower (chartRing B S hS X'.1 X'.2 (G.obj W))
      (chartRing B S hS X'.1 X'.2 (G.obj V)) (M.val.obj (op (G.obj V))) :=
    chartSections_isScalarTower M (G.map k)
  exact Algebra.IsPushout.bijective_liftBaseChange_of_addEquiv (chartRestrictLinear M (G.map k)) hM
    (iR₂ := chartSectionsModule (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) k)
    (iT₂ := chartSections_isScalarTower (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) k)
    (chartRestrictLinear (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) k) (AddEquiv.refl _) (AddEquiv.refl _)
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

/-- **The direct image of a module cartesian on affine charts along an affine morphism is
cartesian on affine charts.** -/
theorem isCartesianOnAffineCharts_smallBaseChangeModulePushforward_of_isAffineHom
    (f : X' ⟶ X) (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    {M : Modules.{u, m} B S hS X'.1 X'.2} (hM : IsCartesianOnAffineCharts M) :
    IsCartesianOnAffineCharts (F := X.1) (hF := X.2)
      ((smallBaseChangeModulePushforward B S hS f hf).obj M) := fun W V hW hV k =>
  bijective_sectionsBaseChange_smallBaseChangeModulePushforward_of_isAffineHom f hf M k
    (isAffine_smallBaseChange_obj B S hS f hf haff W hW) hV hW
    (hM _ _ (isAffine_smallBaseChange_obj B S hS f hf haff W hW)
      (isAffine_smallBaseChange_obj B S hS f hf haff V hV) _)

/-- **The direct image of a quasi-coherent module along an affine morphism is quasi-coherent**,
for the direct image along base change of charts. -/
theorem isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom
    (f : X' ⟶ X) (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    {M : Modules.{u, u} B S hS X'.1 X'.2} (hM : M.IsQuasicoherentOnSite) :
    ((smallBaseChangeModulePushforward B S hS f hf).obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_smallBaseChangeModulePushforward_of_isAffineHom f hf haff
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X'.1 X'.2 M hM))

/-- **The quasi-coherence assertion of Stacks 07U8.** The direct image of Stacks 03LU of a
quasi-coherent module along an affine morphism of algebraic spaces is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePushforward_of_isAffineHom' (f : X' ⟶ X)
    (haff : IsAffineHom B S hS f.hom) {M : Modules.{u, u} B S hS X'.1 X'.2}
    (hM : M.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS f).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePushforwardChartIso B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff)).app M).symm
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom f _ haff hM)

end AlgebraicGeometry.Space

end
