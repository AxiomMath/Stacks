module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingSpectrum
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional

/-!
# The stalk of a higher direct image at a geometric point

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`
with `Y` locally Noetherian, `F` a quasi-coherent `𝒪_X`-module and `ȳ` a geometric point of `Y`.
Let `A` be the model in `Type u` of the étale local ring `𝒪_{Y, ȳ}`
(`AlgebraicGeometry.Space.etaleLocalRingModel`) and `X' = Spec A ×_Y X` the base change of `f`
to it, with `F'` the pullback of `F`.  Then

`(R ᵖ f_* F)_ȳ ≅ H ᵖ (X', F')`

as `A`-modules: flat base change along `Spec 𝒪_{Y, ȳ} ⟶ Y` identifies the stalk with global
cohomology over the strictly henselian local scheme.

The isomorphism is built over the chosen affine étale neighbourhood `U₀` of `ȳ`.  There
`G = R ᵖ f_* F` is quasi-coherent (Stacks 0720), so its stalk at `ȳ` is
`𝒪_{Y, ȳ} ⊗_{𝒪(U₀)} G(U₀)` (`AlgebraicGeometry.Space.geometricModuleStalkTensorEquiv`); its
sections over `U₀` are `H ᵖ (U₀ ×_Y X, F)` as `𝒪(U₀)`-modules (Stacks 08EX,
`AlgebraicGeometry.Space.chartSectionsHigherDirectImageLinearEquiv`); and since
`Spec A ⟶ U₀` is flat, `A ⊗_{𝒪(U₀)} H ᵖ (U₀ ×_Y X, F) ≅ H ᵖ (X', F')` by Stacks 073K,
part (2) (`AlgebraicGeometry.Space.cohomologyFlatBaseChangeEquiv`).

## Main definitions

* `AlgebraicGeometry.Space.geometricBaseChange`: the base change
  `X' = Spec A ×_{U₀} (U₀ ×_Y X)` of `f` to the spectrum of the étale local ring.
* `AlgebraicGeometry.Space.geometricBaseChangeModule`: the pullback `F'` of `F` to `X'`.
* `AlgebraicGeometry.Space.geometricBaseChangeRingHom`: the action of `A` on `X'`.
* `AlgebraicGeometry.Space.etaleLocalRingSpecFunctionsEquiv`: `Γ(Spec A, 𝒪) ≅ 𝒪_{Y, ȳ}`.
* `AlgebraicGeometry.Space.geometricStalkCohomologyLinearEquiv`: `(R ᵖ f_* F)_ȳ ≅ H ᵖ (X', F')`
  as modules over `Γ(Spec A, 𝒪)`.
* `ModuleCat.restrictScalarsSemilinearCompositeEquiv`: a composite of linear and semilinear
  equivalences as a linear equivalence onto a restriction of scalars.

## Implementation notes

`AlgebraicGeometry.Space.etaleLocalRingSpecFunctionsEquiv` is irreducible, and the linear
structure of the composite is assembled by the generic
`ModuleCat.restrictScalarsSemilinearCompositeEquiv` rather than proved on the concrete terms:
checking the semilinearity there makes the elaborator compare the ring structures on the
functions of `Spec A` through `Scheme.ΓSpecIso`, which does not terminate in practice.

## References

* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 08EX](https://stacks.math.columbia.edu/tag/08EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (y : GeometricPoint B S hS Y.1)
  (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))

/-- The projection `U₀ ×_Y X ⟶ U₀` over the chosen affine neighbourhood `U₀` of `ȳ`. -/
abbrev geometricChartProjection :
    chartBaseChangeSpace B S hS f (affineEtaleNeighborhood Y y).chart ⟶
      schemeSpace ((SmallEtale.toOver B S hS Y.1).obj (affineEtaleNeighborhood Y y).chart) :=
  chartBaseChangeProjection B S hS f (affineEtaleNeighborhood Y y).chart

/-- **The base change `X' = Spec 𝒪_{Y, ȳ} ×_Y X`**, formed as `Spec A ×_{U₀} (U₀ ×_Y X)` over the
chosen affine neighbourhood `U₀` of `ȳ`. -/
abbrev geometricBaseChange : AlgebraicSpaces B S hS :=
  pullback (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY)) (geometricChartProjection f y)

/-- The pullback `F'` of an `𝒪_X`-module to `X' = Spec 𝒪_{Y, ȳ} ×_Y X`. -/
abbrev geometricBaseChangeModule (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS (geometricBaseChange f y hY).1 (geometricBaseChange f y hY).2 :=
  (modulePullback B S hS (pullback.snd _ _)).obj
    ((chartBaseChangeModulePullback B S hS f (affineEtaleNeighborhood Y y).chart).obj F)

/-- The action of the model `A` of `𝒪_{Y, ȳ}` on the functions of `X' = Spec A ×_Y X`. -/
abbrev geometricBaseChangeRingHom :
    etaleLocalRingModel Y y →+* GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (geometricBaseChange f y hY).1
        (geometricBaseChange f y hY).2).O) :=
  (baseFunctionsToGlobalSections B S hS (pullback.fst _ _ :
    geometricBaseChange f y hY ⟶ schemeSpace (etaleLocalRingSpecObject (y := y) hY))).comp
    (Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).inv.hom

/-- The functions on `Spec A` are the étale local ring `𝒪_{Y, ȳ}`. -/
noncomputable irreducible_def etaleLocalRingSpecFunctionsEquiv :
    Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤) ≃+*
      etaleLocalRing B S hS Y.1 y :=
  (Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).commRingCatIsoToRingEquiv.trans
    (etaleLocalRingModelEquiv Y y)

/-- Under `etaleLocalRingSpecFunctionsEquiv`, the pullback of a function `a` on the chosen affine
étale neighbourhood of `ȳ` to `Spec A` is the germ of `a` in the étale local ring `𝒪_{Y, ȳ}`. -/
theorem etaleLocalRingSpecFunctionsEquiv_appTop
    (a : Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS Y.1).obj (affineEtaleNeighborhood Y y).chart), ⊤)) :
    etaleLocalRingSpecFunctionsEquiv y hY
        (((BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY)).appTop a) =
      etaleLocalRingGerm B S hS Y.1 y (op (affineEtaleNeighborhood Y y)) a := by
  rw [etaleLocalRingSpecFunctionsEquiv_def]
  change etaleLocalRingModelEquiv Y y ((Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).hom
    ((etaleLocalRingSpecToChartScheme Y y).appTop a)) = _
  rw [etaleLocalRingSpecToChartScheme_appTop, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply, etaleLocalRingModelEquiv_germ]

/-- `R ⊗_K M ≃ R' ⊗_K M` along an isomorphism `R ≃ R'` of `K`-algebras is semilinear for the
left actions. -/
theorem _root_.AlgEquiv.rTensor_smul {K R R' M : Type*} [CommRing K] [CommRing R] [CommRing R']
    [Algebra K R] [Algebra K R'] [AddCommGroup M] [Module K M] (θ : R ≃ₐ[K] R') (r : R)
    (z : R ⊗[K] M) :
    θ.toLinearEquiv.rTensor M (r • z) = θ r • θ.toLinearEquiv.rTensor M z := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]
  | tmul s m =>
    rw [TensorProduct.smul_tmul', LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul,
      TensorProduct.smul_tmul', AlgEquiv.toLinearEquiv_apply, AlgEquiv.toLinearEquiv_apply,
      smul_eq_mul, smul_eq_mul, map_mul]

/-- **A composite `e₁ ∘ e₂ ∘ e₃ ∘ e₄⁻¹` of an `R`-linear, a `θ`-semilinear and two `O`-linear
equivalences, as an `R`-linear equivalence** from an `R`-module `N` onto the restriction of
scalars along `θ` of an `O`-module `M`.  The module structures on the intermediate types are
read off the equivalences. -/
def _root_.ModuleCat.restrictScalarsSemilinearCompositeEquiv {R O P Q Q' : Type*} [CommRing R]
    [CommRing O] (θ : R →+* O) {N : ModuleCat.{v} R} {M : ModuleCat.{v} O} {_ : AddCommGroup P}
    {_ : Module R P} {_ : AddCommGroup Q} {_ : Module O Q} {_ : AddCommGroup Q'} {_ : Module O Q'}
    (e₄ : P ≃ₗ[R] N) (e₃ : P ≃+ Q) (h₃ : ∀ (r : R) (x : P), e₃ (r • x) = θ r • e₃ x)
    (e₂ : Q ≃ₗ[O] Q') (e₁ : Q' ≃ₗ[O] M) :
    N ≃ₗ[R] (ModuleCat.restrictScalars θ).obj M :=
  AddEquiv.toLinearEquiv (M₂ := (ModuleCat.restrictScalars θ).obj M)
    (e₄.symm.toAddEquiv.trans (e₃.trans (e₂.toAddEquiv.trans e₁.toAddEquiv))) fun r z => by
      change e₁ (e₂ (e₃ (e₄.symm (r • z)))) = θ r • e₁ (e₂ (e₃ (e₄.symm z)))
      rw [map_smul e₄.symm, h₃, map_smul, map_smul]

variable {f}

/-- **`(R ᵖ f_* F)_ȳ ≅ H ᵖ (X', F')`**, for `f` quasi-compact and quasi-separated, `Y` locally
Noetherian and `F` quasi-coherent, where `X' = Spec 𝒪_{Y, ȳ} ×_Y X` and `F'` is the pullback of
`F`, as modules over `Γ(Spec 𝒪_{Y, ȳ}, 𝒪)`, the stalk being a module through
`Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ≅ 𝒪_{Y, ȳ}` (`AlgebraicGeometry.Space.etaleLocalRingSpecFunctionsEquiv`).
It is the composite of the base change `𝒪_{Y, ȳ} ⊗_{𝒪(U₀)} G(U₀) ≅ G_ȳ` for the quasi-coherent
`G = R ᵖ f_* F`, of Stacks 08EX over `U₀`, of `Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ≅ 𝒪_{Y, ȳ}` and of the flat
base change of Stacks 073K, part (2), along `Spec 𝒪_{Y, ȳ} ⟶ U₀`. -/
def geometricStalkCohomologyLinearEquiv (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (p : ℕ) :
    cohomologyRes (baseFunctionsToGlobalSections B S hS
        (pullback.fst (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY))
          (geometricChartProjection f y))) p
        ((modulePullback B S hS
          (pullback.snd (schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY))
            (geometricChartProjection f y))).obj
          ((chartBaseChangeModulePullback B S hS f (affineEtaleNeighborhood Y y).chart).obj F))
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)]
      (ModuleCat.restrictScalars (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom).obj
        (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)) :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let N := affineEtaleNeighborhood Y y
  let V := (SmallEtale.toOver B S hS Y.1).obj N.chart
  let G := moduleHigherPushforward B S hS f F p
  have hG : G.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f
      hfqc hfqs F p
  haveI : ((chartBaseChangeModulePullback B S hS f N.chart).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS (chartBaseChangeInclusion B S hS f N.chart)
      (isEtale_chartBaseChangeInclusion B S hS f N.chart) F inferInstance
  letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (etaleLocalRing B S hS Y.1 y) :=
    etaleLocalRingChartAlgebra Y y N
  letI :=
    ((BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY)).appTop.hom.toAlgebra
  let θ : Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤) ≃ₐ[
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] etaleLocalRing B S hS Y.1 y :=
    AlgEquiv.ofRingEquiv (f := etaleLocalRingSpecFunctionsEquiv y hY)
      fun a => etaleLocalRingSpecFunctionsEquiv_appTop y hY a
  let H := cohomologyRes (baseFunctionsToGlobalSections B S hS (geometricChartProjection f y)) p
    ((chartBaseChangeModulePullback B S hS f N.chart).obj F)
  let e₁ := geometricModuleStalkTensorEquiv Y y G hG N (isAffine_affineEtaleNeighborhood Y y)
  let e₂ := LinearEquiv.baseChange (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    (etaleLocalRing B S hS Y.1 y) _ _
    (chartSectionsHigherDirectImageLinearEquiv f hfqc hfqs F N.chart
      (isAffine_affineEtaleNeighborhood Y y) p)
  let e₃ := θ.toLinearEquiv.rTensor H
  let e₄ := cohomologyFlatBaseChangeEquiv B S hS (etaleLocalRingSpecToChart (y := y) hY)
    (geometricChartProjection f y)
    ((chartBaseChangeModulePullback B S hS f N.chart).obj F)
    (isQuasiCompact_chartBaseChangeProjection B S hS f N.chart hfqc)
    (isQuasiSeparated_chartBaseChangeProjection B S hS f N.chart hfqs) inferInstance p
  ModuleCat.restrictScalarsSemilinearCompositeEquiv
    (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom e₄ e₃.toAddEquiv
    (fun r x => (AlgEquiv.rTensor_smul θ r x).trans (congrArg (· • _)
      (by simp only [θ, AlgEquiv.ofRingEquiv_apply]; rfl))) e₂ e₁

end AlgebraicGeometry.Space

end
