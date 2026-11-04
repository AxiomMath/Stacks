module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartComparison
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs

/-!
# Tensoring with the structure sheaf on an affine chart is exact

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `d` be a diagram of
étale scheme charts over `f` whose chart `V = Spec A` of `X` is affine, and write `Γ` for the
ring of global functions of the small étale site of `X` localized at `V`, which evaluation at the
final object identifies with `A`.  For a `Γ`-module `M` the sheaf `M ⊗_Γ 𝒪` on the localized
site is the sheafification of `U ↦ 𝒪_X(U) ⊗_Γ M`
(`Stacks.Cohomology.SiteModules.sectionTensorSheafFunctor`).

This file proves that `M ↦ M ⊗_Γ 𝒪` carries injective maps to monomorphisms.  Since it is a left
adjoint it preserves cokernels, so it is an exact functor.  The proof is the usual one: at a
geometric point `x` of `X` lifted to `V` the stalk `𝒪_{X,x}` is a filtered colimit of étale
`A`-algebras (`AlgebraicGeometry.Space.chartStalk_ind_etale`), hence flat over `A`, hence over
`Γ`; so an element of `𝒪_X(U) ⊗_Γ M'` killed in `𝒪_X(U) ⊗_Γ M` has vanishing germ in
`𝒪_{X,x} ⊗_Γ M'`, and therefore vanishes on a smaller neighbourhood
(`CategoryTheory.GrothendieckTopology.Point.exists_restrictTensor_eq_zero`).  Coverings of the
localized site are detected at geometric points
(`AlgebraicGeometry.Space.mem_over_of_forall_geometricFiber`), so the presheaf map is locally
injective, and sheafification turns a locally injective map into a monomorphism
(`Stacks.SheafOfModules.FlatSheafification.moduleSheafification_map_mono_of_locallyInjective`).

## Main results

* `AlgebraicGeometry.Space.bijective_chartEvalTop`: `Γ → A` is bijective.
* `AlgebraicGeometry.Space.chartStalk_flat_global`: the stalk of `𝒪_X` at a geometric point
  lifted to `V` is flat over `Γ`.
* `AlgebraicGeometry.Space.isLocallyInjective_chartSectionTensorMap`: an injective `Γ`-linear
  map induces a locally injective map of the presheaves `U ↦ 𝒪_X(U) ⊗_Γ (-)`.
* `AlgebraicGeometry.Space.mono_chartSectionTensor_map`: `M ↦ M ⊗_Γ 𝒪` preserves
  monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
  TensorProduct Stacks.Cohomology.SiteModules

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-! ### The global functions of the slice -/

/-- A global function of the slice at `V` is determined by its value at the final object. -/
theorem chartEvalTop_injective : Function.Injective (chartEvalTop B S hS f d) := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  funext U
  refine (chartDiagramRestrictO_chartEvalTop B S hS f d U.unop γ₁).symm.trans ?_
  rw [h]
  exact chartDiagramRestrictO_chartEvalTop B S hS f d U.unop γ₂

/-- **Evaluation at the final object identifies the global functions of the slice with `A`.** -/
theorem bijective_chartEvalTop : Function.Bijective (chartEvalTop B S hS f d) :=
  ⟨chartEvalTop_injective B S hS f d, fun a =>
    ⟨chartGlobalSection B S hS f d a, chartEvalTop_chartGlobalSection B S hS f d a⟩⟩

/-! ### Germs of global functions -/

/-- Evaluation of a global function of the slice at a chart `U` over `V`. -/
abbrev chartGlobalEval (U : Over d.U) :
    chartGlobalRing B S hS f d →+* (chartSliceRing B S hS f d).obj.obj (op U) :=
  globalSectionEvalHom (chartSliceRing B S hS f d) (op U)

/-- Evaluating a global function of the slice commutes with restriction along `g : U₂ ⟶ U₁`. -/
theorem chartGlobalEval_naturality {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (γ : chartGlobalRing B S hS f d) :
    (chartSliceRing B S hS f d).obj.map g.op (chartGlobalEval B S hS f d U₁ γ) =
      chartGlobalEval B S hS f d U₂ γ :=
  globalSectionEvalHom_naturality g.op γ

section Stalk

variable {x : GeometricPoint B S hS X.1} (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)

/-- The stalk of the structure sheaf of the slice at the point attached to `p`. -/
abbrev chartSliceStalk : CommRingCat.{u} :=
  ((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
    (chartSliceRing B S hS f d).obj

/-- The germ `Γ → 𝒪_{X,x}` of a global function of the slice at the point. -/
abbrev chartGlobalStalkHom :
    chartGlobalRing B S hS f d →+* ToType (chartSliceStalk B S hS f d p) :=
  ((chartStalkPoint B S hS f d p).toPresheafFiber (Over.mk (𝟙 d.U))
    (chartStalkPointTop B S hS f d p) (chartSliceRing B S hS f d).obj).hom.comp
    (chartGlobalEval B S hS f d (Over.mk (𝟙 d.U)))

/-- The germ of the value of a global function at a neighbourhood is its germ. -/
theorem toPresheafFiber_chartGlobalEval (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U) (γ : chartGlobalRing B S hS f d) :
    (chartStalkPoint B S hS f d p).toPresheafFiber U q (chartSliceRing B S hS f d).obj
        (chartGlobalEval B S hS f d U γ) = chartGlobalStalkHom B S hS f d p γ := by
  refine (congrArg ((chartStalkPoint B S hS f d p).toPresheafFiber U q
    (chartSliceRing B S hS f d).obj)
    (chartGlobalEval_naturality B S hS f d (chartToTop B S hS f d U) γ).symm).trans ?_
  refine (Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) (chartToTop B S hS f d U) q
    (chartSliceRing B S hS f d).obj _).trans ?_
  rw [chartStalkPoint_map_toTop]
  rfl

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))

include hU in
/-- **The stalk of `𝒪_X` at a geometric point lifted to `V` is flat over `Γ`.** -/
theorem chartStalk_flat_global :
    letI := (chartGlobalStalkHom B S hS f d p).toAlgebra
    Module.Flat (chartGlobalRing B S hS f d) (ToType (chartSliceStalk B S hS f d p)) := by
  let := (chartGlobalStalkHom B S hS f d p).toAlgebra
  let : Algebra (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (ToType (chartSliceStalk B S hS f d p)) := (chartStalkGerm B S hS f d p).toAlgebra
  let := (chartEvalTop B S hS f d).toAlgebra
  have : Module.Flat (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (ToType (chartSliceStalk B S hS f d p)) :=
    CommAlgCat.flat_of_ind_etale (chartStalk_ind_etale B S hS f d p hU)
  have : Module.Flat (chartGlobalRing B S hS f d)
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective
      (Algebra.linearMap (chartGlobalRing B S hS f d)
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))))
      (bijective_chartEvalTop B S hS f d)).symm
  have : IsScalarTower (chartGlobalRing B S hS f d)
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (ToType (chartSliceStalk B S hS f d p)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Flat.trans (chartGlobalRing B S hS f d)
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) _

end Stalk

/-! ### Local injectivity -/

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))

/-- The tensor product `𝒪_X(U) ⊗_Γ M` of the sections over a chart `U` over `V` with a module
over the global functions `Γ` of the slice. -/
abbrev chartSliceTensor (M : ModuleCat.{u + 1} (chartGlobalRing B S hS f d)) (U : Over d.U) :
    Type (u + 1) :=
  TensorProduct (chartGlobalRing B S hS f d) ((chartSliceRing B S hS f d).obj.obj (op U)) M

/-- The arrows along which an element of `𝒪_X(U) ⊗_Γ M` restricts to zero. -/
def chartSectionTensorVanishingSieve (M : ModuleCat.{u + 1} (chartGlobalRing B S hS f d))
    (U : Over d.U) (t : chartSliceTensor B S hS f d M U) : Sieve U where
  arrows _ g := tensorRestriction (O := chartSliceRing B S hS f d) M g.op t = 0
  downward_closed {_ _} g hg k := by
    change tensorRestriction (O := chartSliceRing B S hS f d) M (g.op ≫ k.op) t = 0
    refine (LinearMap.congr_fun (tensorRestriction_comp (O := chartSliceRing B S hS f d) M g.op
      k.op) t).trans ?_
    exact (congrArg (tensorRestriction (O := chartSliceRing B S hS f d) M k.op) hg).trans
      (map_zero _)

include hU in
/-- **Tensoring with the structure presheaf over `Γ` preserves injectivity locally.**  If
`φ : M' → M` is an injective `Γ`-linear map, an element of `𝒪_X(U) ⊗_Γ M'` whose image in
`𝒪_X(U) ⊗_Γ M` vanishes restricts to zero on a covering of `U`. -/
theorem chartSectionTensorVanishingSieve_mem
    {M' M : ModuleCat.{u + 1} (chartGlobalRing B S hS f d)}
    (φ : M' ⟶ M) (hφ : Function.Injective φ) (U : Over d.U)
    (t : chartSliceTensor B S hS f d M' U)
    (ht : tensorCoefficient (O := chartSliceRing B S hS f d) φ (op U) t = 0) :
    chartSectionTensorVanishingSieve B S hS f d M' U t ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  refine mem_over_of_forall_geometricFiber B S hS f d U _ fun x p => ?_
  let p₀ := (etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p
  let Φ := chartStalkPoint B S hS f d p₀
  let P := (chartSliceRing B S hS f d).obj
  let ε := chartGlobalEval B S hS f d
  let εΦ := chartGlobalStalkHom B S hS f d p₀
  have hε : ∀ {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) (γ : chartGlobalRing B S hS f d),
      P.map g.op (ε U₁ γ) = ε U₂ γ := chartGlobalEval_naturality B S hS f d
  have hεΦ : ∀ (U' : Over d.U) (q : Φ.fiber.obj U') (γ : chartGlobalRing B S hS f d),
      Φ.toPresheafFiber U' q P (ε U' γ) = εΦ γ :=
    toPresheafFiber_chartGlobalEval B S hS f d p₀
  let q := chartFiberLift B S hS f d U p
  let := εΦ.toAlgebra
  have hflat := chartStalk_flat_global B S hS f d p₀ hU
  have hgerm : (φ.hom.lTensor _).comp (Point.germTensor Φ P ε εΦ hεΦ M' U q) =
      (Point.germTensor Φ P ε εΦ hεΦ M U q).comp
        (tensorCoefficient (O := chartSliceRing B S hS f d) φ (op U)) :=
    TensorProduct.ext' fun _ _ => rfl
  have h0 : Point.germTensor Φ P ε εΦ hεΦ M' U q t = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap φ.hom hφ <| by
      simpa only [LinearMap.comp_apply, ht, map_zero] using LinearMap.congr_fun hgerm t
  obtain ⟨U', g, q', hq', hg⟩ := Point.exists_restrictTensor_eq_zero Φ P ε hε εΦ hεΦ M' q t h0
  exact ⟨U', g, hg, q'.1, congrArg Subtype.val hq'⟩

include hU in
/-- **An injective `Γ`-linear map induces a locally injective map of the presheaves
`U ↦ 𝒪_X(U) ⊗_Γ (-)`.** -/
theorem isLocallyInjective_chartSectionTensorMap
    {M' M : ModuleCat.{u + 1} (chartGlobalRing B S hS f d)} (φ : M' ⟶ M)
    (hφ : Function.Injective φ) :
    Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS X.1).over d.U)
      ((PresheafOfModules.toPresheaf _).map
        (sectionTensorPresheafFunctorMap (O := chartSliceRing B S hS f d) φ)) := by
  refine ⟨fun {U} x y hxy => ?_⟩
  have ht : tensorCoefficient (O := chartSliceRing B S hS f d) φ U (x - y) = 0 :=
    ((tensorCoefficient (O := chartSliceRing B S hS f d) φ U).map_sub x y).trans
      (sub_eq_zero.mpr hxy)
  refine GrothendieckTopology.superset_covering _ ?_
    (chartSectionTensorVanishingSieve_mem B S hS f d hU φ hφ U.unop (x - y) ht)
  intro V g hg
  exact sub_eq_zero.mp
    (((tensorRestriction (O := chartSliceRing B S hS f d) M' g.op).map_sub x y).symm.trans hg)

include hU in
/-- **`M ↦ M ⊗_Γ 𝒪` carries injective maps to monomorphisms** on the slice of the small étale
site of `X` at an affine chart `V`. -/
theorem mono_chartSectionTensor_map {M' M : ModuleCat.{u + 1} (chartGlobalRing B S hS f d)}
    (φ : M' ⟶ M) (hφ : Function.Injective φ) :
    Mono ((sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).map φ) :=
  Stacks.SheafOfModules.FlatSheafification.moduleSheafification_map_mono_of_locallyInjective _
    (𝟙 _) _ (isLocallyInjective_chartSectionTensorMap B S hS f d hU φ hφ)

end AlgebraicGeometry.Space

end
