module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.ObjectwiseDifferentialsLocallyBijective

/-!
# The degree `0` cohomology of the chart comparison of `NL_{X/Y}`

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a diagram of
étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R` of `Y`.
`StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartFinitePresentation` builds the canonical
chain map `(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V`.  This file proves that the map it induces on the
cokernels of the two differentials is an isomorphism, that is, the chain map is an isomorphism
on degree `0` cohomology.

Both cokernels are sheaves of differentials.  On the right, the conormal sequence of `f♯` is exact
with epimorphic right-hand map, so the cokernel of the differential of `NL_{X/Y}` is `Ω_{X/Y}`
(`Stacks.Sites.Conormal.imageDifferentialsIso`), and restriction to the slice at `V` preserves
finite colimits.  On the left, `Ω_{A/R}` is the cokernel of the differential of `NL_{A/R}`
(`Algebra.Extension.exact_cotangentComplex_toKaehler`) and `N ↦ N ⊗_A 𝒪` is right exact, so the
cokernel is `Ω_{A/R} ⊗_A 𝒪`.  Under these identifications the map on cokernels becomes the
morphism `ψ : Ω_{A/R} ⊗_A 𝒪 ⟶ Ω_{X/Y}|_V` attached to `d a ↦ d a`, which is checked on the
generators `d[a]` of the cotangent space of the canonical presentation.

`ψ` is an isomorphism because its presheaf-level map `𝒪_X(U) ⊗_A Ω_{A/R} → Ω_{X/Y}(U)` factors as
`μ ∘ σ`, where `σ : 𝒪_X(U) ⊗_A Ω_{A/R} → Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` is locally bijective on the
slice (`AlgebraicGeometry.Space.chartKaehlerTensorVanishingSieve_mem`,
`AlgebraicGeometry.Space.chartKaehlerTensorLiftSieve_mem`) and `μ` is the locally bijective
comparison of the objectwise differentials with the sheaf of differentials (Stacks 08TP,
`AlgebraicGeometry.SheafOfModules.isLocallyInjective_objectwiseDifferentialsToSheaf`,
`AlgebraicGeometry.SheafOfModules.isLocallySurjective_objectwiseDifferentialsToSheaf`).

## Main definitions

* `AlgebraicGeometry.Space.spaceDifferentials`: `Ω_{X/Y}`, at the module universe of `NL_{X/Y}`.
* `AlgebraicGeometry.Space.chartKaehlerTensorHom`: `ψ : Ω_{A/R} ⊗_A 𝒪 ⟶ Ω_{X/Y}|_V`.
* `AlgebraicGeometry.Space.chartTensorCokernelIso` and
  `AlgebraicGeometry.Space.chartDifferentialsCokernelIso`: the identifications of the two
  cokernels with `Ω_{A/R} ⊗_A 𝒪` and `Ω_{X/Y}|_V`.

## Main results

* `AlgebraicGeometry.Space.isIso_chartKaehlerTensorHom`: `ψ` is an isomorphism.
* `AlgebraicGeometry.Space.chartCokernelMap_eq`: the map on cokernels is `ψ` under the
  identifications.
* `AlgebraicGeometry.Space.isIso_chartCokernelMap`: the map on cokernels is an isomorphism.

## References

* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
  TensorProduct Stacks.Cohomology.SiteModules Algebra

universe u

attribute [local instance 1]
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-! ### `Ω_{A/R}` and `𝒪_X(U) ⊗_Γ Ω_{A/R} = 𝒪_X(U) ⊗_A Ω_{A/R}` -/

/-- `Ω_{A/R}` as an object of `ModuleCat A`. -/
abbrev chartKaehlerModule : ModuleCat.{u} (chartSourceRing B S hS f d) :=
  letI := chartDiagramAlgebraInst B S hS f d
  ModuleCat.of _ (chartKaehler B S hS f d)

/-- The tensor product over `Γ` appearing in the presheaf `U ↦ 𝒪_X(U) ⊗_Γ Ω_{A/R}`. -/
abbrev chartGlobalKaehlerTensor (U : Over d.U) : Type (u + 1) :=
  TensorProduct (chartGlobalRing B S hS f d) ((chartSliceRing B S hS f d).obj.obj (op U))
    ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d))

/-- The tensor product over `A` on which `σ_U` is defined. -/
abbrev chartLocalKaehlerTensor (U : Over d.U) : Type u :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d

/-- An element of `Ω_{A/R}`, as an element of the `Γ`-module `Ω_{A/R}`. -/
def chartKaehlerUp (ω : chartKaehler B S hS f d) :
    (chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d) :=
  ULift.up ω

/-- The element of `Ω_{A/R}` underlying an element of the `Γ`-module `Ω_{A/R}`. -/
def chartKaehlerDown (m : (chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) :
    chartKaehler B S hS f d :=
  ULift.down m

/-- A global function acts on `Ω_{A/R}` through its value at the final object. -/
theorem chartKaehlerDown_smul (γ : chartGlobalRing B S hS f d)
    (m : (chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) :
    letI := chartDiagramAlgebraInst B S hS f d
    chartKaehlerDown B S hS f d (γ • m) =
      chartEvalTop B S hS f d γ • chartKaehlerDown B S hS f d m :=
  rfl

/-- `𝒪_X(U) ⊗_Γ Ω_{A/R} ⟶ 𝒪_X(U) ⊗_A Ω_{A/R}`, `s ⊗ ω ↦ s ⊗ ω`. -/
def chartKaehlerTensorToLocal (U : Over d.U) :
    chartGlobalKaehlerTensor B S hS f d U →+ chartLocalKaehlerTensor B S hS f d U :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun m => ofSliceSection B S hS f d U s ⊗ₜ chartKaehlerDown B S hS f d m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun m₁ m₂ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun m => TensorProduct.zero_tmul _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun m => TensorProduct.add_tmul _ _ _ }
    (fun γ s m => by
      change ofSliceSection B S hS f d U (γ • s) ⊗ₜ[ToType
            ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehlerDown B S hS f d m =
        ofSliceSection B S hS f d U s ⊗ₜ[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj
            (op d.U))] (chartEvalTop B S hS f d γ • chartKaehlerDown B S hS f d m)
      rw [ofSliceSection_smul]
      exact TensorProduct.smul_tmul (chartEvalTop B S hS f d γ) (ofSliceSection B S hS f d U s)
        (chartKaehlerDown B S hS f d m))

/-- The identification on a pure tensor. -/
theorem chartKaehlerTensorToLocal_tmul (U : Over d.U)
    (s : (chartSliceRing B S hS f d).obj.obj (op U))
    (m : (chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    chartKaehlerTensorToLocal B S hS f d U (s ⊗ₜ m) =
      ofSliceSection B S hS f d U s ⊗ₜ chartKaehlerDown B S hS f d m :=
  rfl

/-- `𝒪_X(U) ⊗_A Ω_{A/R} ⟶ 𝒪_X(U) ⊗_Γ Ω_{A/R}`, `s ⊗ ω ↦ s ⊗ ω`. -/
def chartKaehlerTensorOfLocal (U : Over d.U) :
    chartLocalKaehlerTensor B S hS f d U →+ chartGlobalKaehlerTensor B S hS f d U :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun ω => toSliceSection B S hS f d U s ⊗ₜ chartKaehlerUp B S hS f d ω
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun ω₁ ω₂ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun ω => TensorProduct.zero_tmul _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun ω => TensorProduct.add_tmul _ _ _ }
    (fun a s ω => by
      have e : (chartGlobalSection B S hS f d a) • chartKaehlerUp B S hS f d ω =
          chartKaehlerUp B S hS f d (a • ω) := by
        change chartKaehlerUp B S hS f d
          (chartEvalTop B S hS f d (chartGlobalSection B S hS f d a) • ω) = _
        rw [chartEvalTop_chartGlobalSection]
      change toSliceSection B S hS f d U (chartDiagramRestrictO B S hS f d U a * s) ⊗ₜ
          chartKaehlerUp B S hS f d ω =
        toSliceSection B S hS f d U s ⊗ₜ chartKaehlerUp B S hS f d (a • ω)
      rw [← e, TensorProduct.tmul_smul]
      rfl)

/-- `chartKaehlerTensorOfLocal` is a left inverse of `chartKaehlerTensorToLocal`. -/
theorem chartKaehlerTensorOfLocal_toLocal (U : Over d.U)
    (t : chartGlobalKaehlerTensor B S hS f d U) :
    chartKaehlerTensorOfLocal B S hS f d U (chartKaehlerTensorToLocal B S hS f d U t) = t :=
  sectionTensorAddHom_ext (O := chartSliceRing B S hS f d)
    (g := (chartKaehlerTensorOfLocal B S hS f d U).comp (chartKaehlerTensorToLocal B S hS f d U))
    (h := AddMonoidHom.id _) (fun _ _ => rfl) t

/-- `chartKaehlerTensorOfLocal` is a right inverse of `chartKaehlerTensorToLocal`. -/
theorem chartKaehlerTensorToLocal_ofLocal (U : Over d.U)
    (t : chartLocalKaehlerTensor B S hS f d U) :
    chartKaehlerTensorToLocal B S hS f d U (chartKaehlerTensorOfLocal B S hS f d U t) = t := by
  let := chartDiagramAlgebraInst B S hS f d
  let := chartDiagramRestrictAlgebra B S hS f d U
  induction t using TensorProduct.inductionOn with
  | tmul s ω => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The identification `𝒪_X(U) ⊗_Γ Ω_{A/R} → 𝒪_X(U) ⊗_A Ω_{A/R}` is injective. -/
theorem chartKaehlerTensorToLocal_injective (U : Over d.U) :
    Function.Injective (chartKaehlerTensorToLocal B S hS f d U) :=
  Function.LeftInverse.injective (chartKaehlerTensorOfLocal_toLocal B S hS f d U)

/-- The identification commutes with restriction. -/
theorem chartKaehlerTensorToLocal_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (t : chartGlobalKaehlerTensor B S hS f d U₁) :
    chartKaehlerTensorToLocal B S hS f d U₂
        (tensorRestriction (O := chartSliceRing B S hS f d)
          ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) g.op t) =
      chartRestrictKaehlerTensor B S hS f d g (chartKaehlerTensorToLocal B S hS f d U₁ t) :=
  sectionTensorAddHom_ext (O := chartSliceRing B S hS f d)
    (g := (chartKaehlerTensorToLocal B S hS f d U₂).comp
      (tensorRestriction (O := chartSliceRing B S hS f d)
        ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) g.op).toAddMonoidHom)
    (h := (chartRestrictKaehlerTensor B S hS f d g).toAddMonoidHom.comp
      (chartKaehlerTensorToLocal B S hS f d U₁)) (fun _ _ => rfl) t

/-! ### The sheaf of relative differentials `Ω_{X/Y}` and the objectwise differentials -/

/-- **`Ω_{X/Y}`**, the sheaf of relative differentials of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` (Stacks 04BN) at
the module universe of `NL_{X/Y}`. -/
abbrev spaceDifferentials :
    _root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) :=
  AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1, u, u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)

/-- The universal derivation `d : 𝒪_X ⟶ Ω_{X/Y}`. -/
abbrev spaceUniversalDerivation :=
  AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1, u, u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)

/-- The comparison `μ` of Stacks 08TP from the objectwise differentials
`U ↦ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` to `Ω_{X/Y}`. -/
abbrev spaceObjectwiseDifferentialsToSheaf :=
  AlgebraicGeometry.SheafOfModules.objectwiseDifferentialsToSheaf.{u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)

/-- An element of `Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`, as a section over `U` of the objectwise
differentials. -/
def chartObjectwiseUp {U : Over d.U} (z : chartSectionsKaehler B S hS f d U) :
    (AlgebraicGeometry.SheafOfModules.objectwiseDifferentials.{u}
      (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
      (structureSharpInverseImage B S hS f)).obj (op U.left) :=
  ULift.up z

/-- `μ` on the differentials of the sections over a chart `U` over `V`. -/
def chartMu (U : Over d.U) (z : chartSectionsKaehler B S hS f d U) :
    (spaceDifferentials B S hS f).val.obj (op U.left) :=
  ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U.left)).hom
    (chartObjectwiseUp B S hS f d z)

/-- `μ` is additive. -/
theorem chartMu_add (U : Over d.U) (z₁ z₂ : chartSectionsKaehler B S hS f d U) :
    chartMu B S hS f d U (z₁ + z₂) = chartMu B S hS f d U z₁ + chartMu B S hS f d U z₂ :=
  map_add ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U.left)).hom
    (chartObjectwiseUp B S hS f d z₁) (chartObjectwiseUp B S hS f d z₂)

/-- `μ` is linear over the regular functions on the chart. -/
theorem chartMu_smul (U : Over d.U)
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
    (z : chartSectionsKaehler B S hS f d U) :
    chartMu B S hS f d U (a • z) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op U.left) from a) • chartMu B S hS f d U z :=
  map_smul ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U.left)).hom
    (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op U.left) from a) (chartObjectwiseUp B S hS f d z)

/-- `μ` sends `d b` to the universal derivation of `Ω_{X/Y}` at `b` (Stacks 08TP). -/
theorem chartMu_D (U : Over d.U)
    (b : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) :
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
    chartMu B S hS f d U (KaehlerDifferential.D _ _ b) =
      (spaceUniversalDerivation B S hS f).d (X := op U.left) b :=
  AlgebraicGeometry.SheafOfModules.objectwiseDifferentialsToSheaf_d.{u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op U.left) b

/-- The restriction maps of the objectwise differentials are the restrictions of the
differentials of the sections. -/
theorem objectwiseDifferentials_map_chartObjectwiseUp {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (z : chartSectionsKaehler B S hS f d U₁) :
    (AlgebraicGeometry.SheafOfModules.objectwiseDifferentials.{u}
      (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
      (structureSharpInverseImage B S hS f)).map g.left.op (chartObjectwiseUp B S hS f d z) =
      chartObjectwiseUp B S hS f d (chartSectionsKaehlerRestrict B S hS f d g z) := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  induction z using Stacks.NaiveCotangent.kaehlerDifferential_induction with
  | D b =>
    refine Eq.trans ?_ (congrArg (chartObjectwiseUp B S hS f d)
      (chartSectionsKaehlerRestrict_D B S hS f d g b).symm)
    exact congrArg ULift.up
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
        (structureSharpInverseImage B S hS f).hom g.left.op b)
  | zero =>
    refine (map_zero _).trans ?_
    exact congrArg (chartObjectwiseUp B S hS f d) (map_zero _).symm
  | add x y hx hy =>
    refine (map_add _ (chartObjectwiseUp B S hS f d x) (chartObjectwiseUp B S hS f d y)).trans ?_
    refine (congrArg₂ (· + ·) hx hy).trans ?_
    exact congrArg (chartObjectwiseUp B S hS f d) (map_add _ _ _).symm
  | smul b x hx =>
    refine ((AlgebraicGeometry.SheafOfModules.objectwiseDifferentials.{u}
      (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
      (structureSharpInverseImage B S hS f)).map_smul g.left.op
        (show (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS X).O).obj.obj (op U₁.left) from b)
        (chartObjectwiseUp B S hS f d x)).trans ?_
    refine (congrArg (fun t => _ • t) hx).trans ?_
    exact congrArg (chartObjectwiseUp B S hS f d)
      (chartSectionsKaehlerRestrict_smul B S hS f d g b x).symm

/-- `μ` commutes with restriction. -/
theorem chartMu_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (z : chartSectionsKaehler B S hS f d U₁) :
    (spaceDifferentials B S hS f).val.map g.left.op (chartMu B S hS f d U₁ z) =
      chartMu B S hS f d U₂ (chartSectionsKaehlerRestrict B S hS f d g z) :=
  (PresheafOfModules.naturality_apply (spaceObjectwiseDifferentialsToSheaf B S hS f)
    g.left.op (chartObjectwiseUp B S hS f d z)).symm.trans
    (congrArg ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U₂.left)).hom
      (objectwiseDifferentials_map_chartObjectwiseUp B S hS f d g z))

/-! ### The morphism `Ω_{A/R} ⊗_A 𝒪 ⟶ Ω_{X/Y}|_V` -/

/-- The `A`-linear map `Ω_{A/R} ⟶ Ω_{X/Y}(V)`, `d a ↦ d a`: the map of Kähler differentials of
the square at `V` followed by `μ`. -/
def chartKaehlerSection :
    chartKaehler B S hS f d →+ (spaceDifferentials B S hS f).val.obj (op d.U) :=
  AddMonoidHom.mk' (fun ω => chartMu B S hS f d (chartTop B S hS f d)
      (chartKaehlerMap B S hS f d (chartTop B S hS f d) ω))
    (fun ω₁ ω₂ => (congrArg (chartMu B S hS f d (chartTop B S hS f d))
      (map_add (chartKaehlerMap B S hS f d (chartTop B S hS f d)) ω₁ ω₂)).trans
      (chartMu_add B S hS f d _ _ _))

/-- The map `Ω_{A/R} → Ω_{X/Y}(V)` is `μ` after the map of the square at `V`. -/
theorem chartKaehlerSection_apply (ω : chartKaehler B S hS f d) :
    chartKaehlerSection B S hS f d ω =
      chartMu B S hS f d (chartTop B S hS f d)
        (chartKaehlerMap B S hS f d (chartTop B S hS f d) ω) :=
  rfl

/-- The map `Ω_{A/R} → Ω_{X/Y}(V)` is `A`-linear. -/
theorem chartKaehlerSection_smul (a : chartSourceRing B S hS f d)
    (ω : chartKaehlerModule B S hS f d) :
    chartKaehlerSection B S hS f d (a • ω) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op d.U) from a) • chartKaehlerSection B S hS f d ω := by
  have e := @Stacks.NaiveCotangent.kaehlerMapOfSquare_smul _ _ _ _ _ _ _ _
    (chartDiagramAlgebraInst B S hS f d)
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
      (op (chartTop B S hS f d).left))
    (chartDiagramRestrictBase B S hS f d (chartTop B S hS f d))
    (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
    (chartSquare_comm B S hS f d (chartTop B S hS f d)) a ω
  refine (congrArg (chartMu B S hS f d (chartTop B S hS f d))
    (e.trans (congrArg (· • _) (chartDiagramRestrictO_top B S hS f d a)))).trans ?_
  exact chartMu_smul B S hS f d (chartTop B S hS f d) a
    (chartKaehlerMap B S hS f d (chartTop B S hS f d) ω)

/-- **The morphism `ψ : Ω_{A/R} ⊗_A 𝒪 ⟶ Ω_{X/Y}|_V`** attached to `d a ↦ d a`. -/
def chartKaehlerTensorHom :
    (chartTensorFunctor B S hS f d).obj (chartKaehlerModule B S hS f d) ⟶
      chartSliceModule B S hS f d (spaceDifferentials B S hS f) :=
  chartSectionsTensorHom B S hS f d (spaceDifferentials B S hS f)
    (N := chartKaehlerModule B S hS f d)
    (chartKaehlerSection B S hS f d) (chartKaehlerSection_smul B S hS f d)

/-- The `Γ`-linear map `Ω_{A/R} ⟶ Γ(Ω_{X/Y}|_V)` corresponding to `ψ`. -/
abbrev chartKaehlerTheta :=
  chartSectionsTheta B S hS f d (spaceDifferentials B S hS f) (N := chartKaehlerModule B S hS f d)
    (chartKaehlerSection B S hS f d) (chartKaehlerSection_smul B S hS f d)

/-- `ψ` corresponds to `chartKaehlerTheta` under the universal property of `M ⊗_Γ 𝒪`. -/
theorem chartKaehlerTensorHom_homEquiv :
    (sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
      (chartSliceModule B S hS f d (spaceDifferentials B S hS f))
        (chartKaehlerTensorHom B S hS f d) =
        chartKaehlerTheta B S hS f d :=
  chartSectionsTensorHom_homEquiv B S hS f d (spaceDifferentials B S hS f)
    (N := chartKaehlerModule B S hS f d) (chartKaehlerSection B S hS f d)
    (chartKaehlerSection_smul B S hS f d)

/-- The morphism of presheaves of modules `(U ↦ 𝒪_X(U) ⊗_Γ Ω_{A/R}) ⟶ Ω_{X/Y}|_V` underlying
`ψ`, `s ⊗ ω ↦ s · (d ω)|_U`. -/
def chartKaehlerPresheafHom :
    sectionTensorPresheaf (O := chartSliceRing B S hS f d)
        ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) ⟶
      underlyingPresheaf.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
        (chartSliceModule B S hS f d (spaceDifferentials B S hS f)) :=
  sectionTensorPresheafHomOfSections.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
    (chartKaehlerTheta B S hS f d)

/-- The unit of sheafification followed by `ψ` is the presheaf-level comparison. -/
theorem chartKaehlerTensorHom_fac :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
        (sectionTensorPresheaf (O := chartSliceRing B S hS f d)
          ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d))) ≫
      (chartKaehlerTensorHom B S hS f d).val = chartKaehlerPresheafHom B S hS f d := by
  have h1 := ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
      (chartSliceRing B S hS f d)).homEquiv_unit _ _ (chartKaehlerTensorHom B S hS f d)).trans
    ((congrArg (fun t => t ≫ (globalSectionsFunctor (chartSliceRingSheaf B S hS f d)).map
        (chartKaehlerTensorHom B S hS f d))
      (sectionTensorSheafAdjunction_unit_app.{u + 1, u, u, u} (chartSliceRing B S hS f d) _)).trans
      (sectionsOfTensorPresheafHom_comp_right.{u + 1, u, u, u} _
        (chartKaehlerTensorHom B S hS f d)).symm)
  have h2 := (sectionTensorPresheafHomEquiv.{u + 1, u, u, u}
    ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d))
    (chartSliceModule B S hS f d (spaceDifferentials B S hS f))).left_inv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
        (sectionTensorPresheaf (O := chartSliceRing B S hS f d)
          ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d))) ≫
      (_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (chartSliceRingSheaf B S hS f d).obj)).map (chartKaehlerTensorHom B S hS f d))
  refine h2.symm.trans ?_
  exact congrArg (fun θ => sectionTensorPresheafHomOfSections.{u + 1, u, u, u}
      (O := chartSliceRing B S hS f d) θ)
    (h1.symm.trans (chartSectionsTensorHom_homEquiv B S hS f d _ _ _))

/-- `μ` over a chart over `V`, as an additive map. -/
def chartMuHom (U : Over d.U) :
    chartSectionsKaehler B S hS f d U →+ (spaceDifferentials B S hS f).val.obj (op U.left) :=
  AddMonoidHom.mk' (chartMu B S hS f d U) (chartMu_add B S hS f d U)

/-- **`ψ` factors as `μ ∘ σ`** on presheaf sections, after the identification of the tensor
products over `Γ` and over `A`. -/
theorem chartKaehlerPresheafHom_app (U : Over d.U) (t : chartGlobalKaehlerTensor B S hS f d U) :
    ((chartKaehlerPresheafHom B S hS f d).app (op U)).hom t =
      chartMu B S hS f d U
        (chartKaehlerTensor B S hS f d U (chartKaehlerTensorToLocal B S hS f d U t)) := by
  refine sectionTensorAddHom_ext (O := chartSliceRing B S hS f d)
    (g := sectionTensorLift.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
      (chartKaehlerTheta B S hS f d) (op U))
    (h := ((chartMuHom B S hS f d U).comp (chartKaehlerTensor B S hS f d U)).comp
      (chartKaehlerTensorToLocal B S hS f d U)) (fun s m => ?_) t
  have h_eval : ((chartKaehlerTheta B S hS f d).hom m).eval (op U) =
      (show (chartSliceModule B S hS f d (spaceDifferentials B S hS f)).val.obj (op U) from
        chartMu B S hS f d U
          (chartKaehlerMap B S hS f d U (chartKaehlerDown B S hS f d m))) :=
    (chartSectionsTheta_apply_val B S hS f d _ _ _ m U).trans
      ((chartMu_restrict B S hS f d (chartToTop B S hS f d U) _).trans
        (congrArg (chartMu B S hS f d U)
          (chartKaehlerMap_restrict B S hS f d (chartToTop B S hS f d U) _)))
  refine (congrArg (fun x => ringSheafSection s • x) h_eval).trans ?_
  exact (chartMu_smul B S hS f d U (ofSliceSection B S hS f d U s) _).symm

/-! ### Local bijectivity of `ψ` -/

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

include hU hW in
/-- **Local injectivity of `ψ`**: an element of `𝒪_X(U) ⊗_Γ Ω_{A/R}` killed by `ψ` restricts,
through `𝒪_X(U) ⊗_Γ Ω_{A/R} = 𝒪_X(U) ⊗_A Ω_{A/R}`, to zero on a covering. -/
theorem chartKaehlerTensorVanishingSieve_mem_of_presheafHom (U : Over d.U)
    (t : chartGlobalKaehlerTensor B S hS f d U)
    (ht : ((chartKaehlerPresheafHom B S hS f d).app (op U)).hom t = 0) :
    chartKaehlerTensorVanishingSieve B S hS f d U (chartKaehlerTensorToLocal B S hS f d U t) ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  let t' := chartKaehlerTensorToLocal B S hS f d U t
  have h1 : ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U.left)).hom
      (chartObjectwiseUp B S hS f d (chartKaehlerTensor B S hS f d U t')) =
    ((spaceObjectwiseDifferentialsToSheaf B S hS f).app (op U.left)).hom 0 :=
    (chartKaehlerPresheafHom_app B S hS f d U t).symm.trans (ht.trans (map_zero _).symm)
  have := AlgebraicGeometry.SheafOfModules.isLocallyInjective_objectwiseDifferentialsToSheaf.{u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)
  have hS1 := Presheaf.equalizerSieve_mem (SmallEtale.topology B S hS X.1)
    ((PresheafOfModules.toPresheaf _).map (spaceObjectwiseDifferentialsToSheaf B S hS f))
    (X := op U.left) (chartObjectwiseUp B S hS f d (chartKaehlerTensor B S hS f d U t')) 0 h1
  refine GrothendieckTopology.transitive _ (overEquiv_symm_mem_over _ U _ hS1) _
    fun V g hg => ?_
  rw [Sieve.overEquiv_symm_iff] at hg
  have h2 : chartKaehlerTensor B S hS f d V (chartRestrictKaehlerTensor B S hS f d g t') = 0 := by
    refine (chartKaehlerTensor_restrict B S hS f d g t').symm.trans ?_
    have h3 := (objectwiseDifferentials_map_chartObjectwiseUp B S hS f d g
      (chartKaehlerTensor B S hS f d U t')).symm.trans (hg.trans (map_zero _))
    exact congrArg ULift.down h3
  refine GrothendieckTopology.superset_covering _ ?_
    (chartKaehlerTensorVanishingSieve_mem B S hS f d hU hW V _ h2)
  intro W k hk
  change chartRestrictKaehlerTensor B S hS f d (k ≫ g) t' = 0
  rw [Point.restrictTensor_comp]
  exact hk

include hU hW in
/-- **Local surjectivity of `ψ`.** -/
theorem chartKaehlerPresheafHom_imageSieve_mem (U : Over d.U)
    (z : (spaceDifferentials B S hS f).val.obj (op U.left)) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (chartKaehlerPresheafHom B S hS f d))
        (show ToType (((PresheafOfModules.toPresheaf _).obj
          (underlyingPresheaf.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
            (chartSliceModule B S hS f d (spaceDifferentials B S hS f)))).obj (op U)) from z) ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  have := AlgebraicGeometry.SheafOfModules.isLocallySurjective_objectwiseDifferentialsToSheaf.{u}
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f)
  have hS1 := Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1)
    ((PresheafOfModules.toPresheaf _).map (spaceObjectwiseDifferentialsToSheaf B S hS f))
    (U := op U.left) z
  refine GrothendieckTopology.transitive _ (overEquiv_symm_mem_over _ U _ hS1) _
    fun V g hg => ?_
  rw [Sieve.overEquiv_symm_iff] at hg
  obtain ⟨y, hy⟩ := hg
  refine GrothendieckTopology.superset_covering _ ?_
    (chartKaehlerTensorLiftSieve_mem B S hS f d hU hW V
      (show chartSectionsKaehler B S hS f d V from ULift.down y))
  rintro W m ⟨t, ht⟩
  refine ⟨chartKaehlerTensorOfLocal B S hS f d W t, ?_⟩
  refine (chartKaehlerPresheafHom_app B S hS f d W _).trans ?_
  refine (congrArg (fun x => chartMu B S hS f d W (chartKaehlerTensor B S hS f d W x))
    (chartKaehlerTensorToLocal_ofLocal B S hS f d W t)).trans ?_
  refine (congrArg (chartMu B S hS f d W) ht).trans ?_
  refine (chartMu_restrict B S hS f d m _).symm.trans ?_
  refine (congrArg ((spaceDifferentials B S hS f).val.map m.left.op) hy).trans ?_
  exact ((spaceDifferentials B S hS f).val.map_comp_apply g.left.op m.left.op z).symm

include hU hW in
/-- The presheaf-level comparison underlying `ψ` is locally injective. -/
theorem chartKaehlerPresheafHom_isLocallyInjective :
    PresheafOfModules.IsLocallyInjective ((SmallEtale.topology B S hS X.1).over d.U)
      (chartKaehlerPresheafHom B S hS f d) := by
  refine ⟨fun {U} x y hxy => ?_⟩
  let x' : chartGlobalKaehlerTensor B S hS f d U.unop := x
  let y' : chartGlobalKaehlerTensor B S hS f d U.unop := y
  have hxy' : ((chartKaehlerPresheafHom B S hS f d).app (op U.unop)).hom x' =
      ((chartKaehlerPresheafHom B S hS f d).app (op U.unop)).hom y' := hxy
  have ht : ((chartKaehlerPresheafHom B S hS f d).app (op U.unop)).hom (x' - y') = 0 := by
    have e := map_sub ((chartKaehlerPresheafHom B S hS f d).app (op U.unop)).hom x' y'
    exact e.trans (sub_eq_zero.mpr hxy')
  have hcov := chartKaehlerTensorVanishingSieve_mem_of_presheafHom B S hS f d hU hW U.unop
    (x' - y') ht
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  intro V g hg
  have e1 := map_sub (chartKaehlerTensorToLocal B S hS f d U.unop) x' y'
  have e2 := map_sub (chartRestrictKaehlerTensor B S hS f d g)
    (chartKaehlerTensorToLocal B S hS f d U.unop x')
    (chartKaehlerTensorToLocal B S hS f d U.unop y')
  have hg' : chartRestrictKaehlerTensor B S hS f d g
        (chartKaehlerTensorToLocal B S hS f d U.unop x') =
      chartRestrictKaehlerTensor B S hS f d g (chartKaehlerTensorToLocal B S hS f d U.unop y') :=
    sub_eq_zero.mp (e2.symm.trans ((congrArg _ e1).symm.trans hg))
  have key : tensorRestriction (O := chartSliceRing B S hS f d)
      ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) g.op x' =
      tensorRestriction (O := chartSliceRing B S hS f d)
        ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)) g.op y' :=
    chartKaehlerTensorToLocal_injective B S hS f d V <|
      (chartKaehlerTensorToLocal_restrict B S hS f d g x').trans
        (hg'.trans (chartKaehlerTensorToLocal_restrict B S hS f d g y').symm)
  exact key

include hU hW in
/-- The presheaf-level comparison underlying `ψ` is locally surjective. -/
theorem chartKaehlerPresheafHom_isLocallySurjective :
    PresheafOfModules.IsLocallySurjective ((SmallEtale.topology B S hS X.1).over d.U)
      (chartKaehlerPresheafHom B S hS f d) :=
  ⟨fun {U} z => chartKaehlerPresheafHom_imageSieve_mem B S hS f d hU hW U z⟩

include hU hW in
/-- **`ψ : Ω_{A/R} ⊗_A 𝒪 ⟶ Ω_{X/Y}|_V` is an isomorphism.** -/
theorem isIso_chartKaehlerTensorHom : IsIso (chartKaehlerTensorHom B S hS f d) := by
  have := chartKaehlerPresheafHom_isLocallyInjective B S hS f d hU hW
  have := chartKaehlerPresheafHom_isLocallySurjective B S hS f d hU hW
  have hi : PresheafOfModules.IsLocallyInjective ((SmallEtale.topology B S hS X.1).over d.U)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
        (sectionTensorPresheaf.{u + 1, u, u, u + 1} (O := chartSliceRing B S hS f d)
          ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)))) := by
    change Presheaf.IsLocallyInjective _ (CategoryTheory.toSheafify _ _)
    exact Presheaf.isLocallyInjective_toSheafify'.{u + 1, u, u + 2, u + 1, u + 1} _ _
  have hs : PresheafOfModules.IsLocallySurjective ((SmallEtale.topology B S hS X.1).over d.U)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
        (sectionTensorPresheaf.{u + 1, u, u, u + 1} (O := chartSliceRing B S hS f d)
          ((chartModuleLift B S hS f d).obj (chartKaehlerModule B S hS f d)))) := by
    change Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ _)
    exact Presheaf.isLocallySurjective_toSheafify'.{u, u + 1, u + 1, u + 2, u + 1} _ _
  exact @Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective _ _ _ _ _ _ _ _ _
    (chartKaehlerTensorHom B S hS f d) (chartKaehlerTensorHom_fac B S hS f d) hi hs ‹_› ‹_›

/-! ### The right-hand cokernel: `Ω_{X/Y}|_V` -/

section RightCokernel

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

/-- Transport of the universal derivation along an equality of ring maps. -/
theorem eqToHom_universalDerivationOfSite_d
    {φ₁ φ₂ : inverseImageStructureSheaf B S hS f ⟶ (smallEtaleRingedTopos B S hS X).O}
    (e : φ₁ = φ₂) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (b : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj U)) :
    (eqToHom (congrArg (fun φ => AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{
        u, u + 1, u, u} (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O φ) e)).val.app U
      ((AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1, u, u}
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O φ₁).d b) =
      (AlgebraicGeometry.SheafOfModules.universalDerivationOfSite.{u, u + 1, u, u}
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O φ₂).d b := by
  subst e
  rfl

/-- The identification of the right-hand term of the conormal sequence of `f♯` with `Ω_{X/Y}`. -/
def naiveCotangentDifferentialsHom :
    (chartCS B S hS f).X₃ ⟶ spaceDifferentials B S hS f :=
  (imageDifferentialsIso.{u, u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
      (inverseImageStructureSheaf B S hS f)
      (freeAlgebraSheaf _ (inverseImageStructureSheaf B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
      (smallEtaleRingedTopos B S hS X).O
      (freeAlgebraSheafCoefficientMap _ (inverseImageStructureSheaf B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
      (Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _))).hom ≫
    eqToHom (congrArg (fun φ => AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{
        u, u + 1, u, u} (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O φ)
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _))

/-- The map `𝒪_X ⊗ Ω ⟶ Ω_{X/Y}` sends the local section `1 ⊗ d p` to `d` of the image of
`p`. -/
theorem naiveCotangentDifferentialsHom_tensorDifferential (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (p : ToType ((freeAlgebraSheaf _ (inverseImageStructureSheaf B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O)).obj.obj U)) :
    ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f).val.app U
        (tensorDifferential.{u, u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
          (inverseImageStructureSheaf B S hS f) _ (smallEtaleRingedTopos B S hS X).O
          (freeAlgebraSheafCoefficientMap _ (inverseImageStructureSheaf B S hS f)
            (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
          (Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
            (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
            (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)) U p) =
      (spaceUniversalDerivation B S hS f).d (X := U)
        (((Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
            (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
            (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)).hom.app U).hom p) := by
  refine (congrArg (fun x => (naiveCotangentDifferentialsHom B S hS f).val.app U x)
    (conormalSequence_g_differential.{u, u + 1, u, u} _ _ _ _ _ _ U p)).trans ?_
  refine (congrArg (fun x => (eqToHom (congrArg (fun φ =>
      AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u + 1, u, u}
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O φ)
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _))).val.app U x)
    (imageDifferentialsIso_d.{u, u + 1, u, u} _ _ _ _ _ _ U p)).trans ?_
  exact eqToHom_universalDerivationOfSite_d B S hS f
    (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _) U _

end RightCokernel

/-! ### The two cokernels and the comparison -/

section Comparison

open Stacks.NaiveCotangentFinitePresentation Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

attribute [local instance] chartDiagramAlgebraInst

/-- The projection `(Ω_{R[A]/R} ⊗ A) ⟶ Ω_{A/R}` from the degree `0` term of `NL_{A/R}`. -/
def chartToKaehler :
    nlMod₀ (chartCanonicalGenerators B S hS f d) ⟶ chartKaehlerModule B S hS f d :=
  ModuleCat.ofHom (chartCanonicalGenerators B S hS f d).toExtension.toKaehler

/-- The differential of `NL_{A/R}` followed by the projection to `Ω_{A/R}` vanishes. -/
theorem nlModD_chartToKaehler :
    nlModD (chartCanonicalGenerators B S hS f d) ≫ chartToKaehler B S hS f d = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (chartCanonicalGenerators B S hS f d).toExtension.exact_cotangentComplex_toKaehler
      |>.apply_apply_eq_zero x)

/-- **`Ω_{A/R}` is the cokernel of the differential of `NL_{A/R}`.** -/
def chartToKaehlerIsColimit :
    IsColimit (CokernelCofork.ofπ (chartToKaehler B S hS f d) (nlModD_chartToKaehler B S hS f d)) :=
  have hEx : (ShortComplex.mk _ _ (nlModD_chartToKaehler B S hS f d)).Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (chartCanonicalGenerators B S hS f d).toExtension.exact_cotangentComplex_toKaehler
  have : Epi (ShortComplex.mk _ _ (nlModD_chartToKaehler B S hS f d)).g :=
    (ModuleCat.epi_iff_surjective _).2
      (chartCanonicalGenerators B S hS f d).toExtension.toKaehler_surjective
  hEx.gIsCokernel

/-- **`Ω_{A/R} ⊗_A 𝒪` is the cokernel of the differential of `(NL_{A/R}) ⊗_A 𝒪`**, the functor
`N ↦ N ⊗_A 𝒪` being right exact. -/
def chartTensorToKaehlerIsColimit :
    IsColimit (CokernelCofork.ofπ ((chartTensorFunctor B S hS f d).map (chartToKaehler B S hS f d))
      (by rw [← Functor.map_comp, nlModD_chartToKaehler, Functor.map_zero]) :
        Cofork ((chartTensorFunctor B S hS f d).map
          (nlModD (chartCanonicalGenerators B S hS f d))) 0) :=
  have : PreservesColimit (parallelPair (nlModD (chartCanonicalGenerators B S hS f d)) 0)
      (ModuleCat.restrictScalars.{u} (chartEvalTop B S hS f d)) := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair
      (ModuleCat.uliftFunctor.{u + 1, u} (chartGlobalRing B S hS f d)) := inferInstance
  have : PreservesColimitsOfShape WalkingParallelPair
      (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)) := inferInstance
  have : PreservesColimit (parallelPair (nlModD (chartCanonicalGenerators B S hS f d)) 0)
      (chartModuleLift B S hS f d) :=
    comp_preservesColimit (ModuleCat.restrictScalars.{u} (chartEvalTop B S hS f d))
      (ModuleCat.uliftFunctor.{u + 1, u} (chartGlobalRing B S hS f d))
  have : PreservesColimit (parallelPair (nlModD (chartCanonicalGenerators B S hS f d)) 0)
      (chartTensorFunctor B S hS f d) :=
    comp_preservesColimit (chartModuleLift B S hS f d)
      (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d))
  isColimitCoforkMapOfIsColimit' (chartTensorFunctor B S hS f d)
    (nlModD_chartToKaehler B S hS f d) (chartToKaehlerIsColimit B S hS f d)

/-- The identification of the right-hand term of the conormal sequence with `Ω_{X/Y}` is an
isomorphism. -/
instance : IsIso (naiveCotangentDifferentialsHom B S hS f) := by
  dsimp only [naiveCotangentDifferentialsHom]
  infer_instance

/-- The differential of `NL_{X/Y}` followed by the projection to `Ω_{X/Y}` vanishes. -/
theorem chartCS_f_differentials :
    (chartCS B S hS f).f ≫ (chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f = 0 := by
  rw [← Category.assoc, (chartCS B S hS f).zero, zero_comp]

/-- **`Ω_{X/Y}` is the cokernel of the differential of `NL_{X/Y}`.** -/
def naiveCotangentDifferentialsIsColimit :
    IsColimit (CokernelCofork.ofπ ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f)
      (chartCS_f_differentials B S hS f)) :=
  IsColimit.ofIsoColimit
    (conormalSequence_exact.{u, u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
      (inverseImageStructureSheaf B S hS f) _ (smallEtaleRingedTopos B S hS X).O
      (freeAlgebraSheafCoefficientMap _ (inverseImageStructureSheaf B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
      (Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
        (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _))).gIsCokernel
    (Cofork.ext (asIso (naiveCotangentDifferentialsHom B S hS f)) rfl)

/-- The differential of `NL_{X/Y}|_V`, read over the structure sheaf of the slice. -/
abbrev chartSliceDifferential :
    chartSliceModule B S hS f d (chartCS B S hS f).X₁ ⟶
      chartSliceModule B S hS f d (chartCS B S hS f).X₂ :=
  (_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f

/-- The projection `(𝒪_X ⊗ Ω)|_V ⟶ Ω_{X/Y}|_V`, read over the structure sheaf of the slice. -/
abbrev chartSliceDifferentialsMap :
    chartSliceModule B S hS f d (chartCS B S hS f).X₂ ⟶
      chartSliceModule B S hS f d (spaceDifferentials B S hS f) :=
  (_root_.SheafOfModules.overFunctor _ d.U).map
    ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f)

/-- The differential of `NL_{X/Y}|_V` followed by the projection to `Ω_{X/Y}|_V` vanishes. -/
theorem chartSliceDifferential_differentialsMap :
    chartSliceDifferential B S hS f d ≫ chartSliceDifferentialsMap B S hS f d = 0 :=
  ((_root_.SheafOfModules.overFunctor _ d.U).map_comp _ _).symm.trans
    ((congrArg (_root_.SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U).map
      (chartCS_f_differentials B S hS f)).trans (Functor.map_zero _ _ _))

/-- **`Ω_{X/Y}|_V` is the cokernel of the differential of `NL_{X/Y}|_V`**, restriction to the
slice preserving finite colimits. -/
def chartDifferentialsIsColimit :
    IsColimit (CokernelCofork.ofπ (chartSliceDifferentialsMap B S hS f d)
      (chartSliceDifferential_differentialsMap B S hS f d)) :=
  have : (_root_.SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U :
        _root_.SheafOfModules.{u + 1} _ ⥤ _).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have : PreservesFiniteColimits (_root_.SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O) d.U :
        _root_.SheafOfModules.{u + 1} _ ⥤ _) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u + 1, u}
      d.U
  isColimitCoforkMapOfIsColimit' (_root_.SheafOfModules.overFunctor _ d.U)
    (chartCS_f_differentials B S hS f) (naiveCotangentDifferentialsIsColimit B S hS f)

/-- The degree `0` comparison on sections over `V` sends the basis vector `d[b]` to the local
section `1 ⊗ d [b]`. -/
theorem chartTensorSection_cotangentSpaceBasis (b : chartSourceRing B S hS f d) :
    chartTensorSection B S hS f d ((chartCanonicalGenerators B S hS f d).cotangentSpaceBasis b) =
      tensorDifferential.{u, u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
        (inverseImageStructureSheaf B S hS f) _ (smallEtaleRingedTopos B S hS X).O
        (freeAlgebraSheafCoefficientMap _ (inverseImageStructureSheaf B S hS f)
          (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
        (Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
          (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)) (op d.U)
        (Stacks.SheafOfModules.freeAlgebraSectionsMap _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (op d.U)
          (MvPolynomial.X (chartDiagramRestrictO B S hS f d (chartTop B S hS f d) b))) := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (chartTop B S hS f d).left)
  have e1 := Stacks.NaiveCotangent.cotangentSpaceMapOfSquare_tmul_D_X
    (chartDiagramRestrictBase B S hS f d (chartTop B S hS f d))
    (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
    (chartSquare_comm B S hS f d (chartTop B S hS f d)) 1 b
  have e2 := Stacks.SheafOfModules.sectionsTensorComparison_tmul.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U)
    (chartDiagramRestrictO B S hS f d (chartTop B S hS f d) 1)
    (MvPolynomial.X (chartDiagramRestrictO B S hS f d (chartTop B S hS f d) b))
  refine (congrArg (chartTensorSection B S hS f d)
    (Generators.cotangentSpaceBasis_apply (chartCanonicalGenerators B S hS f d) b)).trans ?_
  refine (congrArg (Stacks.SheafOfModules.sectionsTensorComparison.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op d.U)) e1).trans (e2.trans ?_)
  exact (congrArg (fun c : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)) =>
    c • tensorDifferential.{u, u + 1, u, u} (smallEtaleRingedTopos B S hS X).J
        (inverseImageStructureSheaf B S hS f) _ (smallEtaleRingedTopos B S hS X).O
        (freeAlgebraSheafCoefficientMap _ (inverseImageStructureSheaf B S hS f)
          (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O))
        (Stacks.SheafOfModules.presentation _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
          (underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)) (op d.U)
        (Stacks.SheafOfModules.freeAlgebraSectionsMap _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (op d.U)
          (MvPolynomial.X (chartDiagramRestrictO B S hS f d (chartTop B S hS f d) b))))
    (map_one (chartDiagramRestrictO B S hS f d (chartTop B S hS f d)))).trans (one_smul _ _)

/-- **The comparison on generators**: over `V`, the degree `0` comparison followed by
`𝒪_X ⊗ Ω ⟶ Ω_{X/Y}` is the projection to `Ω_{A/R}` followed by `d a ↦ d a`. -/
theorem naiveCotangentDifferentialsHom_chartTensorSection
    (x : (chartCanonicalGenerators B S hS f d).toExtension.CotangentSpace) :
    ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f).val.app (op d.U)
        (chartTensorSection B S hS f d x) =
      chartKaehlerSection B S hS f d
        ((chartCanonicalGenerators B S hS f d).toExtension.toKaehler x) := by
  induction x using Stacks.NaiveCotangent.cotangentSpace_induction with
  | basis b =>
    refine (congrArg (fun y => ((chartCS B S hS f).g ≫
      naiveCotangentDifferentialsHom B S hS f).val.app (op d.U) y)
      (chartTensorSection_cotangentSpaceBasis B S hS f d b)).trans ?_
    refine (naiveCotangentDifferentialsHom_tensorDifferential B S hS f (op d.U) _).trans ?_
    refine (congrArg (fun c => (spaceUniversalDerivation B S hS f).d (X := op d.U) c)
      (Stacks.SheafOfModules.freeAlgebraSectionsMap_X _ (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op d.U)
        _)).trans ?_
    refine Eq.trans ?_ (congrArg (chartKaehlerSection B S hS f d)
      (Generators.toKaehler_cotangentSpaceBasis b)).symm
    refine Eq.trans ?_ (congrArg (chartMu B S hS f d (chartTop B S hS f d))
      (@Stacks.NaiveCotangent.kaehlerMapOfSquare_D _ _ _ _ _ _ _ _
        (chartDiagramAlgebraInst B S hS f d)
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
          (op (chartTop B S hS f d).left))
        (chartDiagramRestrictBase B S hS f d (chartTop B S hS f d))
        (chartDiagramRestrictO B S hS f d (chartTop B S hS f d))
        (chartSquare_comm B S hS f d (chartTop B S hS f d)) b)).symm
    exact (chartMu_D B S hS f d (chartTop B S hS f d) _).symm
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul a x hx =>
    rw [chartTensorSection_smul, map_smul, hx, map_smul, chartKaehlerSection_smul]

/-- **The comparison square**: the degree `0` component followed by `Ω_{X/Y}|_V` is the
projection to `Ω_{A/R} ⊗_A 𝒪` followed by `ψ`. -/
theorem chartTensorTensorHom_comp_differentials :
    chartTensorTensorHom B S hS f d ≫ chartSliceDifferentialsMap B S hS f d =
      (chartTensorFunctor B S hS f d).map (chartToKaehler B S hS f d) ≫
        chartKaehlerTensorHom B S hS f d := by
  apply ((sectionTensorSheafAdjunction.{u + 1, u, u, u} (chartSliceRing B S hS f d)).homEquiv _
    _).injective
  refine ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ ((sectionTensorSheafAdjunction.{u + 1, u, u, u}
    (chartSliceRing B S hS f d)).homEquiv_naturality_left _ _).symm
  refine (congrArg (fun t => t ≫ (globalSectionsFunctor
    (chartSliceRingSheaf B S hS f d)).map ((_root_.SheafOfModules.overFunctor _ d.U).map
      ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f)))
    (chartSectionsTensorHom_homEquiv B S hS f d _ (chartTensorSection B S hS f d)
      (chartTensorSection_smul B S hS f d))).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (chartModuleLift B S hS f d).map
    (chartToKaehler B S hS f d) ≫ t) (chartKaehlerTensorHom_homEquiv B S hS f d)).symm
  refine ModuleCat.hom_ext (LinearMap.ext fun m => PresheafOfModules.sections_ext _ _ fun U => ?_)
  change ((chartCS B S hS f).g ≫ naiveCotangentDifferentialsHom B S hS f).val.app
      (op U.unop.left) ((chartCS B S hS f).X₂.val.map U.unop.hom.op
        (chartTensorSection B S hS f d (ULift.down m))) =
    (spaceDifferentials B S hS f).val.map U.unop.hom.op
      (chartKaehlerSection B S hS f d
        ((chartCanonicalGenerators B S hS f d).toExtension.toKaehler (ULift.down m)))
  refine (PresheafOfModules.naturality_apply ((chartCS B S hS f).g ≫
    naiveCotangentDifferentialsHom B S hS f).val U.unop.hom.op _).trans ?_
  exact congrArg ((spaceDifferentials B S hS f).val.map U.unop.hom.op)
    (naiveCotangentDifferentialsHom_chartTensorSection B S hS f d (ULift.down m))

/-! ### The map on cokernels -/

/-- The cokernel of the differential of `(NL_{A/R}) ⊗_A 𝒪` is `Ω_{A/R} ⊗_A 𝒪`. -/
def chartTensorCokernelIso :
    cokernel ((chartTensorFunctor B S hS f d).map
        (nlModD (chartCanonicalGenerators B S hS f d))) ≅
      (chartTensorFunctor B S hS f d).obj (chartKaehlerModule B S hS f d) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (chartTensorToKaehlerIsColimit B S hS f d)

/-- The identification of the left-hand cokernel, on the projection. -/
theorem cokernel_π_chartTensorCokernelIso_hom :
    cokernel.π ((chartTensorFunctor B S hS f d).map
        (nlModD (chartCanonicalGenerators B S hS f d))) ≫
      (chartTensorCokernelIso B S hS f d).hom =
        (chartTensorFunctor B S hS f d).map (chartToKaehler B S hS f d) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (chartTensorToKaehlerIsColimit B S hS f d) WalkingParallelPair.one

/-- The cokernel of the differential of `NL_{X/Y}|_V` is `Ω_{X/Y}|_V`. -/
def chartDifferentialsCokernelIso :
    cokernel (chartSliceDifferential B S hS f d) ≅
      chartSliceModule B S hS f d (spaceDifferentials B S hS f) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (chartDifferentialsIsColimit B S hS f d)

/-- The identification of the right-hand cokernel, on the projection. -/
theorem cokernel_π_chartDifferentialsCokernelIso_hom :
    cokernel.π (chartSliceDifferential B S hS f d) ≫
      (chartDifferentialsCokernelIso B S hS f d).hom = chartSliceDifferentialsMap B S hS f d :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (chartDifferentialsIsColimit B S hS f d) WalkingParallelPair.one

/-- **The map on cokernels is `ψ`**, read through the identifications of the two cokernels with
`Ω_{A/R} ⊗_A 𝒪` and `Ω_{X/Y}|_V`. -/
theorem chartCokernelMap_eq :
    cokernel.map ((chartTensorFunctor B S hS f d).map
        (nlModD (chartCanonicalGenerators B S hS f d)))
      ((_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f)
      (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
      (chartTensorHom_comm B S hS f d) =
    (chartTensorCokernelIso B S hS f d).hom ≫ chartKaehlerTensorHom B S hS f d ≫
      (chartDifferentialsCokernelIso B S hS f d).inv := by
  refine (cancel_epi (cokernel.π _)).1 ?_
  refine (cokernel.π_desc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc (cokernel.π _) (chartTensorCokernelIso B S hS f d).hom
    (chartKaehlerTensorHom B S hS f d ≫ (chartDifferentialsCokernelIso B S hS f d).inv))
  refine Eq.trans ?_ (congrArg (fun t => t ≫ chartKaehlerTensorHom B S hS f d ≫
    (chartDifferentialsCokernelIso B S hS f d).inv)
    (cokernel_π_chartTensorCokernelIso_hom B S hS f d)).symm
  refine Eq.trans ?_ (Category.assoc ((chartTensorFunctor B S hS f d).map
    (chartToKaehler B S hS f d)) (chartKaehlerTensorHom B S hS f d)
    (chartDifferentialsCokernelIso B S hS f d).inv)
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (chartDifferentialsCokernelIso B S hS f d).inv)
    (chartTensorTensorHom_comp_differentials B S hS f d))
  refine Eq.trans ?_ (Category.assoc (chartTensorTensorHom B S hS f d)
    (chartSliceDifferentialsMap B S hS f d) (chartDifferentialsCokernelIso B S hS f d).inv).symm
  exact congrArg (fun t => chartTensorTensorHom B S hS f d ≫ t)
    ((Iso.eq_comp_inv _).2 (cokernel_π_chartDifferentialsCokernelIso_hom B S hS f d))

include hU hW in
/-- **The map induced on the cokernels of the two differentials by the chain map
`(NL_{A/R}) ⊗_A 𝒪 ⟶ NL_{X/Y}|_V` is an isomorphism**: both cokernels are `Ω`, namely
`Ω_{A/R} ⊗_A 𝒪` and `Ω_{X/Y}|_V`, and the map between them is the isomorphism `ψ`. -/
theorem isIso_chartCokernelMap :
    IsIso (cokernel.map ((chartTensorFunctor B S hS f d).map
        (nlModD (chartCanonicalGenerators B S hS f d)))
      ((_root_.SheafOfModules.overFunctor _ d.U).map (chartCS B S hS f).f)
      (chartConormalTensorHom B S hS f d) (chartTensorTensorHom B S hS f d)
      (chartTensorHom_comm B S hS f d)) := by
  have := isIso_chartKaehlerTensorHom B S hS f d hU hW
  rw [chartCokernelMap_eq]
  infer_instance

end Comparison

end AlgebraicGeometry.Space
