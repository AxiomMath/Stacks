module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartH1
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentCohomologySheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.SectionTensorTerminalPresentation

/-!
# The degree `-1` cohomology sheaf of `NL_{X/Y}` on an affine chart diagram

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a diagram of
étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R` of `Y`.
Write `H = H₁(L_{A/R})`, `𝒦` for the kernel of the differential of the naive cotangent complex
`NL_{X/Y}` (its degree `-1` cohomology sheaf), and `Γ` for the ring of global functions of the
slice of the small étale site of `X` at `V`, which evaluation at the final object identifies with
`A`.

This file proves that the restriction of `𝒦` to the slice at `V` is the sheaf `H ⊗_Γ 𝒪` attached
to the `Γ`-module `H`, that is the sheafification of `U ↦ 𝒪_X(U) ⊗_A H`.  The comparison is the
morphism of presheaves of modules

`𝒪_X(U) ⊗_A H ⟶ 𝒦(U)`, `s ⊗ h ↦ s · (image of h in 𝒦(V))|_U`,

which factors as `τ` of `AlgebraicGeometry.Space.chartH1Tensor` followed by the comparison
`σ` of `Stacks.SheafOfModules.sectionsH1Comparison`; both are locally bijective
(`AlgebraicGeometry.Space.chartTensorVanishingSieve_mem`,
`AlgebraicGeometry.Space.chartTensorLiftSieve_mem`,
`Stacks.SheafOfModules.sectionsH1VanishingSieve_mem`,
`Stacks.SheafOfModules.sectionsH1LiftSieve_mem`), hence so is the comparison, and a locally
bijective morphism into a sheaf identifies the sheaf with the sheafification.  Since `H ⊗_Γ 𝒪`
is quasi-coherent
(`Stacks.Cohomology.SiteModules.isQuasicoherentOnSite_sectionTensor_of_isTerminal`),
so is the restriction of `𝒦` to `V`; the charts carrying an affine chart diagram cover `X`, so
`𝒦` is quasi-coherent (Stacks 03DN).

## Main definitions

* `AlgebraicGeometry.Space.chartH1GlobalModule`: `H`, as a module over the global functions of
  the slice at `V`.
* `AlgebraicGeometry.Space.chartTensorEquiv`: the identification of `𝒪_X(U) ⊗_Γ H` with
  `𝒪_X(U) ⊗_A H`.
* `AlgebraicGeometry.Space.chartKernelPresheafHom`: the comparison morphism of presheaves of
  modules.
* `AlgebraicGeometry.Space.chartKernelSliceIso`: `𝒦|_V ≅ H ⊗_Γ 𝒪`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_naiveCotangentKernel`: `𝒦` is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_negOne_naiveCotangentComplex`: the
  degree `-1` cohomology sheaf of `NL_{X/Y}` is quasi-coherent.

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite Algebra
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

/-! ### The ring of global functions of the slice at `V` -/

/-- The structure sheaf of `X`, restricted to the slice of the small étale site at the chart
`V` of the diagram. -/
abbrev chartSliceRing : Sheaf ((SmallEtale.topology B S hS X.1).over d.U) CommRingCat.{u} :=
  (smallEtaleRingedTopos B S hS X).O.over d.U

/-- The ring `Γ` of global functions of the slice at `V`. -/
abbrev chartGlobalRing : Type (u + 1) := GlobalFunctionRing (chartSliceRing B S hS f d)

/-- Evaluation `Γ → A` of a global function at the final object of the slice. -/
abbrev chartEvalTop : chartGlobalRing B S hS f d →+*
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)) :=
  globalSectionEvalHom (chartSliceRing B S hS f d) (op (Over.mk (𝟙 d.U)))

/-- The global function of the slice restricted from a function on `V`. -/
def chartGlobalSection (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :
    chartGlobalRing B S hS f d :=
  ⟨fun U => chartDiagramRestrictO B S hS f d U.unop a,
    fun {_ _} g => chartDiagramRestrictO_naturality B S hS f d g.unop a⟩

/-- Evaluating at the final object the global function restricted from a function `a` on `V`
gives back `a`. -/
theorem chartEvalTop_chartGlobalSection
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :
    chartEvalTop B S hS f d (chartGlobalSection B S hS f d a) = a :=
  ConcreteCategory.congr_hom ((smallEtaleRingedTopos B S hS X).O.obj.map_id (op d.U)) a

/-- A global function of the slice, evaluated at a chart `U` over `V`, is the restriction of its
value at the final object. -/
theorem chartDiagramRestrictO_chartEvalTop (U : Over d.U) (γ : chartGlobalRing B S hS f d) :
    chartDiagramRestrictO B S hS f d U (chartEvalTop B S hS f d γ) = γ.1 (op U) :=
  globalSectionEvalHom_naturality (chartToTop B S hS f d U).op γ

/-! ### `H` as a module over `Γ` -/

/-- The `Γ`-module structure on `H` through evaluation at the final object. -/
abbrev chartH1ModuleInst : Module (chartGlobalRing B S hS f d) (chartH1 B S hS f d) :=
  letI := chartDiagramAlgebraInst B S hS f d
  Module.compHom _ (chartEvalTop B S hS f d)

/-- **`H = H₁(L_{A/R})` as a module over the global functions of the slice at `V`**, with its
elements lifted to the universe of the sections of `NL_{X/Y}`. -/
def chartH1GlobalModule : ModuleCat.{u + 1} (chartGlobalRing B S hS f d) :=
  letI := chartH1ModuleInst B S hS f d
  ModuleCat.of _ (ULift.{u + 1} (chartH1 B S hS f d))

/-- An element of `H`, as an element of the `Γ`-module `H`. -/
def chartH1Up (h : chartH1 B S hS f d) : chartH1GlobalModule B S hS f d :=
  ULift.up h

/-- The element of `H` underlying an element of the `Γ`-module `H`. -/
def chartH1Down (m : chartH1GlobalModule B S hS f d) : chartH1 B S hS f d :=
  ULift.down m

/-- `chartH1Down` is a left inverse of `chartH1Up`. -/
@[simp] theorem chartH1Down_up (h : chartH1 B S hS f d) :
    chartH1Down B S hS f d (chartH1Up B S hS f d h) = h := rfl

/-- `chartH1Up` is a left inverse of `chartH1Down`. -/
@[simp] theorem chartH1Up_down (m : chartH1GlobalModule B S hS f d) :
    chartH1Up B S hS f d (chartH1Down B S hS f d m) = m := rfl

/-- The element of `H` underlying `0` is `0`. -/
theorem chartH1Down_zero : chartH1Down B S hS f d 0 = 0 := rfl

/-- Passing from the `Γ`-module `H` to `H` is additive. -/
theorem chartH1Down_add (m₁ m₂ : chartH1GlobalModule B S hS f d) :
    chartH1Down B S hS f d (m₁ + m₂) = chartH1Down B S hS f d m₁ + chartH1Down B S hS f d m₂ :=
  rfl

/-- A global function `γ` acts on the `Γ`-module `H` as its value at the final object acts on
`H`. -/
theorem chartH1Down_smul (γ : chartGlobalRing B S hS f d) (m : chartH1GlobalModule B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    chartH1Down B S hS f d (γ • m) = chartEvalTop B S hS f d γ • chartH1Down B S hS f d m :=
  rfl

/-! ### `𝒪_X(U) ⊗_Γ H = 𝒪_X(U) ⊗_A H` -/

/-- The tensor product over `Γ` appearing in the presheaf `U ↦ 𝒪_X(U) ⊗_Γ H`. -/
abbrev chartGlobalTensor (U : Over d.U) : Type (u + 1) :=
  TensorProduct (chartGlobalRing B S hS f d) ((chartSliceRing B S hS f d).obj.obj (op U))
    (chartH1GlobalModule B S hS f d)

/-- The tensor product over `A` on which `τ` is defined. -/
abbrev chartLocalTensor (U : Over d.U) : Type u :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d

/-- A regular function on a chart `U` over `V`, read as a section of the restricted structure
sheaf. -/
def toSliceSection (U : Over d.U)
    (s : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) :
    (chartSliceRing B S hS f d).obj.obj (op U) :=
  s

/-- A section of the restricted structure sheaf, read as a regular function on the chart. -/
def ofSliceSection (U : Over d.U) (s : (chartSliceRing B S hS f d).obj.obj (op U)) :
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)) :=
  s

/-- A global function acts on the regular functions on a chart over `V` through its value at
the final object. -/
theorem ofSliceSection_smul (U : Over d.U) (γ : chartGlobalRing B S hS f d)
    (s : (chartSliceRing B S hS f d).obj.obj (op U)) :
    ofSliceSection B S hS f d U (γ • s) =
      chartDiagramRestrictO B S hS f d U (chartEvalTop B S hS f d γ) *
        ofSliceSection B S hS f d U s :=
  congrArg (· * ofSliceSection B S hS f d U s)
    (chartDiagramRestrictO_chartEvalTop B S hS f d U γ).symm

/-- `𝒪_X(U) ⊗_Γ H ⟶ 𝒪_X(U) ⊗_A H`, `s ⊗ h ↦ s ⊗ h`. -/
def chartTensorToLocal (U : Over d.U) :
    chartGlobalTensor B S hS f d U →+ chartLocalTensor B S hS f d U :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun m => ofSliceSection B S hS f d U s ⊗ₜ chartH1Down B S hS f d m
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun m₁ m₂ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun m => TensorProduct.zero_tmul _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun m => TensorProduct.add_tmul _ _ _ }
    (fun γ s m => by
      change ofSliceSection B S hS f d U (γ • s) ⊗ₜ[ToType
            ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1Down B S hS f d m =
        ofSliceSection B S hS f d U s ⊗ₜ[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj
            (op d.U))] (chartEvalTop B S hS f d γ • chartH1Down B S hS f d m)
      rw [ofSliceSection_smul]
      exact TensorProduct.smul_tmul (chartEvalTop B S hS f d γ) (ofSliceSection B S hS f d U s)
        (chartH1Down B S hS f d m))

/-- `chartTensorToLocal` sends `s ⊗ m` to `s ⊗ m`. -/
theorem chartTensorToLocal_tmul (U : Over d.U)
    (s : (chartSliceRing B S hS f d).obj.obj (op U)) (m : chartH1GlobalModule B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    chartTensorToLocal B S hS f d U (s ⊗ₜ m) =
      ofSliceSection B S hS f d U s ⊗ₜ chartH1Down B S hS f d m :=
  rfl

/-- `𝒪_X(U) ⊗_A H ⟶ 𝒪_X(U) ⊗_Γ H`, `s ⊗ h ↦ s ⊗ h`. -/
def chartTensorOfLocal (U : Over d.U) :
    chartLocalTensor B S hS f d U →+ chartGlobalTensor B S hS f d U :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => toSliceSection B S hS f d U s ⊗ₜ chartH1Up B S hS f d h
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun h₁ h₂ => TensorProduct.tmul_add _ _ _ }
      map_zero' := AddMonoidHom.ext fun h => TensorProduct.zero_tmul _ _
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h => TensorProduct.add_tmul _ _ _ }
    (fun a s h => by
      have e : (chartGlobalSection B S hS f d a) • chartH1Up B S hS f d h =
          chartH1Up B S hS f d (a • h) := by
        change chartH1Up B S hS f d
          (chartEvalTop B S hS f d (chartGlobalSection B S hS f d a) • h) = _
        rw [chartEvalTop_chartGlobalSection]
      change toSliceSection B S hS f d U (chartDiagramRestrictO B S hS f d U a * s) ⊗ₜ
          chartH1Up B S hS f d h = toSliceSection B S hS f d U s ⊗ₜ chartH1Up B S hS f d (a • h)
      rw [← e, TensorProduct.tmul_smul]
      rfl)

/-- `chartTensorOfLocal` sends `s ⊗ h` to `s ⊗ h`. -/
theorem chartTensorOfLocal_tmul (U : Over d.U)
    (s : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
    (h : chartH1 B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    chartTensorOfLocal B S hS f d U (s ⊗ₜ h) =
      toSliceSection B S hS f d U s ⊗ₜ chartH1Up B S hS f d h :=
  rfl

/-- **`𝒪_X(U) ⊗_Γ H = 𝒪_X(U) ⊗_A H`.** -/
def chartTensorEquiv (U : Over d.U) :
    chartGlobalTensor B S hS f d U ≃+ chartLocalTensor B S hS f d U where
  toFun := chartTensorToLocal B S hS f d U
  invFun := chartTensorOfLocal B S hS f d U
  left_inv t := by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s m => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  right_inv t := by
    let := chartDiagramAlgebraInst B S hS f d
    let := chartDiagramRestrictAlgebra B S hS f d U
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s h => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  map_add' := map_add _

/-- The identification `chartTensorEquiv` is given by `chartTensorToLocal`. -/
theorem chartTensorEquiv_apply (U : Over d.U) (t : chartGlobalTensor B S hS f d U) :
    chartTensorEquiv B S hS f d U t = chartTensorToLocal B S hS f d U t :=
  rfl

/-- The identification commutes with restriction. -/
theorem chartTensorToLocal_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (t : chartGlobalTensor B S hS f d U₁) :
    chartTensorToLocal B S hS f d U₂
        (tensorRestriction (O := chartSliceRing B S hS f d) (chartH1GlobalModule B S hS f d)
          g.op t) =
      chartRestrictTensor B S hS f d g (chartTensorToLocal B S hS f d U₁ t) :=
  sectionTensorAddHom_ext (O := chartSliceRing B S hS f d)
    (g := (chartTensorToLocal B S hS f d U₂).comp
      (tensorRestriction (O := chartSliceRing B S hS f d) (chartH1GlobalModule B S hS f d)
        g.op).toAddMonoidHom)
    (h := (chartRestrictTensor B S hS f d g).toAddMonoidHom.comp
      (chartTensorToLocal B S hS f d U₁)) (fun _ _ => rfl) t

/-! ### The degree `-1` cohomology sheaf -/

/-- The conormal sequence of the canonical presentation of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, whose left-hand
map is the differential of `NL_{X/Y}`. -/
abbrev naiveCotangentConormalSequence :=
  Stacks.SheafOfModules.presentationConormalSequence.{u, u + 1, u, u}
    _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)

/-- **The kernel `𝒦` of the differential of `NL_{X/Y}`**, its degree `-1` cohomology sheaf. -/
abbrev naiveCotangentKernel :=
  kernel (naiveCotangentConormalSequence B S hS f).f

/-- The inclusion of `𝒦` into the conormal sheaf, on sections over a chart. -/
abbrev naiveCotangentKernelι (U : SmallEtale B S hS X.1) :=
  ((kernel.ι (naiveCotangentConormalSequence B S hS f).f).val.app (op U)).hom

/-- The inclusion of `𝒦` into the conormal sheaf is injective on sections over each chart. -/
theorem naiveCotangentKernelι_injective (U : SmallEtale B S hS X.1) :
    Function.Injective (naiveCotangentKernelι B S hS f U) :=
  Stacks.SheafOfModules.injective_app_kernel_ι _ (op U)

/-- The comparison `σ` of `Stacks.SheafOfModules.sectionsH1Comparison` for `f♯`. -/
abbrev naiveCotangentSigma (U : SmallEtale B S hS X.1) :=
  Stacks.SheafOfModules.sectionsH1Comparison.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (op U)

/-- The image under `σ` of an element of `H` in `H₁(L_{𝒪_X(V)/(f⁻¹𝒪_Y)(V)})` is the image of a
section of `𝒦` over `V`. -/
theorem exists_chartKernelSection (h : chartH1 B S hS f d) :
    ∃ k : ToType ((naiveCotangentKernel B S hS f).val.obj (op d.U)),
      naiveCotangentKernelι B S hS f d.U k =
        naiveCotangentSigma B S hS f d.U (chartH1Map B S hS f d (Over.mk (𝟙 d.U)) h) :=
  Stacks.SheafOfModules.exists_kernel_section _ (op d.U) _
    (Stacks.SheafOfModules.sectionsH1Comparison_d.{u, u + 1, u, u} _ _ _ _ (op d.U) _)

/-- The section of `𝒦` over `V` attached to an element of `H`: the comparison `σ` applied to its
image in `H₁(L_{𝒪_X(V)/(f⁻¹𝒪_Y)(V)})`, which is killed by the differential. -/
def chartKernelSection (h : chartH1 B S hS f d) :
    ToType ((naiveCotangentKernel B S hS f).val.obj (op d.U)) :=
  (exists_chartKernelSection B S hS f d h).choose

/-- The image of `chartKernelSection h` in the conormal sheaf is the image of `h` under `σ`. -/
theorem naiveCotangentKernelι_chartKernelSection (h : chartH1 B S hS f d) :
    naiveCotangentKernelι B S hS f d.U (chartKernelSection B S hS f d h) =
      naiveCotangentSigma B S hS f d.U (chartH1Map B S hS f d (Over.mk (𝟙 d.U)) h) :=
  (exists_chartKernelSection B S hS f d h).choose_spec

/-- `chartKernelSection` is additive. -/
theorem chartKernelSection_add (h₁ h₂ : chartH1 B S hS f d) :
    chartKernelSection B S hS f d (h₁ + h₂) =
      chartKernelSection B S hS f d h₁ + chartKernelSection B S hS f d h₂ := by
  apply naiveCotangentKernelι_injective B S hS f d.U
  refine (naiveCotangentKernelι_chartKernelSection B S hS f d _).trans ?_
  refine Eq.trans ?_ (map_add (naiveCotangentKernelι B S hS f d.U) _ _).symm
  refine (congrArg (naiveCotangentSigma B S hS f d.U)
    (map_add (chartH1Map B S hS f d (Over.mk (𝟙 d.U))) h₁ h₂)).trans ?_
  refine (map_add (naiveCotangentSigma B S hS f d.U) _ _).trans ?_
  exact congrArg₂ (· + ·) (naiveCotangentKernelι_chartKernelSection B S hS f d h₁).symm
    (naiveCotangentKernelι_chartKernelSection B S hS f d h₂).symm

/-- `chartKernelSection` is linear over the functions on `V`. -/
theorem chartKernelSection_smul (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
    (h : chartH1 B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    chartKernelSection B S hS f d (a • h) =
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).obj.obj
        (op d.U)) • chartKernelSection B S hS f d h := by
  let := chartDiagramAlgebraInst B S hS f d
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (op (Over.mk (𝟙 d.U)).left)
  apply naiveCotangentKernelι_injective B S hS f d.U
  refine (naiveCotangentKernelι_chartKernelSection B S hS f d (a • h)).trans ?_
  refine Eq.trans ?_ (map_smul (naiveCotangentKernelι B S hS f d.U) _ _).symm
  refine Eq.trans ?_ (congrArg (_ • ·) (naiveCotangentKernelι_chartKernelSection B S hS f d h).symm)
  have e : chartH1Map B S hS f d (Over.mk (𝟙 d.U)) (a • h) =
      (show ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op (Over.mk (𝟙 d.U)).left))
        from a) • chartH1Map B S hS f d (Over.mk (𝟙 d.U)) h := by
    refine (Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ a h).trans ?_
    exact congrArg (· • chartH1Map B S hS f d (Over.mk (𝟙 d.U)) h)
      (ConcreteCategory.congr_hom ((smallEtaleRingedTopos B S hS X).O.obj.map_id (op d.U)) a)
  refine (congrArg (naiveCotangentSigma B S hS f d.U) e).trans ?_
  exact Stacks.SheafOfModules.sectionsH1Comparison_smul.{u, u + 1, u, u} _ _ _ _ (op d.U) a _

/-! ### The comparison morphism on the slice at `V` -/

/-- The final object of the slice at `V`, with the canonical morphisms into it. -/
def chartTopIsTerminal : IsTerminal (Over.mk (𝟙 d.U)) :=
  IsTerminal.ofUniqueHom (fun U => chartToTop B S hS f d U) (fun U m =>
    Over.OverMorphism.ext (by simpa using Over.w m))

/-- The structure sheaf of the slice at `V`, as a sheaf of rings, in the spelling of the
global-sections API. -/
abbrev chartSliceRingSheaf :=
  @ringSheafOfSite _ _ _ (Stacks.hasSheafCompose_forget₂_commRingCat _) (chartSliceRing B S hS f d)

/-- **The restriction of `𝒦` to the slice at `V`.** -/
abbrev chartKernelSlice : _root_.SheafOfModules.{u + 1} (chartSliceRingSheaf B S hS f d) :=
  (naiveCotangentKernel B S hS f).over d.U

/-- The global section of `𝒦|_V` attached to an element of `H`. -/
def chartKernelGlobalSection (h : chartH1 B S hS f d) : (chartKernelSlice B S hS f d).sections :=
  (chartKernelSlice B S hS f d).val.sectionsOfIsTerminal (chartTopIsTerminal B S hS f d)
    (chartKernelSection B S hS f d h)

/-- The value of `chartKernelGlobalSection h` at a chart `U` over `V` is the restriction of
`chartKernelSection h` to `U`. -/
theorem chartKernelGlobalSection_val (h : chartH1 B S hS f d) (U : Over d.U) :
    (chartKernelGlobalSection B S hS f d h).val (op U) =
      (naiveCotangentKernel B S hS f).val.map U.hom.op (chartKernelSection B S hS f d h) :=
  rfl

/-- **The `Γ`-linear map `H ⟶ Γ(𝒦|_V)`** sending `h` to the global section restricted from the
section of `𝒦` over `V` attached to `h`. -/
def chartKernelTheta :
    chartH1GlobalModule B S hS f d ⟶
      (globalSectionsFunctor (chartSliceRingSheaf B S hS f d)).obj (chartKernelSlice B S hS f d) :=
  ModuleCat.ofHom (X := chartH1GlobalModule B S hS f d)
      (Y := (globalSectionsFunctor (chartSliceRingSheaf B S hS f d)).obj
        (chartKernelSlice B S hS f d))
    { toFun := fun m => chartKernelGlobalSection B S hS f d (chartH1Down B S hS f d m)
      map_add' := fun m₁ m₂ => by
        refine PresheafOfModules.sections_ext _ _ fun U => ?_
        change (naiveCotangentKernel B S hS f).val.map U.unop.hom.op
            (chartKernelSection B S hS f d (chartH1Down B S hS f d m₁ +
              chartH1Down B S hS f d m₂)) =
          (naiveCotangentKernel B S hS f).val.map U.unop.hom.op
              (chartKernelSection B S hS f d (chartH1Down B S hS f d m₁)) +
            (naiveCotangentKernel B S hS f).val.map U.unop.hom.op
              (chartKernelSection B S hS f d (chartH1Down B S hS f d m₂))
        rw [chartKernelSection_add]
        exact map_add _ _ _
      map_smul' := fun γ m => by
        let := chartDiagramAlgebraInst B S hS f d
        refine PresheafOfModules.sections_ext _ _ fun U => ?_
        have e := chartKernelSection_smul B S hS f d (chartEvalTop B S hS f d γ)
          (chartH1Down B S hS f d m)
        change (chartKernelSlice B S hS f d).val.map
            ((chartTopIsTerminal B S hS f d).from U.unop).op
            (chartKernelSection B S hS f d
              (chartEvalTop B S hS f d γ • chartH1Down B S hS f d m)) =
          γ.1 U • ((chartKernelSlice B S hS f d).val.map
            ((chartTopIsTerminal B S hS f d).from U.unop).op
            (chartKernelSection B S hS f d (chartH1Down B S hS f d m)) :
              (chartKernelSlice B S hS f d).val.obj U)
        rw [e]
        exact ((chartKernelSlice B S hS f d).val.map_smul _ _ _).trans
          (congrArg (· • _) (globalSectionEvalHom_naturality _ γ)) }

/-- The value of `chartKernelTheta m` at a chart `U` over `V` is the restriction to `U` of the
section of `𝒦` over `V` attached to `m`. -/
theorem chartKernelTheta_apply_val (m : chartH1GlobalModule B S hS f d) (U : Over d.U) :
    ((chartKernelTheta B S hS f d).hom m).val (op U) =
      (naiveCotangentKernel B S hS f).val.map U.hom.op
        (chartKernelSection B S hS f d (chartH1Down B S hS f d m)) :=
  chartKernelGlobalSection_val B S hS f d _ U

/-- **The comparison morphism of presheaves of modules** `(U ↦ 𝒪_X(U) ⊗_Γ H) ⟶ 𝒦|_V`,
`s ⊗ h ↦ s · (image of h in 𝒦(V))|_U`. -/
def chartKernelPresheafHom :
    sectionTensorPresheaf (O := chartSliceRing B S hS f d) (chartH1GlobalModule B S hS f d) ⟶
      underlyingPresheaf.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
        (chartKernelSlice B S hS f d) :=
  sectionTensorPresheafHomOfSections.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
    (chartKernelTheta B S hS f d)

/-- The image in `𝒦(V)` of an element of `H` restricts to the image of its image in
`H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`. -/
theorem naiveCotangentKernelι_map_chartKernelSection (U : Over d.U) (h : chartH1 B S hS f d) :
    naiveCotangentKernelι B S hS f U.left
        ((naiveCotangentKernel B S hS f).val.map U.hom.op (chartKernelSection B S hS f d h)) =
      naiveCotangentSigma B S hS f U.left (chartH1Map B S hS f d U h) := by
  refine (PresheafOfModules.naturality_apply
    (kernel.ι (naiveCotangentConormalSequence B S hS f).f).val U.hom.op _).trans ?_
  refine (congrArg _ (naiveCotangentKernelι_chartKernelSection B S hS f d h)).trans ?_
  refine (Stacks.SheafOfModules.sectionsH1Comparison_restrict.{u, u + 1, u, u} _ _ _ _
    U.hom.op _).symm.trans ?_
  exact congrArg (naiveCotangentSigma B S hS f U.left)
    (chartH1Map_restrict B S hS f d (chartToTop B S hS f d U) h)

/-- **The comparison factors as `σ ∘ τ`**: composed with the inclusion of `𝒦` into the conormal
sheaf, it is `τ` followed by `σ`. -/
theorem naiveCotangentKernelι_chartKernelPresheafHom (U : Over d.U)
    (t : chartGlobalTensor B S hS f d U) :
    naiveCotangentKernelι B S hS f U.left (((chartKernelPresheafHom B S hS f d).app (op U)).hom t) =
      naiveCotangentSigma B S hS f U.left
        (chartH1Tensor B S hS f d U (chartTensorToLocal B S hS f d U t)) := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  refine sectionTensorAddHom_ext (O := chartSliceRing B S hS f d)
    (g := (naiveCotangentKernelι B S hS f U.left).toAddMonoidHom.comp
      (sectionTensorLift.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
        (chartKernelTheta B S hS f d) (op U)))
    (h := ((naiveCotangentSigma B S hS f U.left).comp (chartH1Tensor B S hS f d U)).comp
      (chartTensorToLocal B S hS f d U)) (fun s m => ?_) t
  show naiveCotangentKernelι B S hS f U.left
      (ringSheafSection s • ((chartKernelTheta B S hS f d).hom m).eval (op U)) =
    naiveCotangentSigma B S hS f U.left
      (ofSliceSection B S hS f d U s • chartH1Map B S hS f d U (chartH1Down B S hS f d m))
  refine (map_smul (naiveCotangentKernelι B S hS f U.left) _ _).trans ?_
  refine (congrArg (fun x => (show (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O).obj.obj (op U.left) from s) • x)
    (naiveCotangentKernelι_map_chartKernelSection B S hS f d U
      (chartH1Down B S hS f d m))).trans ?_
  exact (Stacks.SheafOfModules.sectionsH1Comparison_smul.{u, u + 1, u, u} _ _ _ _ (op U.left)
    (ofSliceSection B S hS f d U s) _).symm

/-- `chartTensorToLocal` is injective. -/
theorem chartTensorToLocal_injective (U : Over d.U) :
    Function.Injective (chartTensorToLocal B S hS f d U) :=
  (chartTensorEquiv B S hS f d U).injective

/-! ### Local bijectivity of the comparison -/

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

include hU hW in
/-- **Local injectivity of the comparison**: an element of `𝒪_X(U) ⊗_Γ H` killed by the
comparison restricts, through `𝒪_X(U) ⊗_Γ H = 𝒪_X(U) ⊗_A H`, to zero on a covering. -/
theorem chartTensorVanishingSieve_mem_of_chartKernelPresheafHom (U : Over d.U)
    (t : chartGlobalTensor B S hS f d U)
    (ht : ((chartKernelPresheafHom B S hS f d).app (op U)).hom t = 0) :
    chartTensorVanishingSieve B S hS f d U (chartTensorToLocal B S hS f d U t) ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  let t' := chartTensorToLocal B S hS f d U t
  have h1 : naiveCotangentSigma B S hS f U.left (chartH1Tensor B S hS f d U t') = 0 := by
    refine (naiveCotangentKernelι_chartKernelPresheafHom B S hS f d U t).symm.trans ?_
    refine (congrArg (naiveCotangentKernelι B S hS f U.left)
      (ht.trans (map_zero ((chartKernelPresheafHom B S hS f d).app (op U)).hom).symm)).trans ?_
    refine (naiveCotangentKernelι_chartKernelPresheafHom B S hS f d U 0).trans ?_
    rw [map_zero, map_zero, map_zero]
  have hS1 := Stacks.SheafOfModules.sectionsH1VanishingSieve_mem.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) _ h1
  refine GrothendieckTopology.transitive _ (overEquiv_symm_mem_over _ U _ hS1) _
    fun V g hg => ?_
  rw [Sieve.overEquiv_symm_iff] at hg
  have h2 : chartH1Tensor B S hS f d V (chartRestrictTensor B S hS f d g t') = 0 := by
    rwa [← chartH1Tensor_restrict]
  refine GrothendieckTopology.superset_covering _ ?_
    (chartTensorVanishingSieve_mem B S hS f d hU hW V _ h2)
  intro W k hk
  show chartRestrictTensor B S hS f d (k ≫ g) t' = 0
  rwa [Point.restrictTensor_comp]

/-- The differential of `NL_{X/Y}` vanishes on the image of `𝒦` in the conormal sheaf. -/
theorem naiveCotangentKernelι_d (U : SmallEtale B S hS X.1)
    (k : ToType ((naiveCotangentKernel B S hS f).val.obj (op U))) :
    (naiveCotangentConormalSequence B S hS f).f.val.app (op U)
      (naiveCotangentKernelι B S hS f U k) = 0 :=
  (congrArg (fun t => t.val.app (op U) k)
    (kernel.condition (naiveCotangentConormalSequence B S hS f).f)).trans rfl

include hU hW in
/-- **Local surjectivity of the comparison.** -/
theorem chartKernelPresheafHom_imageSieve_mem (U : Over d.U)
    (k : ToType ((naiveCotangentKernel B S hS f).val.obj (op U.left))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map (chartKernelPresheafHom B S hS f d))
        (show ToType (((PresheafOfModules.toPresheaf _).obj
          (underlyingPresheaf.{u + 1, u, u, u} (O := chartSliceRing B S hS f d)
            (chartKernelSlice B S hS f d))).obj (op U)) from k) ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  have hS1 := Stacks.SheafOfModules.sectionsH1LiftSieve_mem.{u, u + 1, u, u} _
    (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
    (structureSharpInverseImage B S hS f) (naiveCotangentKernelι B S hS f U.left k)
    (naiveCotangentKernelι_d B S hS f U.left k)
  refine GrothendieckTopology.transitive _ (overEquiv_symm_mem_over _ U _ hS1) _
    fun V g hg => ?_
  rw [Sieve.overEquiv_symm_iff] at hg
  obtain ⟨z, hz⟩ := hg
  refine GrothendieckTopology.superset_covering _ ?_
    (chartTensorLiftSieve_mem B S hS f d hU hW V z)
  rintro W m ⟨t, ht⟩
  refine ⟨chartTensorOfLocal B S hS f d W t, ?_⟩
  apply naiveCotangentKernelι_injective B S hS f W.left
  refine (naiveCotangentKernelι_chartKernelPresheafHom B S hS f d W _).trans ?_
  refine (congrArg (fun x => naiveCotangentSigma B S hS f W.left (chartH1Tensor B S hS f d W x))
    ((chartTensorEquiv B S hS f d W).apply_symm_apply t)).trans ?_
  refine (congrArg (naiveCotangentSigma B S hS f W.left) ht).trans ?_
  refine (Stacks.SheafOfModules.sectionsH1Comparison_restrict.{u, u + 1, u, u} _ _ _ _
    m.left.op z).trans ?_
  refine (congrArg ((naiveCotangentConormalSequence B S hS f).X₁.val.map m.left.op) hz).trans ?_
  refine ((naiveCotangentConormalSequence B S hS f).X₁.val.map_comp_apply g.left.op m.left.op
    _).symm.trans ?_
  exact (PresheafOfModules.naturality_apply
    (kernel.ι (naiveCotangentConormalSequence B S hS f).f).val (m ≫ g).left.op k).symm

include hU hW in
/-- The comparison morphism `chartKernelPresheafHom` is locally injective. -/
theorem chartKernelPresheafHom_isLocallyInjective :
    PresheafOfModules.IsLocallyInjective ((SmallEtale.topology B S hS X.1).over d.U)
      (chartKernelPresheafHom B S hS f d) := by
  constructor
  intro U x y hxy
  let x' : chartGlobalTensor B S hS f d U.unop := x
  let y' : chartGlobalTensor B S hS f d U.unop := y
  have hxy' : ((chartKernelPresheafHom B S hS f d).app (op U.unop)).hom x' =
      ((chartKernelPresheafHom B S hS f d).app (op U.unop)).hom y' := hxy
  have ht : ((chartKernelPresheafHom B S hS f d).app (op U.unop)).hom (x' - y') = 0 :=
    (map_sub ((chartKernelPresheafHom B S hS f d).app (op U.unop)).hom x' y').trans
      (sub_eq_zero.mpr hxy')
  refine GrothendieckTopology.superset_covering _ ?_
    (chartTensorVanishingSieve_mem_of_chartKernelPresheafHom B S hS f d hU hW U.unop (x' - y') ht)
  intro V g hg
  have e1 := map_sub (chartTensorToLocal B S hS f d U.unop) x' y'
  have e2 := map_sub (chartRestrictTensor B S hS f d g) (chartTensorToLocal B S hS f d U.unop x')
    (chartTensorToLocal B S hS f d U.unop y')
  have hg' : chartRestrictTensor B S hS f d g (chartTensorToLocal B S hS f d U.unop x') =
      chartRestrictTensor B S hS f d g (chartTensorToLocal B S hS f d U.unop y') :=
    sub_eq_zero.mp (e2.symm.trans ((congrArg _ e1).symm.trans hg))
  have key : tensorRestriction (O := chartSliceRing B S hS f d) (chartH1GlobalModule B S hS f d)
      g.op x' = tensorRestriction (O := chartSliceRing B S hS f d)
        (chartH1GlobalModule B S hS f d) g.op y' :=
    chartTensorToLocal_injective B S hS f d V ((chartTensorToLocal_restrict B S hS f d g x').trans
      (hg'.trans (chartTensorToLocal_restrict B S hS f d g y').symm))
  exact key

include hU hW in
/-- The comparison morphism `chartKernelPresheafHom` is locally surjective. -/
theorem chartKernelPresheafHom_isLocallySurjective :
    PresheafOfModules.IsLocallySurjective ((SmallEtale.topology B S hS X.1).over d.U)
      (chartKernelPresheafHom B S hS f d) := by
  constructor
  intro U k
  exact chartKernelPresheafHom_imageSieve_mem B S hS f d hU hW U k

/-! ### The identification `𝒦|_V ≅ H ⊗_Γ 𝒪` -/

/-- The morphism of sheaves of modules `H ⊗_Γ 𝒪 ⟶ 𝒦|_V` induced by the comparison, through the
universal property of sheafification. -/
def chartKernelSliceHom :
    (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).obj
        (chartH1GlobalModule B S hS f d) ⟶ chartKernelSlice B S hS f d :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (chartSliceRingSheaf B S hS f d).obj)).homEquiv
    _ _).symm (chartKernelPresheafHom B S hS f d)

/-- The unit of sheafification followed by `chartKernelSliceHom` is `chartKernelPresheafHom`. -/
theorem chartKernelSliceHom_fac :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
        (sectionTensorPresheaf (O := chartSliceRing B S hS f d) (chartH1GlobalModule B S hS f d)) ≫
      (chartKernelSliceHom B S hS f d).val = chartKernelPresheafHom B S hS f d :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (chartSliceRingSheaf B S hS f d).obj)).homEquiv_unit _ _ _).symm.trans
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (chartSliceRingSheaf B S hS f d).obj)).homEquiv _ _).apply_symm_apply _)

include hU hW in
/-- The morphism `chartKernelSliceHom : H ⊗_Γ 𝒪 ⟶ 𝒦|_V` is an isomorphism. -/
theorem isIso_chartKernelSliceHom : IsIso (chartKernelSliceHom B S hS f d) := by
  have := chartKernelPresheafHom_isLocallyInjective B S hS f d hU hW
  have := chartKernelPresheafHom_isLocallySurjective B S hS f d hU hW
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (chartSliceRingSheaf B S hS f d).obj)).unit.app
    (sectionTensorPresheaf.{u + 1, u, u, u + 1} (O := chartSliceRing B S hS f d)
      (chartH1GlobalModule B S hS f d))
  have hi : PresheafOfModules.IsLocallyInjective
      ((SmallEtale.topology B S hS X.1).over d.U) η := by
    show Presheaf.IsLocallyInjective _ (CategoryTheory.toSheafify _ _)
    exact Presheaf.isLocallyInjective_toSheafify'.{u + 1, u, u + 2, u + 1, u + 1} _ _
  have hs : PresheafOfModules.IsLocallySurjective
      ((SmallEtale.topology B S hS X.1).over d.U) η := by
    show Presheaf.IsLocallySurjective _ (CategoryTheory.toSheafify _ _)
    exact Presheaf.isLocallySurjective_toSheafify'.{u, u + 1, u + 1, u + 2, u + 1} _ _
  exact @Stacks.SheafOfModules.isIso_of_fac_of_isLocallyBijective _ _ _ _ _ _ _ _ _
    (chartKernelSliceHom B S hS f d) (chartKernelSliceHom_fac B S hS f d) hi hs ‹_› ‹_›

/-- **`𝒦|_V ≅ H ⊗_Γ 𝒪`**: the restriction of the degree `-1` cohomology sheaf of `NL_{X/Y}` to
the slice at an affine chart `V = Spec A` lying over an affine chart `W = Spec R` of `Y` is the
sheaf attached to the module `H₁(L_{A/R})`. -/
def chartKernelSliceIso :
    (sectionTensorSheafFunctor.{u + 1, u, u, u} (chartSliceRing B S hS f d)).obj
        (chartH1GlobalModule B S hS f d) ≅ chartKernelSlice B S hS f d :=
  have := isIso_chartKernelSliceHom B S hS f d hU hW
  asIso (chartKernelSliceHom B S hS f d)

include hU hW in
/-- `𝒦|_V` has a global presentation. -/
theorem hasGlobalPresentation_chartKernelSlice :
    (chartKernelSlice B S hS f d).HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_iso (chartKernelSliceIso B S hS f d hU hW)
    (hasGlobalPresentation_sectionTensor_of_isTerminal (O := chartSliceRing B S hS f d)
      (chartTopIsTerminal B S hS f d) (chartH1GlobalModule B S hS f d))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The chart diagram carried by a chart of `X` with an affine chart diagram over `f`. -/
def chartDiagramOfHasAffineChartDiagram {W : SmallEtale B S hS X.1}
    (hW : HasAffineChartDiagram B S hS f W) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := W
  V := hW.2.choose
  g := hW.2.choose_spec.choose
  comm := hW.2.choose_spec.choose_spec.1.symm

/-- **The degree `-1` cohomology sheaf `𝒦` of `NL_{X/Y}` is quasi-coherent.**  On each chart of
`X` carrying an affine chart diagram over `f` it has a global presentation
(`AlgebraicGeometry.Space.hasGlobalPresentation_chartKernelSlice`), and those charts cover `X`
(`AlgebraicGeometry.Space.mem_topology_of_hasAffineChartDiagram`). -/
theorem isQuasicoherentOnSite_naiveCotangentKernel :
    (naiveCotangentKernel B S hS f).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation _
    (I := {W : SmallEtale B S hS X.1 // HasAffineChartDiagram B S hS f W}) (W := Subtype.val)
    (fun U => mem_topology_of_hasAffineChartDiagram B S hS f U _
      fun {W} _ hW => ⟨⟨W, hW⟩, ⟨𝟙 W⟩⟩) fun i => ?_
  exact hasGlobalPresentation_chartKernelSlice B S hS f
    (chartDiagramOfHasAffineChartDiagram B S hS f i.2) i.2.1
    i.2.2.choose_spec.choose_spec.2

/-- The degree `-1` cohomology sheaf of `NL_{X/Y}` is the kernel `𝒦` of its differential. -/
noncomputable def naiveCotangentComplexHomologyNegOneIso :
    (naiveCotangentComplex B S hS f).homology (-1) ≅ naiveCotangentKernel B S hS f :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplexHomologyNegOneIso.{u, u + 1, u, u}
    (SmallEtale.topology B S hS X.1) (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f)
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf _ (smallEtaleRingedTopos B S hS X).O) (𝟙 _)

/-- **The degree `-1` cohomology sheaf of `NL_{X/Y}` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_homology_negOne_naiveCotangentComplex :
    ((naiveCotangentComplex B S hS f).homology (-1)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (naiveCotangentComplexHomologyNegOneIso B S hS f).symm
    (isQuasicoherentOnSite_naiveCotangentKernel B S hS f)

end AlgebraicGeometry.Space
