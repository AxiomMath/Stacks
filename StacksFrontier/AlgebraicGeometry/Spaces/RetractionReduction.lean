module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.RingTheory.TensorProduct.OneTmulKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# Reduction of a module along a section of a retraction

Let `r : X' ⟶ X₀` be a representable morphism of algebraic spaces over a scheme `S` and
`i : X₀ ⟶ X'` a section of it, `i ≫ r = 𝟙`. For an `𝒪_{X'}`-module `ℱ` let `r_*ℱ` be its direct
image along small-chart base change, whose sections over an étale chart `U` of `X₀` are the
sections of `ℱ` over `U' = U ×_{X₀} X'`. The section `i` gives, over every chart `U`, a diagram of
étale charts `U ⟶ U'` over `i`, and the chart component of the unit of the adjunction
`i^* ⊣ i_*` at that diagram is a map `ℱ(U') ⟶ (i^*ℱ)(U)`. These maps make up a morphism of
`𝒪_{X₀}`-modules

`r_*ℱ ⟶ i^*ℱ`,

the *reduction* of `ℱ` along `i`. When `X'` is a first order thickening of `X₀` split by `r`,
this is the projection of the direct image of a deformation onto the special fibre, and it is the
right-hand map of the extension classifying the deformation in Stacks 08W8.

## Main definitions

* `AlgebraicGeometry.Space.retractionChartDiagram`: the diagram `U ⟶ U ×_{X₀} X'` of étale charts
  over `i`.
* `AlgebraicGeometry.Space.reductionMap`: the reduction `r_*ℱ ⟶ i^*ℱ`.

## Main results

* `AlgebraicGeometry.Space.reductionMap_app`: on sections over a chart `U` it is the chart
  component of the unit at `U ⟶ U'`.
* `AlgebraicGeometry.Space.reductionMap_naturality`: it is natural in `ℱ`.
* `AlgebraicGeometry.Space.surjective_reductionMap_app`: it is surjective on the sections over an
  affine chart when `ℱ` is quasi-coherent and the pullback of functions along `U ⟶ U'` is
  surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X₀ X' : AlgebraicSpaces B S hS} (r : X' ⟶ X₀) (hrep : yoneda.relativelyRepresentable r.hom)
  (i : X₀ ⟶ X') (hi : i ≫ r = 𝟙 X₀)

/-- The morphism `U ⟶ U ×_{X₀} X'` of the site attached to a section `i` of `r`: its two
components are the identity of `U` and the composite `U ⟶ X₀ ⟶ X'`. -/
def retractionChartMap (U : SmallEtale B S hS X₀.1) : U.1.left ⟶ hrep.pullback U.1.hom :=
  hrep.lift (U.1.hom ≫ i.hom) (𝟙 _) (by
    rw [Category.assoc, show i.hom ≫ r.hom = 𝟙 _ from congrArg (fun f => f.hom) hi,
      Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp])

/-- The composite `U ⟶ U ×_{X₀} X' ⟶ U` of the chart map with the second projection is the
identity. -/
theorem retractionChartMap_snd (U : SmallEtale B S hS X₀.1) :
    retractionChartMap B S hS r hrep i hi U ≫ hrep.snd U.1.hom = 𝟙 _ :=
  hrep.lift_snd _ _ _

/-- The composite of the chart map `U ⟶ U ×_{X₀} X'` with the first projection to `X'` is the
composite `U ⟶ X₀ ⟶ X'`. -/
theorem retractionChartMap_fst (U : SmallEtale B S hS X₀.1) :
    yoneda.map (retractionChartMap B S hS r hrep i hi U) ≫ hrep.fst U.1.hom =
      U.1.hom ≫ i.hom :=
  hrep.lift_fst _ _ _

/-- **The diagram of étale charts `U ⟶ U ×_{X₀} X'` over the section `i`.** -/
def retractionChartDiagram (U : SmallEtale B S hS X₀.1) : ChartDiagram B S hS X₀.1 X'.1 i.hom where
  U := U
  V := (smallBaseChange B S hS r hrep).obj U
  g := retractionChartMap B S hS r hrep i hi U
  comm := (retractionChartMap_fst B S hS r hrep i hi U).symm

/-- The chart maps commute with étale restriction of the chart of `X₀`. -/
theorem retractionChartMap_naturality {U₁ U₂ : SmallEtale B S hS X₀.1} (k : U₁ ⟶ U₂) :
    (SmallEtale.toOver B S hS X₀.1).map k ≫ retractionChartMap B S hS r hrep i hi U₂ =
      retractionChartMap B S hS r hrep i hi U₁ ≫
        (SmallEtale.toOver B S hS X'.1).map ((smallBaseChange B S hS r hrep).map k) := by
  let L : hrep.pullback U₁.1.hom ⟶ hrep.pullback U₂.1.hom :=
    hrep.lift (hrep.fst U₁.1.hom) (hrep.snd U₁.1.hom ≫ k.hom.left)
      (representablePullback_lift_cond B S hS r hrep k)
  have hk : yoneda.map k.hom.left ≫ U₂.1.hom = U₁.1.hom := CostructuredArrow.w k.hom
  have key : (k.hom.left ≫ retractionChartMap B S hS r hrep i hi U₂ :
        U₁.1.left ⟶ hrep.pullback U₂.1.hom) =
      retractionChartMap B S hS r hrep i hi U₁ ≫ L := by
    apply hrep.hom_ext
    · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        retractionChartMap_fst, hrep.lift_fst, retractionChartMap_fst, ← Category.assoc, hk]
    · rw [Category.assoc, Category.assoc, retractionChartMap_snd, hrep.lift_snd,
        ← Category.assoc, retractionChartMap_snd, Category.comp_id, Category.id_comp]
  exact key

/-- Pulling back the structure map of small-chart base change along the chart map is the
identity: the composite `U ⟶ U ×_{X₀} X' ⟶ U` is the identity. -/
theorem chartDiagramRestrict_retractionChartDiagram_smallBaseChangeSharp
    (U : SmallEtale B S hS X₀.1) (a : chartRing B S hS X₀.1 X₀.2 U) :
    chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)
        ((smallBaseChangeSharp B S hS r hrep).hom.app (op U) a) = a := by
  have h : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep.snd U.1.hom)).op ≫
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (retractionChartMap B S hS r hrep i hi U)).op = 𝟙 _ := by
    rw [← Scheme.Γ.map_comp, ← op_comp, ← Functor.map_comp, retractionChartMap_snd,
      CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  exact congrArg (fun f => f.hom a) h

/-- **The direct image along small-chart base change**, as a functor between the categories of
modules of the two algebraic spaces: the sections of `r_*ℱ` over a chart `U` of `X₀` are the
sections of `ℱ` over `U ×_{X₀} X'`. This is
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, typed with the module categories
`AlgebraicGeometry.Space.Modules` of the two spaces. -/
def retractionPushforward :
    Modules.{u, u} B S hS X'.1 X'.2 ⥤ Modules.{u, u} B S hS X₀.1 X₀.2 :=
  smallBaseChangeModulePushforward B S hS r hrep

variable (F : Modules.{u, u} B S hS X'.1 X'.2)

/-- **The reduction of `ℱ` along the section `i`**, `r_*ℱ ⟶ i^*ℱ`: over a chart `U` of `X₀` it
is the chart component of the unit of `i^* ⊣ i_*` at the diagram `U ⟶ U ×_{X₀} X'`. -/
def reductionMap :
    (retractionPushforward B S hS r hrep).obj F ⟶ (modulePullback B S hS i).obj F where
  val := PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := (modulePullbackChartFMap B S hS i F).app
            (retractionChartDiagram B S hS r hrep i hi U.unop)
          map_zero' := by
            have h := (modulePullbackChartFMap B S hS i F).map_add
              (retractionChartDiagram B S hS r hrep i hi U.unop) 0 0
            rw [add_zero] at h
            exact left_eq_add.mp h
          map_add' := (modulePullbackChartFMap B S hS i F).map_add
            (retractionChartDiagram B S hS r hrep i hi U.unop) }
      naturality := fun {U₁ U₂} k => by
        ext s
        exact (modulePullbackChartFMap B S hS i F).naturality
          (retractionChartDiagram B S hS r hrep i hi U₁.unop)
          (retractionChartDiagram B S hS r hrep i hi U₂.unop) k.unop
          ((smallBaseChange B S hS r hrep).map k.unop)
          (retractionChartMap_naturality B S hS r hrep i hi k.unop) s }
    (fun U a s => by
      refine ((modulePullbackChartFMap B S hS i F).map_smul
        (retractionChartDiagram B S hS r hrep i hi U.unop)
        ((smallBaseChangeSharp B S hS r hrep).hom.app U a) s).trans ?_
      congr 1
      exact chartDiagramRestrict_retractionChartDiagram_smallBaseChangeSharp B S hS r hrep i hi
        U.unop a)

/-- On sections over a chart `U` of `X₀`, the reduction is the chart component of the unit of
`i^* ⊣ i_*` at the diagram `U ⟶ U ×_{X₀} X'`. -/
theorem reductionMap_app (U : SmallEtale B S hS X₀.1)
    (s : F.val.obj (op ((smallBaseChange B S hS r hrep).obj U))) :
    (reductionMap B S hS r hrep i hi F).val.app (op U) s =
      modulePullbackChartSection B S hS i F (retractionChartDiagram B S hS r hrep i hi U) s := by
  show (modulePullbackChartFMap B S hS i F).app
    (retractionChartDiagram B S hS r hrep i hi U) s = _
  exact modulePullbackChartFMap_app B S hS i F (retractionChartDiagram B S hS r hrep i hi U) s

/-- The reduction is natural in the module. -/
theorem reductionMap_naturality {F F' : Modules.{u, u} B S hS X'.1 X'.2} (φ : F ⟶ F') :
    (retractionPushforward B S hS r hrep).map φ ≫ reductionMap B S hS r hrep i hi F' =
      reductionMap B S hS r hrep i hi F ≫ (modulePullback B S hS i).map φ := by
  ext U s
  have h1 := reductionMap_app B S hS r hrep i hi F' U.unop
    (φ.val.app (op ((smallBaseChange B S hS r hrep).obj U.unop)) s)
  have h2 := reductionMap_app B S hS r hrep i hi F U.unop s
  have h3 := modulePullbackChartSection_map B S hS i F φ
    (retractionChartDiagram B S hS r hrep i hi U.unop) s
  exact h1.trans (h3.symm.trans (congrArg (((modulePullback B S hS i).map φ).val.app U) h2.symm))

/-- **The reduction is surjective on the sections over an affine chart**, for a quasi-coherent
module, as soon as the pullback of functions along `U ⟶ U ×_{X₀} X'` is surjective: the sections
of `i^*ℱ` over `U` are the base change of those of `ℱ` over `U ×_{X₀} X'`
(`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`). -/
theorem surjective_reductionMap_app (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS r hrep).obj U)))
    (hsurj : Function.Surjective
      (chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U))) :
    Function.Surjective ((reductionMap B S hS r hrep i hi F).val.app (op U)) := by
  let d := retractionChartDiagram B S hS r hrep i hi U
  let := chartDiagramAlgebra B S hS i d
  have hbij := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS i F hF d
    hU hU'
  intro x
  obtain ⟨t, rfl⟩ := hbij.2 x
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a s =>
    obtain ⟨a', rfl⟩ := hsurj a
    refine ⟨a' • s, (reductionMap_app B S hS r hrep i hi F U _).trans ?_⟩
    rw [modulePullbackChartBaseChange_tmul, modulePullbackChartSection_smul]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [map_add, hs, ht, map_add]; rfl⟩

/-- **The kernel of the reduction on the sections over an affine chart**, for a quasi-coherent
module, when the pullback of functions along `U ⟶ U ×_{X₀} X'` is surjective: it is the
submodule generated by the products of the functions vanishing on `U` with the sections. -/
theorem reductionMap_app_eq_zero_iff (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hU' : IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS r hrep).obj U)))
    (hsurj : Function.Surjective
      (chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)))
    (s : F.val.obj (op ((smallBaseChange B S hS r hrep).obj U))) :
    (reductionMap B S hS r hrep i hi F).val.app (op U) s = 0 ↔
      s ∈ (RingHom.ker (chartDiagramRestrict B S hS i
        (retractionChartDiagram B S hS r hrep i hi U))) •
          (⊤ : Submodule (chartRing B S hS X'.1 X'.2
              (retractionChartDiagram B S hS r hrep i hi U).V)
            (F.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V))) := by
  let d := retractionChartDiagram B S hS r hrep i hi U
  let := chartDiagramAlgebra B S hS i d
  have hbij := bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS i F hF d
    hU hU'
  have h1 : modulePullbackChartSection B S hS i F d s =
      modulePullbackChartBaseChange B S hS i F d
        (TensorProduct.tmul (chartRing B S hS X'.1 X'.2 d.V) (1 : chartRing B S hS X₀.1 X₀.2 d.U)
          s) :=
    ((modulePullbackChartBaseChange_tmul B S hS i F d 1 s).trans (one_smul _ _)).symm
  refine (Iff.of_eq (congrArg (· = 0) ((reductionMap_app B S hS r hrep i hi F U s).trans h1))).trans
    ((map_eq_zero_iff _ hbij.1).trans ?_)
  exact @TensorProduct.one_tmul_eq_zero_iff_of_surjective_ringHom _ _ _ _
    (chartDiagramRestrict B S hS i d) hsurj (F.val.obj (op d.V)) _ _ s

/-- **The reduction carries multiplication by a global function to multiplication by its
restriction**: if a global function `a` of `X'` restricts along every chart map
`U ⟶ U ×_{X₀} X'` to the global function `a₀` of `X₀`, then multiplication by `a` followed by
the reduction is the reduction followed by multiplication by `a₀`. -/
theorem globalSmul_comp_reductionMap
    (a : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))
    (a₀ : Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O))
    (h : ∀ U : SmallEtale B S hS X₀.1,
      chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)
        (a.1 (op ((smallBaseChange B S hS r hrep).obj U))) = a₀.1 (op U)) :
    (retractionPushforward B S hS r hrep).map
        (Stacks.Cohomology.SiteModules.globalSmul _ a F) ≫ reductionMap B S hS r hrep i hi F =
      reductionMap B S hS r hrep i hi F ≫
        Stacks.Cohomology.SiteModules.globalSmul _ a₀ ((modulePullback B S hS i).obj F) := by
  ext U s
  have h1 := reductionMap_app B S hS r hrep i hi F U.unop
    ((Stacks.Cohomology.SiteModules.globalSmul _ a F).val.app
      (op ((smallBaseChange B S hS r hrep).obj U.unop)) s)
  have h2 := reductionMap_app B S hS r hrep i hi F U.unop s
  have h3 := modulePullbackChartSection_smul B S hS i F
    (retractionChartDiagram B S hS r hrep i hi U.unop)
    (a.1 (op ((smallBaseChange B S hS r hrep).obj U.unop))) s
  rw [h U.unop] at h3
  refine h1.trans (h3.trans ?_)
  exact congrArg (fun (x : ((modulePullback B S hS i).obj F).val.obj U) => a₀.1 U • x) h2.symm

end AlgebraicGeometry.Space

end
