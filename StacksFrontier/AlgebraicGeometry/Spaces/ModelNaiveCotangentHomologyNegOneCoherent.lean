module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModelNaiveCotangentHomologyCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentKernelLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts

/-!
# The degree `-1` cohomology sheaf of `NL_{X/Y}` on the model is coherent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, locally of finite type, with
`X` and `Y` locally Noetherian.  The degree `-1` cohomology sheaf `𝒦` of `NL_{X/Y}`, restricted to
an affine chart `V = Spec A` of `X` lying over an affine chart `W = Spec R` of `Y`, is the sheaf
attached to `H₁(L_{A/R})` (Stacks 0D0Y, through `AlgebraicGeometry.Space.chartKernelSliceIso`).
Here `R` is Noetherian and `A` is of finite type over `R`, so `H₁(L_{A/R})` is a finite
`A`-module, and the images of finitely many generators generate `𝒦` locally over `V`
(`AlgebraicGeometry.Space.naiveCotangentKernel_exists_sum_eq`).  Carried down to the degree `-1`
cohomology sheaf on the model, which has its sections one universe lower, this makes that sheaf of
finite type, hence coherent on the locally Noetherian `X` (Stacks 07UB).  This is the degree `-1`
content of Stacks 0D0Z for a morphism locally of finite type with Noetherian source and target.

## Main results

* `Algebra.moduleFinite_h1Cotangent_of_finiteType`: `H₁(L_{A/R})` is finite over `A` for `A` of
  finite type over a Noetherian `R`.
* `AlgebraicGeometry.Space.isCoherent_modelNaiveCotangentHomology_negOne`

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v v'

namespace Algebra

/-- **`H₁(L_{B/A})` is a finite `B`-module** for `B` of finite type over a Noetherian ring `A`:
it is the kernel of a map out of the conormal module `I/I²` of a finite presentation, which is
finite because `I` is finitely generated. -/
theorem moduleFinite_h1Cotangent_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] :
    Module.Finite B (Algebra.H1Cotangent A B) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := Algebra.Presentation.ofFinitePresentation A B
  have : Module.Finite B P.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P.fg_ker
  have : Module.Finite B P.toExtension.H1Cotangent := by
    show Module.Finite B ↥P.toExtension.cotangentComplex.ker
    infer_instance
  exact Module.Finite.of_surjective P.equivH1Cotangent.toLinearMap
    P.equivH1Cotangent.surjective

end Algebra

namespace Stacks.SheafOfModules

/-- **Relations among restricted sections pull back along a natural family of injective linear
maps.**  If `ψ` carries `M` into `N` linearly, naturally and injectively, then a relation
`∑ cᵢ · ψ(gᵢ)|_D = ψ(y)|_D` among the images gives the same relation in `M`. -/
theorem sum_smul_map_eq_of_injective {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} (M : SheafOfModules.{v} R) (N : SheafOfModules.{v'} R)
    (ψ : ∀ W : Cᵒᵖ, M.val.obj W →ₗ[R.obj.obj W] N.val.obj W)
    (hnat : ∀ {W W' : Cᵒᵖ} (q : W ⟶ W') (x : M.val.obj W),
      ψ W' ((M.val.map q).hom x) = (N.val.map q).hom (ψ W x))
    (hinj : ∀ W, Function.Injective (ψ W)) {n : ℕ} {U V D : C} (g : Fin n → M.val.obj (op U))
    (q : D ⟶ U) (k : D ⟶ V) (y : M.val.obj (op V)) (c : Fin n → R.obj.obj (op D))
    (h : ∑ i, c i • (show N.val.obj (op D) from (N.val.map q.op).hom (ψ (op U) (g i))) =
      (show N.val.obj (op D) from (N.val.map k.op).hom (ψ (op V) y))) :
    ∑ i, c i • (M.val.map q.op).hom (g i) = (M.val.map k.op).hom y := by
  apply hinj (op D)
  refine (map_sum (ψ (op D)) (fun i => c i • (show M.val.obj (op D) from
    (M.val.map q.op).hom (g i))) Finset.univ).trans ?_
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h.trans (hnat k.op y).symm)
  rw [map_smul]
  exact congrArg (c i • ·) (hnat q.op (g i))

end Stacks.SheafOfModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-! ### The chart rings of a diagram -/

/-- **The ring of an affine chart is of finite type over the ring of the chart below it**, for
`f` locally of finite type. -/
theorem algebraFiniteType_chartDiagram (hf : IsLocallyOfFiniteType B S hS f.hom)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebraInst B S hS f d
    Algebra.FiniteType (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) := by
  have hloc : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map d.g) :=
    hf d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
  have : IsAffine (Opposite.unop ((SmallEtale.toOver B S hS X.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op d.U))) := hU
  have : IsAffine (Opposite.unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op d.V))) := hW
  exact HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ hloc

/-- The ring of an affine chart of a locally Noetherian algebraic space is Noetherian. -/
theorem isNoetherianRing_toposChartRing_of_isAffine
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    IsNoetherianRing (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op V))) := by
  have : IsAffine (Opposite.unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op V))) := hV
  have : IsLocallyNoetherian (Opposite.unop ((SmallEtale.toOver B S hS Y.1 ⋙
      BigFppfOver.toScheme B S hS).op.obj (op V))) := isLocallyNoetherian_chart B S hS hY V
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-! ### Carrying the local generators down to the model -/

/-- The degree `-1` cohomology sheaf on the model, with its sections raised, is `𝒦`. -/
def modelNaiveCotangentHomologyNegOneULiftIso :
    (spaceULift B S hS X).obj (modelNaiveCotangentHomology B S hS f (-1)) ≅
      naiveCotangentKernel B S hS f :=
  spaceULiftModelNaiveCotangentHomologyIso B S hS f (-1) ≪≫
    naiveCotangentComplexHomologyNegOneIso B S hS f

/-- The sections of the degree `-1` cohomology sheaf on the model corresponding to elements of
`H₁(L_{A/R})` for a chart diagram. -/
def modelNaiveCotangentHomologyNegOneSection (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : chartH1 B S hS f d) :
    (modelNaiveCotangentHomology B S hS f (-1)).val.obj (op d.U) :=
  ULift.down (((modelNaiveCotangentHomologyNegOneULiftIso B S hS f).inv.val.app (op d.U)).hom
    (chartKernelSection B S hS f d x))

/-! ### Coherence -/

/-- **The degree `-1` cohomology sheaf of `NL_{X/Y}` on the model is of finite type over an affine
chart carrying an affine chart diagram.** -/
theorem hasFiniteGlobalGenerators_modelNaiveCotangentHomology_negOne
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    {W : SmallEtale B S hS X.1} (hW : HasAffineChartDiagram B S hS f W) :
    SheafOfModules.HasFiniteGlobalGenerators ((modelNaiveCotangentHomology B S hS f (-1)).over
      (show (smallEtaleRingedSite B S hS X.1 X.2).C from W)) := by
  let d := chartDiagramOfHasAffineChartDiagram B S hS f hW
  have hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) :=
    hW.1
  have hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) :=
    hW.2.choose_spec.choose_spec.2
  let := chartDiagramAlgebraInst B S hS f d
  have := isNoetherianRing_toposChartRing_of_isAffine B S hS hY d.V hV
  have := algebraFiniteType_chartDiagram B S hS f hf d hU hV
  have := Algebra.moduleFinite_h1Cotangent_of_finiteType
    (A := ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
    (B := ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
  obtain ⟨n, h, hspan⟩ := Module.Finite.exists_fin
    (R := ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
    (M := chartH1 B S hS f d)
  let G := modelNaiveCotangentHomology B S hS f (-1)
  let θ := modelNaiveCotangentHomologyNegOneULiftIso B S hS f
  refine Stacks.SheafOfModules.hasFiniteGlobalGenerators_over_of_locally_span G d.U
    (fun i => modelNaiveCotangentHomologyNegOneSection B S hS f d (h i)) ?_
  intro V p y
  obtain ⟨T, hT, hc⟩ := naiveCotangentKernel_exists_sum_eq B S hS f d hU hV h hspan V p
    ((θ.hom.val.app (op V)).hom (ULift.up y))
  refine ⟨T, hT, fun D k hk => ?_⟩
  obtain ⟨c, hcc⟩ := hc k hk
  refine ⟨c, ?_⟩
  -- carry the relation in `𝒦` back along the injection `G(W) ⟶ 𝒦(W)` given by `θ`
  have hi : ∀ W (z : G.val.obj W), (θ.inv.val.app W).hom ((θ.hom.val.app W).hom (ULift.up z)) =
      ULift.up z := fun W z => congrArg (fun φ => (φ.val.app W).hom (ULift.up z)) θ.hom_inv_id
  have hsec : ∀ i, (θ.hom.val.app (op d.U)).hom
      (ULift.up (modelNaiveCotangentHomologyNegOneSection B S hS f d (h i))) =
      chartKernelSection B S hS f d (h i) := fun i =>
    congrArg (fun φ => (φ.val.app (op d.U)).hom (chartKernelSection B S hS f d (h i)))
      θ.inv_hom_id
  refine Stacks.SheafOfModules.sum_smul_map_eq_of_injective G (naiveCotangentKernel B S hS f)
    (fun W => { toFun := fun z => (θ.hom.val.app W).hom (ULift.up z)
                map_add' := fun a b => (θ.hom.val.app W).hom.map_add (ULift.up a) (ULift.up b)
                map_smul' := fun r z => (θ.hom.val.app W).hom.map_smul r (ULift.up z) })
    (fun q z => PresheafOfModules.naturality_apply θ.hom.val q (ULift.up z)) (fun W z₁ z₂ hz => ?_)
    _ (k ≫ p) k y c ?_
  · change (θ.hom.val.app W).hom (ULift.up z₁) = (θ.hom.val.app W).hom (ULift.up z₂) at hz
    exact ULift.up_injective ((hi W z₁).symm.trans
      ((congrArg (θ.inv.val.app W).hom hz).trans (hi W z₂)))
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hcc
    congr 1
    exact congrArg ((naiveCotangentKernel B S hS f).val.map (k ≫ p).op).hom (hsec i)

/-- **The degree `-1` cohomology sheaf of `NL_{X/Y}` on the model is of finite type.** -/
theorem isFiniteTypeOnSite_modelNaiveCotangentHomology_negOne
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    (modelNaiveCotangentHomology B S hS f (-1)).IsFiniteTypeOnSite := by
  refine ⟨fun U => ⟨Σ W : SmallEtale B S hS X.1, {a : W ⟶ U // HasAffineChartDiagram B S hS f W},
    fun i => i.1, fun i => i.2.1, ?_, fun i =>
      hasFiniteGlobalGenerators_modelNaiveCotangentHomology_negOne B S hS f hf hY i.2.2⟩⟩
  exact mem_topology_of_hasAffineChartDiagram B S hS f U _
    fun {W} a hW => Sieve.ofArrows_mk (fun i : Σ W : SmallEtale B S hS X.1,
      {a : W ⟶ U // HasAffineChartDiagram B S hS f W} => i.1) (fun i => i.2.1) ⟨W, a, hW⟩

/-- **The degree `-1` cohomology sheaf of `NL_{X/Y}` on the model is coherent**, for `f` locally
of finite type and `X`, `Y` locally Noetherian. -/
theorem isCoherent_modelNaiveCotangentHomology_negOne (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    IsCoherent B S hS X.1 X.2 (modelNaiveCotangentHomology B S hS f (-1)) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 _).2
    ⟨isQuasicoherentOnSite_modelNaiveCotangentHomology B S hS f (-1),
      Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
        (isFiniteTypeOnSite_modelNaiveCotangentHomology_negOne B S hS f hf hY)⟩

end AlgebraicGeometry.Space

end
