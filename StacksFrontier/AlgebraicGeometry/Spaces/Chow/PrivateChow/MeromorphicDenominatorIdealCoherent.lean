module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.DenominatorIdealBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.MeromorphicDenominatorIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian

/-!
# The ideal of denominators of a meromorphic section is quasi-coherent

Let `X` be an algebraic space satisfying the two hypotheses of Stacks 0EN6, `ℒ` an invertible
`𝒪_X`-module and `t` a meromorphic section of `ℒ`. Over an affine étale chart `U` the meromorphic
sections of `ℒ` are `𝒦_X(U) ⊗ ℒ(U)`, and the ideal of denominators of `t` over `U` is the ideal of
denominators `{a : a t ∈ ℒ(U)}` of that tensor; the algebra of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.DenominatorIdealBaseChange` makes it
cartesian on the affine charts, hence quasi-coherent by Stacks 03DX.

## Main results

* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_meromorphicDenominatorIdeal`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS X.1 X.2)
  (t : MeromorphicSection.{u, u} B S hS X.1 X.2 L)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property L)

/-- The sections of the presheaf of meromorphic sections over a chart, as a module over the
regular functions of the chart. -/
@[instance_reducible]
noncomputable def meromorphicSectionStructureModuleChartModule (U : SmallEtale B S hS X.1) :
    Module (chartRing B S hS X.1 X.2 U)
      ((meromorphicSectionStructureModule B S hS X L).obj (op U)) :=
  inferInstanceAs (Module ((structurePresheaf B S hS X.1 ⋙ forget₂ CommRingCat RingCat).obj (op U))
    ((meromorphicSectionStructureModule B S hS X L).obj (op U)))

attribute [local instance] meromorphicSectionStructureModuleChartModule

/-- The pure meromorphic section `m ↦ 1 ⊗ m`, as a linear map into the presheaf of meromorphic
sections read as a presheaf of `𝒪_X`-modules. -/
noncomputable def pureMeromorphicSectionLinear (U : SmallEtale B S hS X.1) :
    L.val.obj (op U) →ₗ[chartRing B S hS X.1 X.2 U]
      (meromorphicSectionStructureModule B S hS X L).obj (op U) where
  toFun m := pureMeromorphicSection B S hS X.1 X.2 L U m
  map_add' m n := pureMeromorphicSection_add B S hS X.1 X.2 L U m n
  map_smul' r m := pureMeromorphicSection_smul B S hS X.1 X.2 L U r m _ rfl

variable (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
  (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

include hL hwa hfin in
/-- Over an affine chart the ideal of denominators of `t` is the ideal of denominators, in the
sense of `Module.denominatorIdeal`, of any meromorphic section of the presheaf `𝒦_X ⊗ ℒ` whose
sheafification is `t`. -/
theorem mem_meromorphicDenominatorIdeal_iff_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (x : (meromorphicSectionStructureModule B S hS X L).obj (op U))
    (hx : toMeromorphicSectionSheaf B S hS X.1 X.2 L U x = t.eval (op U))
    (r : chartRing B S hS X.1 X.2 U) :
    IsMeromorphicDenominator B S hS X L t U r ↔
      ∃ m, pureMeromorphicSectionLinear B S hS X L U m = r • x := by
  have hinj := (bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite B S hS X L
    (isQuasicoherentOnSite_of_isInvertible B S hS X L hL) hwa hfin U hU).1
  have hsmul : toMeromorphicSectionSheaf B S hS X.1 X.2 L U (r • x) =
      chartMeromorphicScalar B S hS X U r • t.eval (op U) := by
    rw [← hx]
    exact toMeromorphicSectionSheaf_smul B S hS X.1 X.2 L U _ x
  refine ⟨fun ⟨m, hm⟩ => ⟨m, hinj (hm.trans hsmul.symm)⟩, fun ⟨m, hm⟩ => ⟨m, ?_⟩⟩
  rw [← hsmul, ← hm]
  rfl

include hL hwa hfin in
/-- **The ideal of denominators of a meromorphic section of an invertible module is cartesian on
the affine charts.** -/
theorem isCartesianOnAffineCharts_meromorphicDenominatorIdeal :
    IsCartesianOnAffineCharts (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules := by
  intro U V hU hV f
  let := chartAlgebra (hF := X.2) f
  have : Module.Flat (chartRing B S hS X.1 X.2 U) (chartRing B S hS X.1 X.2 V) :=
    moduleFlat_chartRing_of_isAffine f hU hV
  have hLq := isQuasicoherentOnSite_of_isInvertible B S hS X L hL
  set P := meromorphicSectionStructureModule B S hS X L with hP
  have hbij : ∀ (W : SmallEtale B S hS X.1) (hW : IsAffine (smallEtaleScheme B S hS X.1 W)),
      Function.Bijective (toMeromorphicSectionSheaf B S hS X.1 X.2 L W) := fun W hW =>
    bijective_toMeromorphicSectionSheaf_of_isQuasicoherentOnSite B S hS X L hLq hwa hfin W hW
  obtain ⟨x₀, hx⟩ := (hbij U hU).2 (t.eval (op U))
  obtain ⟨x₀', hx'⟩ := (hbij V hV).2 (t.eval (op V))
  let x : P.obj (op U) := x₀
  let x' : P.obj (op V) := x₀'
  let cP : (chartRing B S hS X.1 X.2 V) ⊗[chartRing B S hS X.1 X.2 U] (P.obj (op U))
      →ₗ[chartRing B S hS X.1 X.2 V] (P.obj (op V)) :=
    (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, u}
      (R := structurePresheaf B S hS X.1) P f.op).hom
  have hcP : Function.Injective cP :=
    ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_restrictionBaseChange_meromorphicSectionStructureModule B S hS X L hLq hwa hfin f hU
        hV)).1
  have hcPt : ∀ (a : chartRing B S hS X.1 X.2 V) (y : P.obj (op U)),
      cP (a ⊗ₜ y) = a • (show ↑(P.obj (op V)) from (P.map f.op).hom y) := fun a y =>
    Stacks.PresheafOfModules.restrictionBaseChange_tmul.{u + 1, u, u, u}
      (R := structurePresheaf B S hS X.1) P f.op a y
  have hsq : ∀ z, pureMeromorphicSectionLinear B S hS X L V (sectionsBaseChange L f z) =
      cP (LinearMap.lTensor _ (pureMeromorphicSectionLinear B S hS X L U) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw]
    | tmul a m =>
      rw [chartBaseChange_tmul, LinearMap.map_smul, LinearMap.lTensor_tmul, hcPt]
      congr 1
      exact (pureMeromorphicSection_map B S hS X.1 X.2 L U V f m).symm
  have hxx : ∀ a, cP (a ⊗ₜ x) = a • x' := by
    intro a
    rw [hcPt]
    congr 1
    refine (hbij V hV).1 ?_
    change toMeromorphicSectionSheaf B S hS X.1 X.2 L V
      (((meromorphicSectionModule B S hS X.1 X.2 L).map f.op).hom x₀) = _
    rw [hx']
    refine (toMeromorphicSectionSheaf_map B S hS X.1 X.2 L U V f x₀).symm.trans ?_
    rw [hx]
    exact PresheafOfModules.sections_property t f.op
  obtain ⟨hinj, hrange⟩ := Module.injective_idealBaseChange_and_range
    (pureMeromorphicSectionLinear B S hS X L U) x (pureMeromorphicSectionLinear B S hS X L V) x'
    (sectionsBaseChange L f) cP
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS X.1 X.2 L hLq hU hV f).2 hcP
    hsq hxx (meromorphicDenominatorIdealAt B S hS X L t U)
    (mem_meromorphicDenominatorIdeal_iff_of_isAffine B S hS X L t hL hwa hfin U hU x hx)
    (meromorphicDenominatorIdealAt B S hS X L t V)
    (mem_meromorphicDenominatorIdeal_iff_of_isAffine B S hS X L t hL hwa hfin V hV x' hx')
  have hval : ∀ z, Subtype.val
      (sectionsBaseChange (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules
        f z : ↥(meromorphicDenominatorIdealAt B S hS X L t V)) =
      Module.idealBaseChange (A := chartRing B S hS X.1 X.2 V)
        (meromorphicDenominatorIdealAt B S hS X L t U) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw =>
      exact (congrArg Subtype.val (map_add _ z w)).trans
        ((congrArg₂ (· + ·) hz hw).trans (map_add _ z w).symm)
    | tmul a r =>
      refine (congrArg Subtype.val (chartBaseChange_tmul
        (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules f a r)).trans ?_
      refine Eq.trans ?_ (Module.idealBaseChange_tmul (R := chartRing B S hS X.1 X.2 U)
        (A := chartRing B S hS X.1 X.2 V) (meromorphicDenominatorIdealAt B S hS X L t U) a r).symm
      rfl
  refine ⟨fun z w h => hinj ?_, fun y => ?_⟩
  · exact (hval z).symm.trans ((congrArg Subtype.val h).trans (hval w))
  · obtain ⟨z, hz⟩ := (hrange (Subtype.val (y : ↥(meromorphicDenominatorIdealAt B S hS X L t V)))).1
      (Subtype.prop (y : ↥(meromorphicDenominatorIdealAt B S hS X L t V)))
    exact ⟨z, Subtype.ext ((hval z).trans hz)⟩

include hL hwa hfin in
/-- The ideal of denominators of a meromorphic section of an invertible module is
quasi-coherent. -/
theorem isQuasicoherentOnSite_meromorphicDenominatorIdeal :
    (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 _).2
    (isCartesianOnAffineCharts_meromorphicDenominatorIdeal B S hS X L t hL hwa hfin)

include hL hwa hfin in
/-- **The ideal of denominators of a meromorphic section of an invertible module on a locally
Noetherian algebraic space is coherent.** -/
theorem isCoherent_meromorphicDenominatorIdeal
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))] :
    IsCoherent B S hS X.1 X.2 (meromorphicDenominatorIdeal B S hS X L t hL).toSheafOfModules :=
  isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2
    (meromorphicDenominatorIdeal B S hS X L t hL).ι
    (isQuasicoherentOnSite_meromorphicDenominatorIdeal B S hS X L t hL hwa hfin) inferInstance

end AlgebraicGeometry.Space

end
