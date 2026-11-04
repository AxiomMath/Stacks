module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionSequence

/-!
# The action of a square-zero ideal, and modules over the reduction

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site, and let
`0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0` be a short exact sequence of sheaves of `O`-modules whose second map
is the structure map. The *action* of the ideal on an `O`-module `M` is the map
`M ⊗_O I ⟶ M ⊗_O O ≅ M`. It vanishes on every `O`-module restricted from an `O₀`-module, and
conversely an `O`-module on which it vanishes is, through the unit of the adjunction between
extension and restriction of scalars, the restriction of its own reduction: the unit is the
cokernel of the action, tensoring being right exact.

Applied degreewise, an `O`-module complex on which the ideal acts by zero is the restriction of
its reduction. This is how an extension of complexes of `O`-modules whose middle term is killed
by the ideal is recognised as an extension of complexes of `O₀`-modules.

## Main definitions

* `Deformation.ComplexLift.idealAction`: the action `M ⊗_O I ⟶ M`, as a natural transformation.

## Main results

* `Deformation.ComplexLift.idealAction_app_restrict`: the ideal acts by zero on the restriction
  of an `O₀`-module.
* `Deformation.ComplexLift.isIso_reductionMap_app_of_idealAction`: an `O`-module on which the
  ideal acts by zero is the restriction of its reduction.
* `Deformation.ComplexLift.isIso_reductionMapComplex_of_idealAction`: the same for complexes.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀}
variable {I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)

/-- **The action of the ideal** on an `O`-module `M`: `M ⊗_O I ⟶ M ⊗_O O ≅ M`. -/
def idealAction : tensorRight O (restrictIdeal f I₀) ⟶ 𝟭 _ :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.map ι ≫
    (tensorRightUnitIso O).hom

/-- The inclusion of the ideal part is the action read through the projection formula. -/
theorem idealPartIncl_eq :
    idealPartIncl f ι = (idealTensorRightIso f I₀).inv ≫ idealAction ι := rfl

/-- The action is the projection formula followed by the inclusion of the ideal part. -/
theorem idealAction_eq :
    idealAction ι = (idealTensorRightIso f I₀).hom ≫ idealPartIncl f ι := by
  rw [idealPartIncl_eq, Iso.hom_inv_id_assoc]

/-- The structure map of the reduction, read through `(O₀ ⊗_O M)|_O ≅ M ⊗_O O₀|_O`, is the unit
law followed by `M` tensored with the structure map `O ⟶ O₀|_O`. -/
theorem tensorRightUnitIso_hom_app_comp_reductionMap_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (tensorRightUnitIso O).hom.app M ≫ (reductionMap f).app M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map
          (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f)) ≫
        (restrictExtensionIsoTensorRight f).inv.app M := by
  have hθ := unit_comp_restrictExtensionIsoTensorRight f M
  have hu : (tensorRightUnitIso O).hom.app M ≫
      (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app M = 𝟙 _ :=
    (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).hom_inv_id_app M
  rw [← cancel_mono ((restrictExtensionIsoTensorRight f).hom.app M), Category.assoc,
    Category.assoc, Iso.inv_hom_id_app]
  exact (congrArg (fun k ↦ (tensorRightUnitIso O).hom.app M ≫ k) hθ).trans
    ((reassoc_of% hu) _ |>.trans (Category.comp_id _).symm)

include hι in
/-- **The ideal acts by zero on a module restricted from `O₀`.** -/
theorem idealAction_app_restrict
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    (idealAction ι).app ((SheafOfModules.restrictScalars (ringSheafMapOf J f)).obj N) = 0 := by
  let M := (SheafOfModules.restrictScalars (ringSheafMapOf J f)).obj N
  have hsplit : (reductionMap f).app M ≫ (SheafOfModules.restrictScalars
      (ringSheafMapOf J f)).map ((extendRestrictAdjunction f).counit.app N) = 𝟙 M :=
    (extendRestrictAdjunction f).right_triangle_components N
  have h : (idealAction ι).app M ≫ (reductionMap f).app M = 0 := by
    have := idealPartIncl_app_comp_reductionMap_app ι hι M
    rw [idealPartIncl_eq, NatTrans.comp_app, Category.assoc] at this
    exact zero_of_epi_comp ((idealTensorRightIso f I₀).inv.app M) this
  have h2 : (idealAction ι).app M ≫ (reductionMap f).app M ≫ (SheafOfModules.restrictScalars
      (ringSheafMapOf J f)).map ((extendRestrictAdjunction f).counit.app N) =
      (idealAction ι).app M := by
    rw [hsplit]; exact Category.comp_id _
  rw [← h2, ← Category.assoc, h, zero_comp]

include hι in
/-- **An `O`-module on which the ideal acts by zero is the restriction of its reduction**: the
structure map `M ⟶ (O₀ ⊗_O M)|_O` is an isomorphism. Tensoring with `M` is right exact, so `M`
tensored with the structure map `O ⟶ O₀|_O` is the cokernel of `M` tensored with the inclusion
of the ideal, which is the action, hence zero. -/
theorem isIso_reductionMap_app_of_idealAction (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (h : (idealAction ι).app M = 0) : IsIso ((reductionMap f).app M) := by
  let G := (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M
  let β := (Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app M
  have hpres : PreservesColimit (parallelPair (idealSequenceOf f I₀ ι hι).f 0)
      (tensorRight O M) :=
    (PreservesFiniteColimits.preservesFiniteColimits (F := tensorRight O M)
      WalkingParallelPair).preservesColimit
  have hc := CokernelCofork.mapIsColimit _ hS.gIsCokernel (tensorRight O M)
  have hz : G.map ι = 0 := zero_of_comp_mono ((tensorRightUnitIso O).hom.app M) h
  have hz' : (tensorRight O M).map ι = 0 := by
    have hn := β.hom.naturality ι
    rw [hz, zero_comp] at hn
    exact zero_of_epi_comp (β.hom.app _) hn.symm
  have hπ' : IsIso ((tensorRight O M).map
      (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f))) :=
    CokernelCofork.IsColimit.isIso_π _ hc hz'
  have hπ : IsIso (G.map
      (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f))) := by
    have hn := β.hom.naturality
      (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f))
    have : IsIso (G.map (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
        (ringSheafMapOf J f)) ≫ β.hom.app _) := by
      rw [hn]; exact IsIso.comp_isIso' inferInstance hπ'
    exact IsIso.of_isIso_comp_right _ (β.hom.app _)
  have e := tensorRightUnitIso_hom_app_comp_reductionMap_app (f := f) M
  have : IsIso ((tensorRightUnitIso O).hom.app M ≫ (reductionMap f).app M) := by
    rw [e]; infer_instance
  exact IsIso.of_isIso_comp_left ((tensorRightUnitIso O).hom.app M) _

include hι in
/-- **A complex of `O`-modules on which the ideal acts by zero is the restriction of its
reduction.** -/
theorem isIso_reductionMapComplex_of_idealAction (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (h : ∀ n, (idealAction ι).app (E.X n) = 0) : IsIso (reductionMapComplex (f := f) E) := by
  have : ∀ n, IsIso ((reductionMapComplex (f := f) E).f n) := fun n ↦
    isIso_reductionMap_app_of_idealAction ι hι hS (E.X n) (h n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ### The action on complexes -/

/-- The action of the ideal on a complex of `O`-modules, degreewise. -/
abbrev idealActionComplex :=
  NatTrans.mapHomologicalComplex (idealAction ι) (ComplexShape.up ℤ)

/-- The projection formula on complexes, degreewise. -/
abbrev idealTensorRightIsoComplex :=
  NatIso.mapHomologicalComplex (idealTensorRightIso f I₀) (ComplexShape.up ℤ)

/-- The action on a complex is the projection formula followed by the inclusion of the ideal
part, degreewise. -/
theorem idealActionComplex_app_eq
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    (idealActionComplex ι).app P =
      (idealTensorRightIsoComplex (f := f) (I₀ := I₀)).hom.app P ≫ idealPartInclComplex ι P := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact NatTrans.congr_app (idealAction_eq ι) (P.X n)

include hι in
/-- The ideal acts by zero on the restriction of a complex of `O₀`-modules. -/
theorem idealActionComplex_app_restrict
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ℤ) :
    (idealActionComplex ι).app
      (((SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact idealAction_app_restrict ι hι (N.X n)

include hι in
/-- A complex of `O`-modules on which the action `idealActionComplex` vanishes is the restriction
of its reduction: the structure map `E ⟶ (O₀ ⊗_O E)|_O` is an isomorphism. -/
theorem isIso_reductionMapComplex_of_idealActionComplex
    (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (h : (idealActionComplex ι).app E = 0) : IsIso (reductionMapComplex (f := f) E) :=
  isIso_reductionMapComplex_of_idealAction ι hι hS E fun n ↦ by
    have := congrArg (fun φ ↦ HomologicalComplex.Hom.f φ n) h
    exact this

end Deformation.ComplexLift

end
