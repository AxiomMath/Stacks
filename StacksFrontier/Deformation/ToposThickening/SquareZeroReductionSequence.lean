module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionTransport
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorExtensionOfScalars
public import StacksFrontier.Deformation.ToposThickening.DerivedTensorUnit
public import StacksFrontier.Deformation.ToposThickening.ExtensionUnitTensor
public import StacksFrontier.Deformation.ToposThickening.IdealTensorProjection

/-!
# The reduction sequence of a flat module over a square-zero thickening

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site and let `I₀` be a sheaf
of `O₀`-modules together with a short exact sequence of sheaves of `O`-modules

`0 ⟶ I₀|_O ⟶ O ⟶ O₀|_O ⟶ 0`

whose second map is the structure map: the square-zero ideal sequence of a thickening, with the
ideal read through its `O₀`-module structure. For a flat sheaf of `O`-modules `M` tensoring that
sequence with `M` and reading the three terms through the projection formula, the unit law and
the identification of `(O₀ ⊗_O M)|_O` with `M ⊗_O O₀|_O` gives the short exact sequence

`0 ⟶ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ⟶ M ⟶ (O₀ ⊗_O M)|_O ⟶ 0`

whose second map is the unit of the adjunction between extension and restriction of scalars.
Applied degreewise to a complex with flat terms it is a short exact sequence of complexes of
`O`-modules, natural in the complex: the *reduction sequence*. Its distinguished triangle in
the derived category is what the reduction triangle of a square-zero thickening is built from.

## Main definitions

* `Deformation.ComplexLift.idealPart` and `Deformation.ComplexLift.reductionPart`: the functors
  `M ↦ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O` and `M ↦ (O₀ ⊗_O M)|_O`.
* `Deformation.ComplexLift.idealPartIncl`: the inclusion `((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ⟶ M` of the
  ideal part, a natural transformation.
* `Deformation.ComplexLift.reductionSequence`: the reduction sequence of a complex of
  `O`-modules, a short complex of complexes.

## Main results

* `Deformation.ComplexLift.shortExact_reductionSequenceModule`: the reduction sequence of a
  flat module is short exact.
* `Deformation.ComplexLift.shortExact_reductionSequence`: the reduction sequence of a complex
  with flat terms is short exact.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable (I₀ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))

/-! ### The three functors -/

/-- The ideal part of the reduction of an `O`-module: `M ↦ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O`. -/
abbrev idealPart :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  extensionOfScalars f ⋙ tensorRight O₀ I₀ ⋙ SheafOfModules.restrictScalars (ringSheafMapOf J f)

/-- The reduction of an `O`-module, read over `O`: `M ↦ (O₀ ⊗_O M)|_O`. -/
abbrev reductionPart :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  extensionOfScalars f ⋙ SheafOfModules.restrictScalars (ringSheafMapOf J f)

variable {I₀}

/-- The inclusion of the ideal part, `((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ⟶ M`: the projection formula
`M ⊗_O I ≅ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O`, then `M` tensored with the inclusion `ι : I ⟶ O` of the
ideal, then the unit law `M ⊗_O O ≅ M`. -/
def idealPartIncl
    (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    idealPart f I₀ ⟶ 𝟭 _ :=
  (idealTensorRightIso f I₀).inv ≫
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.map ι ≫
      (tensorRightUnitIso O).hom

/-- The structure map of the reduction, `M ⟶ (O₀ ⊗_O M)|_O`: the unit of the adjunction between
extension and restriction of scalars. -/
abbrev reductionMap : 𝟭 _ ⟶ reductionPart f := (extendRestrictAdjunction f).unit

variable {f}

/-! ### The reduction sequence of a flat module -/

section Module

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)

/-- `M ⊗_O -` applied to the ideal sequence. -/
abbrev tensoredIdealSequence (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (idealSequenceOf f I₀ ι hι).map
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M)

include hι in
/-- The inclusion of the ideal part followed by the structure map of the reduction is zero. -/
theorem idealPartIncl_app_comp_reductionMap_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (idealPartIncl f ι).app M ≫ (reductionMap f).app M = 0 := by
  have hθ := unit_comp_restrictExtensionIsoTensorRight f M
  have h0 : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map ι ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map
        (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
          (ringSheafMapOf J f)) = 0 := by
    rw [← Functor.map_comp, hι, Functor.map_zero]
  rw [← cancel_mono ((restrictExtensionIsoTensorRight f).hom.app M), Category.assoc, hθ,
    zero_comp]
  simp only [idealPartIncl, NatTrans.comp_app, Category.assoc]
  change _ ≫ _ ≫ (tensorRightUnitIso O).hom.app M ≫
    ((Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app M ≫ _) = 0
  have hu : (tensorRightUnitIso O).hom.app M ≫
      (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app M = 𝟙 _ :=
    (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).hom_inv_id_app M
  rw [reassoc_of% hu]
  change _ ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map ι ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map
        (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f)) = 0
  rw [h0, comp_zero]

/-- The reduction sequence `((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ⟶ M ⟶ (O₀ ⊗_O M)|_O` of an `O`-module. -/
abbrev reductionSequenceModule (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  ShortComplex.mk ((idealPartIncl f ι).app M) ((reductionMap f).app M)
    (idealPartIncl_app_comp_reductionMap_app ι hι M)

/-- The reduction sequence of `M` is `M ⊗_O -` applied to the ideal sequence, read through the
projection formula, the unit law and `(O₀ ⊗_O M)|_O ≅ M ⊗_O O₀|_O`. -/
def reductionSequenceModuleIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    tensoredIdealSequence ι hι M ≅ reductionSequenceModule ι hι M :=
  ShortComplex.isoMk ((idealTensorRightIso f I₀).app M) ((tensorRightUnitIso O).app M)
    ((restrictExtensionIsoTensorRight f).app M).symm
    (by
      simp only [Iso.app_hom, idealPartIncl, NatTrans.comp_app, Iso.hom_inv_id_app_assoc]
      rfl)
    (by
      have hθ := unit_comp_restrictExtensionIsoTensorRight f M
      have hu : (tensorRightUnitIso O).hom.app M ≫
          (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).inv.app M = 𝟙 _ :=
        (Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize.{u, v', u'} O).hom_inv_id_app M
      change (tensorRightUnitIso O).hom.app M ≫ (reductionMap f).app M =
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M).map
          (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f)) ≫
          (restrictExtensionIsoTensorRight f).inv.app M
      rw [← cancel_mono ((restrictExtensionIsoTensorRight f).hom.app M), Category.assoc,
        Category.assoc, Iso.inv_hom_id_app]
      exact (congrArg (fun k ↦ (tensorRightUnitIso O).hom.app M ≫ k) hθ).trans
        ((reassoc_of% hu) _ |>.trans (Category.comp_id _).symm))

variable (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
include hS

/-- **The reduction sequence of a flat module is short exact**: tensoring the ideal sequence
with a flat module keeps it short exact. -/
theorem shortExact_reductionSequenceModule
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (hM : flatObjects O M) :
    (reductionSequenceModule ι hι M).ShortExact := by
  have hex : exactFunctor _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M) :=
    (exactFunctor _ _).prop_of_iso
      (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding.{u', v', u} O).app M).symm) hM
  have : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M) := hex.1
  have : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj M) := hex.2
  exact ShortComplex.shortExact_of_iso (reductionSequenceModuleIso ι hι M)
    (hS.map_of_exact _)

end Module

/-! ### The reduction sequence of a complex -/

section Complex

variable (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (hι : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J f) = 0)

/-- The inclusion of the ideal part of a complex of `O`-modules, degreewise. -/
def idealPartInclComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P where
  f n := (idealPartIncl f ι).app (P.X n)
  comm' i j _ := ((idealPartIncl f ι).naturality (P.d i j)).symm

/-- The structure map of the reduction of a complex of `O`-modules, degreewise. -/
def reductionMapComplex
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    P ⟶ ((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P where
  f n := (reductionMap f).app (P.X n)
  comm' i j _ := ((reductionMap f).naturality (P.d i j)).symm

/-- The degreewise inclusion of the ideal part of a complex is natural in the complex. -/
@[reassoc]
theorem idealPartInclComplex_naturality
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (g : P ⟶ P') :
    ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
        idealPartInclComplex ι P' = idealPartInclComplex ι P ≫ g :=
  HomologicalComplex.hom_ext _ _ fun n ↦ (idealPartIncl f ι).naturality (g.f n)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The degreewise structure map of the reduction of a complex is natural in the complex. -/
@[reassoc]
theorem reductionMapComplex_naturality
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (g : P ⟶ P') :
    g ≫ reductionMapComplex P' =
      reductionMapComplex (f := f) P ≫
        ((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).map g :=
  HomologicalComplex.hom_ext _ _ fun n ↦ (reductionMap f).naturality (g.f n)

/-- **The reduction sequence of a complex of `O`-modules**
`((O₀ ⊗_O P) ⊗_{O₀} I₀)|_O ⟶ P ⟶ (O₀ ⊗_O P)|_O`, degreewise. -/
abbrev reductionSequence
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :
    ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ) :=
  ShortComplex.mk (idealPartInclComplex ι P) (reductionMapComplex (f := f) P)
    (HomologicalComplex.hom_ext _ _ fun n ↦ idealPartIncl_app_comp_reductionMap_app ι hι (P.X n))

/-- The reduction sequence is natural in the complex. -/
def reductionSequenceMap
    {P P' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ}
    (g : P ⟶ P') : reductionSequence ι hι P ⟶ reductionSequence ι hι P' where
  τ₁ := ((idealPart f I₀).mapHomologicalComplex (ComplexShape.up ℤ)).map g
  τ₂ := g
  τ₃ := ((reductionPart f).mapHomologicalComplex (ComplexShape.up ℤ)).map g
  comm₁₂ := idealPartInclComplex_naturality ι g
  comm₂₃ := reductionMapComplex_naturality g

/-- **The reduction sequence of a complex with flat terms is short exact.** -/
theorem shortExact_reductionSequence (hS : (idealSequenceOf f I₀ ι hι).ShortExact)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hP : ∀ n, flatObjects O (P.X n)) :
    (reductionSequence ι hι P).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    shortExact_reductionSequenceModule ι hι hS (P.X n) (hP n)

end Complex

end Deformation.ComplexLift

end
