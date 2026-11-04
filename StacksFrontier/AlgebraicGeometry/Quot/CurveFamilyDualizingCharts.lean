module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyChartSquare
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenus
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.NodalShape
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.ProperOverField
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic

/-!
# The relative dualizing sheaves of the étale charts of a family of curves

Let `f : X ⟶ S` be a family of curves (Stacks 0D4Z). For an étale chart `U` of the total space,
`U ⟶ S` is a flat morphism of schemes locally of finite presentation
(`AlgebraicGeometry.CurveFamily.chartMorphism`); its chosen relative dualizing complex
`ω^•_{U/S}` (Stacks 0E2T, 0E2X) gives the module `ω_{U/S} = H^{-1}(ω^•_{U/S})`
(`AlgebraicGeometry.CurveFamily.chartDualizingSheaf`). For a family which is at-worst-nodal of
relative dimension one, `ω^•_{U/S} = ω_{U/S}[1]` and `ω_{U/S}` is invertible (Stacks 0E6P, 0E6R on
the chart).

When the total space is the scheme `V` itself (as for the fibre of a family over a field-valued
point), the identity chart of `V` lies over the structure morphism, and for a proper `V` over a
field the module of the identity chart is the dualizing sheaf of Stacks 0BS2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

open StrictlyPerfect (OXMod)

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase} (F : CurveFamily B hZ)

/-- The morphism of schemes `U ⟶ S` of an étale chart `U` of the total space. -/
abbrev chartMorphism (U : Space.SmallEtale B integerBase hZ F.total.1) :
    Space.chartScheme U ⟶ (BigFppfOver.toScheme B integerBase hZ).obj F.base :=
  (BigFppfOver.toScheme B integerBase hZ).map (F.chartToBase U)

/-- The morphism `U ⟶ S` of an étale chart `U` of the total space is flat. -/
instance (U : Space.SmallEtale B integerBase hZ F.total.1) : Flat (F.chartMorphism U) :=
  F.flat_chartToBase U

/-- The morphism `U ⟶ S` of an étale chart `U` of the total space is locally of finite
presentation. -/
instance (U : Space.SmallEtale B integerBase hZ F.total.1) :
    LocallyOfFinitePresentation (F.chartMorphism U) :=
  F.locallyOfFinitePresentation_chartToBase U

/-- **The relative dualizing complex of an étale chart** `ω^•_{U/S}`. -/
abbrev chartDualizingComplex (U : Space.SmallEtale B integerBase hZ F.total.1) :
    @DerivedCategory (OXMod.{u, u} (Space.chartScheme U).toRingedSpace) _ _
      (HasDerivedCategory.standard _) :=
  Scheme.Hom.relDualizingComplex (F.chartMorphism U)

/-- **The relative dualizing sheaf of an étale chart** `ω_{U/S} = H^{-1}(ω^•_{U/S})`. -/
def chartDualizingSheaf (U : Space.SmallEtale B integerBase hZ F.total.1) :
    (Space.chartScheme U).Modules :=
  letI := HasDerivedCategory.standard (Space.chartScheme U).Modules
  (DerivedCategory.homologyFunctor (Space.chartScheme U).Modules (-1)).obj
    (F.chartDualizingComplex U)

variable {F}

/-- For a nodal family, the shape of the relative dualizing complex of a chart. -/
theorem chartDualizingComplex_shape (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom) (U : Space.SmallEtale B integerBase hZ F.total.1) :
    letI := HasDerivedCategory.standard (Space.chartScheme U).Modules
    (∀ j : ℤ, j ≠ -1 → IsZero ((DerivedCategory.homologyFunctor (Space.chartScheme U).Modules j).obj
        (F.chartDualizingComplex U))) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (F.chartDualizingSheaf U) 1 ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible (Space.chartScheme U).presheaf
        (Space.chartScheme U).ringCatSheaf.2 (F.chartDualizingSheaf U) ∧
      Nonempty (F.chartDualizingComplex U ≅
        (DerivedCategory.singleFunctor (Space.chartScheme U).Modules (-1)).obj
          (F.chartDualizingSheaf U)) :=
  let (T : RingedSpace.{u, u}) := HasDerivedCategory.standard (OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  Stacks.Duality.NodalShape.isRelativeDualizingComplex_shape_of_isAtWorstNodal
    (F.chartMorphism U) (F.holds_chartToBase hF U) _ _ _
    (Scheme.Hom.isRelativeDualizingComplex_relDualizing (F.chartMorphism U))

/-- For a nodal family, the relative dualizing sheaf of a chart is invertible. -/
theorem isInvertibleModule_chartDualizingSheaf (hF : Space.IsAtWorstNodalOfRelativeDimensionOne B
      integerBase hZ F.toBase.hom) (U : Space.SmallEtale B integerBase hZ F.total.1) :
    Stacks.Ample.IsInvertibleModule (Space.chartScheme U) (F.chartDualizingSheaf U) :=
  (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one _ _).mpr
    (chartDualizingComplex_shape hF U).2.1

/-! ### The identity chart of the fibre over a field-valued point -/

section Fibre

variable (F : CurveFamily B hZ)
  {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
  {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ F.total.obj}

/-- The identity chart of the fibre lies over the structure morphism of the fibre. -/
theorem chartToBase_fibreFamily_idEtaleChart
    (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    (F.fibreFamily hsq).chartToBase (Space.idEtaleChart B integerBase hZ V) = v :=
  Yoneda.fullyFaithful.map_injective
    ((yoneda_map_chartToBase _ _).trans (Category.id_comp (yoneda.map v)))

/-- The dualizing sheaf of a proper scheme over a field depends only on the structure morphism. -/
def dualizingSheafOverFieldCongr {k : Type u} [Field k] {Y : Scheme.{u}}
    {φ ψ : Y ⟶ Spec (CommRingCat.of k)} [IsProper φ] [IsProper ψ] (h : φ = ψ) :
    Stacks.Duality.dualizingSheafOverField φ ≅ Stacks.Duality.dualizingSheafOverField ψ := by
  subst h
  exact Iso.refl _

/-- The structure morphism of the fibre over a field-valued point, with target written as the
spectrum of the field. -/
abbrev fibreStructureMorphism (v : V ⟶ p.siteObject) :
    (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ Spec (CommRingCat.of p.carrier) :=
  (BigFppfOver.toScheme B integerBase hZ).map v

/-- **On the fibre over a field-valued point, the relative dualizing sheaf of the identity chart is
the dualizing sheaf of the fibre** (Stacks 0BS2, through Stacks 0E2Z). -/
theorem nonempty_chartDualizingSheaf_fibre_iso
    (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value))
    [hv : IsProper (F.fibreStructureMorphism v)] :
    Nonempty ((F.fibreFamily hsq).chartDualizingSheaf (Space.idEtaleChart B integerBase hZ V) ≅
      @Stacks.Duality.dualizingSheafOverField p.carrier _ _ (F.fibreStructureMorphism v) hv) := by
  let (T : RingedSpace.{u, u}) := HasDerivedCategory.standard (OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let φ : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ Spec (CommRingCat.of p.carrier) :=
    (F.fibreFamily hsq).chartMorphism (Space.idEtaleChart B integerBase hZ V)
  have e : φ = F.fibreStructureMorphism v :=
    congrArg (BigFppfOver.toScheme B integerBase hZ).map
      (F.chartToBase_fibreFamily_idEtaleChart hsq)
  have : IsProper φ := e ▸ hv
  have : Flat φ := (F.fibreFamily hsq).flat_chartToBase (Space.idEtaleChart B integerBase hZ V)
  have : LocallyOfFinitePresentation φ :=
    (F.fibreFamily hsq).locallyOfFinitePresentation_chartToBase
      (Space.idEtaleChart B integerBase hZ V)
  open Stacks.Duality.CurveFamilyDualizing in
  obtain ⟨i⟩ :=
    nonempty_homology_neg_one_iso_dualizingSheafOverField_of_isRelativeDualizingComplex
      φ (Scheme.Hom.isRelativeDualizingComplex_relDualizing φ)
  exact ⟨i ≪≫ @dualizingSheafOverFieldCongr p.carrier _ _ _ _ _ hv e⟩

end Fibre

end AlgebraicGeometry.CurveFamily

end
