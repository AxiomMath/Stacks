module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineFinitePresentationFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyIdealDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyPushforwardSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# The situation of Stacks 0GUY along an isomorphism of algebraic spaces

The situation of Stacks 0GUY over an algebraic space `X`, and a surjection from a finite locally
free module onto `π_*ℐ`, carry along an isomorphism `e : X ≅ X'`: the chart, the space `Y`, the
open immersion `j` and the ideal `ℐ` are kept, and `φ` and `π` are composed with `e`.

## Main definitions

* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.ofIso`: the situation over `X'`.

## Main results

* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.exists_epi_idealDirectImage_ofIso`:
  a surjection `ℰ ⟶ π_*ℐ` from a finite locally free module over `X` gives one over `X'`, namely
  its inverse image along `e⁻¹`.
* `AlgebraicGeometry.Space.ResolutionPropertyDescentSituation.isFinitePresentation_π_ofIso`:
  `π` stays of finite presentation.

## Implementation notes

The inverse image along `e⁻¹` is identified with the direct image along `e` through the
equivalence of module categories that `e` induces (the unit and composition laws of Stacks 03LU).

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

section ModuleIso

variable {X X' : AlgebraicSpaces B S hS}

/-- The equivalence of module categories induced by an isomorphism of algebraic spaces, with
functor the inverse image along `e⁻¹`. -/
private def moduleEquivOfIso (e : X ≅ X') :
    Modules.{u, u} B S hS X.1 X.2 ≌ Modules.{u, u} B S hS X'.1 X'.2 :=
  CategoryTheory.Equivalence.mk (modulePullback B S hS e.inv) (modulePullback B S hS e.hom)
    ((modulePullbackIdIso B S hS X).symm ≪≫
      eqToIso (congrArg (modulePullback B S hS) e.hom_inv_id.symm) ≪≫
      (modulePullbackCompIso B S hS e.hom e.inv).symm)
    (modulePullbackCompIso B S hS e.inv e.hom ≪≫
      eqToIso (congrArg (modulePullback B S hS) e.inv_hom_id) ≪≫ modulePullbackIdIso B S hS X')

/-- Along an isomorphism `e`, the inverse image along `e⁻¹` is the direct image along `e`. -/
private def modulePullbackInvIsoModulePushforward (e : X ≅ X') :
    modulePullback B S hS e.inv ≅ modulePushforward B S hS e.hom :=
  Adjunction.rightAdjointUniq (moduleEquivOfIso B S hS e).symm.toAdjunction
    (modulePullbackAdjunction B S hS e.hom)

end ModuleIso

namespace ResolutionPropertyDescentSituation

variable {B S hS hZ} {X X' : AlgebraicSpaces B S hS} {hqc : IsQuasiCompactSpace B S hS X.1}
    {hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1}

/-- **The situation of Stacks 0GUY carried along an isomorphism `e : X ≅ X'`.**  The chart `V`,
the space `Y`, the open immersion `j` and the ideal `ℐ` are kept; `φ` and `π` are composed with
`e`. -/
def ofIso (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs) (e : X ≅ X')
    (hqc' : IsQuasiCompactSpace B S hS X'.1) (hqs' : IsAbsolutelyQuasiSeparated B S hS hZ X'.1) :
    ResolutionPropertyDescentSituation B S hS hZ X' hqc' hqs' where
  V := sit.V
  isAffine_V := sit.isAffine_V
  φ := sit.φ ≫ e.hom.hom
  isSurjective_φ := isSurjective_comp B S hS sit.isSurjective_φ
    (isSurjective_of_isIso B S hS e.hom.hom)
  isEtale_φ := isEtale_comp B S hS sit.isEtale_φ (isEtale_of_isIso B S hS e.hom.hom)
  Y := sit.Y
  j := sit.j
  π := sit.π ≫ e.hom.hom
  isOpenImmersion_j := sit.isOpenImmersion_j
  isFinite_π := isFinite_comp B S hS sit.isFinite_π (isFinite_of_isIso_hom B S hS e.hom.hom)
  comp_eq := by rw [← Category.assoc, sit.comp_eq]
  I := sit.I
  isFiniteTypeQuasicoherent_I := sit.isFiniteTypeQuasicoherent_I
  idealZeroLocus_I := sit.idealZeroLocus_I

variable (sit : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs) (e : X ≅ X')
    (hqc' : IsQuasiCompactSpace B S hS X'.1) (hqs' : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)

/-- The finite morphism `π` of the situation carried along `e` is `π ≫ e`. -/
@[simp] theorem ofIso_π : (sit.ofIso e hqc' hqs').π = sit.π ≫ e.hom.hom := rfl

/-- The space `Y` of the situation carried along `e` is unchanged. -/
@[simp] theorem ofIso_Y : (sit.ofIso e hqc' hqs').Y = sit.Y := rfl

/-- An isomorphism of algebraic spaces is of finite presentation. -/
private theorem isFinitePresentation_of_isIso' {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [IsIso f] : IsFinitePresentation B S hS f :=
  ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS f),
    isQuasiCompact_of_isIso B S hS f,
    isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isIso B S hS f)⟩

/-- `π` stays of finite presentation along an isomorphism. -/
theorem isFinitePresentation_π_ofIso (h : IsFinitePresentation B S hS sit.π) :
    IsFinitePresentation B S hS (sit.ofIso e hqc' hqs').π :=
  isFinitePresentation_comp B S hS sit.Y.2 X.2 X'.2 _ _ h (isFinitePresentation_of_isIso' e.hom.hom)

/-- The direct image `π_*ℐ` of the situation carried along `e` is the direct image along `e` of
`π_*ℐ`, read as the inverse image along `e⁻¹`. -/
private def idealDirectImageOfIsoIso :
    (modulePullback B S hS e.inv).obj (sit.idealDirectImage B S hS hZ) ≅
      (sit.ofIso e hqc' hqs').idealDirectImage B S hS hZ :=
  (modulePullbackInvIsoModulePushforward B S hS e).app _ ≪≫
    (modulePushforward B S hS e.hom).mapIso
      ((modulePushforwardChartIso B S hS sit.πHom
        (relativelyRepresentable_hom_of_isFinite B S hS sit.πHom sit.isFinite_π)).app
          sit.I.toSheafOfModules).symm ≪≫
    (modulePushforwardCompIso B S hS sit.πHom e.hom).app sit.I.toSheafOfModules ≪≫
    (modulePushforwardChartIso B S hS ((sit.ofIso e hqc' hqs').πHom)
        (relativelyRepresentable_hom_of_isFinite B S hS (sit.ofIso e hqc' hqs').πHom
          (sit.ofIso e hqc' hqs').isFinite_π)).app sit.I.toSheafOfModules

/-- **A surjection from a finite locally free module onto `π_*ℐ` carries along an isomorphism**:
its inverse image along `e⁻¹` is a surjection onto `π_*ℐ` for the situation carried along `e`. -/
theorem exists_epi_idealDirectImage_ofIso
    (h : ∃ (E : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ sit.idealDirectImage B S hS hZ), Epi p) :
    ∃ (E : Modules.{u, u} B S hS X'.1 X'.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite E)
      (p : E ⟶ (sit.ofIso e hqc' hqs').idealDirectImage B S hS hZ), Epi p := by
  obtain ⟨E, hE, p, hp⟩ := h
  refine ⟨(modulePullback B S hS e.inv).obj E,
    isFiniteLocallyFreeOnSite_modulePullback B S hS e.inv E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOnSite E hE) hE,
    (modulePullback B S hS e.inv).map p ≫ (idealDirectImageOfIsoIso sit e hqc' hqs').hom, ?_⟩
  have := preservesEpimorphisms_modulePullback B S hS e.inv
  exact epi_comp' ((modulePullback B S hS e.inv).map_epi p)
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))

end ResolutionPropertyDescentSituation

end AlgebraicGeometry.Space

end
