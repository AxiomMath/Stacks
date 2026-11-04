module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Restriction
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Existence
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.UnitCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceOrbit
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceFromModel
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TopDifferentialRelative
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DualizingNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexStandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.RelativeDualizingComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Relative Poincaré duality for de Rham cohomology

Let `S` be quasi-compact and quasi-separated and `f : X ⟶ S` proper and smooth, all of whose
fibres are nonempty and equidimensional of dimension `n` ([Stacks, Tag 0G8G]). There is an
`𝒪_S`-module map `t : R^{2n}f_*Ω^•_{X/S} ⟶ 𝒪_S`, unique up to precomposing by multiplication by a
unit of `H^0(X, 𝒪_X)`, such that the pairing
`Rf_*Ω^•_{X/S} ⊗^L Rf_*Ω^•_{X/S}[2n] ⟶ 𝒪_S`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, is a perfect pairing of
perfect complexes ([Stacks, Tag 0G8K]).

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.existsUnique_deRhamPoincareTrace`:
  [Stacks, Tag 0G8K].

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- `Scheme.Hom.exists_eq_formsShiftSMul_comp` from a perfect pairing in degree zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_eq_formsShiftSMul_comp_of_isPerfectDerivedPairing
    {X S : Scheme.{u}} {f : X ⟶ S} (DY : DerivedTensorHomAdjunction S) (n : ℤ)
    {t : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj}
    (ht : IsPerfectDerivedPairing DY (f.relativeHodgePairing n 0 (n - 0) (by ring) t))
    (t' : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    ∃ g : Γ(X, ⊤), t' = f.formsShiftSMul n g ≫ t :=
  Scheme.Hom.exists_eq_formsShiftSMul_comp DY n ht.2.2 t'

/-- `H^0(Rf_*(Ω^•[2n])) ≅ R^{2n}f_*Ω^•`. -/
def deRhamDirectImageTopHomologyIso :
    (DerivedCategory.homologyFunctor D.S.Modules 0).obj D.deRhamDirectImageTop ≅
      D.deRhamTopCohomology :=
  letI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  (DerivedCategory.homologyFunctor D.S.Modules 0).mapIso
      (((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso (2 * D.n : ℤ)).app
        (Scheme.deRhamDerived D.f)) ≪≫
    ((DerivedCategory.homologyFunctor D.S.Modules 0).shiftIso (2 * D.n : ℤ) 0 (2 * D.n : ℤ)
      (by omega)).app _

/-- The identification of `H^0` with `R^{2n}` is natural in maps of `Ω^•`. -/
theorem deRhamDirectImageTopHomologyIso_naturality
    (φ : Scheme.deRhamDerived D.f ⟶ Scheme.deRhamDerived D.f) :
    (DerivedCategory.homologyFunctor D.S.Modules 0).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map
          ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf)
            (2 * D.n : ℤ)).map φ)) ≫ D.deRhamDirectImageTopHomologyIso.hom =
      D.deRhamDirectImageTopHomologyIso.hom ≫
        (DerivedCategory.homologyFunctor D.S.Modules (2 * D.n : ℤ)).map
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).map φ) := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  exact ((DerivedCategory.homologyFunctor D.S.Modules 0).map_comp_assoc _ _ _).symm.trans
    ((congrArg (fun x => (DerivedCategory.homologyFunctor D.S.Modules 0).map x ≫ _)
      (((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso
        (2 * D.n : ℤ)).hom.naturality φ)).trans
      (((DerivedCategory.homologyFunctor D.S.Modules 0).map_comp_assoc _ _ _).trans
        (congrArg (_ ≫ ·) (((DerivedCategory.homologyFunctor D.S.Modules 0).shiftIso
          (2 * D.n : ℤ) 0 (2 * D.n : ℤ) (by omega)).hom.naturality
            ((derivedPushforward (inverseImageBaseProjection D.f)).map φ)))))

/-- The equivalence `Hom(Rf_*Ω^•[2n], 𝒪_S) ≃ Hom(R^{2n}f_*Ω^•, 𝒪_S)`. -/
def deRhamTraceEquiv :
    (D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) ≃
      (D.deRhamTopCohomology ⟶ SheafOfModules.unit D.S.ringCatSheaf) :=
  (Equiv.ofBijective _ (@DerivedCategory.bijective_homologyFunctor_map_of_isLE_of_isGE _ _ _ _
    D.deRhamDirectImageTop (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj 0
    D.isLE_deRhamDirectImageTop (by exact DerivedCategory.instIsGEObjSingleFunctor _ _))).trans
    (Iso.homCongr D.deRhamDirectImageTopHomologyIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso D.S.Modules 0).app _))

/-- **Maps out of `Rf_*(Ω^•[2n])` are determined by their restriction to the top piece**, since
`d : Rⁿf_*Ω^{n-1} ⟶ Rⁿf_*Ωⁿ` vanishes ([Stacks, Tag 0G8J]). -/
theorem bijective_topInclusion_comp : Function.Bijective
    (fun s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj =>
      D.topInclusion ≫ s) :=
  D.bijective_topInclusion_comp_of_topDifferential
    (Stacks.WeilDeRham.higherDirectImage_map_deRham_d_top_eq_zero D)

/-- The identification `Hom(Rf_*(Ω^•[2n]), 𝒪_S) ≃ Hom(R^{2n}f_*Ω^•, 𝒪_S)` is compatible with
multiplication by a global function. -/
theorem deRhamTraceEquiv_smul_comp (g : Γ(D.X, ⊤))
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj) :
    D.deRhamTraceEquiv (D.deRhamDirectImageTopSMul g ≫ s) =
      D.deRhamTopCohomologySMul g ≫ D.deRhamTraceEquiv s := by
  have key : D.deRhamDirectImageTopHomologyIso.inv ≫
      (DerivedCategory.homologyFunctor D.S.Modules 0).map (D.deRhamDirectImageTopSMul g) =
      D.deRhamTopCohomologySMul g ≫ D.deRhamDirectImageTopHomologyIso.inv :=
    (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
      (D.deRhamDirectImageTopHomologyIso_naturality (D.deRhamDerivedSMul g))).trans
        (Category.assoc _ _ _))
  exact (congrArg (D.deRhamDirectImageTopHomologyIso.inv ≫ ·)
      ((DerivedCategory.homologyFunctor D.S.Modules 0).map_comp_assoc _ _ _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _)))

/-- The assembly, from a trace of [Stacks, Tag 0G8I] whose lifts have the property. -/
theorem existsUnique_deRhamPoincareTrace_of_trace {t₀}
    (ht₀ : D.IsRelativePoincareTrace t₀)
    (hB : ∀ s, D.topInclusion ≫ s = t₀ → D.IsDeRhamPoincareTrace s) :
    ∃ t : D.deRhamTopCohomology ⟶ SheafOfModules.unit D.S.ringCatSheaf,
      D.IsDeRhamPoincareTrace (D.deRhamTraceEquiv.symm t) ∧
      ∀ t' : D.deRhamTopCohomology ⟶ SheafOfModules.unit D.S.ringCatSheaf,
        D.IsDeRhamPoincareTrace (D.deRhamTraceEquiv.symm t') ↔
          ∃ u : (Γ(D.X, ⊤))ˣ, t' = D.deRhamTopCohomologySMul (u : Γ(D.X, ⊤)) ≫ t := by
  obtain ⟨s, hs⟩ := D.bijective_topInclusion_comp.2 t₀
  have hP : D.IsDeRhamPoincareTrace s := hB s hs
  refine ⟨D.deRhamTraceEquiv s, by simpa using hP, fun t' => ⟨fun ht' => ?_, ?_⟩⟩
  · obtain ⟨g, hg⟩ := Scheme.Hom.exists_eq_formsShiftSMul_comp_of_isPerfectDerivedPairing _ D.n
      (ht₀ 0) (D.topInclusion ≫ D.deRhamTraceEquiv.symm t')
    have e : D.deRhamTraceEquiv.symm t' = D.deRhamDirectImageTopSMul g ≫ s := by
      apply D.bijective_topInclusion_comp.1
      show D.topInclusion ≫ _ = D.topInclusion ≫ _
      have hs' : D.topInclusion ≫ s = t₀ := hs
      exact hg.trans ((congrArg (D.f.formsShiftSMul D.n g ≫ ·) hs'.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ s) (D.topInclusion_comp_smul g).symm).trans (Category.assoc _ _ _))))
    have hu : IsUnit g := D.isUnit_of_isDeRhamPoincareTrace_smul_comp g s hP (e ▸ ht')
    refine ⟨hu.unit, ?_⟩
    rw [← D.deRhamTraceEquiv_smul_comp, IsUnit.unit_spec, ← e, Equiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    rw [← D.deRhamTraceEquiv_smul_comp, Equiv.symm_apply_apply]
    exact D.isDeRhamPoincareTrace_smul_comp u s hP

/-- **[Stacks, Tag 0G8K].** In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]):
`S` quasi-compact and quasi-separated, `f : X ⟶ S` proper and smooth, all of whose fibres are
nonempty and equidimensional of dimension `n`. There is an `𝒪_S`-module map
`t : R^{2n}f_*Ω^•_{X/S} ⟶ 𝒪_S` such that the pairing
`Rf_*Ω^•_{X/S} ⊗^L Rf_*Ω^•_{X/S}[2n] ⟶ 𝒪_S`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, is a perfect pairing of
perfect complexes (`IsDeRhamPoincareTrace`, read through the identification
`Hom(Rf_*(Ω^•[2n]), 𝒪_S) ≃ Hom(R^{2n}f_*Ω^•, 𝒪_S)` of `deRhamTraceEquiv`, which holds as
`Rf_*(Ω^•[2n])` has no cohomology in positive degrees), and `t` is unique up to precomposing with
multiplication by a unit of `H^0(X, 𝒪_X)`: the maps with this property are exactly the
`t ∘ u` for `u` a unit of `Γ(X, 𝒪_X)`. -/
@[stacks 0G8K "relative Poincaré duality for de Rham cohomology: there is t : R^{2n}f_*Omega^. \
-> O_S, unique up to a unit of H^0(X, O_X), such that (xi, xi') |-> t(xi cup xi') is a perfect \
pairing Rf_*Omega^. (x)^L Rf_*Omega^.[2n] -> O_S of perfect complexes"]
theorem existsUnique_deRhamPoincareTrace :
    ∃ t : D.deRhamTopCohomology ⟶ SheafOfModules.unit D.S.ringCatSheaf,
      D.IsDeRhamPoincareTrace (D.deRhamTraceEquiv.symm t) ∧
      ∀ t' : D.deRhamTopCohomology ⟶ SheafOfModules.unit D.S.ringCatSheaf,
        D.IsDeRhamPoincareTrace (D.deRhamTraceEquiv.symm t') ↔
          ∃ u : (Γ(D.X, ⊤))ˣ, t' = D.deRhamTopCohomologySMul (u : Γ(D.X, ⊤)) ≫ t := by
  obtain ⟨ψ₀⟩ :=
    Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian
      D.f D.n (fun h =>
        ⟨Stacks.Duality.singleFunctorExteriorPowerIsoRelativeDualizingComplex h D.n⟩)
  exact D.existsUnique_deRhamPoincareTrace_of_trace
    (D.isRelativePoincareTrace_of_iso (D.formsShiftIsoRelativeDualizingComplexOfModel ψ₀))
    (fun s hs => D.isDeRhamPoincareTrace_of_topInclusion_comp
      (D.formsShiftIsoRelativeDualizingComplexOfModel ψ₀) s hs)

end AlgebraicGeometry.RelativeDualitySituation

end
