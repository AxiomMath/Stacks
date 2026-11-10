module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ProperOverLocalBase
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.RingTheory.Dualizing.NormalizedSingleSelfField

/-!
# The dualizing complex of a proper scheme over a field

Let `X` be a proper scheme over a field `k` with structure morphism `f : X ⟶ Spec k`, and let
`ω_X^• = a(𝒪_{Spec k})` be the value on `𝒪_{Spec k}[0]` of the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec k})` ([Stacks, Tag 0A9E]); this is
`Stacks.Duality.relativeDualizingComplex`, and `ω_X = H^{-dim X}(ω_X^•)` is
`Stacks.Duality.relativeDualizingModule`. This file proves parts (1)–(4) of
[Stacks, Tag 0FVV] together with the assertion that `ω_X^•` is a dualizing complex, from the
affine chart description of `a(𝒪_{Spec k})`.

## Main results

* `Stacks.Duality.ProperOverField.isDualizingComplex_of_charts` and the companions for the four
  parts.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality.ProperOverField

variable {k : Type u} [Field k]

/-- The ring of global sections of the spectrum of a field is a field. -/
theorem isField_globalSections : IsField Γ(Spec (.of k), ⊤) :=
  (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)

/-- The ring of global sections of the spectrum of a field is a local ring. -/
instance isLocalRing_globalSections : IsLocalRing Γ(Spec (.of k), ⊤) :=
  letI := (isField_globalSections (k := k)).toField
  inferInstance

/-- The ring of global sections of the spectrum of a field is a Noetherian ring. -/
instance isNoetherianRing_globalSections : IsNoetherianRing Γ(Spec (.of k), ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- On the spectrum of a field the structure sheaf in degree zero is modelled on `⊤` by the
normalized dualizing complex `Γ(Spec k, ⊤)[0]`. -/
theorem isTildeModelOn_derivedStructureSheaf :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Spec (.of k), ⊤))
    IsTildeModelOnAnyModel (DerivedPushforward.derivedStructureSheaf (Spec (.of k))).obj ⊤
      (isAffineOpen_top _)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Spec (.of k), ⊤)) 0).obj
        (ModuleCat.of Γ(Spec (.of k), ⊤) Γ(Spec (.of k), ⊤))) :=
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Spec (.of k), ⊤))
  isTildeModelOnAnyModel_unit ⊤ (isAffineOpen_top _)

section Charts

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The affine chart condition on `ω_X^•` ([Stacks, Tag 0BV2] for `a(𝒪_{Spec k})`): over every
affine `U ⊆ X` and for every polynomial presentation of `Γ(Spec k, ⊤) → Γ(X, U)`, `ω_X^•|_U` is the
associated sheaf of the algebraic upper shriek of `Γ(Spec k, ⊤)[0]`. -/
abbrev HasCharts : Prop :=
  HasTopCharts f
    (@DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Spec (.of k), ⊤)) _ _
      (HasDerivedCategory.standard _) 0 |>.obj
        (ModuleCat.of Γ(Spec (.of k), ⊤) Γ(Spec (.of k), ⊤)))
    (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj

/-- **The chart description of `ω_X^•`**, from [Stacks, Tag 0BV2] for `𝒪_{Spec k}`
(`Stacks.Duality.upperShriekStructureSheafCharts`) at the compactification `X̄ = X`, transported
along `Stacks.Duality.upperShriekProperIso` and from the locally small to the standard model of
`D(𝒪_U)`. -/
theorem hasCharts : HasCharts f := by
  have : IsProper (ftsHomToBase f).left := ‹IsProper f›
  intro U hU p
  have : IsAffine (FTS.mk (𝟙 (Spec (.of k)))).left := inferInstanceAs (IsAffine (Spec (.of k)))
  obtain ⟨e⟩ := upperShriekStructureSheafCharts (ftsHomToBase f)
    (properCompactification (ftsHomToBase f))
    ⊤ (isAffineOpen_top _) U hU le_top p
  refine isTildeModelOnAnyModel_of_iso ((ObjectProperty.ι _).mapIso
    ((upperShriekProperIso (ftsHomToBase f)).app _)) ⟨?_⟩
  exact Stacks.Injectives.isoOfTargetModelIso.{u} U.toScheme.Modules
    (Scheme.Modules.restrictFunctor U.ι)
    (hd₂ := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U)))
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) _ _ e

variable {f} [IsLocallyNoetherian X]

/-- `ω_X^•` is a dualizing complex, given its chart description. -/
theorem isDualizingComplex_of_charts (hchart : HasCharts f) :
    IsDualizingComplex (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj :=
  isDualizingComplex_of_hasTopCharts f
    (Dualizing.isNormalizedDualizingComplex_single_self_of_isField isField_globalSections).1 hchart

/-- `ω_X^•` is normalized at the closed points, given its chart description. -/
theorem associatedShiftFunction_eq_zero_of_charts (hchart : HasCharts f) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    associatedShiftFunction (relativeDualizingComplex f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj x = 0 :=
  associatedShiftFunction_eq_zero_of_hasTopCharts f
    (Dualizing.isNormalizedDualizingComplex_single_self_of_isField isField_globalSections)
    hchart x hx

section CompactSpace

variable [CompactSpace X]

/-- A compact locally Noetherian scheme is Noetherian. -/
private instance isNoetherian_of_compactSpace : AlgebraicGeometry.IsNoetherian X := ⟨⟩

/-- The four conclusions of [Stacks, Tag 0AWN] for `ω_X^•`, given its chart description:
cohomology in degrees `-dim X, …, 0` only, supports of dimension at most `-i`, and the first
cohomology sheaf `ω_X` coherent with property `(S₂)`, supported on the top-dimensional
components. -/
theorem vanishing_and_support_of_charts (hchart : HasCharts f) :
    letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
    let ω := (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj
    (∀ i : ℤ, ¬ Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj ω) →
      i ≤ 0 ∧ (((-i).toNat : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) ∧
    (∀ i : ℤ, topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj ω)) ≤
      if i ≤ 0 then (((-i).toNat : ℕ) : WithBot ℕ∞) else ⊥) ∧
    (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).IsCoherent ∧
    SheafHasPropertySk X (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) 2 ∧
    _root_.SheafOfModules.supp (relativeDualizingModule f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = topologicalKrullDim X} :=
  vanishing_and_support_of_hasTopCharts f
    (Dualizing.isNormalizedDualizingComplex_single_self_of_isField isField_globalSections) hchart

/-- The cohomology sheaves of `ω_X^•` vanish below degree `-dim X`, given its chart description;
this is the input of part (6) of [Stacks, Tag 0FVV]. -/
theorem isZero_homology_of_lt_of_charts (hchart : HasCharts f) :
    ∀ j < -(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ),
      Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj
        (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj) := by
  intro j hj
  by_contra hne
  have := mem_Icc_of_not_isZero_homology_of_associatedShiftFunction_eq_zero
    (isDualizingComplex_of_charts hchart) (associatedShiftFunction_eq_zero_of_charts hchart) j hne
  exact absurd this.1 (not_le.mpr hj)

/-- Part (4) of [Stacks, Tag 0FVV] given the chart description: at a closed point `x`, one of
`H^i(ω_{X,x}^•), …, H^0(ω_{X,x}^•)` is nonzero exactly when `depth(𝒪_{X,x}) ≤ -i`. -/
theorem exists_nontrivial_iff_depth_le_of_charts (hchart : HasCharts f) {x : X}
    (hx : IsClosed ({x} : Set X)) (i : ℤ) :
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧ Nontrivial (moduleStalkAtPoint
        ((DerivedCategory.homologyFunctor X.Modules j).obj
          (relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (DerivedPushforward.derivedStructureSheaf (Spec (.of k)))).obj) x)) ↔
      i ≤ 0 ∧ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≤ ((-i).toNat : ℕ∞) :=
  exists_nontrivial_iff_depth_le_of_hasTopCharts f
    (Dualizing.isNormalizedDualizingComplex_single_self_of_isField isField_globalSections)
    hchart hx i

end CompactSpace

end Charts

end Stacks.Duality.ProperOverField

end
