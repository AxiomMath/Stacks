module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafCurve
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochZeroScheme

/-!
# The degree formula for an invertible module on a proper integral curve

Let `k` be a field and let `X` be a proper integral curve over `k`. For every invertible
`𝒪_X`-module `ℒ`,

`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`,

equation [Stacks, Tag 0BRY], and consequently

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`,

equation [Stacks, Tag 0BRZ], with no hypothesis on `ℒ` beyond invertibility.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `moduleIso_app_inv_hom`: an isomorphism of `𝒪_X`-modules is inverted on global sections.
* `curveDegree_one_eq_curveChernDegree_of_eval_top_ne_zero`: equation [Stacks, Tag 0BRY] for an
  invertible module with a nonzero global section on a proper integral scheme of dimension at
  most one.
* `curveChernDegree_tensorObj`: `deg(c₁(ℒ) ∩ [X]_1) + deg(c₁(𝒩) ∩ [X]_1) = deg(c₁(ℒ ⊗ 𝒩) ∩ [X]_1)`.
* `curveChernDegree_congr`: the Chern side depends only on the isomorphism class.
* `curveDegree_one_tensorObj`: `deg(ℒ ⊗ 𝒩) = deg(ℒ) + deg(𝒩)` at rank one.
* `curveDegree_one_eq_curveChernDegree_of_isCurve`: equation [Stacks, Tag 0BRY] for an invertible
  module on a proper integral curve.
* `eulerCharacteristic_eq_curveChernDegree_add_of_isCurve`: equation [Stacks, Tag 0BRZ] for an
  invertible module on a proper integral curve.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Chow Stacks.Divisors
open Stacks.SheafOfModules (sectionsOfTop sectionsOfTop_eval_top)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-! ### Global sections across an isomorphism -/

/-- **An isomorphism of `𝒪_X`-modules is inverted on global sections**: `e.hom (e.inv y) = y` for
a global section `y`. -/
theorem moduleIso_app_inv_hom {Y : Scheme.{u}} {F G : Y.Modules} (e : F ≅ G) (y : Γ(G, ⊤)) :
    Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app e.inv ⊤ y) = y :=
  (ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.inv_hom_id e)) y).trans
    (CategoryTheory.id_apply y)

/-! ### Equation 0BRY from a nonzero global section -/

/-- **Equation [Stacks, Tag 0BRY] for an invertible module with a nonzero global section on a
proper integral scheme of dimension at most one**: `deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`. -/
theorem curveDegree_one_eq_curveChernDegree_of_eval_top_ne_zero [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (s : M.sections) (hs : s.eval (op ⊤) ≠ 0) :
    curveDegree k p hdim M 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 M) := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback (𝟙 X)).obj M) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (Scheme.Hom.toLRSHom (𝟙 X)).toShHom M hM
  obtain ⟨t, ht⟩ : ∃ t : ((Scheme.Modules.pullback (𝟙 X)).obj M).sections,
      t.eval (op ⊤) = Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId X).app M).inv ⊤
        (s.eval (op ⊤)) :=
    ⟨sectionsOfTop (X := X.toRingedSpace) _ _, sectionsOfTop_eval_top (X := X.toRingedSpace) _ _⟩
  exact curveDegree_one_eq_curveChernDegree_of_isIntegral k p hdim M s hs t
    (ht ▸ moduleIso_app_inv_hom _ _)

/-! ### Additivity of the two sides in the tensor product -/

/-- **[Stacks, Tag 02SP] read through the degree of the zero cycle.** For `ℒ` and `𝒩` invertible
on a proper scheme of dimension at most one over a field,

`deg(c₁(ℒ) ∩ [X]_1) + deg(c₁(𝒩) ∩ [X]_1) = deg(c₁(ℒ ⊗ 𝒩) ∩ [X]_1)`. -/
theorem curveChernDegree_tensorObj (hdim : topologicalKrullDim X ≤ 1) (L N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 N) =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0
        (Scheme.Modules.tensorObj L N)) := by
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L N) := isInvertible_tensorObj _ _
  rw [curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible,
    curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible,
    curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible, ← map_add,
    firstChernClassCapOfInvertible_tensorObj]

/-- **The Chern side of the degree formula depends only on the isomorphism class of the
invertible module.** -/
theorem curveChernDegree_congr (hdim : topologicalKrullDim X ≤ 1) (L N : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (e : L ≅ N) :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 N) := by
  rw [curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible,
    curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible,
    firstChernClassCapOfInvertible_congr (fieldChowSituation k) p 0 L N e]

/-- **[Stacks, Tag 0AYX] at rank one.** For `ℒ` and `𝒩` of rank one on a proper curve,

`deg(ℒ ⊗ 𝒩) = deg(ℒ) + deg(𝒩)`. -/
theorem curveDegree_one_tensorObj [IsCurve k p] (hdim : topologicalKrullDim X ≤ 1)
    (L N : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Modules.tensorObj L N) 1] :
    curveDegree k p hdim (Scheme.Modules.tensorObj L N) 1 =
      curveDegree k p hdim L 1 + curveDegree k p hdim N 1 := by
  have h := curveDegree_tensorSheaf_eq_add k p hdim L N 1 1
  simp only [one_mul, Nat.cast_one] at h
  exact h

/-! ### Equation 0BRY on a proper integral curve -/

section

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

/-- **Equation [Stacks, Tag 0BRY] for an invertible module on a proper integral curve**:

`deg(ℒ) = deg(c₁(ℒ) ∩ [X]_1)`. -/
theorem curveDegree_one_eq_curveChernDegree_of_isCurve [IsCurve k p]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    curveDegree k p hdim L 1 =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) := by
  have : IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field p
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field p
  have hLm : Stacks.Ample.IsInvertibleModule X L := hL
  obtain ⟨D, D', hD, hD', -, -, ⟨e⟩⟩ :=
    InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf_of_isReduced
      hdim L (E := (∅ : Set X)) Set.finite_empty
  have hA : Stacks.Ample.IsInvertibleModule X (invertibleSheaf' D) :=
    invertibleSheaf_isInvertible D
  have hB : Stacks.Ample.IsInvertibleModule X (invertibleSheaf' D') :=
    invertibleSheaf_isInvertible D'
  have hA' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (invertibleSheaf' D) := hA
  have hB' : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (invertibleSheaf' D') := hB
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (invertibleSheaf' D) 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X _
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (invertibleSheaf' D') 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X _
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Modules.tensorObj L (invertibleSheaf' D')) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X L (invertibleSheaf' D') 1 1
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L (invertibleSheaf' D')) := isInvertible_tensorObj _ _
  have e' : Scheme.Modules.tensorObj L (invertibleSheaf' D') ≅ invertibleSheaf' D :=
    (Stacks.SheafOfModules.tensorObjIso X.sheaf.obj X.ringCatSheaf.property L
      (invertibleSheaf' D')).symm ≪≫ e
  have hAeq := curveDegree_one_eq_curveChernDegree_of_eval_top_ne_zero k p hdim
    (invertibleSheaf' D) (canonicalSections D) (canonicalSections_eval_top_ne_zero D ‹_›)
  have hBeq := curveDegree_one_eq_curveChernDegree_of_eval_top_ne_zero k p hdim
    (invertibleSheaf' D') (canonicalSections D') (canonicalSections_eval_top_ne_zero D' ‹_›)
  have hdeg := curveDegree_one_tensorObj k p hdim L (invertibleSheaf' D')
  have hdegiso := curveDegree_eq_of_iso k p hdim (E := Scheme.Modules.tensorObj L
    (invertibleSheaf' D')) (E' := invertibleSheaf' D) 1 e'
  have hch := curveChernDegree_tensorObj k p hdim L (invertibleSheaf' D')
  have hchiso := curveChernDegree_congr k p hdim
    (Scheme.Modules.tensorObj L (invertibleSheaf' D')) (invertibleSheaf' D) e'
  linear_combination -hdeg + hdegiso + hAeq - hBeq - hch - hchiso

/-- **Riemann-Roch, equation [Stacks, Tag 0BRZ], for an invertible module on a proper integral
curve**:

`χ(X, ℒ) = deg(c₁(ℒ) ∩ [X]_1) + χ(X, 𝒪_X)`. -/
theorem eulerCharacteristic_eq_curveChernDegree_add_of_isCurve [IsCurve k p]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] [L.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    eulerCharacteristic k p L =
      curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 L) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible k p hdim L
    (curveDegree_one_eq_curveChernDegree_of_isCurve k p hdim L)

end

end AlgebraicGeometry

end
