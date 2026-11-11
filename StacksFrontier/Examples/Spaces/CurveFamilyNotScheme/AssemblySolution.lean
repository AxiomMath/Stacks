module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyAlgebraization
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyStalkDimension
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyResidueField
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveAlgebraizationLocalRings
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalModification
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationOfScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies

/-!
# Artin's contraction of the strict transform of the central fibre

In the construction of [Stacks, Tag 0D5E], `Z` is the blowup of the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` at the chosen point of the central fibre, over
`S = A¹_k`, and `C ⊆ Z` is the strict transform of the central fibre. With
`A = lim Γ(Cₙ, 𝒪)` and the algebraization `f : Z~ ⟶ Spec A` of the formal neighbourhood of `C`
(`StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/AssemblyAlgebraization.lean`), the completion
of `f` along the closed point is a formal modification
`g : Z_{/C} ≅ Z~_{/f⁻¹(𝔪)} ⟶ (Spec A)_{/\{𝔪\}}` (Stacks 0GDM), which completes the data of
Situation 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation.ofScheme`): `X' = h_Z`, `T' = |C|`,
`W = (Spec A)_{/\{𝔪\}}`. Artin's theorem on contractions (Stacks 0GIB) then gives a solution
`(f : X' ⟶ X, T, a)`.

The big fppf site is chosen to contain `A¹_k`, `Z`, `Spec A` and `Spec ℤ`, so no cardinality
bound is needed.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.cubicSite`: the big fppf site.
* `Stacks.Examples.CurveFamilyNotScheme.cubicBlowupObject`: `Z` as an object of the site over
  `A¹_k`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicFormalModification`: `g`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicContraction`: the situation of Stacks 0GH8.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isFormalModification_cubicFormalModification`: `g` is a
  formal modification.
* `Stacks.Examples.CurveFamilyNotScheme.exists_solution_cubicContraction`: Stacks 0GIB for it.

## References

* [Stacks Project, Tag 0GDM](https://stacks.math.columbia.edu/tag/0GDM)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] Space.pointTopology

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-! ### The big fppf site -/

/-- A big fppf site containing `A¹_k`, `Z`, `Spec A` and `Spec ℤ`. -/
theorem exists_cubicSite :
    ∃ B : BigFppfSite.{u}, B.Contains (affineLine k) ∧ B.Contains (cubicBlowup k h3) ∧
      B.Contains (Spec (.of (cubicFormalRing k h3))) ∧ B.Contains integerBase := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({affineLine k, cubicBlowup k h3, Spec (.of (cubicFormalRing k h3)), integerBase} :
      Set Scheme.{u})
  exact ⟨B, hB _ (by simp), hB _ (by simp), hB _ (by simp), hB _ (by simp)⟩

/-- The big fppf site of the construction. -/
def cubicSite : BigFppfSite.{u} := (exists_cubicSite k h3).choose

/-- The site contains `A¹_k`. -/
theorem cubicSite_contains_affineLine : (cubicSite k h3).Contains (affineLine k) :=
  (exists_cubicSite k h3).choose_spec.1

/-- The site contains `Z`. -/
theorem cubicSite_contains_cubicBlowup : (cubicSite k h3).Contains (cubicBlowup k h3) :=
  (exists_cubicSite k h3).choose_spec.2.1

/-- The site contains `Spec A`. -/
theorem cubicSite_contains_spec_cubicFormalRing :
    (cubicSite k h3).Contains (Spec (.of (cubicFormalRing k h3))) :=
  (exists_cubicSite k h3).choose_spec.2.2.1

/-- The site contains `Spec ℤ`. -/
theorem cubicSite_contains_integerBase : (cubicSite k h3).Contains integerBase :=
  (exists_cubicSite k h3).choose_spec.2.2.2

/-- `Z`, as an object of the big fppf site over `A¹_k`. -/
abbrev cubicBlowupObject :
    BigFppfOver (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3) :=
  siteObject (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3)
    (cubicSite_contains_cubicBlowup k h3) (cubicToLine k h3)

/-! ### The formal modification -/

/-- `Spec A ⟶ A¹_k`, from `k[t] ⟶ Γ(Z, 𝒪) ⟶ A`. -/
abbrev cubicFormalRingToLine : Spec (.of (cubicFormalRing k h3)) ⟶ affineLine k :=
  formalNeighborhoodToSpec (strictTransformCentralFibre k h3) (cubicToLine k h3)

/-- The thickenings of `C` lie over `A¹_k` compatibly with `Spec A ⟶ A¹_k`. -/
theorem thickeningToSpec_cubicFormalRingToLine (n : ℕ) :
    thickeningToSpec (strictTransformCentralFibre k h3) n ≫ cubicFormalRingToLine k h3 =
      (strictTransformCentralFibre k h3 ^ (n + 1)).subschemeι ≫ cubicToLine k h3 :=
  thickeningToSpec_formalNeighborhoodToSpec _ _ n

/-- `Z` is regular. -/
theorem isRegular_cubicBlowup : IsRegular (cubicBlowup k h3) :=
  isRegular_pointBlowup _ _ (isRegular_cubicSurface k h3)
    (ringKrullDim_stalk_cubicSurface k h3 _ (isClosed_chosenPoint k h3))

/-- **The algebraization is integral of dimension at most two.** -/
theorem isIntegral_cubicAlgebraization_and_topologicalKrullDim_le_two :
    IsIntegral (cubicAlgebraization k h3) ∧ topologicalKrullDim (cubicAlgebraization k h3) ≤ 2 :=
  isIntegral_and_topologicalKrullDim_le_two (strictTransformCentralFibre k h3)
    monotone_cubicTowerIndex (cubicAlgebraizationHom k h3) (cubicAlgebraizationTower k h3)
    (adicTowerSucc_comp_cubicAlgebraizationTower k h3) (isPullback_cubicAlgebraizationTower k h3)
    le_cubicTowerIndex (bijective_appTop_cubicAlgebraizationHom k h3)
    (fun z _ => (isRegular_cubicBlowup k h3).isRegularLocalRing_stalk z)
    (fun z _ => ringKrullDim_stalk_cubicBlowup_le_two k h3 z)

/-- The algebraization is irreducible. -/
instance irreducibleSpace_cubicAlgebraization : IrreducibleSpace (cubicAlgebraization k h3) :=
  have := (isIntegral_cubicAlgebraization_and_topologicalKrullDim_le_two k h3).1
  inferInstance

/-- `A ⟶ Γ(Z~, 𝒪)` is an isomorphism. -/
instance isIso_appTop_cubicAlgebraizationHom : IsIso (cubicAlgebraizationHom k h3).appTop := by
  have h : IsIso ((Scheme.ΓSpecIso (.of (cubicFormalRing k h3))).inv ≫
      (cubicAlgebraizationHom k h3).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_appTop_cubicAlgebraizationHom k h3)
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of (cubicFormalRing k h3))).inv _

/-- **The formal contraction of `C`**: `g : Z_{/C} ≅ Z~_{/f⁻¹(𝔪)} ⟶ (Spec A)_{/\{𝔪\}}`. -/
def cubicFormalModification :=
  algebraizationCompletionMap (strictTransformCentralFibre k h3)
    (cubicSite_contains_cubicBlowup k h3) (cubicToLine k h3) monotone_cubicTowerIndex
    (hS := cubicSite_contains_affineLine k h3)
    (cubicSite_contains_spec_cubicFormalRing k h3) (cubicFormalRingToLine k h3)
    (thickeningToSpec_cubicFormalRingToLine k h3) (cubicAlgebraizationHom k h3)
    (isPullback_cubicAlgebraizationTower k h3) (maximalIdeal_cubicFormalRing_eq k h3).le
    le_cubicTowerIndex (adicTowerSucc_comp_cubicAlgebraizationTower k h3)

/-- **`g` is a formal modification** (Stacks 0GDK). -/
theorem isFormalModification_cubicFormalModification :
    FormalSpace.IsFormalModification _ _ _ (cubicFormalModification k h3) :=
  isFormalModification_algebraizationCompletionMap (strictTransformCentralFibre k h3)
    (cubicSite_contains_cubicBlowup k h3) (cubicToLine k h3) monotone_cubicTowerIndex
    (hS := cubicSite_contains_affineLine k h3)
    (cubicSite_contains_spec_cubicFormalRing k h3) (cubicFormalRingToLine k h3)
    (thickeningToSpec_cubicFormalRingToLine k h3) (cubicAlgebraizationHom k h3)
    (isPullback_cubicAlgebraizationTower k h3) (maximalIdeal_cubicFormalRing_eq k h3).le
    le_cubicTowerIndex (adicTowerSucc_comp_cubicAlgebraizationTower k h3)
    (ringKrullDim_cubicFormalRing k h3).ge
    (isIntegral_cubicAlgebraization_and_topologicalKrullDim_le_two k h3).2

/-! ### The contraction situation and Artin's theorem -/

/-- The closed point of `Spec A` is of finite type over `A¹_k`. -/
theorem locallyOfFiniteType_closedPoint_cubicFormalRingToLine :
    LocallyOfFiniteType
      ((Spec (.of (cubicFormalRing k h3))).fromSpecResidueField
          (IsLocalRing.closedPoint (cubicFormalRing k h3)) ≫ cubicFormalRingToLine k h3) := by
  have : CompactSpace (cubicBlowup k h3) :=
    QuasiCompact.compactSpace_of_compactSpace (cubicToLine k h3)
  obtain ⟨p, -, -, -⟩ := exists_point_conormal_iso k h3
  exact locallyOfFiniteType_fromSpecResidueField_comp_formalNeighborhoodToSpec _
    (maximalIdeal_cubicFormalRing_eq k h3).le
    ⟨_, subschemeι_mem_support (GenusOne.point p)⟩ (cubicToLine k h3)

/-- **The situation of Stacks 0GH8 for the contraction of `C`**: `X' = h_Z` over `S = A¹_k`,
`T' = |C|`, `W = (Spec A)_{/\{𝔪\}}` and the formal modification `g`. -/
def cubicContraction :
    Artin.ContractionSituation (cubicSite k h3) (affineLine k)
      (cubicSite_contains_affineLine k h3) :=
  Artin.ContractionSituation.ofScheme
    (Artin.ContractionSituation.isLocallyNoetherian_spec_of_finiteType k (Polynomial k))
    (cubicBlowupObject k h3) (inferInstanceAs (LocallyOfFiniteType (cubicToLine k h3)))
    ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3))
    (strictTransformCentralFibre k h3).support.isClosed
    (cubicSite_contains_spec_cubicFormalRing k h3) (cubicFormalRingToLine k h3)
    (locallyOfFiniteType_closedPoint_cubicFormalRingToLine k h3)
    (cubicFormalModification k h3) (isFormalModification_cubicFormalModification k h3)

/-- The algebraic space `X'` of the situation is `h_Z`. -/
@[simp]
theorem cubicContraction_X' : (cubicContraction k h3).X' = yoneda.obj (cubicBlowupObject k h3) :=
  rfl

/-- The closed subset `T'` of the situation is `|C|`. -/
@[simp]
theorem cubicContraction_T' :
    (cubicContraction k h3).T' =
      Space.pointsToScheme _ _ _ (cubicBlowupObject k h3) ⁻¹'
        ((strictTransformCentralFibre k h3).support : Set (cubicBlowup k h3)) :=
  rfl

/-- **Artin's contraction of `C`** (Stacks 0GIB in the construction of Stacks 0D5E): there is an
algebraic space `X` over `A¹_k` with a solution `(f : h_Z ⟶ X, T, a)` of the contraction problem
for `C ⊆ Z`, whose open subspace `U ≅ Z ∖ C` has point set `|X| ∖ T`. -/
theorem exists_solution_cubicContraction :
    ∃ (X : (BigFppfOver (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3))ᵒᵖ ⥤
        Type u) (s : Artin.ContractionSituation.Solution (cubicContraction k h3) X),
      Set.range (Space.pointsMap _ _ _ s.U.toFunctor s.U.ι) = s.Tᶜ :=
  Artin.ContractionSituation.exists_solution_ofScheme_spec k (cubicBlowupObject k h3)
    (inferInstanceAs (LocallyOfFiniteType (cubicToLine k h3)))
    (inferInstanceAs (AlgebraicGeometry.IsSeparated (cubicToLine k h3))) _
    (strictTransformCentralFibre k h3).support.isClosed _ _
    (locallyOfFiniteType_closedPoint_cubicFormalRingToLine k h3) _
    (isFormalModification_cubicFormalModification k h3)

end Stacks.Examples.CurveFamilyNotScheme

end
