module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyNotScheme
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyFibreDimension
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.AssemblyFormalRingTorsion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase

/-!
# The contraction of the strict transform of the central fibre is a family of curves

In the construction of [Stacks, Tag 0D5E], `Z` is the blowup of the cubic surface
`Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` over `S = A¹_k` at the chosen point of the central
fibre, `C ⊆ Z` is the strict transform of the central fibre, and Artin's contraction (Stacks 0GIB)
contracts `C` to a point of an algebraic space `X` over `A¹_k`. This file shows that `X ⟶ A¹_k`,
read over `Spec ℤ`, is a family of curves in the sense of Stacks 0D4Z whose total space is not a
scheme.

The inputs of
`AlgebraicGeometry.Artin.ContractionSituation.Solution.exists_curveFamily_of_solution_of_affineOver`
are proved here for the concrete data: `Z` is flat over `A¹_k` (an integral scheme dominating
the spectrum of a Dedekind domain, by
`Stacks.Examples.CurveFamilyNotScheme.isDominant_cubicToLine`), its fibres have dimension at most
one (`StacksFrontier/Examples/Spaces/CurveFamilyNotScheme/AssemblyFibreDimension.lean`), the residue
field of `A = lim Γ(Cₙ, 𝒪)` is `Γ(C, 𝒪_C) = k`, hence algebraically closed, and `A` is
torsion-free over `k[t]` (`…/AssemblyFormalRingTorsion.lean`). The contraction is taken with a
limit preserving target
(`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_limitPreserving_of_isSeparated`).
Non-representability is
`Stacks.Examples.CurveFamilyNotScheme.not_exists_iso_yoneda_solution_cubicContraction`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.flat_cubicToLine`: `Z` is flat over `A¹_k`.
* `Stacks.Examples.CurveFamilyNotScheme.isAlgClosed_residueField_cubicFormalRing`: the residue
  field of `A` is algebraically closed.
* `Stacks.Examples.CurveFamilyNotScheme.exists_solution_limitPreserving_cubicContraction`:
  Artin's contraction of `C` with a limit preserving target.
* `Stacks.Examples.CurveFamilyNotScheme.exists_curveFamily_cubicContraction`: the family of
  curves over `A¹_k` whose total space is not a scheme.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] Space.pointTopology

variable (k : Type u) [Field k] [IsAlgClosed k] [Uncountable k] (h3 : ringChar k ≠ 3)

/-! ### Flatness of `Z` over `A¹_k` -/

/-- **`Z` is flat over `A¹_k`**: an integral scheme whose generic point maps to the generic point
of the spectrum of the Dedekind domain `k[t]`. -/
instance flat_cubicToLine : Flat (cubicToLine k h3) :=
  flat_of_genericPoint_map_eq (A := Polynomial k) (cubicToLine k h3)
    (((tfae_isDominant_of_isIntegral (cubicToLine k h3)).out 1 2).mp
      (inferInstance : IsDominant (cubicToLine k h3)))

/-! ### The residue field of `A` -/

/-- **The residue field of `A = lim Γ(Cₙ, 𝒪)` is algebraically closed**: it is
`A / F₁ ≅ Γ(C, 𝒪_C) = k`. -/
instance isAlgClosed_residueField_cubicFormalRing :
    IsAlgClosed (IsLocalRing.ResidueField (cubicFormalRing k h3)) := by
  obtain ⟨p, hp, _, ⟨ψ⟩⟩ := exists_point_conormal_iso k h3
  have h0 := finrank_structureSheafCohomology_zero_strictTransformCentralFibre k h3
  have hg := genus_strictTransformCentralFibre k h3
  have hsurj := surjective_thickeningRestriction_of_isZero (strictTransformCentralFibre k h3)
    (isZero_H1_conormalPow_of_genusOne h0 hg p hp
      (fun n => (nonempty_pullback_negativeTwist_pow_iso _ _ ψ n).some))
  let e : IsLocalRing.ResidueField (cubicFormalRing k h3) ≃+* k :=
    ((Ideal.quotEquivOfEq (maximalIdeal_cubicFormalRing_eq k h3)).trans
      (residueRingEquiv (strictTransformCentralFibre k h3)
        (surjective_formalNeighborhoodProjection _ hsurj 0))).trans
      (RingEquiv.ofBijective _ (GenusOne.bijective_globalSectionsHom _ h0)).symm
  exact IsAlgClosed.of_ringEquiv k _ e.symm

/-! ### Artin's contraction with a limit preserving target -/

/-- **Artin's contraction of `C`, with a limit preserving target** (Stacks 0GIB): there is an
algebraic space `X` over `A¹_k`, limit preserving, with a solution `(f : h_Z ⟶ X, T, a)` of the
contraction problem for `C ⊆ Z` whose open subspace `U ≅ Z ∖ C` has point set `|X| ∖ T`. -/
theorem exists_solution_limitPreserving_cubicContraction :
    ∃ (X : (BigFppfOver (cubicSite k h3) (affineLine k) (cubicSite_contains_affineLine k h3))ᵒᵖ ⥤
        Type u) (s : Artin.ContractionSituation.Solution (cubicContraction k h3) X),
      Set.range (Space.pointsMap _ _ _ s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u}
          (BigFppfOver.toScheme (cubicSite k h3) (affineLine k)
            (cubicSite_contains_affineLine k h3)) X :=
  Artin.ContractionSituation.exists_solution_limitPreserving_of_isSeparated _
    (isGRing_stalk_of_isFiniteTypePoint_spec k (Polynomial k))
    (Space.isSeparated_terminal_from_yoneda (cubicBlowupObject k h3)
      (inferInstanceAs (AlgebraicGeometry.IsSeparated (cubicToLine k h3))))
    (FormalSpace.isSeparatedMorphism_terminal_from_completionAtClosedPoint _ _)

/-! ### The family of curves -/

/-- `Γ(A¹_k, 𝒪) ≅ k[t]` is a principal ideal ring. -/
instance isPrincipalIdealRing_sections_affineLine : IsPrincipalIdealRing Γ(affineLine k, ⊤) :=
  IsPrincipalIdealRing.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).commRingCatIsoToRingEquiv.symm.surjective

/-- `Γ(A¹_k, 𝒪) ≅ k[t]` is a Dedekind domain. -/
instance isDedekindDomain_sections_affineLine : IsDedekindDomain Γ(affineLine k, ⊤) :=
  inferInstance

/-- The curve `C` being contracted is nonempty: it has a `k`-point. -/
theorem cubicContraction_T'_nonempty : (cubicContraction k h3).T'.Nonempty := by
  obtain ⟨p, -, -, -⟩ := exists_point_conormal_iso k h3
  exact ⟨(cubicPointsEquiv (h3 := h3)).symm _,
    (symm_cubicPointsEquiv_mem_T'_iff _).mpr (subschemeι_mem_support (GenusOne.point p))⟩

/-- **The contraction of `C` is a family of curves whose total space is not a scheme**
(Stacks 0D5E). There is a family of curves `F` (Stacks 0D4Z) in the big fppf site of the
construction, with base `A¹_k` over `Spec ℤ`, whose total space is not isomorphic to the
algebraic space of any scheme of the site: `F` is Artin's contraction `X` of the strict transform
`C` of the central fibre in the blowup `Z` of the cubic surface `Y` at the chosen point, read over
`Spec ℤ`. -/
theorem exists_curveFamily_cubicContraction :
    ∃ F : CurveFamily (cubicSite k h3) (cubicSite_contains_integerBase k h3),
      F.base = Over.mk (integerBaseMap (cubicSite k h3) (cubicSite_contains_affineLine k h3)
        (cubicSite_contains_integerBase k h3)) ∧
      ¬ ∃ V : BigFppfOver (cubicSite k h3) integerBase (cubicSite_contains_integerBase k h3),
        Nonempty (F.total ≅ schemeSpace V) := by
  obtain ⟨X, s, hU, hl⟩ := exists_solution_limitPreserving_cubicContraction k h3
  have hT' := cubicContraction_T'_nonempty k h3
  have hW := FormalSpace.isSeparatedMorphism_terminal_from_completionAtClosedPoint
    (hS := cubicSite_contains_affineLine k h3) (cubicSite_contains_spec_cubicFormalRing k h3)
    (cubicFormalRingToLine k h3)
  have hWpt : FormalSpace.HasAtMostOnePoint (cubicContraction k h3).W :=
    FormalSpace.hasAtMostOnePoint_completionSheaf_of_subsingleton
      (BigFppfOver.isSheaf_yoneda_obj _ _ _ _)
      (Set.subsingleton_singleton.preimage (Space.pointsEquivScheme _ _ _ _).injective)
  have hX'p : Space.IsProper _ _ _ (terminal.from (cubicContraction k h3).X') :=
    Space.isProper_terminal_from_yoneda _ _ _ (cubicBlowupObject k h3)
      (inferInstanceAs (IsProper (cubicToLine k h3)))
  have hft := s.isLocallyOfFiniteType_terminal_from_of_limitPreserving hl
  obtain ⟨F, hb, -, -, himp⟩ := s.exists_curveFamily_of_solution_of_affineOver
    (cubicSite_contains_integerBase k h3) hU hl (Iso.refl _)
    (inferInstanceAs (IsProper (cubicToLine k h3)))
    (inferInstanceAs (Flat (cubicToLine k h3)))
    (topologicalKrullDimAt_fiber_cubicToLine_le_one k h3) hT' hW
    (isAdicComplete_cubicFormalRing k h3) (cubicSite_contains_spec_cubicFormalRing k h3)
    (cubicFormalRingToLine k h3) (isSMulRegular_cubicFormalRingToLine k h3) (Iso.refl _)
  refine ⟨F, hb, fun hV => ?_⟩
  obtain ⟨x, hx, -⟩ := s.exists_T_eq_singleton hWpt hT'
  exact not_exists_iso_yoneda_solution_cubicContraction s
    (s.isProper_of_hasAtMostOnePoint hU hX'p hW hWpt hT' hft)
    (s.surjective_pointsMap_f hWpt hT' hU) ⟨x, hx⟩ (himp hV)

end Stacks.Examples.CurveFamilyNotScheme

end
