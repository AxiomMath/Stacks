module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08HN: approximation by perfect complexes across an elementary distinguished square

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S` with `U` quasi-compact, `V` affine and `U ×_X V` quasi-compact.  **Stacks 08HN**: if
approximation by perfect complexes holds on `U`, it holds on `X`.

## The proof

Fix a closed `T ⊆ |X|` with quasi-compact open complement, let `r_U` be the integer of
Stacks 08HJ for `(U, T ∩ |U|)` and let `r'` be the integer of the base case on `V`
(`AlgebraicGeometry.Space.exists_approximation_edsEtale`).  For `r = r_U + r'` and a triple
`(T, E, m)` with `E` `(m - r)`-pseudo-coherent and supported on `T` from degree `m - r` on, the
approximation is obtained by induction on the largest `t` with `Hᵗ(E)|_U ≠ 0`
(`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_amplitudeInduction`):

* such a `t` exists, `U` being quasi-compact
  (`AlgebraicGeometry.Space.exists_cohomologySupportedOnFrom_compl_range`);
* **base case** `t ≤ m - r'`: `Hⁱ(E)` is supported on `T' = T ∖ |U|` from degree `m - r' + 1`
  on, so approximation holds on `V` for `(j^{-1}T', E|_V, m)` and Stacks 08HL descends it to
  `(T', E, m)`, which is an approximation of `(T, E, m)`;
* **step**: `AlgebraicGeometry.Space.exists_approximation_step`, a distinguished triangle
  `R ⟶ E ⟶ E' ⟶ R[1]` with `R` perfect and supported on `T` and `E'` of lower amplitude over
  `U`, together with the closing move of the source through Stacks 08G9.

The source takes `r = max(r_U, r')` and approximates `E|_U` at the degree `m` in the step; but
the step needs a surjection on `Hᵗ` with `t` possibly smaller than `m`, so the approximation is
taken at the degree `t`, which needs `E|_U` to be `(t - r_U)`-pseudo-coherent, hence the sum
`r = r_U + r'` (`t > m - r'`).  The integer `r` is existentially quantified in the conclusion, so
this changes nothing in the statement.

## Main results

* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isElementaryDistinguishedSquare`:
  **Stacks 08HN**.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
* [Stacks Project, Tag 08HL](https://stacks.math.columbia.edu/tag/08HL)
* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance] pointTopology etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- Stacks 08HN at an algebraic space given as an object of `AlgebraicSpaces`. -/
theorem approximationByPerfectComplexes_of_eds {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor W.1} {f : V ⟶ W.1}
    (hsq' : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVaff : IsAffineSpace B S hS V)
    (hUVqc : IsQuasiCompactSpace B S hS (U.preimage f).toFunctor)
    (hU : ApproximationByPerfectComplexes.{u, u} B S hS U.toFunctor hsq'.isOpenSubspace.1) :
    ApproximationByPerfectComplexes.{u, u} B S hS W.1 W.2 := by
  have hUVqc' : IsQuasiCompactSpace B S hS (edsInter B S hS hsq').1 :=
    isQuasiCompactSpace_of_iso B S hS ((Subfunctor.isPullback_preimage f U).isoPullback ≪≫
      (Iso.refl _ : pullback U.ι f ≅ (edsInter B S hS hsq').1)) hUVqc
  refine approximationByPerfectComplexes_of_amplitudeInduction B S hS W.1 W.2
    (edsComplementPoints B S hS U)
    ⟨fun T Tri hTri h₁ h₃ => cohomologySupportedOn_obj₂_of_distinguished B S hS W.1 W.2 T Tri hTri
      h₁ h₃, ?_⟩
  intro T hT hTqc
  have hTU : IsClosed (pointsMap B S hS U.toFunctor U.ι ⁻¹' T) :=
    hT.preimage (continuous_pointsMap B S hS _)
  have hTUqc := isQuasiCompact_openSubspacesOrderIso_symm_preimage B S hS W.2
    hsq'.isOpenSubspace.1 U.ι T hT hTqc hTU
  obtain ⟨rU, hrU⟩ := hU _ hTU hTUqc
  obtain ⟨rV, hrV⟩ := exists_approximation_edsEtale B S hS hsq' hVaff hUVqc' T hT hTqc
  have hlift := supportedLiftProperty_edsSnd B S hS hsq' hVaff hUVqc' T hT hTqc
  refine ⟨max rU 0 + (max rV 0 + 1), max rV 0 + 1, ?_, ?_, ?_⟩
  · -- the base case
    intro m E hin hamp
    have hT'U : T ∩ edsComplementPoints B S hS U ⊆ edsComplementPoints B S hS U :=
      Set.inter_subset_right
    have hsuppT' : ∀ i : ℤ, m - max rV 0 ≤ i →
        supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E.obj)) ⊆
        T ∩ edsComplementPoints B S hS U := fun i hi =>
      Set.subset_inter (hin.2 i (by omega)) (hamp i (by omega))
    have happrox := hrV ((quasicoherentDerivedEtalePullback B S hS (edsEtaleHom B S hS hsq')
        (isEtale_edsEtaleHom B S hS hsq')).obj E) m
      (isPseudoCoherentFrom_of_le B S hS _ _ (isPseudoCoherentFrom_etaleModulePullback B S hS
        (edsEtaleHom B S hS hsq') (isEtale_edsEtaleHom B S hS hsq') E.obj _ hin.1) (by omega))
      (fun i hi p hp => by
        have hp' := (supportOfSheaf_eq_of_iso B S hS (edsEtale B S hS hsq')
          (((edsRestrictEtale B S hS hsq').mapDerivedCategoryHomologyIso i).app E.obj)).le hp
        have hp'' := (Set.ext_iff.1 (supportOfSheaf_toSheaf_etaleModulePullback B S hS
          (edsEtaleHom B S hS hsq') (isEtale_edsEtaleHom B S hS hsq')
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E.obj)) p).1 hp'
        exact hsuppT' i (by omega) hp'')
    obtain ⟨P, hP, hPs, α, hαi, hαe⟩ := approximationHolds_of_approximationHolds_edsEtale B S hS
      hsq' (T ∩ edsComplementPoints B S hS U) hT'U E m happrox
      (fun i hi => hsuppT' i (by omega))
    exact ⟨P, hP, hPs.mono B S hS W.1 W.2 Set.inter_subset_left, α, hαi, hαe⟩
  · -- the step
    intro m t E ht hin hamp
    refine exists_approximation_step B S hS hsq' T hlift (max rU 0) (fun E' m' hpc hs => ?_)
      _ _ le_rfl m t E ht hin hamp
    exact hrU E' m' (isPseudoCoherentFrom_of_le B S hS _ _ hpc (by omega))
      (fun i hi => hs i (by omega))
  · -- the amplitude exists, `U` being quasi-compact
    intro m E hin
    exact exists_cohomologySupportedOnFrom_compl_range B S hS (edsOpenHom B S hS hsq')
      (isEtale_edsOpenHom B S hS hsq') hUqc E _ hin.1

/-- **Stacks 08HN.**  Let `S` be a scheme and let `(U ⊆ X, j : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`, with `U` quasi-compact, `V` affine and
`U ×_X V` quasi-compact.  If approximation by perfect complexes holds on `U`, then approximation
by perfect complexes holds on `X`. -/
@[stacks 08HN]
theorem approximationByPerfectComplexes_of_isElementaryDistinguishedSquare
    {X V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : Subfunctor X) (f : V ⟶ X)
    (hsq : IsElementaryDistinguishedSquare B S hS hX U f)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVaff : IsAffineSpace B S hS V)
    (hUVqc : IsQuasiCompactSpace B S hS (U.preimage f).toFunctor)
    (hU : ApproximationByPerfectComplexes.{u, u} B S hS U.toFunctor hsq.isOpenSubspace.1) :
    ApproximationByPerfectComplexes.{u, u} B S hS X hX :=
  approximationByPerfectComplexes_of_eds B S hS (W := ⟨X, hX⟩) hsq hUqc hVaff hUVqc hU

end AlgebraicGeometry.Space
