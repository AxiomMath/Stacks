module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTaylorSum
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsTaylor
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFunctor07JG
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorFirstOrder
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCoordinates

/-!
# The Taylor expansion of the cosimplicial module of a crystal over the whole space

For a crystal `ℱ` in quasi-coherent modules, the proof of [Stacks, Lemma 60.17.3, Tag 07JG]
expands the restriction along the second projection `p₁ : T(1)_e → T_e` of a section over `T_e`
as a finite sum `p₁^* m = ∑_K ξ^{[K]} · p₀^* θ_K(m)` (`...SmallSite.crysRestrict_δ_zero_eq_sum`).
This module assembles that levelwise expansion into the form the cosimplicial module
`M(•) = ...SmallSite.wholeSpaceCosimplicialModule` of [Stacks, Proposition 60.21.3, Tag 07LG] is
compared with: modulo `pⁿ M(1)` the transition `M(0) → M(1)` along `δ = (0 ↦ 1)` is the finite
sum `∑_K ξ^{[K]} · σ(θ_K m)`, over any finite set of multi-indices containing those `K` with
`θ_K m ∉ p^k M(0)`, for `k` large.

## Main results

* `...SmallSite.coordinateDifference_wsCoordinate_mem` — the coordinate differences
  `ξ_c = x_c(0) - x_c(1)` lie in the divided power ideal of `E(1)`, and
  `...SmallSite.taylorCoefficient_wsCoordinate` identifies their completed divided power monomials
  with `Crystalline.envelopeTaylorMonomial`.
* `...SmallSite.finite_crystalTheta_notMem_pPowSmul` — only finitely many `θ_K m` lie outside
  `pⁿ M(0)`.
* `...SmallSite.wholeSpace_taylorExpansion` — the Taylor expansion of `M(0) → M(1)` modulo `pⁿ`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The coordinate difference `ξ_c = σ(x_c) - δ(x_c)` of the whole space is the image of
`x_c(0) - x_c(1)` in `E(1)`. -/
theorem coordinateDifference_wsCoordinate (c : wholeSpaceIndex S hp) :
    CosimplicialCompletedModule.coordinateDifference (E := wholeSpaceDPAlgebra hp)
        (wsCoordinate hp) c =
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 1).algebraMap.toRingHom
        (coprojectionDifference (affineSituation S hp) 1 (c, 0)) := by
  have h0 : (wholeSpaceDPAlgebra hp).map (CosimplicialDPAlgebra.coprojection 1)
      (wsCoordinate hp c) =
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 1).algebraMap.toRingHom
        (MvPolynomial.X ((0 : Fin 2), c)) :=
    (envelopeReindex_polynomial (affineSituation S hp) _ _ _).trans
      (congrArg _ (MvPolynomial.rename_X _ _))
  have h1 : (wholeSpaceDPAlgebra hp).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
      (wsCoordinate hp c) =
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 1).algebraMap.toRingHom
        (MvPolynomial.X ((1 : Fin 2), c)) :=
    (envelopeReindex_polynomial (affineSituation S hp) _ _ _).trans
      (congrArg _ (MvPolynomial.rename_X _ _))
  rw [CosimplicialCompletedModule.coordinateDifference, h0, h1]
  exact (map_sub _ _ _).symm

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The coordinate differences `ξ_c` lie in the divided power ideal of `E(1)`**: `x_c(0) -
x_c(1)` lies in the kernel `J(1)` of `P ⊗ P → C`. -/
theorem coordinateDifference_wsCoordinate_mem (c : wholeSpaceIndex S hp) :
    CosimplicialCompletedModule.coordinateDifference (E := wholeSpaceDPAlgebra hp)
        (wsCoordinate hp) c ∈ (wholeSpaceDPAlgebra hp).ideal 1 := by
  rw [coordinateDifference_wsCoordinate]
  refine (tensorPowerEnvelope (affineSituation S hp)
    (wholeSpacePresentation S hp) 1).algebraMap.ideal_comp
      (Ideal.mem_map_of_mem _ ?_)
  rw [RingHom.mem_ker]
  change (tensorPowerPresentation (affineSituation S hp)
    (wholeSpacePresentation S hp) 1) (coprojectionDifference _ 1 (c, 0)) = 0
  simp only [tensorPowerPresentation, coprojectionDifference, AlgHom.comp_apply, map_sub,
    MvPolynomial.rename_X, sub_self]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The divided power monomials of the coordinate differences of the whole space are the
monomials `ξ^{[K]}` of `Crystalline.envelopeTaylorMonomial`. -/
theorem taylorMonomial_coordinateDifference_wsCoordinate
    (K : wholeSpaceIndex S hp →₀ ℕ) :
    taylorMonomial (CosimplicialCompletedModule.degreeOneDPRing (E := wholeSpaceDPAlgebra hp))
        (CosimplicialCompletedModule.coordinateDifference (wsCoordinate hp)) K =
      envelopeTaylorMonomial (affineSituation S hp)
        (wholeSpacePresentation S hp) K := by
  rw [envelopeTaylorMonomial_eq_prod_dpow, taylorMonomial, Finsupp.prod]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [coordinateDifference_wsCoordinate]
  rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The completed divided power monomials of the coordinate differences of the whole space**
are the completions of `Crystalline.envelopeTaylorMonomial`. -/
theorem taylorCoefficient_wsCoordinate (K : wholeSpaceIndex S hp →₀ ℕ) :
    CosimplicialCompletedModule.taylorCoefficient (p := S.p) (E := wholeSpaceDPAlgebra hp)
        (wsCoordinate hp) K =
      wsCompletionMap hp 1 (envelopeTaylorMonomial (affineSituation S hp)
        (wholeSpacePresentation S hp) K) := by
  rw [CosimplicialCompletedModule.taylorCoefficient,
    taylorMonomial_coordinateDifference_wsCoordinate]
  rfl

variable (Fc : QuasiCoherentCrystal S)

/-- **Only finitely many `θ_K m` lie outside `pⁿ M(0)`**: one outside `pⁿ M(0)` is nonzero at the
level `n`, and the Taylor expansion at a level is a finite sum. -/
theorem finite_crystalTheta_notMem_pPowSmul (m : (wholeSpaceCosimplicialModule hp Fc).carrier 0)
    (n : ℕ) :
    {K | crystalTheta hp Fc K m ∉ pPowSmul S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
      ((wholeSpaceCosimplicialModule hp Fc).carrier 0) n}.Finite := by
  refine (finite_crystalTheta_ne_zero hp Fc m n).subset fun K hK h0 ↦ hK ?_
  have hmem := (mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero hp Fc
    (isSurjectiveComparison_of_isSheafCrystal Fc.property.2) 0 n _).mpr h0
  exact pPowSmul_mono S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
    ((wholeSpaceCosimplicialModule hp Fc).carrier 0) (Nat.le_add_left n _) hmem

/-- **The Taylor expansion of `M(0) → M(1)` modulo `pⁿ`**: for `k = N + n`, if a finite set `T`
of multi-indices contains every `K` with `θ_K m ∉ p^k M(0)`, then
`δ(m) - ∑_{K ∈ T} ξ^{[K]} · σ(θ_K m) ∈ pⁿ M(1)`.  At the level `n` the left hand side is the
levelwise Taylor expansion `...SmallSite.crysRestrict_δ_zero_eq_sum`, whose coefficients outside
`T` vanish. -/
theorem wholeSpace_taylorExpansion (n : ℕ) : ∃ k : ℕ,
    ∀ (m : (wholeSpaceCosimplicialModule hp Fc).carrier 0)
      (T : Finset ((wholeSpaceIndex S hp) →₀ ℕ)),
      (∀ K, crystalTheta hp Fc K m ∉ pPowSmul S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
          ((wholeSpaceCosimplicialModule hp Fc).carrier 0) k → K ∈ T) →
      (wholeSpaceCosimplicialModule hp Fc).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m -
          ∑ K ∈ T, CosimplicialCompletedModule.taylorCoefficient (p := S.p) (wsCoordinate hp) K •
            (wholeSpaceCosimplicialModule hp Fc).map (CosimplicialDPAlgebra.coprojection 1)
              (crystalTheta hp Fc K m) ∈
        pPowSmul S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 1)
          ((wholeSpaceCosimplicialModule hp Fc).carrier 1) n := by
  classical
  refine ⟨_root_.Crystalline.uniformLevel (affineSituation S hp) + n, fun m T hT ↦ ?_⟩
  have hsurj : CohomologyRestriction.IsSurjectiveComparison
      (Fc.obj.val : PresheafOfModules.{u} (crisRing S)) :=
    isSurjectiveComparison_of_isSheafCrystal Fc.property.2
  refine pPowSmul_mono S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 1)
    ((wholeSpaceCosimplicialModule hp Fc).carrier 1)
    (Nat.le_add_left n (_root_.Crystalline.uniformLevel (affineSituation S hp))) ?_
  refine (mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero hp Fc hsurj 1 n _).mpr ?_
  -- the coefficients of the levelwise expansion outside `T` vanish
  have hvan : ∀ K ∉ T, wholeSpaceSectionsVal hp Fc (crystalTheta hp Fc K m) n = 0 := by
    intro K hK
    by_contra hne
    exact hK (hT K fun hmem ↦ hne
      ((mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero hp Fc hsurj 0 n _).mp hmem))
  have hδ0 : SimplexCategory.δ (n := 0) 0 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 := by
    ext i; fin_cases i; rfl
  have hδ1 : SimplexCategory.δ (n := 0) 1 = CosimplicialDPAlgebra.coprojection 1 := by
    ext i; fin_cases i; rfl
  have hexp := crysRestrict_δ_zero_eq_sum hp Fc n (wholeSpaceSectionsVal hp Fc m n)
  rw [hδ0, hδ1] at hexp
  have hsub : ∀ x y : wholeSpaceSections hp Fc ⦋1⦌,
      wholeSpaceSectionsVal hp Fc (x - y) n =
        wholeSpaceSectionsVal hp Fc x n - wholeSpaceSectionsVal hp Fc y n :=
    fun x y ↦ map_sub (wholeSpaceSectionsValHom hp Fc ⦋1⦌ n) x y
  refine (hsub _ _).trans (sub_eq_zero.mpr (hexp.trans ?_))
  refine Eq.symm ((map_sum (wholeSpaceSectionsValHom hp Fc ⦋1⦌ n) _ T).trans ?_)
  rw [Finsupp.sum]
  refine (Finset.sum_congr rfl fun K _ ↦ ?_).trans
    (Finset.sum_subset (fun K hK ↦ ?_) (fun K _ hK ↦ ?_)).symm
  · refine (wholeSpaceSectionsVal_smul hp Fc _ _ n).trans ?_
    have hc : levelSectionsScalars hp ⦋1⦌ n
        (CosimplicialCompletedModule.taylorCoefficient (p := S.p) (wsCoordinate hp) K) =
        levelTaylorMonomial hp n K := by
      rw [taylorCoefficient_wsCoordinate]
      rfl
    exact congrArg (· • _) hc
  · by_contra hKT
    exact (Finsupp.mem_support_iff.mp hK) (hvan K hKT)
  · have h0 : (levelTaylorExpansion hp Fc n).coeffs (wholeSpaceSectionsVal hp Fc m n) K = 0 :=
      Finsupp.notMem_support_iff.mp hK
    rw [h0, map_zero, smul_zero]

end Crystalline.GlobalCrystallineSituation.SmallSite

end
