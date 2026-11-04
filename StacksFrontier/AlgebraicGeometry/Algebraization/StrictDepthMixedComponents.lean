module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedPrimeOverSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthGeneralization
public import StacksFrontier.AlgebraicGeometry.Algebraization.MixedComponentsClosureBridge
public import StacksFrontier.AlgebraicGeometry.Algebraization.StrictDepthInequalitiesDepthOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSerreOneAlternativeProof

/-!
# Depth one at a point whose closed fibre has components on both sides of `Z`

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`. Let `A` be `I`-adically complete with a dualizing
complex and `cd(A, I) ≤ d`, and let `ℱ` be a coherent `𝒪_U`-module whose completion along
`I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of [Stacks, Tag 0EJ3]. Let `x ∈ U` be a
point whose closure `W = \overline{\{x\}}` meets the closed fibre in components lying on both
sides of `Z`. Then `depth(ℱ_x) ≥ 1`.

This is [Stacks, Tag 0EJ5], and this file is its assembly from the four inputs below.

## Main results

* `Stacks.Algebraization.one_le_depth_stalk_of_mixed_irreducibleComponents` — the positive-depth
  bound, **Stacks Tag 0EJ5**.

## Implementation notes

### The four inputs

* `Stacks.Algebraization.exists_distanceToZ_eq_one_specializes_of_mixed_irreducibleComponents`
  is the geometric half: the mixed components give a crossing point `z` of low local dimension
  by [Stacks, Tag 0EG5], and an immediate generalization `r` of it inside the closed fibre but
  outside `Z` by [Stacks, Tag 02IM]. It returns the point `y ∈ U` below `x` that `r` determines,
  the equality `δ^Y_Z(r) = 1`, and the height bound `height(𝔭_y(A/𝔭_x)) ≤ d`.
* `Stacks.Algebraization.exists_primeSpectrum_completedLocalRing_of_specializes` turns that
  height bound into a prime `𝔭` of `𝒪_{U,y}^∧` over the prime of `x`, minimal over its
  extension, not containing `I𝒪_{U,y}^∧`, with `dim(𝒪_{U,y}^∧/𝔭) ≤ d` — the dimension
  splitting of [Stacks, Tag 0EHW].
* `Stacks.Algebraization.one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities` reads
  `depth((ℱ_y^∧)_𝔭) ≥ 1` off the strict inequalities at that point and that prime.
* `Stacks.Algebraization.one_le_depth_stalk_of_one_le_completedStalkDepth` transports that bound
  to `depth(ℱ_x)`, by [Stacks, Tag 0338] and [Stacks, Tag 0EHW].

Only `Stacks.Algebraization.not_le_asIdeal_of_mixed_irreducibleComponents` is proved here: the
mixed components rule out `I ⊆ 𝔭_x`, which is what makes `I𝒪_{U,y}^∧` miss the prime of `x`.

### The comparison of Stacks 0EIF

`Stacks.Algebraization.exists_distanceToZ_eq_one_specializes_of_mixed_irreducibleComponents`
takes [Stacks, Tag 0EG5] in the form proved relative to the comparison of [Stacks, Tag 0EIF];
that comparison is `Stacks.Algebraization.serreOneAlternativeComparison`, proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/FormalSectionsSerreOneAlternativeProof.lean`, and
it is supplied here, so nothing beyond the hypotheses of [Stacks, Tag 0EJ5] is assumed.

### Points of `X` outside `U`

The source lets `x` range over `X`, but `ℱ_x` is only defined for `x ∈ U`. For `x ∈ Z` the
closure `W` lies in `Z`, so every irreducible component of `W ∩ Y` is contained in `Z` and the
hypothesis fails; so the statement over the points of `U` is the source's statement.

## References

* [Stacks Project, Tag 0EJ5](https://stacks.math.columbia.edu/tag/0EJ5)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3)
* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5)
* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
* [Stacks Project, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **Mixed components on the closed fibre force `I ⊄ 𝔭_x`.** If `I ⊆ 𝔭_x` then the point of
`X = Spec(A)` corresponding to `x` lies on `Y = V(I)`, so the closed fibre
`Y_ι^{-1}(\overline{\{x\}})` is the closure of a single point of `Y`, hence irreducible: it has
exactly one irreducible component, and that component cannot be both inside and outside `Z`. -/
public theorem not_le_asIdeal_of_mixed_irreducibleComponents (S : AlgebraizationSituation.{u})
    (x : S.U.toScheme)
    (hmixed :
      let W : Set S.Y := S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)
      let Z : Set W := {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}
      (∃ C : Set W, C ∈ irreducibleComponents W ∧ C ⊆ Z) ∧
        (∃ C : Set W, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Z)) :
    ¬ S.I ≤ (S.U.ι.base x).asIdeal := by
  dsimp only at hmixed
  intro hIp
  have hrange : Set.range S.Yι.base = PrimeSpectrum.zeroLocus (S.I : Set S.A) := by
    show Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk S.I)) = _
    rw [range_comap_of_surjective (S.A ⧸ S.I) (Ideal.Quotient.mk S.I)
      Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker]
  obtain ⟨w, hw⟩ : S.U.ι.base x ∈ Set.range S.Yι.base := by
    rw [hrange]
    exact hIp
  have hWeq : S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X) = closure ({w} : Set S.Y) := by
    ext y
    rw [Set.mem_preimage, ← specializes_iff_mem_closure, ← specializes_iff_mem_closure, ← hw]
    exact S.Yι.isClosedEmbedding.isEmbedding.specializes_iff
  have : IrreducibleSpace ↥(S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)) :=
    Subtype.irreducibleSpace (hWeq ▸ isIrreducible_singleton.closure)
  obtain ⟨⟨inside, hinside, hinsideZ⟩, outside, houtside, houtsideZ⟩ := hmixed
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hinside houtside
  exact houtsideZ (houtside ▸ hinside ▸ hinsideZ)

/-- **Stacks Project, Tag 0EJ5.** Let `A` be a Noetherian ring with ideals `I ⊆ 𝔞`, write
`X = Spec(A)`, `Y = V(I)`, `Z = V(𝔞)`, `U = X ∖ Z`, and suppose `A` is `I`-adically complete,
has a dualizing complex, and has `cd(A, I) ≤ d` with `d ≥ 1`. Let `ℱ` be a coherent
`𝒪_U`-module whose completion along `I𝒪_U` satisfies the strict `(1, 1 + d)`-inequalities of
[Stacks, Tag 0EJ3]. Let `x ∈ U` be a point such that the closed fibre
`\overline{\{x\}} ∩ Y` has an irreducible component contained in `Z` and an irreducible
component not contained in `Z`. Then

  `depth_{𝒪_{U,x}}(ℱ_x) ≥ 1`.

The source states this for `x ∈ X`; a point of `Z` never satisfies the hypothesis, its closure
lying in `Z`, and `ℱ_x` is defined only on `U`, so `x` ranges over `U`.

The components on both sides disconnect the closed fibre once their intersection is removed, so
[Stacks, Tag 0EG5] produces a point `z` of the closed fibre inside `Z` with
`dim(𝒪_{\overline{\{x\}}, z}) ≤ d + 1`; [Stacks, Tag 02IM] produces an immediate generalization
`r` of `z` still in the closed fibre but outside `Z`, whose distance to `Z` is therefore exactly
`1` and whose local dimension is at most `d`. At the point `y ∈ U` that `r` determines the
strict inequalities, evaluated at a prime of `𝒪_{U,y}^∧` minimal over the extension of the prime
of `x`, force `depth((ℱ_y^∧)_𝔭) ≥ 1`; and that depth is `depth(ℱ_x)`, by [Stacks, Tag 0338] and
[Stacks, Tag 0EHW]. -/
@[stacks 0EJ5]
public theorem one_le_depth_stalk_of_mixed_irreducibleComponents
    (S : AlgebraizationSituation.{u}) [IsAdicComplete S.I S.A]
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (d : ℤ) (hd : 1 ≤ d)
    (K : DerivedCategory (ModuleCat.{u} S.A)) (hK : Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      S.I.fg_of_isNoetherianRing ≤ d)
    (hstrict : SatisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) 1 (1 + d))
    (x : S.U.toScheme)
    (hmixed :
      let W : Set S.Y := S.Yι.base ⁻¹' closure ({S.U.ι.base x} : Set S.X)
      let Z : Set W := {y | S.Yι.base y.1 ∈ Set.range S.Zι.base}
      (∃ C : Set W, C ∈ irreducibleComponents W ∧ C ⊆ Z) ∧
        (∃ C : Set W, C ∈ irreducibleComponents W ∧ ¬ C ⊆ Z)) :
    1 ≤ Module.depth (S.U.toScheme.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (S.U.toScheme.presheaf.stalk x))
      ((stalkModuleFunctor x).obj F.obj) := by
  dsimp only at hmixed
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  obtain ⟨y, r, hyr, hdist, hxy, hheight⟩ :=
    exists_distanceToZ_eq_one_specializes_of_mixed_irreducibleComponents S K hK d hcd x
      hmixed
  let _ : Algebra (S.U.toScheme.presheaf.stalk y) (S.U.toScheme.presheaf.stalk x) :=
    (S.U.toScheme.presheaf.stalkSpecializes hxy).hom.toAlgebra
  obtain ⟨P, hover, hmin, hJnot, hdimP⟩ :=
    exists_primeSpectrum_completedLocalRing_of_specializes S x y hxy r hyr
      (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK)
      (not_le_asIdeal_of_mixed_irreducibleComponents S x hmixed) d (by omega) hheight
  have := hover
  exact one_le_depth_stalk_of_one_le_completedStalkDepth (idealOnOpen S) F hxy P hmin
    (one_le_completedStalkDepth_of_satisfiesStrictDepthInequalities S
      ((completionFunctor S.U.toScheme (idealOnOpen S)).obj F) d hstrict y r hyr hdist P hJnot
      hdimP)

end Stacks.Algebraization

end
