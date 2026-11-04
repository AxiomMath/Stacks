module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AlgebraizationBlowupFibres
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AlgebraizationIdealChange
public import StacksFrontier.AlgebraicGeometry.Blowup.FewGeneratorsFibreDimension
public import StacksFrontier.RingTheory.Dualizing.IsDualizingComplexModels
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence

/-!
# Algebraization for ideals with few generators

[Stacks, Tag 0EJN]. In Situation 0EHC let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Assume

1. `A` has a dualizing complex,
2. `V(I) = V(f₁, …, f_d)` for some `d ≥ 1` and `f₁, …, f_d ∈ A`,
3. either `(ℱₙ)` satisfies the `(d + 1, d + 2)`-inequalities of [Stacks, Tag 0EJ3], or
   `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > d + 2` for every `y ∈ U ∩ Y` and every prime
   `𝔭 ⊆ 𝒪_{X,y}^∧` with `𝔭 ∉ V(I𝒪_{X,y}^∧)`.

Then `(ℱₙ)` extends to `X`; in particular, if `A` is `I`-adically complete, `(ℱₙ)` is the
completion of a coherent `𝒪_U`-module.

## Proof

The source's. Replace `I` by `J = (f₁^{N+1}, …, f_d^{N+1}) ⊆ I`, which has the same radical
([Stacks, Tag 0EHR]; `Stacks.Algebraization.extendsToX_of_withIdeal` and the transport lemmas of
`AlgebraizationIdealChange.lean`). The blowup of `Spec A` in an ideal with `d` generators has
fibres of dimension `≤ d - 1`
(`Stacks.Blowup.topologicalKrullDim_fiber_algebraicGeometry_blowUpToBase_lt_of_eq_span`), so
[Stacks, Tag 0EJK] (`Stacks.Algebraization.extendsToX_of_blowUp_fiber_dim_lt`) applies. The final
statement is [Stacks, Tag 0EIL].

The dualizing complex is taken in any model of `D(A)`; it is moved to the standard model, in which
0EJK is stated, by `Dualizing.exists_isDualizingComplex_iff_of_models`. Stacks Remark 0EJQ records
as open whether "`I` has `d` generators" can be replaced by `cd(A, I) ≤ d`.

## References

* [Stacks Project, Tag 0EJN](https://stacks.math.columbia.edu/tag/0EJN)
* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0EHR](https://stacks.math.columbia.edu/tag/0EHR)
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EJN, first assertion.** Under the hypotheses of 0EJN, `(ℱₙ)` extends
to `X`. -/
public theorem extendsToX_of_zeroLocus_eq_range_of_depthBound
    (S : AlgebraizationSituation.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (d : ℕ) (_hd : 1 ≤ d) (f : Fin d → S.A)
    (hV : PrimeSpectrum.zeroLocus (S.I : Set S.A) = PrimeSpectrum.zeroLocus (Set.range f))
    (h3 : SatisfiesDepthInequalities S F (d + 1) (d + 2) ∨
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt)) :
    ExtendsToX S (toKerSystem S F) := by
  have hdual' := (Dualizing.exists_isDualizingComplex_iff_of_models (A := S.A) inferInstance
    (HasDerivedCategory.standard (ModuleCat.{u} S.A))).mp hdual
  -- `V(I) = V(f₁, …, f_d)`: the ideals have the same radical.
  have hradf : (Ideal.span (Set.range f)).radical = S.I.radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span, hV]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    ((show Ideal.span (Set.range f) ≤ (Ideal.span (Set.range f)).radical from
      fun _ h => Ideal.le_radical h).trans hradf.le) (Submodule.fg_span (Set.finite_range f))
  -- Replace `I` by `J = (f₁^{N+1}, …, f_d^{N+1}) ⊆ I`, with the same radical.
  set g : Fin d → S.A := fun i => f i ^ (N + 1) with hg
  set J : Ideal S.A := Ideal.span (Set.range g) with hJ
  have hgmem : ∀ i, g i ∈ Ideal.span (Set.range f) ^ (N + 1) := fun i =>
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _
  have hJI : J ≤ S.I := Ideal.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hN (Ideal.pow_le_pow_right (Nat.le_succ N) (hgmem i)))
  have hrad : J.radical = S.I.radical := by
    rw [← hradf]
    refine le_antisymm (Ideal.radical_mono (Ideal.span_le.mpr ?_)) ?_
    · rintro _ ⟨i, rfl⟩
      exact Ideal.pow_le_self (Nat.succ_ne_zero N) (hgmem i)
    · refine (Ideal.radical_mono (Ideal.span_le.mpr ?_)).trans (Ideal.radical_idem J).le
      rintro _ ⟨i, rfl⟩
      exact ⟨N + 1, Ideal.subset_span (Set.mem_range_self (f := g) i)⟩
  obtain ⟨c, hc1, hc⟩ := exists_pow_idealOnOpen_le_withIdeal S hJI hrad
  refine extendsToX_of_withIdeal S hJI hc F hc1 ?_
  refine extendsToX_of_blowUp_fiber_dim_lt (S.withIdeal J (le_a_of_le_I S hJI))
    (transferToWithIdeal S hJI hc F) d hdual' (fun y => ?_) ?_
  · rw [Int.toNat_natCast]
    exact Stacks.Blowup.topologicalKrullDim_fiber_algebraicGeometry_blowUpToBase_lt_of_eq_span
      S.A d g y
  · exact h3.imp (satisfiesDepthInequalities_withIdeal S hJI hrad hc F)
      (depthAddDimAddDistance_gt_withIdeal S hJI hrad hc F)


/-- **Stacks Project, Tag 0EJN, in-particular clause.** Under the hypotheses of 0EJN, if moreover
`A` is `I`-adically complete then `(ℱₙ)` is the completion of a coherent `𝒪_U`-module. -/
public theorem essImage_completionFunctor_of_zeroLocus_eq_range_of_depthBound
    (S : AlgebraizationSituation.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (d : ℕ) (hd : 1 ≤ d) (f : Fin d → S.A)
    (hV : PrimeSpectrum.zeroLocus (S.I : Set S.A) = PrimeSpectrum.zeroLocus (Set.range f))
    (h3 : SatisfiesDepthInequalities S F (d + 1) (d + 2) ∨
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt)) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage (toKerSystem S F) :=
  (isCompletion_iff_ofRestriction S (toKerSystem S F)).mpr
    ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (toKerSystem S F)).mpr
      (isRestrictionOfCompletion_of_extendsToX S (toKerSystem S F)
        (extendsToX_of_zeroLocus_eq_range_of_depthBound S F hdual d hd f hV h3)))

/-- **Stacks Project, Tag 0EJN (Algebraization for ideals with few generators).** In Situation
0EHC let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Assume (1) `A` has a dualizing complex, (2)
`V(I) = V(f₁, …, f_d)` for some `d ≥ 1`, and (3) `(ℱₙ)` satisfies the `(d + 1, d + 2)`-inequalities
or `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) + δ^Y_Z(y) > d + 2` at every `y ∈ U ∩ Y` and every prime
`𝔭 ∉ V(I𝒪_{X,y}^∧)`. Then `(ℱₙ)` extends to `X`, and if `A` is `I`-adically complete then `(ℱₙ)`
is the completion of a coherent `𝒪_U`-module. -/
@[stacks 0EJN "the whole statement: (F_n) extends to X, and over an I-adically complete A it is \
the completion of a coherent O_U-module"]
public theorem algebraization_of_zeroLocus_eq_range_of_depthBound
    (S : AlgebraizationSituation.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} S.A)]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (d : ℕ) (hd : 1 ≤ d) (f : Fin d → S.A)
    (hV : PrimeSpectrum.zeroLocus (S.I : Set S.A) = PrimeSpectrum.zeroLocus (Set.range f))
    (h3 : SatisfiesDepthInequalities S F (d + 1) (d + 2) ∨
      ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        ∀ p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y),
          ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal →
          depthAddDimAddDistance S F y z p > ((d + 2 : ℤ) : EInt)) :
    ExtendsToX S (toKerSystem S F) ∧
      (IsAdicComplete S.I S.A →
        (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage (toKerSystem S F)) :=
  ⟨extendsToX_of_zeroLocus_eq_range_of_depthBound S F hdual d hd f hV h3, fun _ =>
    essImage_completionFunctor_of_zeroLocus_eq_range_of_depthBound S F hdual d hd f hV h3⟩

end Stacks.Algebraization

end
