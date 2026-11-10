module

public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.Homology.Perfect.FiniteComplexEulerCharacteristic
import StacksFrontier.RingTheory.Flat.DerivedFlat.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of the derived fibres of a bounded complex of projectives

Let `R` be a commutative ring and `P` a bounded complex of finite projective `R`-modules. At a
prime `p` of `R` the alternating sum `∑ (-1)^i dim_{κ(p)} Hⁱ(P ⊗ᴸ_R κ(p))` of the derived-fibre
Betti numbers of `P` is the alternating sum `∑ (-1)^i rank_p(P^i)` of the ranks of its terms, and
so it is a locally constant function on `PrimeSpectrum R`.

## Main results

* `StacksDraft.Perfect.finsum_negOnePow_fibreBetti_eq_rankAtStalk`: the alternating sum of the
  derived-fibre Betti numbers at `p` is the alternating sum of the ranks at `p` of the terms.
* `StacksDraft.Perfect.isLocallyConstant_finsum_negOnePow_fibreBetti`: that alternating sum is
  locally constant on `PrimeSpectrum R`.

## Implementation notes

The derived fibre of a bounded above complex of projectives is computed by termwise extension of
scalars (`comparison_isIso_of_projective`), whose terms are the vector spaces `κ(p) ⊗_R P^i` of
dimension `rank_p(P^i)` (`Module.rankAtStalk_baseChange`). The Euler characteristic of a bounded
complex of finite-dimensional vector spaces is that of its terms,
`StacksDraft.Perfect.homologyEulerChar_eq_eulerChar`. The ranks of a finite projective module are
locally constant, `Module.isLocallyConstant_rankAtStalk`, and only finitely many terms are
nonzero.

The sums are `finsum`s over `ℤ` with the signs `Int.negOnePow`, the spelling of
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre`.

## References

* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {R : Type u} [CommRing R]

/-- The prime of `R` under the closed point of `Spec κ(p)` is `p`. -/
theorem comap_algebraMap_residueField (p : PrimeSpectrum R)
    (q : PrimeSpectrum p.asIdeal.ResidueField) :
    q.comap (algebraMap R p.asIdeal.ResidueField) = p := by
  ext x
  have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  change algebraMap R p.asIdeal.ResidueField x ∈ q.asIdeal ↔ x ∈ p.asIdeal
  rw [hq, Ideal.mem_bot, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]

/-- A complex concentrated in degrees `[a, b]` is zero outside `[a, b]`. -/
theorem isZero_X_of_notMem_Icc (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] {i : ℤ} (hi : i ∉ Set.Icc a b) : IsZero (P.X i) := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with h | h
  · exact P.isZero_of_isStrictlyGE a i h
  · exact P.isZero_of_isStrictlyLE b i h

/-- **The alternating sum of the derived-fibre Betti numbers of a bounded complex of finite
projective modules is the alternating sum of the ranks of its terms.** At a prime `p`,
`∑ (-1)^i dim_{κ(p)} Hⁱ(P ⊗ᴸ_R κ(p)) = ∑ (-1)^i rank_p(P^i)`. -/
theorem finsum_negOnePow_fibreBetti_eq_rankAtStalk (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] (p : PrimeSpectrum R) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (fibreBetti.{u, u} (DerivedCategory.Q.obj P) i p : ℤ) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) := by
  classical
  let k := p.asIdeal.ResidueField
  let D := totalDerivedExtensionScalars.{u, u, u} (algebraMap R k)
  have : ∀ j, Projective (P.X j) := fun j => inferInstance
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  let Pκ := ((ModuleCat.extendScalars.{u, u, u} (algebraMap R k)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  let eT (i : ℤ) : (k ⊗[R] P.X i) ≃ₗ[k] Pκ.X i :=
    (StacksDraft.DerivedFlat.extendScalarsObjTensorIso (P := k) (P.X i)).symm.toLinearEquiv
  have hterm (i : ℤ) : Module.finrank k (Pκ.X i) = Module.rankAtStalk (P.X i) p := by
    let s : PrimeSpectrum k := IsLocalRing.closedPoint k
    have h₁ := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := k ⊗[R] P.X i)) s
    have h₂ := Module.rankAtStalk_baseChange (R := R) (M := P.X i) s
    rw [comap_algebraMap_residueField] at h₂
    rw [← (eT i).finrank_eq]
    exact h₁.symm.trans h₂
  have hfin (i : ℤ) : Module.Finite k (Pκ.X i) := Module.Finite.equiv (eT i)
  have hsupp : {i : ℤ | ¬ IsZero (Pκ.X i)}.Finite :=
    (Set.finite_Icc a b).subset fun i hi => by_contra fun hab =>
      hi (Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} (algebraMap R k))
        (isZero_X_of_notMem_Icc P a b hab))
  calc ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (fibreBetti.{u, u} (DerivedCategory.Q.obj P) i p : ℤ)
      = HomologicalComplex.homologyEulerChar Pκ :=
        finsum_congr fun i => congrArg (fun r : ℕ => (i.negOnePow : ℤ) * (r : ℤ))
          ((finrank_homologyFunctor_eq_of_iso.{u, u} (asIso (D.comparison.app P)) i).trans
            (finrank_homologyFunctor_Q_obj.{u, u} Pκ i))
    _ = HomologicalComplex.eulerChar Pκ := homologyEulerChar_eq_eulerChar Pκ hfin hsupp
    _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) :=
        finsum_congr fun i => congrArg (fun r : ℕ => (i.negOnePow : ℤ) * (r : ℤ)) (hterm i)

/-- **The alternating sum of the derived-fibre Betti numbers of a bounded complex of finite
projective modules is locally constant on `PrimeSpectrum R`.** This is the affine form of
Stacks 0BDJ for a complex of projectives. -/
@[ega "III 7.9.3" "more general", sga "6 III 5.5" "5.5(i), special case"]
theorem isLocallyConstant_finsum_negOnePow_fibreBetti (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (fibreBetti.{u, u} (DerivedCategory.Q.obj P) i p : ℤ)) := by
  classical
  rw [funext (finsum_negOnePow_fibreBetti_eq_rankAtStalk P a b)]
  have hsum : (fun p : PrimeSpectrum R =>
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ)) =
      fun p => ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) := by
    funext p
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Finset.coe_Icc]
    by_contra hab
    apply hi
    have : Subsingleton (P.X i) :=
      ModuleCat.subsingleton_of_isZero (isZero_X_of_notMem_Icc P a b hab)
    simp [Module.rankAtStalk_eq_zero_of_subsingleton]
  rw [hsum]
  have hfn : (fun p : PrimeSpectrum R =>
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ)) =
      ∑ i ∈ Finset.Icc a b,
        fun p : PrimeSpectrum R => (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) :=
    (Finset.sum_fn _ _).symm
  rw [hfn]
  refine Finset.sum_induction _ IsLocallyConstant (fun f g hf hg => hf.add hg)
    (IsLocallyConstant.const 0) fun i _ => ?_
  have := Module.finitePresentation_of_projective R (P.X i)
  exact ((Module.isLocallyConstant_rankAtStalk (R := R) (M := P.X i)).comp
    (fun n : ℕ => (n : ℤ))).comp (fun n : ℤ => (i.negOnePow : ℤ) * n)

end StacksDraft.Perfect

end
