module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.StandardExample
import all StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
import all StacksFrontier.RingTheory.DiscreteValuationRing.Unramified

/-!
# Kummer extensions with a constant field extension are tamely ramified

Let `O` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be finite separable.

* If `O` is an algebra over a field `k` and `L` is generated over `K` by the image of a finite
  separable extension `F / k`, then `L` is unramified with respect to `O`: the image of
  `O ⊗_k F` is a finite formally unramified `O`-algebra generating `L`.
* If `L` is generated over `K` by an `n`-th root of `π`, with `n` invertible in the residue field,
  and an unramified subfield, then `L` is tamely ramified with respect to `O`: it is the compositum
  of a quotient of the Kummer extension `K(π^{1/n})` of [Stacks, Tag 09EV] and an unramified
  extension.

## Main results

* `IsDiscreteValuationRing.isUnramifiedWithRespectTo_of_adjoin_range_eq_top`
* `IsDiscreteValuationRing.isTamelyRamifiedWithRespectTo_of_pow_eq_of_sup`

## References

* [Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
-/

@[expose] public noncomputable section

open Polynomial IntermediateField
open scoped TensorProduct

namespace IsDiscreteValuationRing

variable {O K L : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [Algebra O L] [IsScalarTower O K L]

/-- **A constant field extension is unramified.** If `L` is generated over `K` by the image of a
finite separable extension `F` of a field of constants `k ⊆ O`, then `L` is unramified with
respect to `O`. -/
theorem isUnramifiedWithRespectTo_of_adjoin_range_eq_top {k F : Type*} [Field k] [Field F]
    [Algebra k O] [Algebra k L] [IsScalarTower k O L] [Algebra k F] [FiniteDimensional k F]
    [Algebra.IsSeparable k F] (ψ : F →ₐ[k] L) (hgen : adjoin K (Set.range ψ) = ⊤) :
    IsUnramifiedWithRespectTo O K L := by
  classical
  have : Algebra.FormallyUnramified k F := Algebra.FormallyUnramified.of_isSeparable k F
  let φ : O ⊗[k] F →ₐ[O] L :=
    Algebra.TensorProduct.lift (Algebra.ofId O L) ψ fun _ _ ↦ Commute.all _ _
  let T : Subalgebra O L := φ.range
  have : Module.Finite O T := by
    have : Module.Finite O (O ⊗[k] F) := Module.Finite.base_change k O F
    exact Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have : Algebra.FormallyUnramified O T :=
    Algebra.FormallyUnramified.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hT : adjoin K (T : Set L) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine adjoin_le_iff.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact subset_adjoin K _ ⟨1 ⊗ₜ a, by simp [φ]⟩
  exact (isUnramifiedWithRespectTo_iff_formallyUnramified O K L).mpr
    (formallyUnramified_integralClosure_of_adjoin_eq_top O K L T hT)

/-- **Kummer extensions with a constant extension are tame.** Let `π` be a uniformizer of `O`,
`n ≥ 1` invertible in the residue field, `θ ∈ L` with `θ^n = π`, and `E ⊆ L` an intermediate field
unramified with respect to `O` with `K(θ) ⊔ E = L`. Then `L` is tamely ramified with respect
to `O`. -/
theorem isTamelyRamifiedWithRespectTo_of_pow_eq_of_sup {π : O} (hπ : Irreducible π) {n : ℕ}
    (hn : 1 ≤ n) (hunit : IsUnit (n : IsLocalRing.ResidueField O)) {θ : L}
    (hθ : θ ^ n = algebraMap O L π) (E : IntermediateField K L)
    (hE : IsUnramifiedWithRespectTo O K E) (hgen : K⟮θ⟯ ⊔ E = ⊤) :
    IsTamelyRamifiedWithRespectTo O K L := by
  have hroot : aeval θ (Stacks.KummerExtension.kummerPoly K π n) = 0 := by
    rw [Stacks.KummerExtension.kummerPoly, map_sub, map_pow, aeval_X, aeval_C, hθ,
      IsScalarTower.algebraMap_apply O K L, sub_self]
  have hθint : _root_.IsIntegral K θ :=
    ⟨_, monic_X_pow_sub_C _ (by omega), hroot⟩
  have : FiniteDimensional K K⟮θ⟯ := adjoin.finiteDimensional hθint
  have hT1 : Stacks.KummerExtension.IsTamelyRamified O K K⟮θ⟯ := by
    rcases eq_or_lt_of_le hn with rfl | hn2
    · have hθK : θ = algebraMap K L (algebraMap O K π) := by
        rw [← IsScalarTower.algebraMap_apply, ← hθ, pow_one]
      have hbot : K⟮θ⟯ = ⊥ := by
        rw [adjoin_simple_eq_bot_iff, hθK]
        exact IntermediateField.algebraMap_mem _ _
      exact isTamelyRamified_of_algHom O K K⟮θ⟯ K
        ((botEquiv K L).toAlgHom.comp (equivOfEq hbot).toAlgHom)
        (AlgebraicGeometry.isTamelyRamified_self (A := O) (K := K))
    · have hn2' : 2 ≤ n := hn2
      have : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n)) :=
        ⟨Stacks.KummerExtension.kummerPoly_irreducible K π n hn hπ⟩
      have hunitO : IsUnit (n : O) :=
        (isUnit_map_iff (IsLocalRing.residue O) _).mp (by rwa [map_natCast])
      have hcop := AlgebraicGeometry.ringChar_residue_coprime_of_isUnit (R := O) n hunitO
      have : Algebra.IsSeparable K (Stacks.KummerExtension.K1 K π n) :=
        Stacks.KummerExtension.isSeparable_K1 K π n hn2' hπ hcop
      let g : Stacks.KummerExtension.K1 K π n →ₐ[K] L :=
        AdjoinRoot.liftAlgHom _ (Algebra.ofId K L) θ hroot
      have hgrange : g.fieldRange = K⟮θ⟯ := by
        refine le_antisymm ?_
          (adjoin_simple_le_iff.mpr ⟨AdjoinRoot.root _, AdjoinRoot.liftAlgHom_root _ _ _ _⟩)
        rintro _ ⟨z, rfl⟩
        obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
        change aeval θ p ∈ K⟮θ⟯
        exact algebra_adjoin_le_adjoin K {θ} (aeval_mem_adjoin_singleton K θ)
      exact isTamelyRamified_of_algHom O K K⟮θ⟯ _
        ((AlgEquiv.ofInjectiveField g).trans (equivOfEq hgrange)).symm.toAlgHom
        (Stacks.KummerExtension.isTamelyRamified_K1 K π n hn2' hπ hcop)
  exact isTamelyRamified_of_algHom O K L (↥(K⟮θ⟯ ⊔ E))
    ((equivOfEq hgen).symm.toAlgHom.comp (topEquiv (F := K) (E := L)).symm.toAlgHom)
    (isTamelyRamified_sup O K L K⟮θ⟯ E hT1
      (isTamelyRamifiedWithRespectTo_of_isUnramifiedWithRespectTo O K E hE))

end IsDiscreteValuationRing

end
