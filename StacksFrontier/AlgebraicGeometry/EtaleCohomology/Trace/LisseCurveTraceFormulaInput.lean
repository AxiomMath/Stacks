module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLineInputs

/-!
# The trace formula for a lisse sheaf on a smooth curve, as one proposition

The Grothendieck–Lefschetz trace formula ([Tag 03V2](https://stacks.math.columbia.edu/tag/03V2),
over the extensions `k_N` of `k`) for a lisse ℓ-adic sheaf `F` on a smooth separated curve `U`
over a finite field `k` — not necessarily connected nor geometrically connected:

`∑_{deg y ∣ N} deg y · Tr(π_y ^ (N / deg y) | F_ȳ ⊗ ℚ_ℓ)`
`= ∑_{i < 3} (-1)ⁱ Tr((π_U^*) ^ N | Hⁱ_c(U_k̄, F ⊗ ℚ_ℓ))`.

`Stacks.EtaleCohomology.CurveTraceFormulaInput` is the case of the sheaf `ℱ_τ` of a
representation on a connected, geometrically connected curve.  The fibres of a family of smooth
affine curves over the closed points of the base, in the induction step of the weight bound of
Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), are smooth curves of the general
kind, which is why the general form is stated here.

## Main definitions

* `Stacks.EtaleCohomology.LisseCurveTraceFormulaInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The trace formula for a lisse sheaf on a smooth curve** (Tag 03V2 over `k_N`): for a lisse
ℓ-adic sheaf `F` on a smooth separated curve `U` over a finite field `k` of characteristic
`p ≠ ℓ`, any compactification of `U`, any algebraic closure `k̄` of `k` and any `N ≥ 1`,
`∑_{deg y ∣ N} deg y · Tr(π_y ^ (N / deg y) | F_ȳ)`
`= ∑_{i < 3} (-1)ⁱ Tr((π_U^*) ^ N | Hⁱ_c(U_k̄, F))`
on rational stalks and rational compactly supported cohomology. -/
public def LisseCurveTraceFormulaInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (F : LAdicSheaf.{u, u + 1} B U ℓ), F.IsLisse → ∀ N : ℕ, 0 < N →
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℚ_[ℓ]) *
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B U ℓ F y.1
          (finite_residueField f y.1 y.2) ^ (N / residueDegree f y.1)) =
      ∑ i ∈ Finset.range 3, (-1 : ℚ_[ℓ]) ^ i * LinearMap.trace ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar F (i : ℤ))
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard F
          (i : ℤ)).hom ^ N)

end Stacks.EtaleCohomology

end
