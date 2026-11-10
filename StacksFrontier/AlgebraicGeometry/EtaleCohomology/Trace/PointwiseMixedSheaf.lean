module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SheafFrobeniusMatrices

/-!
# Pointwise mixed ℓ-adic sheaves

An ℓ-adic sheaf `F` on a scheme `X` of finite type over a finite field `k` with `q` elements is
pointwise `ι`-mixed of weights `≤ w` (Weil II 1.2.2) when at every closed point `y` of `X`, of
degree `deg y` over `k`, every complex root of the characteristic polynomial of the geometric
Frobenius `π_y` on the rational stalk `F_ȳ ⊗ ℚ_ℓ`, read along `ι : ℚ_ℓ →+* ℂ`, has absolute value
`q ^ (deg y · w' / 2)` for an integer `w' ≤ w`.

For `F = ℱ_ρ` the geometric Frobenius on the stalk at `y` has the characteristic polynomial of
`ρ(F_y)` (`charpoly_rationalStalkFrobenius_representationSheaf_eq`), so pointwise mixedness of
`ℱ_ρ` is that of `ρ`; in particular the conclusions of Deligne's conjecture, the hypotheses of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), make `ℱ_ρ` pointwise `ι`-mixed of weights
`≤ 0` for every `ι`.

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `LAdicSheaf.IsPointwiseMixedOfWeightLE`: pointwise `ι`-mixedness of weights `≤ w`.

## Main results

* `LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff`: `ℱ_ρ` is pointwise mixed of
  weights `≤ w` exactly when the Frobenius elements `ρ(F_y)` are.
* `LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_of_hasDeligneConclusions`: under the
  conclusions of Deligne's conjecture, `ℱ_ρ` is pointwise `ι`-mixed of weights `≤ 0`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* P. Deligne, *La conjecture de Weil. II*, 1.2.2 and 3.3
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **Pointwise `ι`-mixedness of weights `≤ w`** of an ℓ-adic sheaf `F` on a scheme of finite type
over a finite field with `q` elements (Weil II 1.2.2): at every closed point `y`, every complex
root of the characteristic polynomial of the geometric Frobenius on the rational stalk
`F_ȳ ⊗ ℚ_ℓ`, read along `ι`, has absolute value `q ^ (deg y · w' / 2)` for an integer `w' ≤ w`. -/
public def LAdicSheaf.IsPointwiseMixedOfWeightLE (F : LAdicSheaf B X ℓ) (q : ℕ)
    (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ) : Prop :=
  ∀ (y : closedPoints X.1) (z : ℂ),
    ((LAdicSheaf.rationalStalkFrobenius B X ℓ F y.1
      (finite_residueField f y.1 y.2)).charpoly.map ι).IsRoot z →
    ∃ w' : ℤ, w' ≤ w ∧ ‖z‖ = (q : ℝ) ^ (((residueDegree f y.1 : ℤ) * w' : ℝ) / 2)

variable {B X ℓ f} in
/-- Pointwise mixedness is monotone in the weight. -/
public theorem LAdicSheaf.isPointwiseMixedOfWeightLE_mono {F : LAdicSheaf B X ℓ} {q : ℕ}
    {ι : ℚ_[ℓ] →+* ℂ} {w w₂ : ℤ} (h : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F q ι w)
    (hw : w ≤ w₂) : LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F q ι w₂ := fun y z hz =>
  let ⟨w', hw', hz'⟩ := h y z hz
  ⟨w', hw'.trans hw, hz'⟩

section Representation

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

variable [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)

/-- `ℱ_ρ` is pointwise mixed of weights `≤ w` exactly when the geometric Frobenius elements
`ρ(F_y)` are: every complex root of the characteristic polynomial of `ρ(F_y)`, read along `ι`, has
absolute value `q ^ (deg y · w' / 2)` for an integer `w' ≤ w`. -/
public theorem LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff (q : ℕ)
    (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f
        (LAdicSheaf.representationSheaf B X x ρ hρ) q ι w ↔
      ∀ (y : closedPoints X.1) (z : ℂ),
        (((ρ (geometricFrobeniusFamily f x y) : GL (Fin r) ℚ_[ℓ]) :
          Matrix (Fin r) (Fin r) ℚ_[ℓ]).charpoly.map ι).IsRoot z →
        ∃ w' : ℤ, w' ≤ w ∧ ‖z‖ = (q : ℝ) ^ (((residueDegree f y.1 : ℤ) * w' : ℝ) / 2) := by
  refine forall_congr' fun y => forall_congr' fun z => ?_
  rw [charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f ρ hρ y]

/-- **The sheaf `ℱ_ρ` of Tag 03VH is pointwise `ι`-mixed of weights `≤ 0`** when `ρ` satisfies
the conclusions of Deligne's conjecture. -/
public theorem LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_of_hasDeligneConclusions
    {p : ℕ} (q : ℕ) {ι : ℚ_[ℓ] →+* ℂ}
    (h : HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f
      (LAdicSheaf.representationSheaf B X x ρ hρ) q ι 0 := by
  rw [LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff]
  intro y z hz
  exact ⟨0, le_rfl, by rw [h.norm_eq_one y z hz]; simp⟩

end Representation

end Stacks.EtaleCohomology

end
