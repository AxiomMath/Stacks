module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth

/-!
# Traces of powers of the local Frobenius on the sheaf of a representation

The characteristic polynomial of an endomorphism of a finite dimensional vector space determines
the traces of its powers. Hence the geometric Frobenius `π_y^*` on the stalk of the `ℚ_ℓ`-sheaf
`ℱ_ρ` of a continuous representation `ρ` of `π₁(X, x̄)` at a closed point `y` satisfies
`Tr((π_y^*)^n | (ℱ_ρ)_ȳ) = Tr(ρ(F_y)^n)` for every `n`, `F_y` the geometric Frobenius element
(`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_representationSheaf_eq`).

## Main results

* `Stacks.EtaleCohomology.trace_pow_eq_of_charpoly_eq`
* `Stacks.EtaleCohomology.trace_rationalStalkFrobenius_representationSheaf_pow`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section TracePow

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Read along `ι : K →+* L` with `L` algebraically closed, the trace of `f ^ n` is the `n`-th
power sum of the roots in `L` of the characteristic polynomial of `f`. -/
private theorem map_trace_pow_eq_sum_roots_map_pow_of_isAlgClosed {L : Type*} [Field L]
    [IsAlgClosed L] (ι : K →+* L) (f : Module.End K V) (n : ℕ) :
    ι (LinearMap.trace K V (f ^ n)) = ((f.charpoly.map ι).roots.map (· ^ n)).sum := by
  classical
  let b := Module.Free.chooseBasis K V
  set A := LinearMap.toMatrix b b f
  have hA : (A.map ι).charpoly = f.charpoly.map ι := by
    rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.toMatrix_pow, AddMonoidHom.map_trace,
    ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, ← Matrix.trace_toLin'_eq,
    Matrix.toLin'_pow, trace_pow_eq_sum_roots_pow, Matrix.charpoly_toLin', hA]

/-- **The characteristic polynomial determines the traces of the powers**: if an endomorphism
`f` of a finite dimensional vector space and a square matrix `A` have the same characteristic
polynomial, then `Tr(f ^ n) = Tr(A ^ n)` for every `n`. Over an algebraic closure both are the
`n`-th power sum of the roots of the common characteristic polynomial. -/
public theorem trace_pow_eq_of_charpoly_eq {m : Type*} [Fintype m] [DecidableEq m]
    (f : Module.End K V) (A : Matrix m m K) (h : f.charpoly = A.charpoly) (n : ℕ) :
    LinearMap.trace K V (f ^ n) = (A ^ n).trace := by
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow,
    map_trace_pow_eq_sum_roots_map_pow_of_isAlgClosed,
    map_trace_pow_eq_sum_roots_map_pow_of_isAlgClosed, Matrix.charpoly_toLin', h]

end TracePow

section SheafFamily

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
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
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)

/-- **`Tr((π_y^*)^n | (ℱ_ρ)_ȳ) = Tr(ρ(F_y)^n)`** for the geometric Frobenius `π_y^*` on the
rational stalk of the sheaf `ℱ_ρ` of a continuous representation at a closed point `y` and the
geometric Frobenius element `F_y`. -/
public theorem trace_rationalStalkFrobenius_representationSheaf_pow (y : closedPoints X.1)
    (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) y.1
          (finite_residueField f y.1 y.2) ^ n) =
      ((ρ (geometricFrobeniusFamily f x y)).val ^ n).trace :=
  trace_pow_eq_of_charpoly_eq _ _
    (charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f ρ hρ y) n

end SheafFamily

end Stacks.EtaleCohomology

end
