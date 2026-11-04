module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.TraceMapPositive.AbsoluteFormsComparison
public import StacksFrontier.RingTheory.FormsTrace.MonogenicFrame

/-!
# Tr = Θ_{S/R}

Let `𝐅_p ⊂ Λ ⊂ R ⊂ S` with `S ≅ R[x]/(x ^ p - a)`.  The trace maps on absolute forms of
Stacks, Lemma 0FLB / Proposition 0FLC for the framed algebra `S/R`
(`Stacks.FormsTrace.ChartFrame.trace`, independent of the frame) induce a map of relative de Rham
complexes `Θ_{S/R} : Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}` (`KaehlerDifferential.relativeTraceComplex`).  Remark
0FLF: this is the map built from the elementary trace `Tr` of Lemma 0AX5
(`KaehlerDifferential.higherTraceComplexMap`).

The proof is the one of the remark.  `Θ_{S/R}` is the base change, along `ℤ[T] → R`, `T ↦ a`, of
the trace maps of the universal root `ℤ[T][x]/(x ^ p - T)`: both carry monogenic frames
(`Stacks.FormsTrace.monogenicFrame`), and framed traces commute with base change.  Over `ℤ[T]`,
whose absolute differentials are torsion free, the projection formula forces
`Θ(x ^ (p - 1) dx) = dT` (Example 0FLD), hence `Θ_{S/R}(x ^ (p - 1) dx) = da`; the vanishing of
`Trace_{S/R}`, the projection formula and compatibility with `d` then pin `Θ_{S/R}` down to `Tr`
(`KaehlerDifferential.relativeTraceComplex_eq_higherTraceComplexMap_of_baseChange`).

## Main results

* `KaehlerDifferential.relativeTraceComplex_trace_eq_higherTraceComplexMap`: **Tr = Θ_{S/R}**,
  for the trace maps of any frame of `S/R`.
* `KaehlerDifferential.relativeTraceComplex_rootExtFrame_eq_higherTraceComplexMap`: the same for
  the monogenic frame, which always exists.

## References

* [Stacks Project, Tag 0FLF](https://stacks.math.columbia.edu/tag/0FLF)
* [Stacks Project, Tag 0FLD](https://stacks.math.columbia.edu/tag/0FLD)
-/

@[expose] public noncomputable section

open Polynomial Stacks.FormsTrace

universe u

namespace KaehlerDifferential

/-- The absolute differentials of a polynomial ring over `ℤ`, for the canonical `ℤ`-algebra
structure `Ring.toIntAlgebra`, have no torsion by positive integers. -/
theorem mvPolynomial_kaehler_eq_zero_of_natCast_smul_int {σ : Type*} {d : ℕ} (hd : 0 < d)
    (J : Algebra ℤ (MvPolynomial σ ℤ)) :
    ∀ ω : @KaehlerDifferential ℤ (MvPolynomial σ ℤ) _ _ J,
      ((d : MvPolynomial σ ℤ)) • ω = 0 → ω = 0 := by
  obtain rfl : J = AddMonoidAlgebra.algebra := Subsingleton.elim _ _
  exact mvPolynomial_kaehler_eq_zero_of_natCast_smul hd

variable {p : ℕ} {Λ R S : Type u} [CommRing Λ] [CommRing R] [CommRing S] [Algebra Λ R]
  [Algebra Λ S] [Algebra R S] [IsScalarTower Λ R S]

section Frame

variable [Nontrivial R]

/-- The power basis `1, x, …, x ^ (p - 1)` of `S ≅ R[x]/(x ^ p - a)`. -/
abbrev rootExtPowerBasis (hp : p.Prime) (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    PowerBasis R S :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C a hp.ne_zero)).map e

/-- The power basis `1, x, …, x ^ (p - 1)` of `S ≅ R[x]/(x ^ p - a)` has `p` elements. -/
theorem rootExtPowerBasis_dim (hp : p.Prime) (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    (rootExtPowerBasis hp a e).dim = p := by
  rw [rootExtPowerBasis, PowerBasis.map_dim, AdjoinRoot.powerBasis'_dim,
    Polynomial.natDegree_X_pow_sub_C]

/-- **The monogenic frame** of `S ≅ R[x]/(x ^ p - a)`. -/
abbrev rootExtFrame (hp : p.Prime) (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ChartFrame p R S :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  monogenicFrame (rootExtPowerBasis hp a e) (rootExtPowerBasis_dim hp a e) hp.one_lt

end Frame

/-- The universal root `ℤ[T][x]/(x ^ p - T)` and its power basis. -/
abbrev universalPowerBasis (hp : p.Prime) : PowerBasis UniversalBase.{u} (UniversalRoot.{u} p) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C universalVar.{u} hp.ne_zero)

/-- The power basis of the universal root `ℤ[T][x]/(x ^ p - T)` has `p` elements. -/
theorem universalPowerBasis_dim (hp : p.Prime) : (universalPowerBasis.{u} hp).dim = p := by
  rw [universalPowerBasis, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]

/-- **Tr = Θ_{S/R}.**  Let `𝐅_p ⊂ Λ ⊂ R ⊂ S` with `S ≅ R[x]/(x ^ p - a)`, and let `f` be any
frame of `S/R` (for instance the monogenic one, `KaehlerDifferential.rootExtFrame`; the trace maps
do not depend on it).  The map of relative de Rham complexes `Θ_{S/R} : Ω^•_{S/Λ} ⟶ Ω^•_{R/Λ}`
induced by the trace maps on absolute forms of Proposition 0FLC is the map built from the trace
`Tr` of Lemma 0AX5. -/
@[stacks 0FLF "Tr = Θ_{S/R}, for Θ_{S/R} the map of relative de Rham complexes induced (0FLC (3)) \
by the trace maps on absolute forms of the framed algebra S/R"]
theorem relativeTraceComplex_trace_eq_higherTraceComplexMap (hp : p.Prime) [CharP Λ p] (a : R)
    (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) {d : ℕ} [NeZero d]
    (f : ChartFrame d R S) :
    relativeTraceComplex Λ f.trace f.isWedgeLinear_trace f.commutesWithD_trace =
      higherTraceComplexMap hp a e := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · ext n : 1
    have := Module.subsingleton R (⋀[R]^n Ω[R⁄Λ])
    ext y
    exact Subsingleton.elim (α := ⋀[R]^n Ω[R⁄Λ]) _ _
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Module.Free R S := Module.Free.of_basis f.basis
  have : Module.Finite R S := Module.Finite.of_basis f.basis
  let pb₀ := universalPowerBasis.{u} hp
  have : Module.Free UniversalBase.{u} (UniversalRoot.{u} p) := Module.Free.of_basis pb₀.basis
  have : Module.Finite UniversalBase.{u} (UniversalRoot.{u} p) := Module.Finite.of_basis pb₀.basis
  let f₀ : ChartFrame p UniversalBase.{u} (UniversalRoot.{u} p) :=
    monogenicFrame pb₀ (universalPowerBasis_dim hp) hp.one_lt
  let : Algebra UniversalBase.{u} R := (universalBaseMap.{u} a).toAlgebra
  let : Algebra (UniversalRoot.{u} p) S := (universalRootMap.{u} a e).toAlgebra
  let : Algebra UniversalBase.{u} S := ((algebraMap R S).comp (universalBaseMap.{u} a)).toAlgebra
  have : IsScalarTower UniversalBase.{u} R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower UniversalBase.{u} (UniversalRoot.{u} p) S :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change _ = universalRootMap.{u} a e (AdjoinRoot.of _ c)
      unfold universalRootMap
      rw [AdjoinRoot.lift_of]
      rfl
  set x := e (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a))
  have hx : algebraMap (UniversalRoot.{u} p) S
      ((AlgEquiv.refl : UniversalRoot.{u} p ≃ₐ[UniversalBase.{u}] UniversalRoot.{u} p)
        (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C universalVar.{u}))) = x :=
    universalRootMap_root a e
  have : Algebra.IsPushout UniversalBase.{u} (UniversalRoot.{u} p) R S := by
    let bU := powerBasisFin pb₀ (universalPowerBasis_dim hp)
    let b := powerBasisFin (rootExtPowerBasis hp a e) (rootExtPowerBasis_dim hp a e)
    refine AlgebraicGeometry.isPushout_of_bases_one bU b fun y => ?_
    have hb : ∀ i, algebraMap (UniversalRoot.{u} p) S (bU i) = b i := fun i => by
      rw [powerBasisFin_apply, powerBasisFin_apply, map_pow]
      exact congrArg (· ^ (i : ℕ)) (universalRootMap_root a e)
    conv_lhs => rw [← bU.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply UniversalBase.{u} R S]
  exact relativeTraceComplex_eq_higherTraceComplexMap_of_baseChange hp a e f.trace
    f.isFormsTrace_trace f.isWedgeLinear_trace f.commutesWithD_trace universalVar.{u}
    AlgEquiv.refl (mvPolynomial_kaehler_eq_zero_of_natCast_smul_int hp.pos _) f₀.trace
    f₀.isFormsTrace_trace (universalBaseMap_var a) hx
    (fun η => ChartFrame.trace_formsMap_of_isPushout R S f₀ f 1 η)

/-- **Tr = Θ_{S/R}** for the monogenic frame `1, x, …, x ^ (p - 1)` of `S ≅ R[x]/(x ^ p - a)`,
which exists for every nonzero `R`. -/
theorem relativeTraceComplex_rootExtFrame_eq_higherTraceComplexMap [Nontrivial R] (hp : p.Prime)
    [CharP Λ p] (a : R) (e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[R] S) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    relativeTraceComplex Λ (rootExtFrame hp a e).trace (rootExtFrame hp a e).isWedgeLinear_trace
        (rootExtFrame hp a e).commutesWithD_trace =
      higherTraceComplexMap hp a e :=
  have : NeZero p := ⟨hp.ne_zero⟩
  relativeTraceComplex_trace_eq_higherTraceComplexMap hp a e (rootExtFrame hp a e)

end KaehlerDifferential

end
