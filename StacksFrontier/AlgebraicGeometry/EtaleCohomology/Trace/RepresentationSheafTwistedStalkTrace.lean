module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelRing

/-!
# Twisted traces of Frobenius on the stalks of `ℱ_ρ`

Let `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous and `A` an `r × r` matrix commuting with `ρ`, so that
`A` induces an endomorphism `ψ_A` of the ℓ-adic sheaf `ℱ_ρ`. At a closed point `y` with finite
residue field,

`Tr(ψ_A ∘ (π_y^*)ⁿ | (ℱ_ρ)_ȳ ⊗ ℚ_ℓ) = tr(A ρ(F_y)ⁿ)`.

For `ρ` the restriction of scalars of `σ : π₁ → GL_m(O)` along a basis of a finite free
`ℤ_ℓ`-algebra `O` and `A` the scalar matrix of `c ∈ O`, this is `Tr_{O/ℤ_ℓ}(c · tr σ(F_y)ⁿ)`.

## Main results

* `trace_rationalStalkMap_comp_rationalStalkEnd_pow_representationLAdicSheaf`: the trace of
  `ψ_A ∘ aⁿ` on the rational stalk of `ℱ_ρ` is `tr(A ρ(g)ⁿ)`.
* `trace_coefficientMatrixRingHom`: the trace of the restriction of scalars of a matrix is the
  trace over `R` of its trace.
* `trace_rationalStalkMap_coefficientScalar_comp_rationalStalkFrobenius_pow`: the trace of
  `c ∘ (π_y^*)ⁿ` on the rational stalk of the sheaf of `σ` is `Tr_{O/ℤ_ℓ}(c · tr σ(F_y)ⁿ)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

section Algebra

variable {R O : Type*} [CommRing R] [CommRing O] [Algebra R O] {d : ℕ}
  (b : Module.Basis (Fin d) R O) (r : ℕ)

/-- **The trace of the restriction of scalars of a matrix is the trace over `R` of its trace.** -/
public theorem trace_coefficientMatrixRingHom (M : Matrix (Fin r) (Fin r) O) :
    (coefficientMatrixRingHom b r M).trace = Algebra.trace R O M.trace := by
  have : Module.Free R O := Module.Free.of_basis b
  have : Module.Finite R O := Module.Finite.of_basis b
  have hconj : (coefficientVecEquiv b r).conj (Matrix.toLin' (coefficientMatrixRingHom b r M)) =
      (Matrix.toLin' M).restrictScalars R := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply, coefficientVecEquiv_mulVec,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ (coefficientVecEquiv b r), hconj,
    trace_restrictScalars_eq_trace_trace, Matrix.trace_toLin'_eq]

end Algebra

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- **The trace of `ψ_A ∘ aⁿ` on the rational stalk of `ℱ_ρ`** is `tr(A ρ(g)ⁿ)`, for an
intertwiner `A` and an endomorphism `a` of the geometric point acting through the element `g`
of `π₁(X, x̄)` transported along a path `t`. -/
public theorem trace_rationalStalkMap_comp_rationalStalkEnd_pow_representationLAdicSheaf
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (a : GeometricPoint.Hom s s) (g : EtaleFundamentalGroup X.1 s)
    (hg : g.hom = finiteEtaleFiberMap a) (A : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ g).val * A) (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap (representationLAdicSheafMap B X x e₀ hρ hρ A hA) s ∘ₗ
          LAdicSheaf.rationalStalkEnd B X ℓ (representationLAdicSheaf B X x e₀ ρ hρ) a ^ n) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (A * (ρ (etaleFundamentalGroupMulEquiv t g)).val ^ n).trace := by
  let T := representationLevelTrivialization B X x ρ hρ t
  have : Module.Free ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x e₀ ρ hρ) s) :=
    Module.Free.of_equiv T.stalkEquiv.symm
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x e₀ ρ hρ) s) :=
    Module.Finite.equiv T.stalkEquiv.symm
  set M := (ρ (etaleFundamentalGroupMulEquiv t g)).val
  have hbc : LAdicSheaf.rationalStalkMap (representationLAdicSheafMap B X x e₀ hρ hρ A hA) s ∘ₗ
      LAdicSheaf.rationalStalkEnd B X ℓ (representationLAdicSheaf B X x e₀ ρ hρ) a ^ n =
      (LAdicSheaf.stalkMap (representationLAdicSheafMap B X x e₀ hρ hρ A hA) s ∘ₗ
        LAdicSheaf.stalkEnd B X ℓ (representationLAdicSheaf B X x e₀ ρ hρ) a ^ n).baseChange
          ℚ_[ℓ] := by
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_pow]
    rfl
  have hE : T.stalkEquiv.conj (LAdicSheaf.stalkEnd B X ℓ
      (representationLAdicSheaf B X x e₀ ρ hρ) a) = Matrix.toLin' M := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply]
    have h := representationLevelTrivialization_stalkEquiv_stalkEnd B X x hρ t a g hg
      (T.stalkEquiv.symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hM : T.stalkEquiv.conj (LAdicSheaf.stalkMap
      (representationLAdicSheafMap B X x e₀ hρ hρ A hA) s) = Matrix.toLin' A := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply_apply, Matrix.toLin'_apply]
    have h := representationLevelTrivialization_stalkEquiv_stalkMap B X x hρ hρ t A hA
      (T.stalkEquiv.symm w)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have hpow : ∀ k : ℕ, T.stalkEquiv.conj (LAdicSheaf.stalkEnd B X ℓ
      (representationLAdicSheaf B X x e₀ ρ hρ) a ^ k) = Matrix.toLin' (M ^ k) := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id, Matrix.toLin'_one]
    | succ k ih =>
        rw [pow_succ, pow_succ, Module.End.mul_eq_comp, LinearEquiv.conj_comp, ih, hE,
          Matrix.toLin'_mul]
  rw [hbc, LinearMap.trace_baseChange, ← LinearMap.trace_conj' _ T.stalkEquiv,
    LinearEquiv.conj_comp, hM, hpow, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq]

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
  {m : ℕ} (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hσ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **The trace of `c ∘ (π_y^*)ⁿ` on the rational stalk of the sheaf of `σ : π₁ → GL_m(O)`** at a
closed point `y` is `Tr_{O/ℤ_ℓ}(c · tr σ(F_y)ⁿ)`. -/
public theorem trace_rationalStalkMap_coefficientScalar_comp_rationalStalkFrobenius_pow
    (c : O) (y : closedPoints X.1) (n : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalStalkMap (representationLAdicSheafMap B X x e₀ hσ hσ
            (coefficientScalarRingHom b m c)
            (fun g => coefficientScalarRingHom_commute b m c (σ g).val))
            (geometricPointAt X.1 y.1) ∘ₗ
          LAdicSheaf.rationalStalkFrobenius B X ℓ (representationLAdicSheaf B X x e₀
            ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hσ) y.1
            (finite_residueField f y.1 y.2) ^ n) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] (Algebra.trace ℤ_[ℓ] O
        (c * ((σ (geometricFrobeniusFamily f x y)).val ^ n).trace)) := by
  have := finite_residueField f y.1 y.2
  let t := (nonempty_finiteEtaleFiberFunctorIso X.1 (geometricPointAt X.1 y.1) x).some
  have h := trace_rationalStalkMap_comp_rationalStalkEnd_pow_representationLAdicSheaf B X x hσ t
    (frobeniusPointHom X.1 y.1) ((frobeniusDataOfPath x y t).localElement⁻¹)
    (inv_localElement_hom x y t) (coefficientScalarRingHom b m c)
    (fun g => coefficientScalarRingHom_commute b m c (σ g).val) n
  refine h.trans (congrArg (algebraMap ℤ_[ℓ] ℚ_[ℓ]) ?_)
  have he : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹ =
      geometricFrobeniusFamily f x y :=
    MulEquiv.map_inv (etaleFundamentalGroupMulEquiv _) _
  rw [he]
  change (coefficientMatrixRingHom b m (Matrix.scalar (Fin m) c) *
      (coefficientMatrixRingHom b m (σ (geometricFrobeniusFamily f x y)).val) ^ n).trace = _
  rw [← map_pow, ← map_mul, trace_coefficientMatrixRingHom, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

end Stacks.EtaleCohomology

end
