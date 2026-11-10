module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.NumberTheory.Padics.LAdicGroupMonodromy

/-!
# Determinantal weights of an `ℓ`-adic representation of `π₁` of a scheme over a finite field

Let `X` be a connected scheme of finite type over a finite field `k` with `q = p ^ n` elements, `x`
a geometric point and `ρ : π₁(X, x) → GL_m(K)` a continuous representation over an algebraically
closed complete ultrametric extension `K` of `ℚ_ℓ` (for instance `ℂ_ℓ`, which receives every
representation into `GL_m(ℚ_ℓ)` through `Stacks.LAdic.ratToUnitsMatrix`). Fix `φ ∈ π₁(X, x)` over
the inverse of the Frobenius of `k`, for instance a lift provided by
`AlgebraicGeometry.exists_etaleFundamentalGroupMap_eq_finiteFieldFrobenius_inv` when `X` is
geometrically connected.

This file reads the group form of the determinantal weights (Weil II 1.3,
`Stacks.LAdic.exists_monodromy_weights_frobenius`) on the geometric Frobenius elements
`F_y = Stacks.EtaleCohomology.geometricFrobeniusFamily f x y` at the closed points `y` of `X`,
whose characteristic polynomials are those of the geometric Frobenius on the stalks of the lisse
sheaf `ℱ_ρ` (`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_representationSheaf_eq`).
The two group-theoretic inputs are discharged here: the quotient of `π₁(X, x)` by the geometric
fundamental group `H = ker(π₁(X, x) → π₁(Spec k))` is abelian because `π₁(Spec k)` is
(`AlgebraicGeometry.commutator_mem_ker_etaleFundamentalGroupMap_of_finite`), and `F_y` lies in
`φ ^ deg y · H` (`AlgebraicGeometry.inv_pow_mul_geometricFrobeniusFamily_mem_ker`).

The geometric input of Weil II 1.3.4 — no nonzero continuous additive character of the geometric
fundamental group of a finite étale Galois cover of `X` is invariant under the Frobenius power
`φ ^ [π₁ : U]`, i.e. `1` is not a Frobenius eigenvalue on `H¹` of any finite étale Galois cover —
is the hypothesis `hD1`, and the semisimplicity of `ρ` is the hypothesis `hss`.

## Main results

* `AlgebraicGeometry.exists_geometricFrobeniusFamily_determinantal_weights` — there is `c > 0`
  such that on every `π₁`-irreducible subspace `W` the numbers `‖ι det(ρ(F_y) | W)‖ ^ c` are
  `r ^ (deg y · dim W)` for a single `r ≥ 0`: `W` has a determinantal weight.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.LAdic

universe u

namespace AlgebraicGeometry

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace Matrix.ultraNormedRing
  Matrix.ultraNormedAlgebra Matrix.isUltrametricDist Matrix.completeSpace_of_ultra

variable {k : Type u} [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p]
  (hq : Fintype.card k = p ^ n)
  {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  (x : GeometricPoint X)
  (ℓ : ℕ) [Fact ℓ.Prime]
  {K : Type*} [NontriviallyNormedField K] [CharZero K] [IsUltrametricDist K]
  [NormedAlgebra ℚ_[ℓ] K] [CompleteSpace K] [IsAlgClosed K]
  {m : Type*} [Fintype m] [DecidableEq m]

include ℓ in
/-- **Determinantal weights at the closed points** (Weil II 1.3, for the geometric Frobenius
elements of a scheme over a finite field). Let `φ` lie over the inverse of the Frobenius of `k`,
`ρ : π₁(X, x) → GL_m(K)` continuous and semisimple, and assume the geometric input `hD1` of Weil
II 1.3.4. Then there is `c > 0` such that for every `π₁(X, x)`-irreducible subspace `W` there is
`r` with `‖ι det(ρ(F_y) | W)‖ ^ c = r ^ (deg y · dim W)` at every closed point `y`. -/
theorem exists_geometricFrobeniusFamily_determinantal_weights (ι : K →+* ℂ)
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹)
    (ρ : EtaleFundamentalGroup X x →* (Matrix m m K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix m m K))
    (hD1 : ∀ U : Subgroup (EtaleFundamentalGroup X x), U.Normal →
      IsOpen (U : Set (EtaleFundamentalGroup X x)) →
      ∀ ψ : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U) → K,
        (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U),
          (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) →
        ψ = 0)
    (hss : ∀ W : Submodule K (m → K), (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (m → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W') :
    ∃ c : ℕ, 0 < c ∧
      ∀ W : Submodule K (m → K), ∀ hW : (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W),
        (∀ W' ≤ W, W' ≠ ⊥ → (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W') →
          W' = W) →
        ∃ r : ℝ, ∀ y : closedPoints X,
          ‖ι (detCharacter ρ hW (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y))‖ ^ c =
            r ^ (Stacks.EtaleCohomology.residueDegree f y.1 * Module.finrank K W) := by
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  obtain ⟨c, hc, N, B, -, -, hW⟩ := exists_monodromy_weights_frobenius (ℓ := ℓ) ι ρ hρ
    (etaleFundamentalGroupMap f x).toMonoidHom.ker φ
    (commutator_mem_ker_etaleFundamentalGroupMap_of_finite k f x) hD1 hss
  refine ⟨c * ℓ ^ N, Nat.mul_pos hc (pow_pos (Fact.out : ℓ.Prime).pos N), fun W hWΓ hirr => ?_⟩
  obtain ⟨-, r, -, hdet⟩ := hW W hWΓ hirr
  refine ⟨r, fun y => ?_⟩
  have := Stacks.EtaleCohomology.finite_residueField f y.1 y.2
  exact hdet _ _ (inv_pow_mul_geometricFrobeniusFamily_mem_ker p n hq f x y φ hφ)

omit [CharZero K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] in
/-- The determinant character on the whole space is the determinant. -/
theorem detCharacter_top_apply {Γ : Type*} [Group Γ] (ρ : Γ →* (Matrix m m K)ˣ)
    (hW : ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra (⊤ : Submodule K (m → K))) (g : Γ) :
    detCharacter ρ hW g = (ρ g : Matrix m m K).det := by
  change LinearMap.det (stabRestrict (ρ g : Matrix m m K) (hW g)) = _
  have h : stabRestrict (ρ g : Matrix m m K) (hW g) =
      (Submodule.topEquiv (R := K) (M := m → K)).symm.toLinearMap ∘ₗ
        Matrix.toLin' (ρ g : Matrix m m K) ∘ₗ
        (Submodule.topEquiv (R := K) (M := m → K)).symm.symm.toLinearMap := by
    ext w : 1
    apply Subtype.ext
    simp [stabRestrict_apply, Matrix.toLin'_apply]
  rw [h, LinearMap.det_conj, LinearMap.det_toLin']

include ℓ in
/-- **Determinantal weight of an irreducible representation** (Weil II 1.3, without the
semisimplicity hypothesis). For `ρ : π₁(X, x) → GL_m(K)` continuous and irreducible, under the
geometric input `hD1` of Weil II 1.3.4, there are `c > 0` and `r` with
`‖ι det ρ(F_y)‖ ^ c = r ^ (deg y · m)` at every closed point `y`. An irreducible representation
is semisimple, so this is `exists_geometricFrobeniusFamily_determinantal_weights` on the whole
space; it applies to every Jordan–Hölder constituent of an arbitrary `ρ`, which is how Weil II
removes semisimplicity. -/
theorem exists_geometricFrobeniusFamily_determinantal_weight_of_irreducible (ι : K →+* ℂ)
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hq (x.map f))⁻¹)
    (ρ : EtaleFundamentalGroup X x →* (Matrix m m K)ˣ)
    (hρ : Continuous fun g => (ρ g : Matrix m m K))
    (hD1 : ∀ U : Subgroup (EtaleFundamentalGroup X x), U.Normal →
      IsOpen (U : Set (EtaleFundamentalGroup X x)) →
      ∀ ψ : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U) → K,
        (∀ a b, ψ (a * b) = ψ a + ψ b) → Continuous ψ →
        (∀ a b : ↥((etaleFundamentalGroupMap f x).toMonoidHom.ker ⊓ U),
          (b : EtaleFundamentalGroup X x) = φ ^ U.index * a * (φ ^ U.index)⁻¹ → ψ b = ψ a) →
        ψ = 0)
    (hirr : ∀ W : Submodule K (m → K), (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∃ r : ℝ, ∀ y : closedPoints X,
      ‖ι (ρ (Stacks.EtaleCohomology.geometricFrobeniusFamily f x y) : Matrix m m K).det‖ ^ c =
        r ^ (Stacks.EtaleCohomology.residueDegree f y.1 * Fintype.card m) := by
  have htop : ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra (⊤ : Submodule K (m → K)) :=
    fun g w _ => Submodule.mem_top
  have hbot : ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra (⊥ : Submodule K (m → K)) :=
    fun g w hw => by rw [Submodule.mem_bot] at hw ⊢; rw [hw, Matrix.mulVec_zero]
  have hss : ∀ W : Submodule K (m → K), (∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W) →
      ∃ W' : Submodule K (m → K), IsCompl W W' ∧
        ∀ g, (ρ g : Matrix m m K) ∈ stabilizerSubalgebra W' := by
    intro W hW
    rcases hirr W hW with rfl | rfl
    · exact ⟨⊤, isCompl_bot_top, htop⟩
    · exact ⟨⊥, isCompl_top_bot, hbot⟩
  obtain ⟨c, hc, hw⟩ := exists_geometricFrobeniusFamily_determinantal_weights p n hq f x ℓ ι φ hφ
    ρ hρ hD1 hss
  obtain ⟨r, hr⟩ := hw ⊤ htop (fun W' _ hW' hW's => (hirr W' hW's).resolve_left hW')
  refine ⟨c, hc, r, fun y => ?_⟩
  rw [← detCharacter_top_apply ρ htop, hr y, finrank_top, Module.finrank_fintype_fun_eq_card]

end AlgebraicGeometry
