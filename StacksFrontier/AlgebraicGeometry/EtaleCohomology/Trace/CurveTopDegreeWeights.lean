module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTraceFormulaOfCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantEigenvector
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree

/-!
# The weights of `H²_c` of a lisse sheaf on a curve

If `H²_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)` is the geometric coinvariants of `ρ`, twisted by `(-1)` (the Frobenius
`π_U^*` acting as `q` times a geometric Frobenius lift `φ`), and `ρ` is pointwise `ι`-mixed of
weights `≤ w`, then the weights of `H²_c` are `≤ w + 2`. No purity is needed: a Frobenius element
`F_y` at a closed point of degree `d` acts on the coinvariants as `φ ^ d`
(`Stacks.EtaleCohomology.isRoot_charpoly_pow_of_isRoot_coinvariantsFrobenius`), so for an
eigenvalue `α` of `φ` there, `α ^ d` is an eigenvalue of `ρ(F_y)` (Weil II 3.2.3, the case of
`H²_c`).

## Main results

* `exists_weight_le_of_isRoot_coinvariantsFrobenius`: the weights of Frobenius on the geometric
  coinvariants of a pointwise mixed representation.
* `exists_weight_le_two_of_isRoot_rationalGeometricCompactlySupportedFrobenius`: the weights of
  `H²_c` of `ℱ_ρ` are `≤ w + 2`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section Coinvariants

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} [ConnectedSpace X] [CompactSpace X]
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : GeometricPoint X) {ℓ : ℕ} [Fact ℓ.Prime]
  {r : ℕ}

/-- **The weights of Frobenius on the geometric coinvariants of a pointwise mixed
representation.** If `ρ` is pointwise `ι`-mixed of weights `≤ w` and `φ` lies over the inverse of
the Frobenius of `k`, every root along `ι` of the characteristic polynomial of `φ` on the geometric
coinvariants of `ρ` has absolute value `q ^ (w' / 2)` for an integer `w' ≤ w`. -/
public theorem exists_weight_le_of_isRoot_coinvariantsFrobenius (p n : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ n) (ρ : EtaleFundamentalGroup X x →* GL (Fin r) ℚ_[ℓ])
    (ι : ℚ_[ℓ] →+* ℂ) {w : ℤ} (hmix : IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ)
    (φ : EtaleFundamentalGroup X x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    {z : ℂ} (hz : ((LinearMap.charpoly (coinvariantsFrobenius
      (etaleFundamentalGroupMap f x).toMonoidHom.ker ρ φ)).map ι).IsRoot z) :
    ∃ w' : ℤ, w' ≤ w ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2) := by
  classical
  obtain ⟨y0, -, hy0⟩ := (isClosed_univ (X := X)).exists_closed_singleton Set.univ_nonempty
  set y : closedPoints X := ⟨y0, hy0⟩
  have hd : 0 < residueDegree f y.1 := residueDegree_pos f y.1 y.2
  have := finite_residueField f y.1 y.2
  have hmem := AlgebraicGeometry.inv_pow_mul_geometricFrobeniusFamily_mem_ker p n hcard f x y φ hφ
  have hroot := isRoot_charpoly_pow_of_isRoot_coinvariantsFrobenius _ ι ρ φ hmem hz
  obtain ⟨w', hw', hn⟩ := hmix y _ hroot
  refine ⟨w', hw', ?_⟩
  have hq : (0 : ℝ) ≤ ((p ^ n : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [norm_pow] at hn
  refine (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hq _) hd.ne').mp ?_
  rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  congr 1
  push_cast
  ring

end Coinvariants

section Sheaf

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
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
  [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1] [CompactSpace U.1]
  {k : Type u} [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [CompactSpace U.1] [QuasiCompact f] [IsSeparated f] in
/-- **The weights of `H²_c` of `ℱ_ρ` on a curve are `≤ w + 2`** for `ρ` pointwise `ι`-mixed of
weights `≤ w`, given the identification of `H²_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)` with the geometric coinvariants
of `ρ` under which `π_U^*` is `q` times a geometric Frobenius lift `φ` (Weil II 3.2.3). -/
public theorem exists_weight_le_two_of_isRoot_rationalGeometricCompactlySupportedFrobenius
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (x : GeometricPoint U.1)
    {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (ι : ℚ_[ℓ] →+* ℂ) {w : ℤ} (hmix : IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ)
    (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (LAdicSheaf.representationSheaf B U x ρ hρ) 2)]
    (e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x ρ hρ) 2 ≃ₗ[ℚ_[ℓ]]
      Representation.Coinvariants ((matrixRepresentation ρ).comp
        (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype))
    (he : ∀ v, e ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
      (LAdicSheaf.representationSheaf B U x ρ hρ) 2).hom v) =
        ((p ^ n : ℕ) : ℚ_[ℓ]) •
          coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker ρ φ (e v))
    {z : ℂ} (hz : ((ModuleCat.Hom.hom (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U
      ℓ f j kbar p n hcard (LAdicSheaf.representationSheaf B U x ρ hρ) 2)).charpoly.map ι).IsRoot
        z) :
    ∃ w' : ℤ, w' ≤ w + 2 ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2) := by
  classical
  set g := coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker ρ φ
  have : FiniteDimensional ℚ_[ℓ] (Representation.Coinvariants ((matrixRepresentation ρ).comp
      (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype)) := e.finiteDimensional
  have hπ : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
      (LAdicSheaf.representationSheaf B U x ρ hρ) 2).hom =
        e.symm.conj (((p ^ n : ℕ) : ℚ_[ℓ]) • g) := by
    ext v
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      LinearMap.smul_apply, he]
  have hq0 : ((p ^ n : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  rw [hπ, LinearEquiv.charpoly_conj] at hz
  have hz' := isRoot_charpoly_div_of_isRoot_charpoly_smul ι g hq0 hz
  obtain ⟨w', hw', hn⟩ := exists_weight_le_of_isRoot_coinvariantsFrobenius f x p n hcard ρ ι hmix φ
    hφ hz'
  refine ⟨w' + 2, by lia, ?_⟩
  have hqpos : (0 : ℝ) < ((p ^ n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  have hιq : ι ((p ^ n : ℕ) : ℚ_[ℓ]) = (((p ^ n : ℕ) : ℝ) : ℂ) := by
    rw [map_natCast, Complex.ofReal_natCast]
  rw [hιq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos,
    div_eq_iff hqpos.ne'] at hn
  rw [hn]
  push_cast
  rw [add_div, Real.rpow_add (by exact_mod_cast hqpos), div_self two_ne_zero, Real.rpow_one]

end Sheaf

end Stacks.EtaleCohomology

end
