module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopDegreeWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing

/-!
# The weights of `Hⁱ_c` of a lisse sheaf on a curve outside degree one

For `ρ` pointwise `ι`-mixed of weights `≤ w` on a smooth curve `U` over a finite field, the weights
of `Hⁱ_c(U_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are `≤ w + i` in every degree `i ≠ 1`, given that `H⁰_c` vanishes and
that `H²_c` is the geometric coinvariants twisted by `(-1)` (Weil II 3.2.3 outside degree one).

## Main results

* `not_isRoot_charpoly_map_of_subsingleton`: an endomorphism of a zero vector space has no
  eigenvalue.
* `exists_weight_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_of_ne_one`:
  the weights of `Hⁱ_c` are `≤ w + i` for `i ≠ 1`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- An endomorphism of a zero vector space has no eigenvalue along any `ι`. -/
public theorem not_isRoot_charpoly_map_of_subsingleton {F M : Type*} [Field F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] [Subsingleton M] (g : M →ₗ[F] M) (ι : F →+* ℂ) (z : ℂ) :
    ¬ ((LinearMap.charpoly g).map ι).IsRoot z := by
  have hc : LinearMap.charpoly g = 1 := Polynomial.eq_one_of_monic_natDegree_zero
    (LinearMap.charpoly_monic g) (by rw [LinearMap.charpoly_natDegree,
      Module.finrank_zero_of_subsingleton])
  simp [hc]

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

omit [CompactSpace U.1] in
/-- **The weights of `Hⁱ_c` of `ℱ_ρ` on a curve in the degrees `i ≠ 1` are `≤ w + i`** for `ρ`
pointwise `ι`-mixed of weights `≤ w`, given that `H⁰_c` vanishes and the identification of `H²_c`
with the geometric coinvariants of `ρ`, twisted by `(-1)`. -/
public theorem exists_weight_le_of_isRoot_rationalGeometricCompactlySupportedFrobenius_of_ne_one
    [SmoothOfRelativeDimension 1 f] [IsAlgClosure k kbar]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (x : GeometricPoint U.1)
    {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
    (ι : ℚ_[ℓ] →+* ℂ) {w : ℤ} (hmix : IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ)
    (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p n hcard (x.map f))⁻¹)
    (h0 : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
      (LAdicSheaf.representationSheaf B U x ρ hρ) 0))
    (e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x ρ hρ) 2 ≃ₗ[ℚ_[ℓ]]
      Representation.Coinvariants ((matrixRepresentation ρ).comp
        (etaleFundamentalGroupMap f x).toMonoidHom.ker.subtype))
    (he : ∀ v, e ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar p n hcard
      (LAdicSheaf.representationSheaf B U x ρ hρ) 2).hom v) =
        ((p ^ n : ℕ) : ℚ_[ℓ]) •
          coinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker ρ φ (e v))
    (i : ℤ) (hi : i ≠ 1)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (LAdicSheaf.representationSheaf B U x ρ hρ) i)]
    {z : ℂ} (hz : ((ModuleCat.Hom.hom (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U
      ℓ f j kbar p n hcard (LAdicSheaf.representationSheaf B U x ρ hρ) i)).charpoly.map ι).IsRoot
        z) :
    ∃ w' : ℤ, w' ≤ w + i ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2) := by
  by_cases h2 : i = 2
  · subst h2
    exact exists_weight_le_two_of_isRoot_rationalGeometricCompactlySupportedFrobenius B U ℓ f j
      kbar p n hcard x ρ hρ ι hmix φ hφ e he hz
  · refine absurd hz (@not_isRoot_charpoly_map_of_subsingleton _ _ _ _ _ _ ?_ _ ι z)
    rcases (show i < 0 ∨ i = 0 ∨ 2 < i by lia) with h' | rfl | h'
    · exact ModuleCat.subsingleton_of_isZero
        (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x ρ hρ) i h')
    · exact h0
    · exact LAdicSheaf.subsingleton_rationalGeometricCompactlySupportedCohomology_of_two_lt B U
        ℓ f j kbar (LAdicSheaf.representationSheaf B U x ρ hρ) i h'

end Sheaf

end Stacks.EtaleCohomology

end
