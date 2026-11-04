module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Torsion of `Pic(X)` from the torsion of the Jacobian

The proof of [Stacks, Tag 0C1Z] identifies the `m`-torsion of the Picard group of a smooth
projective curve `X` with the `m`-torsion of the group of `k`-points of the Jacobian
`J = Pic⁰_{X/k}`: an `m`-torsion class has degree zero, so it lies in `Pic⁰(X)`, which is
`J(k)`.  This file performs that transport for the actual Picard group `Stacks.Picard.ofScheme X`
and its degree homomorphism `Stacks.Picard.ofSchemeDegree`, against a group scheme `J` over `k`
given together with the identification of its `k`-points with `Pic⁰(X)`.

The two results below are the two clauses of Tag 0C1Z read off from the corresponding torsion
statements for `J`; they are the last step of the assembly in
`StacksFrontier/AlgebraicGeometry/Picard/TorsionSmoothProjectiveCurve.lean`.

## Main definitions

* `Stacks.Picard.torsionByOfSchemeAddEquivPoints`: the `m`-torsion of `Pic(X)` is the
  `m`-torsion of `J(k)`, for `m ≠ 0`, given `e : Pic⁰(X) ≃+ J(k)`.

## Main results

* `Stacks.Picard.nonempty_torsionBy_ofScheme_addEquiv_pi_zmod_of_addEquiv_points`
* `Stacks.Picard.exists_rank_torsionBy_ofScheme_prime_pow_of_addEquiv_points`

## References

* [Stacks Project, Lemma 53.17.1 (Tag 0C1Z)](https://stacks.math.columbia.edu/tag/0C1Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Picard

/-- The additive `m`-torsion subgroup and the `ℤ`-submodule `m`-torsion of an abelian group are
the same subset, so the same group. -/
def addSubgroupTorsionByAddEquivSubmodule (A : Type*) [AddCommGroup A] (m : ℤ) :
    AddSubgroup.torsionBy A m ≃+ Submodule.torsionBy ℤ A m where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- **The `m`-torsion of `Pic(X)` is the `m`-torsion of the group of `k`-points of the
Jacobian**, for `m ≠ 0`, given an identification `e` of `Pic⁰(X) = ker deg` with those points. -/
def torsionByOfSchemeAddEquivPoints {H : Type*} [AddCommGroup H]
    (e : ofSchemeDegreeZero k f hdim ≃+ H) {m : ℤ} (hm : m ≠ 0) :
    Submodule.torsionBy ℤ (ofScheme X) m ≃+ Submodule.torsionBy ℤ H m :=
  torsionByDegreeKerAddEquiv (ofSchemeDegree k f hdim) e hm

/-- **Clause (1) of Tag 0C1Z, from the torsion of the Jacobian.** Let `X` be proper of dimension
at most one over `k`, and `J` a commutative group scheme over `k` with an identification
`e : Pic⁰(X) ≃+ J(k)`.  If `J(k)[n] ≅ (ℤ/nℤ)^{⊕2 dim J}` and `dim J = genus X`, then
`Pic(X)[n] ≅ (ℤ/nℤ)^{⊕2g}`. -/
theorem nonempty_torsionBy_ofScheme_addEquiv_pi_zmod_of_addEquiv_points
    (J : Over (Spec (.of k))) [GrpObj J] [IsCommMonObj J]
    (e : ofSchemeDegreeZero k f hdim ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))
    (hJ : Stacks.Groupoids.abelianVarietyDimension J = genus f) (n : ℕ) (hn : n ≠ 0)
    (htors : Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) (n : ℤ)
      ≃+ (Fin (2 * Stacks.Groupoids.abelianVarietyDimension J) → ZMod n))) :
    Nonempty (Submodule.torsionBy ℤ (ofScheme X) (n : ℤ) ≃+ (Fin (2 * genus f) → ZMod n)) := by
  obtain ⟨t⟩ := htors
  rw [← hJ]
  exact ⟨(torsionByOfSchemeAddEquivPoints f hdim e (by exact_mod_cast hn)).trans t⟩

/-- **Clause (2) of Tag 0C1Z, from the torsion of the Jacobian.** In the situation of
`Stacks.Picard.nonempty_torsionBy_ofScheme_addEquiv_pi_zmod_of_addEquiv_points`, if some
`r ≤ dim J` has `J(k)[p^m] ≅ (ℤ/p^mℤ)^{⊕r}` for all `m ≥ 1`, then the same `r ≤ g` has
`Pic(X)[p^m] ≅ (ℤ/p^mℤ)^{⊕r}` for all `m ≥ 1`. -/
theorem exists_rank_torsionBy_ofScheme_prime_pow_of_addEquiv_points
    (J : Over (Spec (.of k))) [GrpObj J] [IsCommMonObj J]
    (e : ofSchemeDegreeZero k f hdim ≃+ Additive (𝟙_ (Over (Spec (.of k))) ⟶ J))
    (hJ : Stacks.Groupoids.abelianVarietyDimension J = genus f) (p : ℕ) (hp : 0 < p)
    (htors : ∃ r : ℕ, r ≤ Stacks.Groupoids.abelianVarietyDimension J ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty (Submodule.torsionBy ℤ (Additive (𝟙_ (Over (Spec (.of k))) ⟶ J)) ((p : ℤ) ^ m)
        ≃+ (Fin r → ZMod (p ^ m)))) :
    ∃ r : ℕ, r ≤ genus f ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty (Submodule.torsionBy ℤ (ofScheme X) ((p : ℤ) ^ m) ≃+ (Fin r → ZMod (p ^ m))) := by
  obtain ⟨r, hr, h⟩ := htors
  refine ⟨r, hJ ▸ hr, fun m hm => ?_⟩
  obtain ⟨t⟩ := h m hm
  have hnz : ((p : ℤ) ^ m) ≠ 0 := pow_ne_zero m (by exact_mod_cast hp.ne')
  exact ⟨(torsionByOfSchemeAddEquivPoints f hdim e hnz).trans t⟩

end Stacks.Picard

end
