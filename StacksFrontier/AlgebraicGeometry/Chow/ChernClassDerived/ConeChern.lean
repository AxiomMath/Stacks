module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DirectSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeComplex

/-!
# The total Chern class and the power sums of a mapping cone

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`α : 𝓔₁^• ⟶ 𝓔₂^•` be a map of locally bounded complexes of finite locally free `𝒪_Y`-modules. Its
mapping cone `C(α)^•` has terms `C(α)^n = 𝓔₁^{n+1} ⊕ 𝓔₂^n`, so it is again a locally bounded
complex of finite locally free modules, and

  `c(𝓔₂^•) = c(𝓔₁^•) c(C(α)^•)`,   `P_p(𝓔₂^•) = P_p(𝓔₁^•) + P_p(C(α)^•)`.

This is the computation in the first paragraph of the proof of Stacks 0F9F: the total Chern
class and the power sums of a complex only see its terms, so those of `C(α)^•` are those of the
termwise biproduct `𝓔₁^•[1] ⊕ 𝓔₂^•`, and the shift inverts them because the cone of the identity
of `𝓔₁^•` is acyclic.

## Main results

* `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_shift`,
  `Stacks.Chow.isLocallyBoundedFiniteLocallyFree_mappingCone` — shifts and mapping cones of
  locally bounded complexes of finite locally free modules are again such complexes.
* `Stacks.Chow.complexChern_shift_mul` — `c(𝓔^•[1]) c(𝓔^•) = 1`.
* `Stacks.Chow.complexChern_eq_mul_mappingCone` — `c(𝓔₂^•) = c(𝓔₁^•) c(C(α)^•)`.
* `Stacks.Chow.powerSumComplex_eq_add_mappingCone` — `P_p(𝓔₂^•) = P_p(𝓔₁^•) + P_p(C(α)^•)`.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y : Scheme.{u}}

/-- **A complex whose terms are isomorphic to those of a locally bounded complex of finite
locally free modules is one again**, the two conditions only seeing the terms. -/
theorem IsLocallyBoundedFiniteLocallyFree.of_iso_X {P P' : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (e : ∀ n, P.X n ≅ P'.X n) :
    IsLocallyBoundedFiniteLocallyFree P' := by
  refine ⟨fun n ↦ ?_, fun x ↦ ?_⟩
  · let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (e n)
  · obtain ⟨U, hxU, lo, hi, hU⟩ := hP.2 x
    exact ⟨U, hxU, lo, hi, fun n hn ↦
      (hU n hn).of_iso ((RingedSpace.restrictModules Y.toRingedSpace U).mapIso (e n)).symm⟩

/-- **The shift of a locally bounded complex of finite locally free modules is one again**: its
`n`-th term is the `(n + m)`-th term of the complex. -/
theorem isLocallyBoundedFiniteLocallyFree_shift {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (m : ℤ) :
    IsLocallyBoundedFiniteLocallyFree ((shiftFunctor (CochainComplex Y.Modules ℤ) m).obj P) := by
  refine ⟨fun n ↦ hP.1 (n + m), fun x ↦ ?_⟩
  obtain ⟨U, hxU, lo, hi, hU⟩ := hP.2 x
  refine ⟨U, hxU, lo - m, hi - m, fun n hn ↦ hU (n + m) ?_⟩
  omega

/-- The `n`-th term of the mapping cone of `α : P ⟶ Q` is the `n`-th term of the termwise
biproduct `P[1] ⊕ Q`. -/
def mappingConeXIsoBiprodShift {P Q : CochainComplex Y.Modules ℤ} (α : P ⟶ Q) (n : ℤ) :
    (CochainComplex.mappingCone α).X n ≅
      ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj P ⊞ Q).X n :=
  haveI : HasBinaryBiproducts Y.Modules := inferInstance
  (HomologicalComplex.homotopyCofiber.XIsoBiprod α n (n + 1) (by simp) :
      (CochainComplex.mappingCone α).X n ≅ P.X (n + 1) ⊞ Q.X n) ≪≫
    (HomologicalComplex.biprodXIso
      ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj P) Q n).symm

variable (C : ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The total Chern class of the mapping cone of `α : P ⟶ Q` is `c(P[1]) c(Q)`. -/
theorem complexChern_mappingCone_eq_shift_mul {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (α : P ⟶ Q) :
    complexChern C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α hP hQ) =
      complexChern C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) * complexChern C sY hQ := by
  rw [← complexChern_biprod C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) hQ]
  exact complexChern_congr C sY _ _ (mappingConeXIsoBiprodShift α)

/-- The power sums of the mapping cone of `α : P ⟶ Q` are `P_p(P[1]) + P_p(Q)`. -/
theorem powerSumComplex_mappingCone {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (α : P ⟶ Q) (p : ℕ) :
    powerSumComplex C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α hP hQ) p =
      powerSumComplex C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) p +
        powerSumComplex C sY hQ p := by
  rw [← powerSumComplex_biprod C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) hQ]
  exact powerSumComplex_congr C sY _ _ (mappingConeXIsoBiprodShift α) p

/-- The mapping cone of the identity of a complex is zero in the derived category. -/
theorem isZero_Q_obj_mappingCone_id (P : CochainComplex Y.Modules ℤ) :
    IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone (𝟙 P))) :=
  Pretriangulated.Triangle.isZero₃_of_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished (𝟙 P))
    (by change IsIso (DerivedCategory.Q.map (𝟙 P)); infer_instance)

/-- **The shift inverts the total Chern class**: `c(P[1]) c(P) = 1`, the mapping cone of the
identity of `P`, whose terms are those of `P[1] ⊕ P`, being zero in the derived category. -/
theorem complexChern_shift_mul {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) :
    complexChern C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) * complexChern C sY hP =
      1 := by
  have h := complexChern_mappingCone_eq_shift_mul C sY hP hP (𝟙 P)
  rw [complexChern_of_isZero C sY _ (isZero_Q_obj_mappingCone_id P)] at h
  exact h.symm

/-- **The shift negates the power sums**: `P_p(P[1]) + P_p(P) = 0`. -/
theorem powerSumComplex_shift_add {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (p : ℕ) :
    powerSumComplex C sY (isLocallyBoundedFiniteLocallyFree_shift hP 1) p +
      powerSumComplex C sY hP p = 0 := by
  have h := powerSumComplex_mappingCone C sY hP hP (𝟙 P) p
  rw [powerSumComplex_of_isZero C sY _ (isZero_Q_obj_mappingCone_id P) p] at h
  exact h.symm

/-- In a monoid, a right inverse of a unit is a two-sided inverse. -/
private theorem mul_eq_one_of_isUnit_of_mul_eq_one {M : Type*} [Monoid M] {a b : M}
    (ha : IsUnit a) (h : b * a = 1) : a * b = 1 := by
  obtain ⟨u, rfl⟩ := ha
  calc (u : M) * b = u * (b * u * ↑u⁻¹) := by rw [mul_assoc b, u.mul_inv, mul_one]
    _ = 1 := by rw [h, one_mul, u.mul_inv]

/-- **The total Chern class of a mapping cone** (the computation in the proof of Stacks 0F9F):
for a map `α : P ⟶ Q` of locally bounded complexes of finite locally free modules,
`c(Q) = c(P) c(C(α))`. -/
theorem complexChern_eq_mul_mappingCone {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (α : P ⟶ Q) :
    complexChern C sY hQ =
      complexChern C sY hP *
        complexChern C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α hP hQ) := by
  have h2 := mul_eq_one_of_isUnit_of_mul_eq_one (isUnit_complexChern C sY hP)
    (complexChern_shift_mul C sY hP)
  rw [complexChern_mappingCone_eq_shift_mul C sY hP hQ α, ← mul_assoc, h2, one_mul]

/-- **The power sums of a mapping cone** (the computation in the proof of Stacks 0F9F): for a map
`α : P ⟶ Q` of locally bounded complexes of finite locally free modules,
`P_p(Q) = P_p(P) + P_p(C(α))`. -/
theorem powerSumComplex_eq_add_mappingCone {P Q : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) (hQ : IsLocallyBoundedFiniteLocallyFree Q)
    (α : P ⟶ Q) (p : ℕ) :
    powerSumComplex C sY hQ p =
      powerSumComplex C sY hP p +
        powerSumComplex C sY (isLocallyBoundedFiniteLocallyFree_mappingCone α hP hQ) p := by
  rw [powerSumComplex_mappingCone C sY hP hQ α p, ← add_assoc, add_comm (powerSumComplex C sY hP p),
    powerSumComplex_shift_add, zero_add]

end Stacks.Chow

end
