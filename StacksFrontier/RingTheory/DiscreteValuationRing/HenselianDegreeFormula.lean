module

public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationCharacterization
public import StacksFrontier.RingTheory.DiscreteValuationRing.FundamentalIdentity
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolutionObstruction

/-!
# Totally ramified finite subextensions, and the finiteness step of §6

Let `A` be a henselian discrete valuation ring whose residue field is algebraically closed, with
fraction field `K`.  For a finite *separable* extension `K₁ / K` the integral closure
`C = integralClosure A K₁` is again a discrete valuation ring
(`Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure`), so the local
  fundamental identity
`[K₁ : K] = e(C/A) · f(C/A)` applies; the residue degree is `1` because the residue field
downstairs is algebraically closed.  Hence

  `[K₁ : K] = e(C/A)`  -- every finite separable extension is totally ramified.

This is the degree formula in the form that the finiteness step below uses.

The second ingredient is a *bound* on `e(C/A)`.  If `C` sits inside a discrete valuation ring
`B'` with fraction field `L ⊇ K₁`, then `e(C/A)` divides `e(B'/A)`: writing a uniformizer of `A`
as `unit · π_C ^ e(C/A)` inside `C` and pushing the factorisation into `B'` exhibits `e(B'/A)` as
a multiple of `e(C/A)`.  When `B'` is a discrete valuation ring with fraction field `L` it is
integrally closed, so *every* `C` of this shape does sit inside it, and the bound is uniform over
all finite subextensions of `L / K`.

Together with `IntermediateField.finiteDimensional_and_finrank_le_of_forall_adjoin_finrank_le`
(the bounded-degree lemma) these give the headline result: a separable algebraic extension
`L / K` whose valuation ring `B'` has finite ramification index over `A` is *finite*, of degree
at most `e(B'/A)`.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.exists_addVal_eq`: the additive valuation of a nonzero
  element is a natural number.
* `Stacks.DiscreteValuationRing.Ramification.exists_unit_mul_pow_eq_of_addVal`: the corresponding
  factorisation.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_dvd_of_forall_mem_range`: `e(C/A) ∣
  e(B'/A)` for an intermediate
  discrete valuation ring `C` whose image in `L` lands in `B'`.
* `finrank_eq_ramificationIdx_of_isAlgClosed_residueField`: `[L : K] = e(B/A)` for a
  module-finite flat local extension over a base with algebraically closed residue field.
* `Stacks.DiscreteValuationRing.Ramification.finrank_eq_ramificationIdx_integralClosure`: the same
  for the integral closure in a
  finite separable extension of the fraction field of a henselian base.
* `Stacks.WeakSolution.Obstruction.ramificationIdx_integralClosure_dvd`: the uniform bound, from
  integral closedness
  of `B'`.
* `Stacks.WeakSolution.Obstruction.finiteDimensional_and_finrank_le_ramificationIdx`: **the
  finiteness step of §6** —
  a separable algebraic extension of the fraction field of a henselian discrete valuation ring
  with algebraically closed residue field is finite, of degree at most the ramification index of
  its valuation ring.

## References

* [The Stacks Project, Tag 09E5](https://stacks.math.columbia.edu/tag/09E5)
* [The Stacks Project, Tag 09E8](https://stacks.math.columbia.edu/tag/09E8)
-/

@[expose] public section

open IsLocalRing IsDiscreteValuationRing

universe u

namespace Stacks.DiscreteValuationRing.Ramification

/-! ### Reading off a uniformizer factorisation from the additive valuation -/

/-- The additive valuation of `u * x ^ n` for a unit `u` is `n` times that of `x`. -/
private theorem addVal_unit_mul_pow {B : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] (u : Bˣ) {x : B} (n : ℕ) :
    addVal B (u * x ^ n) = n • addVal B x := by
  rw [addVal_mul, addVal_pow, addVal_eq_zero_of_unit, zero_add]

/-- The additive valuation of a nonzero element of a discrete valuation ring is a natural
number. -/
theorem exists_addVal_eq (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {y : B} (hy : y ≠ 0) : ∃ m : ℕ, addVal B y = (m : ℕ∞) := by
  obtain ⟨π, hπp⟩ := exists_prime B
  obtain ⟨m, u, hm⟩ := eq_unit_mul_pow_irreducible hy hπp.irreducible
  exact ⟨m, by rw [hm, addVal_unit_mul_pow u, addVal_uniformizer hπp.irreducible,
    nsmul_eq_mul, mul_one]⟩

/-- An element of additive valuation `n` is a unit times the `n`-th power of any uniformizer. -/
theorem exists_unit_mul_pow_eq_of_addVal (B : Type*) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] {y : B} (hy : y ≠ 0) {π : B} (hπ : Irreducible π) {n : ℕ}
    (hn : addVal B y = (n : ℕ∞)) : ∃ u : Bˣ, y = (u : B) * π ^ n := by
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible hy hπ
  obtain rfl : k = n := by exact_mod_cast (addVal_def y u hπ k hk).symm.trans hn
  exact ⟨u, hk⟩

/-! ### The ramification bound from an ambient discrete valuation ring -/

section Bound

variable (A C B' L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing B'] [IsDomain B'] [IsDiscreteValuationRing B']
  [Algebra A C] [FaithfulSMul A C] [IsLocalHom (algebraMap A C)]
  [Algebra A B'] [FaithfulSMul A B']
  [Field L] [Algebra B' L] [IsFractionRing B' L]
  [Algebra A L] [IsScalarTower A B' L]

include L in
/-- **The ramification bound.** Let `A ⊆ C` and `A ⊆ B'` be extensions of discrete valuation
rings, with `L` the fraction field of `B'`.  If some `A`-compatible ring map `ι : C → L` takes
every element of `C` into `B'`, then `e(C/A)` divides `e(B'/A)`.

The proof pushes the factorisation `π_A = u · π_C ^ e(C/A)` of a uniformizer of `A` inside `C`
forward along `ι` and pulls it back into `B'`, where the unit stays a unit; comparing additive
valuations of the two sides exhibits `e(B'/A)` as `e(C/A)` times the valuation of the image of
`π_C`.

No relation between `C` and `B'` beyond `ι` is assumed, and `ι` need not be injective. -/
theorem ramificationIdx_dvd_of_forall_mem_range (ι : C →+* L)
    (hι : ∀ a : A, ι (algebraMap A C a) = algebraMap A L a)
    (h : ∀ x : C, ∃ y : B', algebraMap B' L y = ι x) :
    ramificationIdx A C ∣ ramificationIdx A B' := by
  obtain ⟨πA, hπAp⟩ := exists_prime A
  have hπA : Irreducible πA := hπAp.irreducible
  obtain ⟨πC, hπCp⟩ := exists_prime C
  set d := ramificationIdx A C
  have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramificationIdx A C)
  have hAC : algebraMap A C πA ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A C)).2 hπA.ne_zero
  obtain ⟨u, hu⟩ := exists_unit_mul_pow_eq_of_addVal C hAC hπCp.irreducible
    (addVal_algebraMap_eq_ramificationIdx A C πA hπA)
  have hinj : Function.Injective (algebraMap B' L) := IsFractionRing.injective B' L
  obtain ⟨yu, hyu⟩ := h (u : C)
  obtain ⟨yu', hyu'⟩ := h ((u⁻¹ : Cˣ) : C)
  obtain ⟨yπ, hyπ⟩ := h πC
  have hunit : yu * yu' = 1 := by
    apply hinj
    rw [map_mul, hyu, hyu', ← map_mul]
    simp
  have hkey : algebraMap A B' πA = yu * yπ ^ d := by
    apply hinj
    rw [map_mul, map_pow, hyu, hyπ, ← IsScalarTower.algebraMap_apply A B' L, ← hι πA, hu,
      map_mul, map_pow]
  have hyπne : yπ ≠ 0 := by
    rintro rfl
    refine (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B')).2 hπA.ne_zero ?_
    rw [hkey, zero_pow hd0, mul_zero]
  obtain ⟨m, hm⟩ := exists_addVal_eq B' hyπne
  have hval := addVal_algebraMap_eq_ramificationIdx A B' πA hπA
  rw [hkey, addVal_unit_mul_pow ⟨yu, yu', hunit, (mul_comm yu' yu).trans hunit⟩, hm,
    nsmul_eq_mul] at hval
  exact ⟨m, by exact_mod_cast hval.symm⟩

end Bound

/-! ### Every finite separable extension is totally ramified -/

section DegreeFormula

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
  [IsScalarTower A B L] [IsScalarTower A K L]

/-- **Total ramification.** For a module-finite flat local extension of discrete valuation rings
over a base with algebraically closed residue field, the degree of the fraction fields equals the
ramification index: the residue degree in `[L : K] = e f` is `1`.

This is the degree formula `[L : K] = e f` combined with the observation that an algebraically
closed residue field admits no nontrivial finite extension. -/
theorem finrank_eq_ramificationIdx_of_isAlgClosed_residueField [IsLocalHom (algebraMap A B)]
    [Module.Finite A B] [Module.Flat A B]
    [IsAlgClosed (maximalIdeal A).ResidueField] :
    Module.finrank K L = ramificationIdx A B := by
  rw [← ramificationIdx_mul_inertiaDeg_eq_finrank A B K L,
    inertiaDeg_eq_one_of_isAlgClosed_residueField A B, mul_one]

end DegreeFormula

section IntegralClosureDegree

variable (A K K₁ : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A] [IsAlgClosed (maximalIdeal A).ResidueField]
  [Field K] [Field K₁] [Algebra A K] [IsFractionRing A K]
  [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [FiniteDimensional K K₁]
  [Algebra.IsSeparable K K₁]

include A K K₁ in
/-- The integral closure of a henselian discrete valuation ring with algebraically closed residue
field, taken in a finite separable extension `K₁` of its fraction field, is a discrete valuation
ring of ramification index exactly `[K₁ : K]`.

Packaged as an existential over the instances so that the statement needs no instance argument
for `IsLocalRing (integralClosure A K₁)`; the instances themselves are available individually
from `StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure`. -/
theorem finrank_eq_ramificationIdx_integralClosure :
    ∃ _ : IsLocalRing (integralClosure A K₁),
      Module.finrank K K₁ = ramificationIdx A (integralClosure A K₁) := by
  refine ⟨isLocalRing_integralClosure A K₁, ?_⟩
  have _ := faithfulSMul_integralClosure A K K₁
  have _ := isDiscreteValuationRing_integralClosure A K K₁
  have _ := isFractionRing_integralClosure A K K₁
  have _ := isLocalHom_algebraMap_integralClosure A K K₁
  have _ := module_finite_integralClosure A K K₁
  have _ := flat_integralClosure A K K₁
  exact finrank_eq_ramificationIdx_of_isAlgClosed_residueField A (integralClosure A K₁) K K₁

end IntegralClosureDegree

end Stacks.DiscreteValuationRing.Ramification

namespace Stacks.WeakSolution.Obstruction

/-! ### The finiteness step of §6 -/

section Section6

variable (A B' K L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A] [IsAlgClosed (maximalIdeal A).ResidueField]
  [CommRing B'] [IsDomain B'] [IsDiscreteValuationRing B']
  [Algebra A B'] [FaithfulSMul A B'] [IsLocalHom (algebraMap A B')]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra B' L] [IsFractionRing B' L] [Algebra A L] [Algebra K L]
  [IsScalarTower A B' L] [IsScalarTower A K L] [Algebra.IsSeparable K L]

omit [IsAlgClosed (maximalIdeal A).ResidueField] [IsLocalHom (algebraMap A B')]
  [Algebra.IsSeparable K L] in
include A B' K L in
/-- The image in `L` of the integral closure of `A` in an intermediate field `J` lands inside
`B'`, because `B'` is integrally closed with fraction field `L`.  Hence
`e(integralClosure A J / A)` divides `e(B'/A)`.

This is the uniform bound §6 needs: one finite integer bounding the ramification index of every
finite subextension. -/
theorem ramificationIdx_integralClosure_dvd (J : IntermediateField K L)
    [FiniteDimensional K J] :
    ∃ _ : IsLocalRing (integralClosure A (J : Type u)),
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx A (integralClosure A (J : Type u)) ∣
        Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B' := by
  refine ⟨Stacks.DiscreteValuationRing.Ramification.isLocalRing_integralClosure A (J : Type u), ?_⟩
  have _ := Stacks.DiscreteValuationRing.Ramification.faithfulSMul_integralClosure A K (J : Type u)
  have _ := Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure A K
    (J : Type u)
  have _ := Stacks.DiscreteValuationRing.Ramification.isLocalHom_algebraMap_integralClosure A K
    (J : Type u)
  have htower : IsScalarTower A (J : Type u) L :=
    IsScalarTower.of_algebraMap_eq fun y => by
      simp [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K (J : Type u)]
  refine Stacks.DiscreteValuationRing.Ramification.ramificationIdx_dvd_of_forall_mem_range A _ B' L
    ((algebraMap (J : Type u) L).comp (algebraMap (integralClosure A (J : Type u)) (J : Type u)))
    (fun a => ?_) (fun x => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A (integralClosure A (J : Type u)) (J : Type u),
      ← IsScalarTower.algebraMap_apply A (J : Type u) L]
  · exact IsIntegrallyClosed.isIntegral_iff.mp
      (IsIntegral.tower_top (R := A) (x.2.map (IsScalarTower.toAlgHom A (J : Type u) L)))

include A B' K L in
/-- **The finiteness step.**

Let `A` be a henselian discrete valuation ring with *algebraically closed* residue field and
fraction field `K`, and let `B'` be a discrete valuation ring extension of `A` whose fraction
field `L` is *separable* over `K`.  Then `L / K` is finite, of degree at most `e(B'/A)`.

In the note, `A = B = 𝒪_{L₁}` and `B' = 𝒪_{L'}`; the residue field of `B` is already
algebraically closed, so condition (2) of 09ET forces `κ_{B'} = κ_B` and every finite
intermediate extension `J / L₁` satisfies `[J : L₁] = e(J / L₁) ≤ e(B'/B)`.  Those two facts are
proved here rather than assumed: the degree identity is
`Stacks.DiscreteValuationRing.Ramification.finrank_eq_ramificationIdx_integralClosure` (the local
  fundamental identity with
residue degree `1`), and the bound is `ramificationIdx_integralClosure_dvd` (integral closedness
of `B'`).  The passage from a uniform bound on finite subextensions to finiteness of the whole
extension is `IntermediateField.finiteDimensional_and_finrank_le_of_forall_adjoin_finrank_le`.

The hypothesis that `L / K` is algebraic is contained in separability; no bound on the degrees of
finite subextensions is assumed. -/
theorem finiteDimensional_and_finrank_le_ramificationIdx :
    FiniteDimensional K L ∧ Module.finrank K L ≤
      Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B' := by
  refine IntermediateField.finiteDimensional_and_finrank_le_of_forall_adjoin_finrank_le
    (N := Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B') fun s => ?_
  have hJfd : FiniteDimensional K (IntermediateField.adjoin K (s : Set L)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨_, hdeg⟩ :=
    Stacks.DiscreteValuationRing.Ramification.finrank_eq_ramificationIdx_integralClosure A K
    (IntermediateField.adjoin K (s : Set L) : Type u)
  obtain ⟨_, hdvd⟩ := ramificationIdx_integralClosure_dvd A B' K L
    (IntermediateField.adjoin K (s : Set L))
  rw [hdeg]
  exact Nat.le_of_dvd (Stacks.DiscreteValuationRing.Ramification.one_le_ramificationIdx A B') hdvd

end Section6

end Stacks.WeakSolution.Obstruction
