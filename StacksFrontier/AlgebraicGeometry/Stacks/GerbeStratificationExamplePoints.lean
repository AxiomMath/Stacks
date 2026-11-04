module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.LocallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationExample

/-!
# Points, stabilizers and strata of the weighted action of Stacks 06RE

`StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationExample` constructs the action of the
multiplicative group on `U = Spec(k[x_0, x_1, x_2, …])` in which `x_i` has weight `p^i`. This file
reads that action on points and proves what the example asserts about `U` and the action: the
strata, their invariance, that they partition the space, that each is locally closed and integral,
that the stabilizer along `X_i` is `μ_{p^i}` and along `X_∞` is `G_m`, and that the stabilizers of
points of two different strata differ.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.smulPoint`: the action read on the points of `U` with
  values in a commutative ring, `t · (a_0, a_1, …) = (t^{p^i} a_i)`, and
  `AlgebraicGeometry.PPowerWeighted.pointStabilizer` its stabilizer, a subgroup of the units.
* `AlgebraicGeometry.PPowerWeighted.IsPointInStratum` and
  `AlgebraicGeometry.PPowerWeighted.IsPointInStratumInf`: the strata read on points — the
  coordinates before the `i`-th vanish and the `i`-th is invertible, respectively all the
  coordinates vanish.
* `AlgebraicGeometry.PPowerWeighted.stratum` and
  `AlgebraicGeometry.PPowerWeighted.stratumInf`: the same strata as subsets of the spectrum.
* `AlgebraicGeometry.PPowerWeighted.stratumQuotient` and
  `AlgebraicGeometry.PPowerWeighted.stratumRing`: the coordinate rings of the closure of the
  `i`-th stratum and of the stratum itself.

## Main results

* `AlgebraicGeometry.PPowerWeighted.pointEval_action_μ_X`: the action on points is the one the
  coaction defines, so `smulPoint` is the registered action and not a second one.
* `AlgebraicGeometry.PPowerWeighted.pointStabilizer_eq_rootsUnitsSubgroup`: on the `i`-th
  stratum the stabilizer of the action is `μ_{p^i}`, and
  `AlgebraicGeometry.PPowerWeighted.pointStabilizer_eq_top`: on the last stratum it is `G_m`.
* `AlgebraicGeometry.PPowerWeighted.isPointInStratum_smulPoint` and
  `AlgebraicGeometry.PPowerWeighted.isPointInStratumInf_smulPoint`: the strata are invariant.
* `AlgebraicGeometry.PPowerWeighted.isLocallyClosed_stratum` and
  `AlgebraicGeometry.PPowerWeighted.isClosed_stratumInf`: the strata are locally closed, the
  last one closed; `AlgebraicGeometry.PPowerWeighted.iUnion_stratum_union_stratumInf` and
  `AlgebraicGeometry.PPowerWeighted.disjoint_stratum` say they partition the spectrum.
* `AlgebraicGeometry.PPowerWeighted.mem_stratum_ker_iff` and
  `AlgebraicGeometry.PPowerWeighted.mem_stratumInf_ker_iff`: the two readings of the strata, on
  points and on the spectrum, agree.
* `AlgebraicGeometry.PPowerWeighted.isDomain_stratumRing` and
  `AlgebraicGeometry.PPowerWeighted.isReduced_stratumRing`: the `i`-th stratum is integral, in
  particular reduced.
* `AlgebraicGeometry.PPowerWeighted.rootsUnitsSubgroup_pow_ne` and
  `AlgebraicGeometry.PPowerWeighted.rootsUnitsSubgroup_ne_top`: the groups `μ_{p^i}` of
  distinct strata, and `G_m`, are pairwise distinct.
* `AlgebraicGeometry.PPowerWeighted.pointStabilizer_ne_pointStabilizer_basisPoint` and
  `AlgebraicGeometry.PPowerWeighted.pointStabilizer_ne_pointStabilizer_basisPoint_zero`: two
  different strata carry points with different stabilizers, so no two strata can be merged into
  a single locus along which the stabilizer is one group — the source's assertion that there is
  no coarser stratification with the same properties.

## Implementation notes

A point of `U` with values in a commutative ring `R` is a family `a : ℕ → R` of coordinates,
and `μ_n` on such a point is the subgroup `AlgebraicGeometry.rootsUnitsSubgroup n` of `Rˣ`,
which `AlgebraicGeometry.rootsOfUnitySections_representableBy_rootsOfUnity` identifies with the
group scheme of `n`-th roots of unity.  `G_m` is the whole unit group, which
`AlgebraicGeometry.unitsOfGlobalSections_representableBy_multiplicativeGroup` identifies with
the multiplicative group scheme.  So the stabilizer computations below are the source's
assertion that the stratum `X_i` has group `μ_{p^i}` and `X_∞` has group `G_m`, read through
the functors of points of those group schemes.

What is proved here is everything the example asserts about `U` and the action: the strata,
their invariance, that they partition the space, that each is locally closed and integral, that
the stabilizer along `X_i` is `μ_{p^i}` and along `X_∞` is `G_m`, and that the stabilizers of
points of two different strata differ — which is the source's last assertion, that there is no
coarser stratification with the same properties.

The quotient stack `[U/G_m]` itself is not formed in this file but in
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeStratificationQuotientStack.lean`, which imports it;
its algebraicity does **not** go through Artin's representability theorem.  Stacks 04TK,
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isSmooth_unconditional` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/SmoothQuotientStackModel.lean`, says that
the quotient stack of a *smooth* groupoid in algebraic spaces is an algebraic stack, and it takes no
hypothesis beyond that smoothness; `G_m` is smooth, so the algebraicity of `[U/G_m]` does not go
through Stacks 06FI
(`StacksFrontier/AlgebraicGeometry/Stacks/QuotientStackDiagonalUnconditional.lean`), which is the
*flat* criterion and is the one carrying Artin's theorem Stacks 06DC as a hypothesis.  Likewise
Stacks 06QJ, the theorem
`isGerbe_iff_isFlat_and_isLocallyOfFinitePresentation_inertiaProjection` of
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeInertiaCharacterization.lean` in the
namespace `AlgebraicGeometry.Stack.AlgebraicStacks`, is unconditional in both directions and
takes only the algebraic stack as an argument.

What had to be supplied is the presentation of the action in the form Stacks 044Q, part (2),
takes, and the smoothness hypothesis of 04TK.  The second of those is in place:
`AlgebraicGeometry.Space.isSmooth_groupoidOfAction` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/SmoothActionGroupoid.lean` is Stacks
04TH for the action groupoid of Stacks 0444 — its source and target morphisms are smooth as soon
as `G ⟶ B` is — and
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction_of_isSmooth` of
`StacksFrontier/AlgebraicGeometry/Stacks/SmoothActionQuotientStackAlgebraic.lean` is 04TK for a
group action: the quotient stack `[X/G]` of an action of a group algebraic space with smooth
structure morphism is an algebraic stack, with nothing carried.

The first is now in place in general.  Part (2) consumes the group and the acted-on space as
objects of the slice of *presheaves on the big fppf site* over the base, with
`CategoryTheory.GrpObj` and `CategoryTheory.ModObj` structures there, while the action of this
file is a `CategoryTheory.ModObj` in a slice of `Scheme`
(`AlgebraicGeometry.GradedGmAction.action`).
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/ModuleBaseChange.lean` bridges the
two in the two steps that `BaseChange.lean` bridges them in for the group alone:
`CategoryTheory.opCompYonedaModObj` is the module counterpart of
`CategoryTheory.grpObjCompForget`, carrying an action in a slice of `Scheme` to an action of
presheaves on the site along the restriction to the site of the functor of points, and
`CategoryTheory.overProdFstModObj` is the module counterpart of
`CategoryTheory.overProdFstGrpObj`; their composite
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSiteModObj` is the module
counterpart of `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`, over the very
group object the latter produces.  `CategoryTheory.opCompYoneda_smul_app` and
`CategoryTheory.overProdFst_smul_left_comp_snd` pin the two transported actions down to the
pointwise ones.  So `AlgebraicGeometry.Stack.quotientStackOfGroupSchemeInSite` of
`StacksFrontier/AlgebraicGeometry/Stacks/SmoothActionQuotientStackAlgebraic.lean` forms the quotient
stack `[Q/G_B]` of an action of a group scheme of the site on a scheme of the site, with both
algebraicity hypotheses of part (2) discharged, and
`isAlgebraicStack_quotientStackOfGroupSchemeInSite_of_isSmooth` there is 04TK for it.

The quotient stack `[U/G_m]` of this file's action is formed, and shown to be an algebraic
stack, in `StacksFrontier/AlgebraicGeometry/Stacks/GerbeStratificationQuotientStack.lean`:
`AlgebraicGeometry.PPowerWeighted.quotientStack` and
`AlgebraicGeometry.PPowerWeighted.isAlgebraicStack_quotientStack`.  The two things that were
owed are in place.  Smoothness of `B ×_S G_m ⟶ B`, that is of `prod.fst : B ⨯ P ⟶ B` for the
group object `ofGroupSchemeInSite` carries, is
`AlgebraicGeometry.Space.isSmooth_prod_fst_pointsOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupSpaces/SmoothProductProjection.lean` — the
binary product is the fibre product over the terminal presheaf, so the projection is a base
change and Stacks 03ZE applies — instantiated at `G_m` by
`AlgebraicGeometry.Space.isSmooth_prod_fst_multiplicativeGroupULift`, whose scheme-level input
is that the Laurent polynomial ring is a smooth algebra.  And the `asOver` spelling that
`AlgebraicGeometry.GradedGmAction.action` uses is matched with no transport:
`AlgebraicGeometry.Space.multiplicativeGroupULiftSiteObject` is built from the structure
morphism of `G_m` itself, so `AlgebraicGeometry.Space.toSchemeOver` of it is definitionally
`G_m.asOver (Spec ℤ)`, and `AlgebraicGeometry.Stack.quotientStackOfGroupSchemeInSiteOnOver`
takes the acted-on scheme as an object of the slice over the base for the same reason.

The one hypothesis carried there is `𝒞.Contains (Spec (MvPolynomial ℕ k))`, which makes `U` an
object of the site.  That is a genuine hypothesis and not a gap: `k[x_0, x_1, x_2, …]` is not of
finite type over `ℤ`, so `AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` does not place it
in every site, and the source's example likewise fixes `k` and asks the ambient site to be large
enough for the construction.  `G_m` needs no such hypothesis, by
`AlgebraicGeometry.Space.contains_multiplicativeGroupULift`.

What remains downstream is to exhibit the strata as substacks of `[U/G_m]` and to state that
each of them is a gerbe.  Both are now reachable: every substack notion of
`StacksFrontier/AlgebraicGeometry/Stacks/Substack.lean` and Stacks 06QJ are indexed by an algebraic
stack, which `[U/G_m]` now is.

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.PPowerWeighted

section Points

variable {R : Type*} [CommRing R]

/-- The weighted action read on the points of `U = Spec(k[x_0, x_1, x_2, …])` with values in a
commutative ring: a point is a family `a : ℕ → R` of coordinates, and a unit `t` sends it to
`t · (a_0, a_1, a_2, …) = (t a_0, t^p a_1, t^{p^2} a_2, …)`. -/
def smulPoint (p : ℕ) (t : Rˣ) (a : ℕ → R) : ℕ → R := fun i => (t : R) ^ p ^ i * a i

/-- The `i`-th coordinate of `t · a` is `t^{p^i} a_i`. -/
@[simp] theorem smulPoint_apply (p : ℕ) (t : Rˣ) (a : ℕ → R) (i : ℕ) :
    smulPoint p t a i = (t : R) ^ p ^ i * a i := rfl

/-- The unit `1` acts trivially on points. -/
@[simp] theorem smulPoint_one (p : ℕ) (a : ℕ → R) : smulPoint p (1 : Rˣ) a = a := by
  funext i
  simp

/-- The action on points is compatible with multiplication: `(t u) · a = t · (u · a)`. -/
theorem smulPoint_mul (p : ℕ) (t u : Rˣ) (a : ℕ → R) :
    smulPoint p (t * u) a = smulPoint p t (smulPoint p u a) := by
  funext i
  simp [mul_pow, mul_assoc]

/-- A coordinate of `t · a` vanishes exactly when the same coordinate of `a` does. -/
theorem smulPoint_eq_zero_iff (p : ℕ) (t : Rˣ) (a : ℕ → R) (i : ℕ) :
    smulPoint p t a i = 0 ↔ a i = 0 := by
  rw [smulPoint_apply, ← Units.val_pow_eq_pow_val]
  exact Units.mul_right_eq_zero _

/-- A coordinate of `t · a` is a unit exactly when the same coordinate of `a` is. -/
theorem isUnit_smulPoint_iff (p : ℕ) (t : Rˣ) (a : ℕ → R) (i : ℕ) :
    IsUnit (smulPoint p t a i) ↔ IsUnit (a i) := by
  rw [smulPoint_apply, ← Units.val_pow_eq_pow_val]
  exact Units.isUnit_units_mul _ _

/-- Evaluation of the coaction's target `A ⊗ ℤ[T,T⁻¹]` at a point `φ` of `Spec A` and a point
`t` of the multiplicative group, both with values in `R`. -/
noncomputable def pointEval {A : Type*} [CommRing A] (φ : A →+* R) (t : Rˣ) :
    TensorProduct ℤ A (LaurentPolynomial ℤ) →+* R :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom
    (LaurentPolynomial.eval₂ (Int.castRingHom R) t).toIntAlgHom
    fun _ _ => Commute.all _ _).toRingHom

/-- `pointEval φ t` sends `a ⊗ T^n` to `φ(a) t^n`. -/
@[simp] theorem pointEval_tmul_T {A : Type*} [CommRing A] (φ : A →+* R) (t : Rˣ) (a : A)
    (n : ℤ) :
    pointEval φ t (a ⊗ₜ[ℤ] LaurentPolynomial.T n) = φ a * ((t ^ n : Rˣ) : R) := by
  simp [pointEval, LaurentPolynomial.eval₂_T]

/-- **Stacks 06RE.** The action on points is the action the registered coaction defines:
evaluating the coaction of `x_i` at a point `φ` of `U` and a unit `t` gives the `i`-th
coordinate `t^{p^i} φ(x_i)` of `t · φ`.  So `smulPoint` is the action of
`AlgebraicGeometry.PPowerWeighted.action` and not a second one. -/
@[stacks 06RE "the action on points is the one the coaction defines"]
theorem pointEval_action_μ_X (k : Type u) [CommRing k] (p i : ℕ)
    (φ : MvPolynomial ℕ k →+* R) (t : Rˣ) :
    pointEval φ t ((action k p).μ (MvPolynomial.X i)) =
      smulPoint p t (fun j => φ (MvPolynomial.X j)) i := by
  rw [action_μ_X, pointEval_tmul_T, smulPoint_apply, ← Nat.cast_pow, zpow_natCast,
    Units.val_pow_eq_pow_val, mul_comm]

/-- The stabilizer of a point of `U` under the weighted action, as a subgroup of the units. -/
def pointStabilizer (p : ℕ) (a : ℕ → R) : Subgroup Rˣ where
  carrier := {t | smulPoint p t a = a}
  one_mem' := smulPoint_one p a
  mul_mem' := by
    intro t u ht hu
    change smulPoint p (t * u) a = a
    rw [smulPoint_mul, show smulPoint p u a = a from hu, show smulPoint p t a = a from ht]
  inv_mem' := by
    intro t ht
    change smulPoint p t⁻¹ a = a
    have h := congrArg (smulPoint p t⁻¹) (show smulPoint p t a = a from ht)
    rw [← smulPoint_mul, inv_mul_cancel, smulPoint_one] at h
    exact h.symm

/-- A unit `t` stabilizes `a` exactly when `t^{p^i} a_i = a_i` for every `i`. -/
theorem mem_pointStabilizer_iff (p : ℕ) (a : ℕ → R) (t : Rˣ) :
    t ∈ pointStabilizer p a ↔ ∀ i, (t : R) ^ p ^ i * a i = a i := by
  show smulPoint p t a = a ↔ _
  simp [funext_iff]

end Points

/-- A property of naturals either holds everywhere or fails first at some index. -/
private theorem forall_or_exists_least (P : ℕ → Prop) :
    (∀ j, P j) ∨ ∃ m, (∀ j < m, P j) ∧ ¬ P m := by
  classical
  by_cases h : ∀ j, P j
  · exact Or.inl h
  · have hex : ∃ m, ¬ P m := not_forall.mp h
    exact Or.inr ⟨Nat.find hex, fun j hj => not_not.mp (Nat.find_min hex hj), Nat.find_spec hex⟩

section Strata

variable {R : Type*} [CommRing R]

/-- A point of `U` lies in the `i`-th stratum when the coordinates before the `i`-th vanish and
the `i`-th one is invertible: this is `x_0 = … = x_{i-1} = 0` and `x_i ≠ 0`. -/
def IsPointInStratum (i : ℕ) (a : ℕ → R) : Prop := (∀ j < i, a j = 0) ∧ IsUnit (a i)

/-- A point of `U` lies in the last stratum when all its coordinates vanish. -/
def IsPointInStratumInf (a : ℕ → R) : Prop := ∀ j, a j = 0

/-- **Stacks 06RE.** On the `i`-th stratum the stabilizer of the weighted action is `μ_{p^i}`:
a unit `t` fixes a point whose first nonvanishing coordinate is the `i`-th exactly when
`t^{p^i} = 1`.  The subgroup `AlgebraicGeometry.rootsUnitsSubgroup n` of the units is the value
at `R` of the functor of points of the group scheme `μ_n`
(`AlgebraicGeometry.rootsOfUnitySections_representableBy_rootsOfUnity`). -/
@[stacks 06RE "the stabilizer along the stratum X_i is mu_{p^i}"]
theorem pointStabilizer_eq_rootsUnitsSubgroup (p i : ℕ) (a : ℕ → R)
    (ha : IsPointInStratum i a) :
    pointStabilizer p a = rootsUnitsSubgroup (p ^ i) := by
  obtain ⟨h0, hi⟩ := ha
  ext t
  rw [mem_pointStabilizer_iff]
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hi
    have h1 : (t : R) ^ p ^ i * (u : R) = (u : R) := by rw [hu]; exact h i
    have key : (t : R) ^ p ^ i = 1 := by
      simpa using congrArg (· * ((u⁻¹ : Rˣ) : R)) h1
    show t ^ p ^ i = 1
    exact Units.val_eq_one.mp (by rw [Units.val_pow_eq_pow_val]; exact key)
  · intro ht j
    have hval : (t : R) ^ p ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, show t ^ p ^ i = 1 from ht, Units.val_one]
    rcases lt_or_ge j i with hj | hj
    · rw [h0 j hj, mul_zero]
    · rw [show p ^ j = p ^ i * p ^ (j - i) by rw [← pow_add, Nat.add_sub_cancel' hj],
        pow_mul, hval, one_pow, one_mul]

/-- **Stacks 06RE.** On the last stratum, where all the coordinates vanish, the stabilizer of
the weighted action is all of `G_m`: the unit group of `R` is the value at `R` of the functor of
points of the multiplicative group scheme
(`AlgebraicGeometry.unitsOfGlobalSections_representableBy_multiplicativeGroup`). -/
@[stacks 06RE "the stabilizer along the stratum X_infinity is G_m"]
theorem pointStabilizer_eq_top (p : ℕ) (a : ℕ → R) (ha : IsPointInStratumInf a) :
    pointStabilizer p a = ⊤ := by
  ext t
  simp [mem_pointStabilizer_iff, show ∀ j, a j = 0 from ha]

/-- **Stacks 06RE.** The `i`-th stratum is invariant under the action. -/
@[stacks 06RE "the stratum X_i is invariant under the action"]
theorem isPointInStratum_smulPoint (p i : ℕ) (t : Rˣ) (a : ℕ → R) :
    IsPointInStratum i (smulPoint p t a) ↔ IsPointInStratum i a := by
  unfold IsPointInStratum
  rw [isUnit_smulPoint_iff]
  exact and_congr_left' (forall_congr' fun j => forall_congr' fun _ =>
    smulPoint_eq_zero_iff p t a j)

/-- **Stacks 06RE.** The last stratum is invariant under the action. -/
@[stacks 06RE "the stratum X_infinity is invariant under the action"]
theorem isPointInStratumInf_smulPoint (p : ℕ) (t : Rˣ) (a : ℕ → R) :
    IsPointInStratumInf (smulPoint p t a) ↔ IsPointInStratumInf a :=
  forall_congr' fun j => smulPoint_eq_zero_iff p t a j

/-- Distinct strata are disjoint. -/
theorem IsPointInStratum.eq_of_eq [Nontrivial R] {i j : ℕ} {a : ℕ → R}
    (hi : IsPointInStratum i a) (hj : IsPointInStratum j a) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact one_ne_zero (isUnit_zero_iff.mp (hj.1 i h ▸ hi.2)).symm
  · exact one_ne_zero (isUnit_zero_iff.mp (hi.1 j h ▸ hj.2)).symm

/-- The last stratum is disjoint from every other one. -/
theorem IsPointInStratum.not_isPointInStratumInf [Nontrivial R] {i : ℕ} {a : ℕ → R}
    (hi : IsPointInStratum i a) : ¬ IsPointInStratumInf a := fun h =>
  one_ne_zero (isUnit_zero_iff.mp (h i ▸ hi.2)).symm

/-- **Stacks 06RE.** The strata cover `U`: a point with values in a field either has all its
coordinates zero, or lies in the stratum indexed by the first index where it does not vanish. -/
@[stacks 06RE "the strata cover: every point lies in exactly one stratum"]
theorem isPointInStratumInf_or_exists_isPointInStratum {K : Type*} [Field K] (a : ℕ → K) :
    IsPointInStratumInf a ∨ ∃ i, IsPointInStratum i a := by
  obtain h | ⟨m, hm, hm'⟩ := forall_or_exists_least fun j => a j = 0
  · exact Or.inl h
  · exact Or.inr ⟨m, hm, isUnit_iff_ne_zero.mpr hm'⟩

end Strata

section Spectrum

variable (k : Type u) [CommRing k]

/-- The `i`-th stratum of `U` as a subset of the spectrum: `x_0, …, x_{i-1}` vanish at the
point and `x_i` does not. -/
def stratum (i : ℕ) : Set (PrimeSpectrum (MvPolynomial ℕ k)) :=
  {q | (∀ j < i, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ q.asIdeal) ∧
    (MvPolynomial.X i : MvPolynomial ℕ k) ∉ q.asIdeal}

/-- The last stratum of `U` as a subset of the spectrum: all the coordinates vanish. -/
def stratumInf : Set (PrimeSpectrum (MvPolynomial ℕ k)) :=
  {q | ∀ j, (MvPolynomial.X j : MvPolynomial ℕ k) ∈ q.asIdeal}

/-- The `i`-th stratum is the complement of the zero locus of `x_i` intersected with the zero
locus of `x_0, …, x_{i-1}`. -/
theorem stratum_eq (i : ℕ) :
    stratum k i =
      (PrimeSpectrum.zeroLocus {(MvPolynomial.X i : MvPolynomial ℕ k)})ᶜ ∩
        PrimeSpectrum.zeroLocus (MvPolynomial.X '' {j | j < i}) := by
  ext q
  rw [Set.mem_inter_iff, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.image_subset_iff]
  exact ⟨fun h => ⟨h.2, fun j hj => h.1 j hj⟩, fun h => ⟨fun j hj => h.2 hj, h.1⟩⟩

/-- The last stratum is the zero locus of all the coordinates. -/
theorem stratumInf_eq :
    stratumInf k =
      PrimeSpectrum.zeroLocus (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ k)) := by
  ext q
  rw [PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff]
  exact Iff.rfl

/-- **Stacks 06RE.** The `i`-th stratum is locally closed: it is the intersection of the open
where `x_i` is invertible with the closed subscheme where `x_0, …, x_{i-1}` vanish. -/
@[stacks 06RE "the stratum X_i is locally closed"]
theorem isLocallyClosed_stratum (i : ℕ) : IsLocallyClosed (stratum k i) :=
  ⟨_, _, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl,
    PrimeSpectrum.isClosed_zeroLocus _, stratum_eq k i⟩

/-- **Stacks 06RE.** The last stratum is closed, being the vanishing locus of all the
coordinates. -/
@[stacks 06RE "the stratum X_infinity is closed, hence locally closed"]
theorem isClosed_stratumInf : IsClosed (stratumInf k) :=
  stratumInf_eq k ▸ PrimeSpectrum.isClosed_zeroLocus _

/-- Distinct strata are disjoint. -/
theorem disjoint_stratum {i j : ℕ} (hij : i ≠ j) : Disjoint (stratum k i) (stratum k j) := by
  rw [Set.disjoint_left]
  intro q hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hi.2 (hj.1 i h)
  · exact hj.2 (hi.1 j h)

/-- The last stratum is disjoint from every other one. -/
theorem disjoint_stratum_stratumInf (i : ℕ) : Disjoint (stratum k i) (stratumInf k) :=
  Set.disjoint_left.mpr fun _ hi hinf => hi.2 (hinf i)

/-- **Stacks 06RE.** The strata cover `U`: a point of the spectrum either kills all the
coordinates, or lies in the stratum indexed by the first coordinate it does not kill. -/
@[stacks 06RE "the strata cover the space"]
theorem iUnion_stratum_union_stratumInf :
    (⋃ i, stratum k i) ∪ stratumInf k = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain h | ⟨m, hm, hm'⟩ :=
    forall_or_exists_least fun j => (MvPolynomial.X j : MvPolynomial ℕ k) ∈ q.asIdeal
  · exact Or.inr h
  · exact Or.inl (Set.mem_iUnion.mpr ⟨m, hm, hm'⟩)

/-- **Stacks 06RE.** The two readings of the `i`-th stratum agree: a point of `U` with values in
a field lies in the `i`-th stratum in the sense of `IsPointInStratum` exactly when the prime it
defines lies in `stratum`. -/
@[stacks 06RE "the strata on points and on the spectrum are the same"]
theorem mem_stratum_ker_iff {K : Type*} [Field K] (φ : MvPolynomial ℕ k →+* K) (i : ℕ) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum (MvPolynomial ℕ k)) ∈
        stratum k i ↔
      IsPointInStratum i (fun j => φ (MvPolynomial.X j)) := by
  show ((∀ j < i, _ ∈ RingHom.ker φ) ∧ _ ∉ RingHom.ker φ) ↔ _
  simp only [RingHom.mem_ker, IsPointInStratum, isUnit_iff_ne_zero, ne_eq]

/-- **Stacks 06RE.** The two readings of the last stratum agree. -/
@[stacks 06RE "the last stratum on points and on the spectrum is the same"]
theorem mem_stratumInf_ker_iff {K : Type*} [Field K] (φ : MvPolynomial ℕ k →+* K) :
    (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum (MvPolynomial ℕ k)) ∈
        stratumInf k ↔
      IsPointInStratumInf (fun j => φ (MvPolynomial.X j)) := by
  show (∀ j, _ ∈ RingHom.ker φ) ↔ _
  simp only [RingHom.mem_ker, IsPointInStratumInf]

/-- A coordinate not among those generating the ideal does not lie in it. -/
theorem X_notMem_coordinateIdeal [Nontrivial k] {s : Set ℕ} {i : ℕ} (hi : i ∉ s) :
    (MvPolynomial.X i : MvPolynomial ℕ k) ∉ coordinateIdeal k s := by
  rw [coordinateIdeal, MvPolynomial.mem_ideal_span_X_image]
  intro h
  obtain ⟨j, hjs, hj⟩ := h (Finsupp.single i 1) (by rw [MvPolynomial.support_X]; simp)
  rw [Finsupp.single_apply] at hj
  rcases eq_or_ne i j with rfl | hne
  · exact hi hjs
  · exact hj (if_neg hne)

/-- The algebra map killing the coordinates indexed by `s`, with the polynomial ring on the
remaining coordinates as target. -/
noncomputable def killCoordinates (s : Set ℕ) :
    MvPolynomial ℕ k →ₐ[k] MvPolynomial (↥(sᶜ)) k :=
  MvPolynomial.killCompl (R := k) (f := ((↑) : ↥(sᶜ) → ℕ)) Subtype.val_injective

/-- The ideal generated by the coordinates indexed by `s` is exactly the kernel of the map
killing them. -/
theorem ker_killCoordinates (s : Set ℕ) :
    RingHom.ker (killCoordinates k s) = coordinateIdeal k s := by
  apply le_antisymm
  · intro f hf
    have hf0 : killCoordinates k s f = 0 := hf
    rw [coordinateIdeal, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    push Not at hcon
    have hsub : ↑m.support ⊆ Set.range ((↑) : ↥(sᶜ) → ℕ) := by
      intro j hj
      rw [Subtype.range_coe]
      exact fun hjs => (Finsupp.mem_support_iff.mp hj) (hcon j hjs)
    obtain ⟨n, rfl⟩ : ∃ n, m = Finsupp.mapDomain ((↑) : ↥(sᶜ) → ℕ) n :=
      ⟨m.comapDomain _ Subtype.val_injective.injOn,
        (Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hsub).symm⟩
    refine (Finsupp.mem_support_iff.mp hm) ?_
    have := MvPolynomial.coeff_killCompl
      (R := k) (f := ((↑) : ↥(sᶜ) → ℕ)) Subtype.val_injective (p := f) (s := n)
    rw [show MvPolynomial.killCompl (R := k) (f := ((↑) : ↥(sᶜ) → ℕ))
      Subtype.val_injective f = 0 from hf0, MvPolynomial.coeff_zero] at this
    exact this.symm
  · rw [coordinateIdeal, Ideal.span_le]
    rintro x ⟨j, hj, rfl⟩
    show killCoordinates k s (MvPolynomial.X j) = 0
    rw [killCoordinates, MvPolynomial.killCompl, MvPolynomial.aeval_X]
    rw [dif_neg (by simpa [Subtype.range_coe] using hj)]

/-- The ideal generated by a set of coordinates is prime. -/
theorem isPrime_coordinateIdeal [IsDomain k] (s : Set ℕ) : (coordinateIdeal k s).IsPrime := by
  rw [← ker_killCoordinates]
  exact RingHom.ker_isPrime _

/-- The coordinate ring of the closure of the `i`-th stratum: the coordinates before the `i`-th
are killed. -/
noncomputable abbrev stratumQuotient (i : ℕ) : Type u :=
  MvPolynomial ℕ k ⧸ coordinateIdeal k {j | j < i}

/-- The coordinate ring of the `i`-th stratum: the coordinates before the `i`-th are killed and
the `i`-th one is inverted. -/
noncomputable abbrev stratumRing (i : ℕ) : Type u :=
  Localization.Away
    (Ideal.Quotient.mk (coordinateIdeal k {j | j < i}) (MvPolynomial.X i))

/-- The coordinate ring of the closure of the `i`-th stratum is a domain when `k` is. -/
theorem isDomain_stratumQuotient [IsDomain k] (i : ℕ) : IsDomain (stratumQuotient k i) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (isPrime_coordinateIdeal k _)

/-- **Stacks 06RE.** The `i`-th stratum is integral, in particular reduced. -/
@[stacks 06RE "the stratum X_i is reduced, being integral"]
theorem isDomain_stratumRing [IsDomain k] (i : ℕ) : IsDomain (stratumRing k i) := by
  have := isDomain_stratumQuotient k i
  refine IsLocalization.isDomain_localization (M := Submonoid.powers _) ?_
  refine Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero ?_)
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact X_notMem_coordinateIdeal k (by simp)

/-- **Stacks 06RE.** The `i`-th stratum is reduced. -/
@[stacks 06RE "the stratum X_i is reduced"]
theorem isReduced_stratumRing [IsDomain k] (i : ℕ) : IsReduced (stratumRing k i) := by
  have := isDomain_stratumRing k i
  infer_instance

/-- **Stacks 06RE.** The last stratum is reduced: it is the origin, cut out by the prime ideal
generated by all the coordinates. -/
@[stacks 06RE "the stratum X_infinity is reduced"]
theorem isDomain_quotient_coordinateIdeal_univ [IsDomain k] :
    IsDomain (MvPolynomial ℕ k ⧸ coordinateIdeal k Set.univ) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (isPrime_coordinateIdeal k _)

end Spectrum

section Minimality

/-- The universal `n`-th root of unity has exact order `n`: for `0 < m < n` its `m`-th power is
not one, because `X^n - 1` does not divide `X^m - 1`. -/
theorem rootsOfUnityCoordinate_pow_ne_one {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    rootsOfUnityCoordinate.{u} n (hm.trans hmn) ^ m ≠ 1 := by
  intro h
  have hn0 : n ≠ 0 := by omega
  have hval :
      (Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ n - 1} :
          Set (Polynomial (ULift.{u} ℤ)))) (Polynomial.X ^ m)) =
        Ideal.Quotient.mk _ 1 := by
    simpa [rootsOfUnityCoordinate, map_pow] using congrArg Units.val h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hval
  have hmonic : (Polynomial.X ^ n - 1 : Polynomial (ULift.{u} ℤ)).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : ULift.{u} ℤ) hn0
  have hne : (Polynomial.X ^ m - 1 : Polynomial (ULift.{u} ℤ)) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hm (1 : ULift.{u} ℤ)
  have hdeg (d : ℕ) : (Polynomial.X ^ d - 1 : Polynomial (ULift.{u} ℤ)).natDegree = d := by
    simpa using Polynomial.natDegree_X_pow_sub_C (R := ULift.{u} ℤ) (n := d) (r := 1)
  have hle := hmonic.natDegree_le_of_dvd hne hval
  rw [hdeg, hdeg] at hle
  omega

/-- For `0 < m < n` the group `μ_m` is not the group `μ_n`: in the coordinate ring of `μ_n` the
universal `n`-th root of unity is an `n`-th root of unity which is not an `m`-th one. -/
theorem rootsUnitsSubgroup_ne {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    rootsUnitsSubgroup (A := rootsOfUnityCoordinateRing.{u} n) m ≠ rootsUnitsSubgroup n := by
  intro h
  have hmem : rootsOfUnityCoordinate.{u} n (hm.trans hmn) ∈
      rootsUnitsSubgroup (A := rootsOfUnityCoordinateRing.{u} n) n :=
    rootsOfUnityCoordinate_pow n (hm.trans hmn)
  rw [← h] at hmem
  exact rootsOfUnityCoordinate_pow_ne_one hm hmn hmem

/-- **Stacks 06RE.** Distinct strata have distinct groups: for `1 < p` and `i < j` the group
`μ_{p^i}` of the stratum `X_i` is not the group `μ_{p^j}` of the stratum `X_j`.  So no two strata
can be merged into a single locus along which the stabilizer is one group, which is why there is
no coarser stratification with the same properties. -/
@[stacks 06RE "distinct strata have distinct groups mu_{p^i}: no coarser stratification"]
theorem rootsUnitsSubgroup_pow_ne (p i j : ℕ) (hp : 1 < p) (hij : i < j) :
    rootsUnitsSubgroup (A := rootsOfUnityCoordinateRing.{u} (p ^ j)) (p ^ i) ≠
      rootsUnitsSubgroup (p ^ j) :=
  rootsUnitsSubgroup_ne (pow_pos (by omega) i) (Nat.pow_lt_pow_right hp hij)

/-- **Stacks 06RE.** The group of a stratum `X_i` is never the group `G_m` of the last stratum
`X_∞`: already in the units of the rationals the `n`-th roots of unity are not everything, since
`2` is a unit with `2^n ≠ 1`.  So the last stratum cannot be merged with any other one either. -/
@[stacks 06RE "the group mu_{p^i} of X_i differs from the group G_m of X_infinity"]
theorem rootsUnitsSubgroup_ne_top {n : ℕ} (hn : 0 < n) :
    rootsUnitsSubgroup (A := ℚ) n ≠ ⊤ := by
  intro h
  have hmem : (Units.mk0 (2 : ℚ) (by norm_num)) ∈ rootsUnitsSubgroup (A := ℚ) n := by
    simp [h]
  have hpow : (2 : ℚ) ^ n = 1 := by
    simpa using congrArg Units.val (show (Units.mk0 (2 : ℚ) (by norm_num)) ^ n = 1 from hmem)
  exact (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)).ne' hpow

/-- The point of `U` with values in `R` whose `i`-th coordinate is one and whose other
coordinates vanish.  It is the simplest point of the stratum `X_i`. -/
def basisPoint (R : Type*) [CommRing R] (i : ℕ) : ℕ → R := fun m => if m = i then 1 else 0

/-- The `m`-th coordinate of `basisPoint R i` is `1` if `m = i` and `0` otherwise. -/
@[simp] theorem basisPoint_apply (R : Type*) [CommRing R] (i m : ℕ) :
    basisPoint R i m = if m = i then 1 else 0 := rfl

/-- The point with `i`-th coordinate one lies in the stratum `X_i`. -/
theorem isPointInStratum_basisPoint (R : Type*) [CommRing R] (i : ℕ) :
    IsPointInStratum i (basisPoint R i) :=
  ⟨fun _ hm => by simp [basisPoint, Nat.ne_of_lt hm], by simp [basisPoint]⟩

/-- The origin lies in the last stratum `X_∞`. -/
theorem isPointInStratumInf_zero (R : Type*) [CommRing R] :
    IsPointInStratumInf (0 : ℕ → R) := fun _ => rfl

/-- **Stacks 06RE.** The strata `X_i` and `X_j` with `i < j` cannot be merged: already over the
coordinate ring of `μ_{p^j}` the stabilizer of a point of `X_i` differs from the stabilizer of a
point of `X_j`, being `μ_{p^i}` against `μ_{p^j}`.  Together with
`AlgebraicGeometry.PPowerWeighted.pointStabilizer_ne_pointStabilizer_basisPoint_zero` this is the
source's last assertion, that there is no coarser stratification with the same properties: a
stratum of a coarser stratification would contain points of two of the strata below and so could
not be a gerbe with a single group. -/
@[stacks 06RE "the strata X_i and X_j cannot be merged: their stabilizers differ"]
theorem pointStabilizer_ne_pointStabilizer_basisPoint (p i j : ℕ) (hp : 1 < p) (hij : i < j) :
    pointStabilizer p (basisPoint (rootsOfUnityCoordinateRing.{u} (p ^ j)) i) ≠
      pointStabilizer p (basisPoint (rootsOfUnityCoordinateRing.{u} (p ^ j)) j) := by
  rw [pointStabilizer_eq_rootsUnitsSubgroup p i _ (isPointInStratum_basisPoint _ i),
    pointStabilizer_eq_rootsUnitsSubgroup p j _ (isPointInStratum_basisPoint _ j)]
  exact rootsUnitsSubgroup_pow_ne p i j hp hij

/-- **Stacks 06RE.** The stratum `X_i` cannot be merged with the last stratum `X_∞`: already over
the rationals the stabilizer of the point of `X_i` with `i`-th coordinate one is `μ_{p^i}`, while
the stabilizer of the origin is all of `G_m`. -/
@[stacks 06RE "the stratum X_i cannot be merged with X_infinity: their stabilizers differ"]
theorem pointStabilizer_ne_pointStabilizer_basisPoint_zero (p i : ℕ) (hp : 0 < p) :
    pointStabilizer p (basisPoint ℚ i) ≠ pointStabilizer p (0 : ℕ → ℚ) := by
  rw [pointStabilizer_eq_rootsUnitsSubgroup p i _ (isPointInStratum_basisPoint _ i),
    pointStabilizer_eq_top p _ (isPointInStratumInf_zero ℚ)]
  exact rootsUnitsSubgroup_ne_top (pow_pos hp i)

end Minimality

end AlgebraicGeometry.PPowerWeighted

end
