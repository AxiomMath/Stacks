module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossSingularityCriterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.FiberBranches
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE

/-!
# Geometric unibranchness of `X` is not detected by the fibres of étale neighbourhoods

Let `f : X ⟶ S`, let `x` be a point of `X` and let `s = f x`. Read with `X` in place of the fibre
`X_s`, part (4) of Tag 0CB5 says: "`X` is geometrically unibranch at `x` if and only if for every
étale neighbourhood `(U, u)` of `(X, x)` there is exactly one irreducible component of `U_s`
passing through `u`". This statement is false. For `f` an isomorphism the right-hand side holds
for every `X` and every `x`, while the spectrum of the two-branch multicross ring
`Stacks.Curves.multicross`, the local ring of a node, is not geometrically unibranch at its closed
point. The statement about the fibre `X_s` is
`AlgebraicGeometry.isGeometricallyUnibranchAt_fiber_iff_existsUnique_irreducibleComponent`.

## Main results

* `AlgebraicGeometry.not_forall_isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent`:
  the literal reading of part (4) is false.
* `AlgebraicGeometry.isNormal_fiber_of_isIso`: the fibre of an isomorphism is a normal scheme.
* `AlgebraicGeometry.isGeometricallyUnibranchAt_fiber_of_isIso`: the fibre of an isomorphism is
  geometrically unibranch at each of its points.
* `AlgebraicGeometry.isLocalRing_multicross`: the multicross ring on a nonempty set of branches
  is a local ring.
* `AlgebraicGeometry.not_isGeometricallyUnibranchRing_multicross`: the two-branch multicross
  ring is not geometrically unibranch.

## References

* [Stacks Project, Tag 0CB5](https://stacks.math.columbia.edu/tag/0CB5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Curves

universe u

namespace AlgebraicGeometry

/-! ### The two-branch multicross ring is local and not geometrically unibranch -/

/-- A tuple of power series with equal, nonzero constant coefficients is a unit of the
multicross ring. -/
private theorem isUnit_of_constantCoeff_ne_zero {k : Type u} [Field k] {n : ℕ}
    (f : ↥(multicross k n)) (i₀ : Fin n)
    (hf : PowerSeries.constantCoeff (f.1 i₀) ≠ 0) : IsUnit f := by
  have hne : ∀ l, PowerSeries.constantCoeff (f.1 l) ≠ 0 := fun l => by
    rw [f.2 l i₀]; exact hf
  obtain ⟨u, hu⟩ := Pi.isUnit_iff.mpr fun i =>
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr (hne i))
  have hmul : f.1 * (↑u⁻¹ : Fin n → PowerSeries k) = 1 := by
    rw [← hu]; exact u.mul_inv
  have hcc : ∀ l, PowerSeries.constantCoeff (f.1 l) *
      PowerSeries.constantCoeff ((↑u⁻¹ : Fin n → PowerSeries k) l) = 1 := by
    intro l
    have h := congrFun hmul l
    simp only [Pi.mul_apply, Pi.one_apply] at h
    rw [← map_mul, h, map_one]
  have hg : (↑u⁻¹ : Fin n → PowerSeries k) ∈ multicross k n := by
    rw [mem_multicross]
    intro i j
    refine mul_left_cancel₀ (hne i) ?_
    rw [hcc i, f.2 i j, hcc j]
  exact IsUnit.of_mul_eq_one ⟨_, hg⟩ (Subtype.ext hmul)

/-- The multicross ring on a nonempty set of branches is a local ring. -/
theorem isLocalRing_multicross (k : Type u) [Field k] {n : ℕ} (i₀ : Fin n) :
    IsLocalRing ↥(multicross k n) := by
  have hnt : Nontrivial ↥(multicross k n) :=
    ⟨⟨0, 1, fun hc => by
      have h0 := congrFun (congrArg Subtype.val hc) i₀
      simp at h0⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases h : PowerSeries.constantCoeff (a.1 i₀) = 0
  · right
    refine isUnit_of_constantCoeff_ne_zero _ i₀ ?_
    have hval : ((1 : ↥(multicross k n)) - a).1 i₀ = 1 - a.1 i₀ := rfl
    rw [hval, map_sub, h, map_one, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_of_constantCoeff_ne_zero a i₀ h)

/-- The two-branch multicross ring is a local ring. -/
instance isLocalRing_multicross_two (k : Type u) [Field k] :
    IsLocalRing ↥(multicross k 2) :=
  isLocalRing_multicross k ⟨0, by norm_num⟩

/-- The two-branch multicross ring is not geometrically unibranch. -/
theorem not_isGeometricallyUnibranchRing_multicross (k : Type u) [Field k] :
    ¬ IsGeometricallyUnibranchRing ↥(multicross k 2) := by
  rintro ⟨hdom, -⟩
  have hprime : (nilradical ↥(multicross k 2)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  obtain ⟨a, b, hab, hset⟩ :=
    Set.encard_eq_two.mp (by simpa using encard_minimalPrimes_multicross k 2)
  have key : ∀ q ∈ minimalPrimes ↥(multicross k 2), q = nilradical ↥(multicross k 2) := by
    intro q hq
    rw [minimalPrimes_eq_minimals] at hq
    have : q.IsPrime := hq.1
    exact le_antisymm (hq.2 hprime (nilradical_le_prime q)) (nilradical_le_prime q)
  have ha : a ∈ minimalPrimes ↥(multicross k 2) := by rw [hset]; exact Set.mem_insert _ _
  have hb : b ∈ minimalPrimes ↥(multicross k 2) := by
    rw [hset]; exact Set.mem_insert_of_mem _ rfl
  exact hab ((key a ha).trans (key b hb).symm)

/-! ### The spectrum of a local ring at its closed point -/

/-- The stalk of the spectrum of a local ring at the closed point is isomorphic to the ring. -/
private def specStalkClosedPointRingEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (Spec (.of R)).presheaf.stalk (IsLocalRing.closedPoint R) ≃+* R :=
  let e : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
    IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
      fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx
  (Spec.stalkIso (.of R) (IsLocalRing.closedPoint R)).commRingCatIsoToRingEquiv.trans
    (e : R ≃+* Localization.AtPrime (IsLocalRing.maximalIdeal R)).symm

/-- A scheme whose local ring at a point is isomorphic to a ring which is not geometrically
unibranch is not geometrically unibranch at that point. -/
private theorem not_isGeometricallyUnibranchAt_of_ringEquiv {X : Scheme.{u}} (x : X)
    (R : Type u) [CommRing R] [IsLocalRing R] (e : X.presheaf.stalk x ≃+* R)
    (hR : ¬ IsGeometricallyUnibranchRing R) : ¬ IsGeometricallyUnibranchAt X x :=
  fun h => hR (isGeometricallyUnibranchRing_of_ringEquiv e h)

/-! ### The fibre of an isomorphism -/

/-- The fibre of an isomorphism at a point is a normal scheme. -/
theorem isNormal_fiber_of_isIso {X S : Scheme.{u}} (f : X ⟶ S) [IsIso f] (y : S) :
    IsNormal (f.fiber y) := by
  have hiso : IsIso (f.fiberToSpecResidueField y) :=
    inferInstanceAs (IsIso (pullback.snd f (S.fromSpecResidueField y)))
  have hnormal : IsNormal (Spec (S.residueField y)) :=
    isNormal_spec_of_isIntegrallyClosed ↥(S.residueField y)
  exact @isNormal_of_iso _ _ (@asIso _ _ _ _ _ hiso) hnormal

/-- The fibre of an isomorphism is geometrically unibranch at every one of its points. -/
theorem isGeometricallyUnibranchAt_fiber_of_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIso f] (y : S) (z : f.fiber y) : IsGeometricallyUnibranchAt (f.fiber y) z :=
  @isGeometricallyUnibranch_of_isNormal _ (isNormal_fiber_of_isIso f y) z

/-! ### The literal reading of part (4) is false -/

/-- It is not true that for every morphism `f : X ⟶ S` and every point `x` of `X`, `X` is
geometrically unibranch at `x` if and only if for every étale neighbourhood `(U, u)` of `(X, x)`
there is exactly one irreducible component of the fibre of `U ⟶ S` over `f x` through `u`. -/
@[stacks 0CB5 "part (4) as printed, about X rather than X_s, is FALSE: counterexample"]
theorem not_forall_isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent :
    ¬ ∀ (X S : Scheme.{u}) (f : X ⟶ S) (x : X),
        IsGeometricallyUnibranchAt X x ↔
          ∀ U : EtaleNeighborhood X x,
            ∃! Z : irreducibleComponents ((U.toBase ≫ f).fiber (f x)),
              ((U.toBase ≫ f).fiberHomeo (f x)).symm ⟨U.point, by simp [U.map_point]⟩ ∈
                (Z : Set ((U.toBase ≫ f).fiber (f x))) := by
  intro h
  let k : Type u := ULift.{u} ℚ
  let R : Type u := ↥(multicross k 2)
  let X : Scheme.{u} := Spec (.of R)
  let x : X := IsLocalRing.closedPoint R
  refine absurd ((h X X (𝟙 X) x).mpr ?_)
    (not_isGeometricallyUnibranchAt_of_ringEquiv x R (specStalkClosedPointRingEquiv R)
      (not_isGeometricallyUnibranchRing_multicross k))
  exact (isGeometricallyUnibranchAt_fiber_iff_existsUnique_irreducibleComponent (𝟙 X) x).mp
    (isGeometricallyUnibranchAt_fiber_of_isIso (𝟙 X) _ _)

end AlgebraicGeometry

end
