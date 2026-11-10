module

public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A node has exactly two geometric branches

Let `A` be a nodal Nagata local algebra over a field `k`. Then
`numberOfGeometricBranchesOfLocalRing A = 2`.

## Main results

* `Stacks.Curves.isReduced_of_isSeparable` — a separable algebra over a field is reduced.
* `Stacks.Curves.two_le_enatCard_sigma_sepDegree_of_surjective` — the weighted count of the
  maximal ideals of a ring surjecting onto a separable two-dimensional algebra over the residue
  field of a local base is at least two.
* `Stacks.Curves.two_le_numberOfGeometricBranchesOfLocalRing_of_isNodalAlgebra` — a node has at
  least two geometric branches.
* `Stacks.Curves.numberOfGeometricBranchesOfLocalRing_eq_two_of_isNodalAlgebra` — a node has
  exactly two geometric branches.
* `Stacks.Curves.deltaInvariant_eq_one_and_two_geometricBranches_of_isNodalAlgebra` — the five
  properties that Stacks Tag 0C4A asserts of a node.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C37](https://stacks.math.columbia.edu/tag/0C37)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### A separable algebra over a field is reduced -/

open Polynomial in
/-- A separable algebra over a field is reduced. -/
public theorem isReduced_of_isSeparable (K : Type*) [Field K] (T : Type*) [CommRing T]
    [Algebra K T] [Algebra.IsSeparable K T] : IsReduced T := by
  refine ⟨fun x ⟨n, hn⟩ => ?_⟩
  have hdvd : minpoly K x ∣ X ^ n := minpoly.dvd K x (by simpa using hn)
  have hsq : Squarefree (minpoly K x) := (Algebra.IsSeparable.isSeparable K x).squarefree
  have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsSeparable.isIntegral K x)
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X n).mp hdvd
  have hi1 : i ≤ 1 := by
    by_contra hcon
    refine Polynomial.not_isUnit_X (hsq X (Dvd.dvd.trans ?_ hassoc.symm.dvd))
    simpa only [pow_two] using pow_dvd_pow (X : K[X]) (by omega : 2 ≤ i)
  have heq : minpoly K x = X ^ i :=
    Polynomial.eq_of_monic_of_associated hmon (Polynomial.monic_X.pow i) hassoc
  have haeval : Polynomial.aeval x (minpoly K x) = 0 := minpoly.aeval K x
  rw [heq] at haeval
  interval_cases i
  · rw [pow_zero, map_one] at haeval
    calc x = x * 1 := (mul_one x).symm
      _ = x * 0 := by rw [haeval]
      _ = 0 := mul_zero x
  · simpa using haeval

/-! ### The weighted count of maximal ideals -/

/-- An extended natural number is at least two as soon as it counts a nontrivial type. -/
private theorem two_le_enatCard_of_nontrivial (α : Type*) (h : Nontrivial α) :
    2 ≤ ENat.card α := by
  rw [show (2 : ℕ∞) = 1 + 1 from rfl, ENat.add_one_le_iff (by simp)]
  exact ENat.one_lt_card

/-- A ring surjecting onto a separable two-dimensional algebra over the residue field of a local
base has weighted maximal-ideal count at least two, the weight of a maximal ideal being the
separable degree of its residue field over that residue field. -/
public theorem two_le_enatCard_sigma_sepDegree_of_surjective
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    {T : Type v} [CommRing T] [Algebra (ResidueField A) T]
    [Module.Finite (ResidueField A) T] [Algebra.IsSeparable (ResidueField A) T]
    (hcontract : ∀ m : MaximalSpectrum B,
      maximalIdeal A = m.asIdeal.comap (algebraMap A B))
    (π : B →+* T) (hsurj : Function.Surjective π)
    (hπ : ∀ a : A, π (algebraMap A B a) = algebraMap (ResidueField A) T (residue A a))
    (hrank : Module.finrank (ResidueField A) T = 2) :
    2 ≤ ENat.card ((m : MaximalSpectrum B) ×
      letI : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
      let f := Ideal.quotientMap m.asIdeal (algebraMap A B) (le_of_eq (hcontract m))
      letI : Algebra (ResidueField A) (B ⧸ m.asIdeal) := f.toAlgebra
      (Field.sepDegree (ResidueField A) (B ⧸ m.asIdeal)).ord.ToType) := by
  classical
  have hTnt : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (R := ResidueField A) (by rw [hrank]; omega)
  have hTart : IsArtinianRing T := IsArtinianRing.of_finite (ResidueField A) T
  have hTred : IsReduced T := isReduced_of_isSeparable (ResidueField A) T
  rcases subsingleton_or_nontrivial (MaximalSpectrum B) with hsub | hnt
  · let g : MaximalSpectrum T → MaximalSpectrum B := fun n =>
      ⟨n.asIdeal.comap π, Ideal.comap_isMaximal_of_surjective π hsurj⟩
    have hsubT : Subsingleton (MaximalSpectrum T) := ⟨fun n₁ n₂ =>
      MaximalSpectrum.ext (Ideal.comap_injective_of_surjective π hsurj
        (congrArg MaximalSpectrum.asIdeal (hsub.allEq (g n₁) (g n₂))))⟩
    obtain ⟨n₀, hn₀⟩ := Ideal.exists_maximal T
    have hTloc : IsLocalRing T := IsLocalRing.of_unique_max_ideal
      ⟨n₀, hn₀, fun J hJ => congrArg MaximalSpectrum.asIdeal
        (hsubT.allEq (⟨J, hJ⟩ : MaximalSpectrum T) ⟨n₀, hn₀⟩)⟩
    have hkermax : (RingHom.ker π).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _
        ((RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isField
          (IsArtinianRing.isField_of_isReduced_of_isLocalRing T))
    let m : MaximalSpectrum B := ⟨RingHom.ker π, hkermax⟩
    let fld : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let alg : Algebra (ResidueField A) (B ⧸ m.asIdeal) :=
      (Ideal.quotientMap m.asIdeal (algebraMap A B) (le_of_eq (hcontract m))).toAlgebra
    let q : (B ⧸ m.asIdeal) ≃+* T := RingHom.quotientKerEquivOfSurjective hsurj
    have hcomm : ∀ r : ResidueField A,
        q (algebraMap (ResidueField A) (B ⧸ m.asIdeal) r) =
          algebraMap (ResidueField A) T r := by
      intro r
      obtain ⟨a, rfl⟩ := residue_surjective r
      change q (Ideal.quotientMap m.asIdeal (algebraMap A B)
        (le_of_eq (hcontract m)) (Ideal.Quotient.mk (maximalIdeal A) a)) = _
      rw [Ideal.quotientMap_mk]
      exact hπ a
    let ealg : (B ⧸ m.asIdeal) ≃ₐ[ResidueField A] T := { __ := q, commutes' := hcomm }
    have hsepq : Algebra.IsSeparable (ResidueField A) (B ⧸ m.asIdeal) :=
      (AlgEquiv.Algebra.isSeparable_iff ealg).mpr ‹_›
    have hdeg : Field.sepDegree (ResidueField A) (B ⧸ m.asIdeal) = 2 := by
      rw [Algebra.IsSeparable.sepDegree_eq, ealg.toLinearEquiv.rank_eq,
        ← Module.finrank_eq_rank, hrank]
      norm_num
    refine le_trans (le_of_eq ?_) (ENat.card_le_card_of_injective
      (f := Sigma.mk m) sigma_mk_injective)
    change (2 : ℕ∞) = ENat.card (Field.sepDegree (ResidueField A) (B ⧸ m.asIdeal)).ord.ToType
    simp [ENat.card, hdeg]
  · obtain ⟨m₁, m₂, hne⟩ := hnt
    have hfib : ∀ m : MaximalSpectrum B,
        Nonempty (let : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
          let f := Ideal.quotientMap m.asIdeal (algebraMap A B) (le_of_eq (hcontract m))
          let : Algebra (ResidueField A) (B ⧸ m.asIdeal) := f.toAlgebra
          (Field.sepDegree (ResidueField A) (B ⧸ m.asIdeal)).ord.ToType) := by
      intro m
      let fld : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
      let alg : Algebra (ResidueField A) (B ⧸ m.asIdeal) :=
        (Ideal.quotientMap m.asIdeal (algebraMap A B) (le_of_eq (hcontract m))).toAlgebra
      change Nonempty (Field.sepDegree (ResidueField A) (B ⧸ m.asIdeal)).ord.ToType
      exact Cardinal.nonempty_ord_toType (NeZero.ne _)
    exact two_le_enatCard_of_nontrivial _
      ⟨⟨m₁, (hfib m₁).some⟩, ⟨m₂, (hfib m₂).some⟩, fun h => hne (congrArg Sigma.fst h)⟩

/-! ### The number of geometric branches of a node -/

/-- A nodal Nagata local algebra has at least two geometric branches. -/
public theorem two_le_numberOfGeometricBranchesOfLocalRing_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (hA : IsNodalAlgebra k A) :
    2 ≤ numberOfGeometricBranchesOfLocalRing A := by
  have : IsNoetherianRing A := hNagata.isNoetherianRing
  have : IsReduced A := hA.2.1
  obtain ⟨-, -, -, hfin⟩ := numberOfBranches_characterizations A
    (henselizationData A).carrier (strictHenselizationData A).carrier
    (SeparableClosure (ResidueField A))
  obtain ⟨-, hcontract, hgeo⟩ := hfin (minimalPrimes.finite_of_isNoetherianRing A)
  change 2 ≤ numberOfGeometricBranches A (SeparableClosure (ResidueField A))
    (strictHenselizationData A).carrier
  rw [hgeo]
  let eC := integralClosureQuotNilradicalAlgEquiv A
  refine @two_le_enatCard_sigma_sepDegree_of_surjective A _ _ _ _ _ (quadraticAlgebra A) _
    (instAlgebraResidueFieldQuadraticAlgebra A) (finite_quadraticAlgebra_of_isNodalAlgebra k A hA)
    (isSeparable_quadraticAlgebra_of_isNodalAlgebra k A hA) hcontract
    ((Ideal.Quotient.mk ((maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A))))).comp eC.toRingHom)
    (Ideal.Quotient.mk_surjective.comp eC.surjective) (fun a => ?_)
    (finrank_quadraticAlgebra_of_isNodalAlgebra k A hA)
  change Ideal.Quotient.mk _ (eC (algebraMap A _ a)) = _
  rw [eC.commutes]
  rfl

/-- A nodal Nagata local algebra has exactly two geometric branches. -/
public theorem numberOfGeometricBranchesOfLocalRing_eq_two_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (hA : IsNodalAlgebra k A) :
    numberOfGeometricBranchesOfLocalRing A = 2 :=
  le_antisymm (numberOfGeometricBranchesOfLocalRing_le_two_of_isNodalAlgebra k A hNagata hA)
    (two_le_numberOfGeometricBranchesOfLocalRing_of_isNodalAlgebra k A hNagata hA)

/-- A nodal Nagata local algebra is reduced and one-dimensional, has separable residue field,
delta invariant one and two geometric branches. -/
@[sga "7 X 2.24" "more general"]
public theorem deltaInvariant_eq_one_and_two_geometricBranches_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (hA : IsNodalAlgebra k A) :
    Algebra.IsSeparableExtension k (ResidueField A) ∧ IsReduced A ∧ ringKrullDim A = 1 ∧
      Ring.deltaInvariant A = 1 ∧ numberOfGeometricBranchesOfLocalRing A = 2 :=
  have : IsNoetherianRing A := hNagata.isNoetherianRing
  ⟨hA.1, hA.2.1, ringKrullDim_eq_one_of_isNodalAlgebra k A hA,
    deltaInvariant_eq_one_of_isNodalAlgebra k A hA,
    numberOfGeometricBranchesOfLocalRing_eq_two_of_isNodalAlgebra k A hNagata hA⟩

end Stacks.Curves

end
