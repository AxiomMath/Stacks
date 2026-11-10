module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.SpecialFibreSerreCriterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ModelOverField
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# The distance to `Z` is at least the dimension of the closure, when `Z` consists of closed points

In Situation 0EHC with `A` of finite type over a field `k`, suppose every prime of `A` containing
`I + 𝔞` is maximal, so that the points of `Z` are closed points of `Y = V(I)`. The dimension of
the closure is a dimension function on `Y` vanishing on the closed points, so by Stacks 0EIY

`δ^Y_Z(z) ≥ dim({z}‾) = dim(A/𝔭)`,

`𝔭` the prime of `A` under `z`. This is the bound `δ^Y_Z(y) ≥ dim({y}‾)` used in the proof of
Stacks 0EL5, where `Z` is the vertex of the cone over a projective scheme.

## Main results

* `Stacks.Algebraization.ringKrullDim_quotient_le_distanceToZ`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Algebraization

/-- `(A/I)/𝔭̄ ≅ A/𝔭`. -/
def quotientQuotientComapEquiv {A : Type u} [CommRing A] (I : Ideal A) (J : Ideal (A ⧸ I)) :
    (A ⧸ I) ⧸ J ≃+* A ⧸ J.comap (Ideal.Quotient.mk I) :=
  (Ideal.quotEquivOfEq (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact J.zero_mem))

variable (S : AlgebraizationSituation.{u})

/-- The dimension of the closure of a point of `Y` is the dimension of `A` modulo its prime. -/
public theorem dimClosureAt_Y_eq_ringKrullDim (z : S.Y) :
    dimClosureAt S.Y z = ringKrullDim (S.A ⧸ (S.Yι.base z).asIdeal) := by
  rw [dimClosureAt, show closure ({z} : Set S.Y) = PrimeSpectrum.zeroLocus
      ((z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal : Set (S.A ⧸ S.I)) from
      PrimeSpectrum.closure_singleton _,
    show (S.Yι.base z).asIdeal =
      (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal.comap (Ideal.Quotient.mk S.I) from rfl]
  exact (_root_.topologicalKrullDim_zeroLocus (R := S.A ⧸ S.I) _).trans
    (ringKrullDim_eq_of_ringEquiv (quotientQuotientComapEquiv S.I _))

/-- If every prime of `A` containing `I + 𝔞` is maximal, the points of `Z` are closed in `Y`. -/
public theorem AlgebraizationSituation.isMaximal_of_mem_closedSubsetZ
    (hZ : ∀ q : Ideal S.A, q.IsPrime → S.I ≤ q → S.a ≤ q → q.IsMaximal)
    {z : S.Y} (hz : z ∈ (S.closedSubsetZ : Set S.Y)) :
    ((z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal).IsMaximal := by
  have := (z : PrimeSpectrum (S.A ⧸ S.I)).isPrime
  have hc : ((z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal.comap
      (Ideal.Quotient.mk S.I)).IsMaximal := by
    exact hZ _ (Ideal.comap_isPrime _ _) (Ideal.mk_ker.ge.trans (Ideal.ker_le_comap _))
      (fun x hx => hz (Ideal.mem_map_of_mem _ hx))
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hc ⊢
  exact (quotientQuotientComapEquiv S.I _).toMulEquiv.isField hc

/-- **`dim(A/𝔭) ≤ δ^Y_Z(z)`** when every prime of `A` containing `I + 𝔞` is maximal, `A` of finite
type over a field. -/
public theorem ringKrullDim_quotient_le_distanceToZ (k : Type u) [Field k] [Algebra k S.A]
    [Algebra.FiniteType k S.A]
    (hZ : ∀ q : Ideal S.A, q.IsPrime → S.I ≤ q → S.a ≤ q → q.IsMaximal) (z : S.Y) :
    ringKrullDim (S.A ⧸ (S.Yι.base z).asIdeal) ≤ (S.distanceToZ z : WithBot ℕ∞) := by
  classical
  let fY : S.Y ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (S.A ⧸ S.I)))
  have : LocallyOfFiniteType fY := locallyOfFiniteType_specMap_algebraMap k (S.A ⧸ S.I)
  let δ := residueFieldTrdegDimensionFunction k S.Y fY
  have hZ0 : ∀ z' ∈ (S.closedSubsetZ : Set S.Y), δ z' = 0 := by
    intro z' hz'
    change ((natTrdegResidueField k S.Y fY z' : ℕ) : ℤ) = 0
    rw [natTrdegResidueField_eq_zero_of_isClosed k S.Y fY z' <|
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
        (S.isMaximal_of_mem_closedSubsetZ hZ hz')]
    rfl
  by_cases hne : (S.closedSubsetZ : Set S.Y).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    have hm : IsGreatest (δ '' (S.closedSubsetZ : Set S.Y)) 0 :=
      ⟨⟨z₀, hz₀, hZ0 z₀ hz₀⟩, by
        rintro _ ⟨z', hz', rfl⟩
        exact (hZ0 z' hz').le⟩
    have hdist := distanceFunction_ge_dimensionFunction_sub_max S.Y S.closedSubsetZ δ 0 hm z
    rw [← dimClosureAt_Y_eq_ringKrullDim S z, dimClosureAt_eq_natTrdegResidueField k fY z]
    have h1 : ((δ z - 0).toNat : ℕ) = natTrdegResidueField k S.Y fY z := by
      change (((natTrdegResidueField k S.Y fY z : ℕ) : ℤ) - 0).toNat = _
      simp
    rw [h1] at hdist
    exact_mod_cast hdist
  · have htop : S.distanceToZ z = ⊤ :=
      distanceFunction_eq_top_of_disjoint S.Y S.closedSubsetZ z fun ⟨w, _, hw⟩ => hne ⟨w, hw⟩
    rw [htop]
    exact le_top

end Stacks.Algebraization

end
