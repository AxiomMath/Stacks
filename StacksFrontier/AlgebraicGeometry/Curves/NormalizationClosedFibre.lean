module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.GoingUp
public import StacksFrontier.AlgebraicGeometry.Curves.NodalAlgebra

/-!
# Counting the maximal ideals of a normalization by its closed fibre

Let `A` be a local ring and let `B` be an `A`-algebra which is integral over `A` — the case of
interest being the normalization `B = integralClosure A (FractionRing A)`, for which
`integralClosure.AlgebraIsIntegral` supplies the hypothesis. Every maximal ideal of `B`
contracts to the maximal ideal of `A`, hence contains the ideal `m_A B`
(`Stacks.Curves.map_maximalIdeal_le_of_isMaximal`), so the maximal ideals of `B` are exactly
the maximal ideals of the **closed fibre** `B ⧸ m_A B`
(`Stacks.Curves.maximalSpectrumQuotientEquiv`). The maximal ideals of a ring that is a
finite-dimensional algebra over a field are at most as many as its dimension
(`Stacks.Curves.encard_maximalSpectrum_le_finrank`), because the Chinese remainder theorem
makes the product of the residue fields a quotient of the ring and each factor contributes at
least one to the dimension.

Combining the two gives the counting half of Stacks Tag 0C4A without any case distinction and
without choosing coordinates: *if the closed fibre of `B` is two-dimensional over some field,
then `B` has one or two maximal ideals*
(`Stacks.Curves.encard_maximalSpectrum_eq_one_or_two_of_finrank_closedFibre_eq_two`). For a
nodal algebra the closed fibre of the normalization is a separable algebra of degree two over
the residue field, which is Stacks Tag 0CBT; one is the non-split case (the fibre is a
separable quadratic field extension) and two the split case (the fibre is `κ × κ`). So this
file reduces the count of maximal ideals of the normalization of a node to Tag 0CBT, in place
of the explicit computation of the normalization of `κ[[x, y]]/(q)` case by case.

The closed fibre is deliberately *not* named here, and no algebra structure is put on
`B ⧸ m_A B`: both belong to Tag 0CBT, which owns that object. Instead the field over which the
fibre is two-dimensional, and the identification of the fibre with an algebra over it, are
taken as arguments, in the manner of the parameterized statements of Chapter 42. A client
supplies a surjection `B →+* T` with kernel `m_A B`; the algebra structure on `T` need not be
compatible with anything, since only the dimension of `T` is used.

## Main definitions

* `Stacks.Curves.maximalSpectrumQuotientEquiv` — the maximal spectrum of a quotient by an ideal
  contained in every maximal ideal.

## Main results

* `Stacks.Curves.map_maximalIdeal_le_of_isMaximal` — a maximal ideal of an integral extension
  of a local ring contains the extension of the maximal ideal.
* `Stacks.Curves.encard_maximalSpectrum_quotient` — the count of maximal ideals is unchanged by
  such a quotient.
* `Stacks.Curves.encard_maximalSpectrum_le_finrank` — a finite-dimensional algebra over a field
  has at most `finrank` many maximal ideals.
* `Stacks.Curves.encard_maximalSpectrum_eq_one_or_two_of_finrank_eq_two` — a two-dimensional
  one has exactly one or two.
* `Stacks.Curves.encard_maximalSpectrum_eq_one_or_two_of_finrank_closedFibre_eq_two` — an
  integral extension of a local ring whose closed fibre is two-dimensional over a field has one
  or two maximal ideals.
* `Stacks.Curves.isSeparable_quotient` — a quotient of a separable algebra over a field is
  separable.
* `Stacks.Curves.isSeparable_quotient_and_finrank_le_two` — the residue fields of a separable
  two-dimensional closed fibre are separable of degree at most two.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/

@[expose] public noncomputable section

universe u v w t

namespace Stacks.Curves

/-! ### Maximal ideals of an integral extension of a local ring -/

/-- **A maximal ideal of an integral extension of a local ring contains the extension of the
maximal ideal.** The contraction of a maximal ideal along an integral extension is maximal,
hence is the maximal ideal of the local ring. -/
theorem map_maximalIdeal_le_of_isMaximal {A : Type u} [CommRing A] [IsLocalRing A]
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (m : Ideal B)
    [m.IsMaximal] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m := by
  have hm : (m.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) m
  rw [Ideal.map_le_iff_le_comap]
  exact le_of_eq (IsLocalRing.eq_maximalIdeal hm).symm

/-! ### The maximal spectrum of a quotient -/

/-- **The maximal ideals of a quotient by an ideal contained in every maximal ideal are the
maximal ideals of the ring.** The bijection is contraction along the quotient map, with inverse
its image. -/
def maximalSpectrumQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ m : MaximalSpectrum R, I ≤ m.asIdeal) :
    MaximalSpectrum (R ⧸ I) ≃ MaximalSpectrum R where
  toFun n :=
    ⟨n.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := n.asIdeal)
        (H := n.isMaximal)⟩
  invFun m :=
    ⟨m.asIdeal.map (Ideal.Quotient.mk I), by
      have := m.isMaximal
      refine Ideal.Quotient.maximal_of_isField _ ?_
      exact (DoubleQuot.quotQuotEquivQuotOfLE (hI m)).toMulEquiv.isField
        (Ideal.Quotient.field m.asIdeal).toIsField⟩
  left_inv n :=
    MaximalSpectrum.ext
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective n.asIdeal)
  right_inv m :=
    MaximalSpectrum.ext (by
      change Ideal.comap (Ideal.Quotient.mk I)
        (Ideal.map (Ideal.Quotient.mk I) m.asIdeal) = m.asIdeal
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        sup_eq_left.2 (hI m)])

/-- **Quotienting by an ideal contained in every maximal ideal does not change the number of
maximal ideals.** -/
theorem encard_maximalSpectrum_quotient {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ m : MaximalSpectrum R, I ≤ m.asIdeal) :
    Set.encard (Set.univ : Set (MaximalSpectrum R)) =
      Set.encard (Set.univ : Set (MaximalSpectrum (R ⧸ I))) := by
  rw [Set.encard_univ, Set.encard_univ]
  exact (ENat.card_congr (maximalSpectrumQuotientEquiv I hI)).symm

/-! ### Counting the maximal ideals of a finite-dimensional algebra -/

/-- The `encard` of the maximal spectrum is its cardinality when the latter is a `Fintype`. -/
private theorem encard_maximalSpectrum_eq_card (T : Type v) [CommRing T]
    [Fintype (MaximalSpectrum T)] :
    Set.encard (Set.univ : Set (MaximalSpectrum T)) = (Fintype.card (MaximalSpectrum T) : ℕ∞) := by
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]

/-- **A finite-dimensional algebra over a field has at most `finrank` many maximal ideals.**
Such an algebra is Artinian, so it has finitely many maximal ideals; distinct maximal ideals are
coprime, so by the Chinese remainder theorem the product of the residue fields is a quotient of
the algebra, and each factor contributes at least one to the dimension. -/
theorem encard_maximalSpectrum_le_finrank (K : Type u) [Field K] (T : Type v) [CommRing T]
    [Algebra K T] [Module.Finite K T] :
    Set.encard (Set.univ : Set (MaximalSpectrum T)) ≤ (Module.finrank K T : ℕ∞) := by
  classical
  have : IsArtinianRing T := IsArtinianRing.of_finite K T
  have : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  have hmax : ∀ m : MaximalSpectrum T, m.asIdeal.IsMaximal := fun m ↦ m.isMaximal
  have hfin : ∀ m : MaximalSpectrum T, Module.Finite K (T ⧸ m.asIdeal) := fun m ↦
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  have hntriv : ∀ m : MaximalSpectrum T, Nontrivial (T ⧸ m.asIdeal) := fun m ↦
    have := hmax m
    (Ideal.Quotient.field m.asIdeal).toNontrivial
  have hsurj : Function.Surjective
      ((LinearMap.pi fun m : MaximalSpectrum T ↦ m.asIdeal.mkQ).restrictScalars K) :=
    Ideal.pi_mkQ_surjective fun _ _ h ↦ MaximalSpectrum.isCoprime_of_ne h
  have hle : Module.finrank K (∀ m : MaximalSpectrum T, T ⧸ m.asIdeal) ≤
      Module.finrank K T :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  have hcard : Fintype.card (MaximalSpectrum T) ≤ Module.finrank K T := by
    refine le_trans (le_trans ?_ (le_of_eq (Module.finrank_pi_fintype K).symm)) hle
    rw [Fintype.card, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun m _ ↦ Module.finrank_pos
  rw [encard_maximalSpectrum_eq_card]
  exact_mod_cast hcard

/-- **An algebra of dimension two over a field has exactly one or two maximal ideals.** -/
theorem encard_maximalSpectrum_eq_one_or_two_of_finrank_eq_two (K : Type u) [Field K]
    (T : Type v) [CommRing T] [Algebra K T] [Module.Finite K T]
    (hrank : Module.finrank K T = 2) :
    Set.encard (Set.univ : Set (MaximalSpectrum T)) = 1 ∨
      Set.encard (Set.univ : Set (MaximalSpectrum T)) = 2 := by
  classical
  have : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (R := K) (M := T) (by rw [hrank]; norm_num)
  have : IsArtinianRing T := IsArtinianRing.of_finite K T
  have : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  have hcount := encard_maximalSpectrum_eq_card T
  have hle : Fintype.card (MaximalSpectrum T) ≤ 2 := by
    have h := encard_maximalSpectrum_le_finrank K T
    rw [hcount, hrank] at h
    exact_mod_cast h
  have hpos : 0 < Fintype.card (MaximalSpectrum T) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal T
    exact Fintype.card_pos_iff.2 ⟨⟨m, hm⟩⟩
  rcases show Fintype.card (MaximalSpectrum T) = 1 ∨
      Fintype.card (MaximalSpectrum T) = 2 from by omega with h | h
  · exact Or.inl (by rw [hcount, h]; rfl)
  · exact Or.inr (by rw [hcount, h]; rfl)

/-! ### The count for an integral extension of a local ring -/

/-- **An integral extension of a local ring whose closed fibre is two-dimensional over a field
has one or two maximal ideals.** This is the counting assertion of Stacks Tag 0C4A for the
normalization `B = integralClosure A (FractionRing A)` of a nodal local ring `A`, reduced to the
statement of Stacks Tag 0CBT that the closed fibre of the normalization of a node is a separable
algebra of degree two over the residue field: the hypothesis is supplied by a surjection of `B`
onto that fibre, and no case distinction between a split and a non-split node is needed. -/
theorem encard_maximalSpectrum_eq_one_or_two_of_finrank_closedFibre_eq_two
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (K : Type w) [Field K] {T : Type t} [CommRing T] [Algebra K T]
    [Module.Finite K T] (f : B →+* T) (hf : Function.Surjective f)
    (hker : RingHom.ker f = (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (hrank : Module.finrank K T = 2) :
    Set.encard (Set.univ : Set (MaximalSpectrum B)) = 1 ∨
      Set.encard (Set.univ : Set (MaximalSpectrum B)) = 2 := by
  have hI : ∀ m : MaximalSpectrum B, RingHom.ker f ≤ m.asIdeal := fun m ↦ by
    have := m.isMaximal
    rw [hker]
    exact map_maximalIdeal_le_of_isMaximal m.asIdeal
  have hquot : Set.encard (Set.univ : Set (MaximalSpectrum B)) =
      Set.encard (Set.univ : Set (MaximalSpectrum T)) := by
    rw [encard_maximalSpectrum_quotient _ hI, Set.encard_univ, Set.encard_univ]
    exact ENat.card_congr
      (maximalSpectrumCongr (RingHom.quotientKerEquivOfSurjective hf))
  rw [hquot]
  exact encard_maximalSpectrum_eq_one_or_two_of_finrank_eq_two K T hrank

/-! ### Residue fields of the closed fibre -/

/-- **A quotient of a separable algebra over a field is separable.** The minimal polynomial of
the class of `x` divides that of `x`, and a divisor of a separable polynomial is separable. -/
theorem isSeparable_quotient (K : Type u) [Field K] {T : Type v} [CommRing T] [Algebra K T]
    [Algebra.IsSeparable K T] (I : Ideal T) : Algebra.IsSeparable K (T ⧸ I) := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h0 : Polynomial.aeval (Ideal.Quotient.mk I x) (minpoly K x) = 0 := by
    have h := congrArg (Ideal.Quotient.mkₐ K I) (minpoly.aeval K x)
    rw [map_zero] at h
    rw [show (Ideal.Quotient.mk I x) = (Ideal.Quotient.mkₐ K I) x from rfl,
      Polynomial.aeval_algHom_apply]
    exact h
  exact (Algebra.IsSeparable.isSeparable K x).of_dvd (minpoly.dvd K _ h0)

/-- **The residue fields of the closed fibre are separable of degree at most two.** With
`Stacks.Curves.maximalSpectrumQuotientEquiv`, which identifies the maximal ideals of an integral
extension `B` of a local ring with those of its closed fibre, this is the residue-field
assertion of Stacks Tag 0C4A reduced to Stacks Tag 0CBT: the residue field at a maximal ideal of
the normalization of a node is a separable extension of degree one (the split case, and both
points of it) or two (the non-split case) of the residue field of the node, and so is separable
over the ground field whenever the residue field of the node is. -/
theorem isSeparable_quotient_and_finrank_le_two (K : Type u) [Field K] {T : Type v} [CommRing T]
    [Algebra K T] [Module.Finite K T] [Algebra.IsSeparable K T]
    (hrank : Module.finrank K T = 2) (m : Ideal T) :
    Algebra.IsSeparable K (T ⧸ m) ∧ Module.finrank K (T ⧸ m) ≤ 2 :=
  ⟨isSeparable_quotient K m, hrank ▸ Submodule.finrank_quotient_le (m.restrictScalars K)⟩

end Stacks.Curves

end
