module

public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.FormallySmooth.Topological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Solutions of extensions of discrete valuation rings

This file provides the common language used by elimination-of-ramification
theorems.  Given an extension of discrete valuation rings `A → B`, with
fraction fields `K → L`, and a finite extension `K → K₁`, the reduced
tensor product and its two integral closures form the base-change package of
Stacks 09EM.  A weak solution asks for ramification index one at every maximal
ideal upstairs; a solution asks for formal smoothness of the corresponding
local homomorphisms.

The structure records the canonical algebraic characterizations of the three
rings instead of fixing implementation-specific carrier types.  This keeps the
predicates usable by constructions that choose different presentations of the
reduced tensor product or integral closures.

## Main definitions

* `IsDiscreteValuationRing.IsExtension`: an injective local map of DVRs.
* `IsDiscreteValuationRing.ramificationIndex` and `residueDegree`: the two numerical invariants.
* `IsDiscreteValuationRing.IsWeaklyUnramified`: ramification index one.
* `IsDiscreteValuationRing.IntegralClosureBaseChange`: the base-change data.
* `IntegralClosureBaseChange.IsWeakSolution`: a weak solution (09EN(1)).
* `IntegralClosureBaseChange.IsSolution`: a solution (09EN(2)).
* `IntegralClosureBaseChange.IsSeparableSolution`: a separable solution.

## Main results

* `IsDiscreteValuationRing.ramificationIndex_characterization`: the ramification index is
  positive, is the unique positive exponent with `m_A B = m_B ^ e`, and is the exponent
  relating any two choices of uniformizers up to a unit.

## References

* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
-/

@[expose] public section

open scoped TensorProduct

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

namespace IsDiscreteValuationRing

/-- An extension of discrete valuation rings is an injective local algebra map. -/
@[stacks 09E4]
class IsExtension (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] : Prop extends
    FaithfulSMul A B, IsLocalHom (algebraMap A B)

/-- The ramification index of an extension of discrete valuation rings. -/
@[stacks 09E4, sga "7 IX 10.3", sga "7 IX 9.7"]
noncomputable abbrev ramificationIndex (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B] : ℕ :=
  Stacks.DiscreteValuationRing.Ramification.ramificationIdx A B

/-- An extension of DVRs is weakly unramified when its ramification index is one. -/
@[stacks 09E4]
abbrev IsWeaklyUnramified (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B] : Prop :=
  ramificationIndex A B = 1

/-- The residue degree of an extension of discrete valuation rings. -/
@[stacks 09E4]
noncomputable abbrev residueDegree (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B] : ℕ :=
  Ideal.inertiaDeg (IsLocalRing.maximalIdeal B) A

/-- The reduced compositum and integral closures associated to a finite extension `K₁/K`.

The compatibility fields identify `L₁` with the reduction of `L ⊗[K] K₁` and ensure
that the maps through `A₁`, `B₁`, and the two fraction fields form the expected square. -/
structure IntegralClosureBaseChange
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] where
  /-- The reduced compositum of `L` and `K₁` over `K`. -/
  L₁ : Type uL₁
  /-- The integral closure of `A` in `K₁`. -/
  A₁ : Type uA₁
  /-- The integral closure of `B` in `L₁`. -/
  B₁ : Type uB₁
  [commRingL₁ : CommRing L₁]
  [commRingA₁ : CommRing A₁]
  [commRingB₁ : CommRing B₁]
  [algebraKL₁ : Algebra K L₁]
  [algebraLL₁ : Algebra L L₁]
  [algebraK₁L₁ : Algebra K₁ L₁]
  [algebraBL₁ : Algebra B L₁]
  [algebraAA₁ : Algebra A A₁]
  [algebraA₁K₁ : Algebra A₁ K₁]
  [algebraBB₁ : Algebra B B₁]
  [algebraB₁L₁ : Algebra B₁ L₁]
  [algebraAB₁ : Algebra A B₁]
  [algebraA₁B₁ : Algebra A₁ B₁]
  [isScalarTowerKLL₁ : IsScalarTower K L L₁]
  [isScalarTowerKK₁L₁ : IsScalarTower K K₁ L₁]
  [isScalarTowerBLL₁ : IsScalarTower B L L₁]
  [isScalarTowerAA₁K₁ : IsScalarTower A A₁ K₁]
  [isScalarTowerBB₁L₁ : IsScalarTower B B₁ L₁]
  [isScalarTowerABB₁ : IsScalarTower A B B₁]
  [isScalarTowerAA₁B₁ : IsScalarTower A A₁ B₁]
  [isIntegralClosureA₁ : IsIntegralClosure A₁ A K₁]
  [isIntegralClosureB₁ : IsIntegralClosure B₁ B L₁]
  /-- The `K`-algebra isomorphism of `L₁` with the reduction of `L ⊗[K] K₁`. -/
  eL₁ : L₁ ≃ₐ[K] ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))
  eL₁_left : ∀ x : L,
    eL₁ (algebraMap L L₁ x) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x)
  eL₁_right : ∀ x : K₁,
    eL₁ (algebraMap K₁ L₁ x) = Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)
  ringSquare : ∀ x : A₁,
    algebraMap B₁ L₁ (algebraMap A₁ B₁ x) =
      algebraMap K₁ L₁ (algebraMap A₁ K₁ x)

namespace IntegralClosureBaseChange

/-- Every localization arising from the base change has ramification index one. -/
@[stacks 09EN "(1), weak solution"]
def IsWeakSolution
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
    {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange A B K L K₁) : Prop :=
  letI := D.commRingA₁
  letI := D.commRingB₁
  letI := D.algebraA₁B₁
  ∀ (q : Ideal D.B₁), q.IsMaximal → q.ramificationIdx D.A₁ = 1

/-- Every localization arising from the base change is formally smooth for the adic topology
defined by the maximal ideal of the target localization. -/
@[stacks 09EN "(2), solution"]
def IsSolution.{v}
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
    {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁) : Prop :=
  letI := D.commRingA₁
  letI := D.commRingB₁
  letI := D.algebraA₁B₁
  ∀ (q : Ideal D.B₁) (hq : q.IsMaximal),
    letI : q.IsPrime := hq.isPrime
    let p := q.comap (algebraMap D.A₁ D.B₁)
    letI : p.IsPrime := Ideal.IsPrime.comap (algebraMap D.A₁ D.B₁)
    RingHom.FormallySmoothNAdic.{v, uA₁, uB₁}
      (Localization.localRingHom p q (algebraMap D.A₁ D.B₁) rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))

/-- A solution whose finite extension `K₁/K` is separable. -/
@[stacks 09EN "separable solution"]
def IsSeparableSolution.{v}
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
    {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁) : Prop :=
  D.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, v} ∧
    Algebra.IsSeparable K K₁

end IntegralClosureBaseChange

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/-- The ramification index is positive, is the unique positive exponent expressing the extended
maximal ideal as a power of the maximal ideal upstairs, and is the exponent relating any choices
of uniformizers up to a unit. -/
@[stacks 09E4, sga "7 IX 10.3" "special case"]
theorem ramificationIndex_characterization (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    1 ≤ ramificationIndex A B ∧
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
        IsLocalRing.maximalIdeal B ^ ramificationIndex A B ∧
      (∀ e : ℕ, 1 ≤ e →
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
          IsLocalRing.maximalIdeal B ^ e →
        e = ramificationIndex A B) ∧
      ∀ πA : A, Irreducible πA → ∀ πB : B, Irreducible πB →
        ∃ u : Bˣ, algebraMap A B πA = (u : B) * πB ^ ramificationIndex A B := by
  have hideal :=
    Stacks.DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx A
      B
  refine ⟨Stacks.DiscreteValuationRing.Ramification.one_le_ramificationIdx A B, hideal, ?_, ?_⟩
  · intro e _ he
    have hpows : IsLocalRing.maximalIdeal B ^ e
        = IsLocalRing.maximalIdeal B ^ ramificationIndex A B := he.symm.trans hideal
    have hcoe : (e : ℕ∞) = (ramificationIndex A B : ℕ∞) :=
      (IsDiscreteValuationRing.idealOrderIsoENat B).symm.injective hpows
    exact_mod_cast hcoe
  · intro πA hπA πB hπB
    have hne : algebraMap A B πA ≠ 0 := fun h =>
      hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (by simpa using h))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπB
    have hval := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx A B
      πA hπA
    have hn : n = ramificationIndex A B := by
      rw [hu, IsDiscreteValuationRing.addVal_mul,
        IsDiscreteValuationRing.addVal_eq_zero_of_unit,
        IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hπB, nsmul_eq_mul,
        zero_add, mul_one] at hval
      exact_mod_cast hval
    rw [hn] at hu
    exact ⟨u, hu⟩

/-- **Weak unramifiedness is generation of the maximal ideal.**

Ramification index one for an extension of discrete valuation rings says exactly that `𝔪_A`
generates `𝔪_B`. Both directions come out of `ramificationIndex_characterization`: one from the
identification of `𝔪_B ^ e` with the image ideal, the other from minimality of `e`. -/
theorem weaklyUnramified_iff_map_maximalIdeal (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    IsWeaklyUnramified A B ↔
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  obtain ⟨h1, h2, h3, -⟩ := ramificationIndex_characterization A B
  unfold IsWeaklyUnramified
  constructor
  · intro h
    rw [h2, h, pow_one]
  · intro h
    exact (h3 1 le_rfl (by rw [h, pow_one])).symm

/-- The image of the maximal ideal of a discrete valuation ring is generated by the image of
any uniformizer. -/
private theorem map_maximalIdeal_eq_span_algebraMap {A B : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [Algebra A B] {π : A} (hπ : Irreducible π) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = Ideal.span {algebraMap A B π} := by
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- An extension of discrete valuation rings carrying some element of the base to a uniformizer
upstairs is weakly unramified; the element is then a uniformizer of the base. -/
theorem isWeaklyUnramified_of_irreducible_algebraMap (A B : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (π : A) (hπ : Irreducible (algebraMap A B π)) :
    IsWeaklyUnramified A B := by
  exact (weaklyUnramified_iff_map_maximalIdeal A B).mpr
    (by rw [map_maximalIdeal_eq_span_algebraMap hπ.of_map, hπ.maximalIdeal_eq])

/-- `IsDiscreteValuationRing.ramificationIndex` is the length-theoretic ramification index of
the maximal ideal upstairs. -/
@[sga "7 IX 10.3" "special case", sga "7 VIII 7.3.5"]
theorem ramificationIndex_eq_ramificationIdx (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B] :
    ramificationIndex A B = (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective A B)
  let : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  exact Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B) (IsDiscreteValuationRing.not_a_field A)

/-! ### Transitivity of the ramification index, and of weak unramifiedness -/

/-- The ramification index is multiplicative in a tower. -/
theorem ramificationIndex_trans (A B C : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsExtension A B]
    [IsExtension B C] [IsExtension A C] :
    ramificationIndex A C =
      ramificationIndex A B * ramificationIndex B C := by
  obtain ⟨h1, h2, -, -⟩ := ramificationIndex_characterization A B
  obtain ⟨h1', h2', -, -⟩ := ramificationIndex_characterization B C
  obtain ⟨-, -, h3, -⟩ := ramificationIndex_characterization A C
  symm
  apply h3 _ (one_le_mul h1 h1')
  rw [IsScalarTower.algebraMap_eq A B C, ← Ideal.map_map, h2, Ideal.map_pow, h2', ← pow_mul,
    mul_comm]

/-- Weak unramifiedness is transitive: if `A → B` and `B → C` each have ramification index one,
so does `A → C`. -/
theorem isWeaklyUnramified_trans (A B C : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [IsExtension A B]
    [IsExtension B C] [IsExtension A C]
    (hAB : IsWeaklyUnramified A B) (hBC : IsWeaklyUnramified B C) :
    IsWeaklyUnramified A C := by
  unfold IsWeaklyUnramified at *
  rw [ramificationIndex_trans A B C, hAB, hBC]

/-- Weak unramifiedness of the whole tower implies weak unramifiedness of its bottom step. -/
theorem isWeaklyUnramified_tower_bot (A B C : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [IsExtension A B] [IsExtension B C] [IsExtension A C]
    (h : IsWeaklyUnramified A C) : IsWeaklyUnramified A B := by
  unfold IsWeaklyUnramified at *
  rw [ramificationIndex_trans A B C] at h
  exact Nat.eq_one_of_mul_eq_one_right h

/-! ### Discrete valuation rings from root adjunction and from directed unions -/

/-- Adjoining a root of a monic polynomial with irreducible reduction to a discrete valuation
ring gives a discrete valuation ring whose maximal ideal is generated by the image of the maximal
ideal. -/
theorem adjoinRoot_isDiscreteValuationRing
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (p : Polynomial R) (hp : p.Monic)
    (hirr : Irreducible (p.map (IsLocalRing.residue R))) :
    ∃ (_ : IsDomain (AdjoinRoot p)) (_ : IsDiscreteValuationRing (AdjoinRoot p)),
      (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot p)) =
        IsLocalRing.maximalIdeal (AdjoinRoot p) := by
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime
    (hp.irreducible_of_irreducible_map (IsLocalRing.residue R) p hirr).prime
  have : Module.Finite R (AdjoinRoot p) := hp.finite_adjoinRoot
  have : Module.Free R (AdjoinRoot p) := hp.free_adjoinRoot
  have : Algebra.IsIntegral R (AdjoinRoot p) := Algebra.IsIntegral.of_finite R _
  let m := (IsLocalRing.maximalIdeal R).map (algebraMap R (AdjoinRoot p))
  have hm : m.IsMaximal := by
    have : (Ideal.span {p.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hirr
    exact Ideal.Quotient.maximal_of_isField _ <| MulEquiv.isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
        (IsLocalRing.maximalIdeal R) p).toMulEquiv
  have : IsLocalRing (AdjoinRoot p) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨m, hm, fun q hq => ?_⟩
    have hc : q.comap (algebraMap R (AdjoinRoot p)) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q)
    exact (hm.eq_of_le hq.ne_top (Ideal.map_le_iff_le_comap.mpr hc.symm.le)).symm
  have he : m = IsLocalRing.maximalIdeal (AdjoinRoot p) := IsLocalRing.eq_maximalIdeal hm
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hgen : IsLocalRing.maximalIdeal (AdjoinRoot p) =
      Ideal.span {algebraMap R (AdjoinRoot p) π} := by
    rw [← he]
    exact map_maximalIdeal_eq_span_algebraMap hπ
  have hnf : ¬ IsField (AdjoinRoot p) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hgen, Ideal.span_singleton_eq_bot]
    simpa using (FaithfulSMul.algebraMap_injective R (AdjoinRoot p)).ne hπ.ne_zero
  have hprin : (IsLocalRing.maximalIdeal (AdjoinRoot p)).IsPrincipal := by
    rw [hgen]
    infer_instance
  exact ⟨inferInstance, ((IsDiscreteValuationRing.TFAE (AdjoinRoot p) hnf).out 5 1).mp hprin, he⟩

/-- A directed union of discrete valuation subrings sharing a uniformizer is a discrete valuation
ring, with that element as a uniformizer. -/
theorem isDiscreteValuationRing_of_directed_union
    {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (S : ι → Subring R) [∀ i, IsDiscreteValuationRing (S i)]
    (hS : Monotone S) (hcover : ∀ x : R, ∃ i, x ∈ S i)
    (π : R) (hmem : ∀ i, π ∈ S i) (hπ : ∀ i, Irreducible (⟨π, hmem i⟩ : S i)) :
    IsDiscreteValuationRing R ∧ Irreducible π := by
  have hπR : Irreducible π := by
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨i, hi⟩ := hcover (↑u⁻¹ : R)
      refine (hπ i).not_isUnit (isUnit_iff_exists_inv.mpr ⟨⟨↑u⁻¹, hi⟩, Subtype.ext ?_⟩)
      show π * (↑u⁻¹ : R) = 1
      rw [← hu, Units.mul_inv]
    · intro a b hab
      obtain ⟨i, hi⟩ := hcover a
      obtain ⟨j, hj⟩ := hcover b
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      have hf : (⟨π, hmem k⟩ : S k) = ⟨a, hS hik hi⟩ * ⟨b, hS hjk hj⟩ := Subtype.ext hab
      exact ((hπ k).isUnit_or_isUnit hf).imp
        (fun ha => ha.map (S k).subtype) (fun hb => hb.map (S k).subtype)
  refine ⟨?_, hπR⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hπR, fun {x} hx => ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  have hxi : (⟨x, hi⟩ : S i) ≠ 0 := fun h => hx (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi (hπ i)
  let v : Rˣ := Units.map (S i).subtype.toMonoidHom u
  have he : x = (v : R) * π ^ n := by
    simpa [v] using congrArg (fun z : S i => (z : R)) hu
  exact ⟨n, v, by rw [he, mul_comm]⟩

/-- A nonempty chain of discrete valuation subalgebras sharing a uniformizer has a discrete
valuation supremum, with the same uniformizer. -/
theorem isDiscreteValuationRing_sSup_chain
    {A Ω : Type*} [CommRing A] [Field Ω] [Algebra A Ω]
    (π : A) (c : Set (Subalgebra A Ω)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hDVR : ∀ S ∈ c, IsDiscreteValuationRing S)
    (hπ : ∀ S ∈ c, Irreducible (algebraMap A S π)) :
    IsDiscreteValuationRing (sSup c : Subalgebra A Ω) ∧
      Irreducible (algebraMap A (sSup c : Subalgebra A Ω) π) := by
  classical
  let U : Subalgebra A Ω := sSup c
  have : Nonempty c := hne.to_subtype
  have : IsDirectedOrder c := ⟨fun i j => by
    rcases hc.total i.property j.property with h | h
    · exact ⟨j, h, le_rfl⟩
    · exact ⟨i, le_rfl, h⟩⟩
  let S (i : c) : Subring U := i.val.toSubring.comap U.val.toRingHom
  let e (i : c) : i.val ≃+* S i :=
    { toFun x := ⟨⟨x, le_sSup i.property x.property⟩, x.property⟩
      invFun x := ⟨x.val.val, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have (i : c) : IsDiscreteValuationRing (S i) := by
    have := hDVR i i.property
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (e i)
  have hmono : Monotone S := fun i j hij _ hx => hij hx
  have hcover (x : U) : ∃ i, x ∈ S i := by
    have hx : (x : Ω) ∈ ⨆ i : c, i.val := by
      simpa only [U, sSup_eq_iSup, iSup_subtype] using x.property
    have hd : Directed (· ≤ ·) (fun i : c => i.val) := fun i j => by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      exact ⟨k, hik, hjk⟩
    change (x : Ω) ∈ ((⨆ i : c, i.val : Subalgebra A Ω) : Set Ω) at hx
    rw [Subalgebra.coe_iSup_of_directed hd, Set.mem_iUnion] at hx
    exact hx
  let πU : U := algebraMap A U π
  have hmem (i : c) : πU ∈ S i := i.val.algebraMap_mem π
  have hπS (i : c) : Irreducible (⟨πU, hmem i⟩ : S i) :=
    (MulEquiv.irreducible_iff (e i)).mpr (hπ i i.property)
  exact isDiscreteValuationRing_of_directed_union S hmono hcover πU hmem hπS

end IsDiscreteValuationRing
