module

import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.RingTheory.IntegralClosure.AlmostIntegral
public import StacksFrontier.RingTheory.KrullAkizuki
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension formula: preliminaries and the one-generator step

Codimension of irreducible closeds of `Spec A` versus heights of primes, additivity of heights
in universally catenary domains, the invariance of residue-field transcendence degrees under
surjections and isomorphisms, and the catenary one-generator step `single_generator_step` of
the dimension formula (Stacks 02IJ): the extensions `A ⊆ A[X]` and `A ⊆ A[X] ⧸ n` with `n` a
height-one prime meeting `A` in `(0)`. The induction on generators and the dimension formula
itself are in `StacksFrontier.RingTheory.DimensionFormula.GeneratorInduction`.

## Main definitions

* `Ideal.ResidueField.algebraOfLiesOver`: the `κ(p)`-algebra structure on `κ(q)` carried by a
  prime `q` lying over `p`.
* `zeroLocusIsoIic`: the closed subset `V(P)` of `Spec A`, ordered by inclusion of primes, is
  antitone-isomorphic to the set of irreducible closeds contained in the closure of `P`.

## Main results

* `topCodim_closureSingleton_eq_height_map_quotientMk`: for primes `p ⊆ q` of `A`, the
  codimension of the closure of `q` inside the closure of `p` in `Spec A` is the height of the
  image of `q` in `A ⧸ p`.

## References

* [StackProject 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
-/

@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
/-- The residue field extension `κ(q)/κ(p)` attached to a prime `q` of `S` lying over a prime
`p` of `R`: the `κ(p)`-algebra structure on `κ(q)` whose structure map is
`Ideal.ResidueField.map p q (algebraMap R S)`.

This is the widely used spelling of `Ideal.residueFieldAlgebra`, which it delegates to so that the
extension is defined once. -/
noncomputable abbrev Ideal.ResidueField.algebraOfLiesOver (p : Ideal R) (q : Ideal S)
    [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Algebra p.ResidueField q.ResidueField :=
  Ideal.residueFieldAlgebra p q

/-- A chain starting at `Y` and ending below `Y'` has length at most `topCodim Y Y'`. -/
private theorem length_le_topCodim_of_last_le {X : Type u} [TopologicalSpace X]
    (Y Y' : TopologicalSpace.IrreducibleCloseds X)
    (p : LTSeries (TopologicalSpace.IrreducibleCloseds X)) (hh : p.head = Y) (hle : p.last ≤ Y') :
    (p.length : ℕ∞) ≤ IrreducibleClosedsCodim.topCodim Y Y' := by
  by_cases hlast : p.last = Y'
  · exact IrreducibleClosedsCodim.length_le_topCodim Y Y' p hh hlast
  · refine le_trans ?_ (IrreducibleClosedsCodim.length_le_topCodim Y Y'
      (p.snoc Y' (lt_of_le_of_ne hle hlast)) (by rw [RelSeries.head_snoc]; exact hh)
      (RelSeries.last_snoc ..))
    rw [RelSeries.snoc_length]; exact_mod_cast Nat.le_succ _

/-- For `Y ≤ Y'` irreducible closeds of a topological space, the codimension of `Y` in `Y'`
equals the order coheight of `Y` in the down-set `Set.Iic Y'`. Both count strictly increasing
chains out of `Y`; on the ambient side they end at `Y'`, on the subposet side they range over
`Iic Y'`, and appending `Y'` identifies the two suprema. -/
theorem topCodim_eq_coheight_Iic {X : Type u} [TopologicalSpace X]
    (Y Y' : TopologicalSpace.IrreducibleCloseds X) (hYY' : Y ≤ Y') :
    IrreducibleClosedsCodim.topCodim Y Y' = Order.coheight (⟨Y, hYY'⟩ : ↑(Set.Iic Y')) := by
  apply le_antisymm
  · rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro p hh hl
    have hmono : ∀ i, p i ≤ Y' := by intro i; rw [← hl]; exact p.monotone (Fin.le_last i)
    set q : LTSeries ↑(Set.Iic Y') := ⟨p.length, fun i => ⟨p i, hmono i⟩, p.step⟩
    have hqh : q.head = ⟨Y, hYY'⟩ := Subtype.ext hh
    exact hqh ▸ Order.length_le_coheight_head (p := q)
  · rw [Order.coheight_eq_iSup_head_eq]
    refine iSup_le fun q => iSup_le fun hqh => ?_
    set p := q.map (fun a => (a : TopologicalSpace.IrreducibleCloseds X)) fun _ _ h => h
    have hph : p.head = Y := congrArg Subtype.val hqh
    exact length_le_topCodim_of_last_le Y Y' p hph q.last.property

/-- For `Ymax` a greatest irreducible closed, the codimension of `Y` in `Ymax` is the order
coheight of `Y`. -/
theorem topCodim_eq_coheight_of_isMax {X : Type u} [TopologicalSpace X]
    (Y Ymax : TopologicalSpace.IrreducibleCloseds X) (hmax : ∀ z, z ≤ Ymax) :
    IrreducibleClosedsCodim.topCodim Y Ymax = Order.coheight Y := by
  apply le_antisymm
  · rw [IrreducibleClosedsCodim.topCodim_le_iff]
    exact fun p hh _ => hh ▸ Order.length_le_coheight_head
  · rw [Order.coheight_eq_iSup_head_eq]
    refine iSup_le fun p => iSup_le fun hh => ?_
    exact length_le_topCodim_of_last_le Y Ymax p hh (hmax _)

/-- The height of a point of `Spec A` is the coheight of its closure, computed through the
order-reversing equivalence `PrimeSpectrum.pointsEquivIrreducibleCloseds` between points and
irreducible closeds. -/
theorem height_eq_coheight_irreducibleCloseds {A : Type u} [CommRing A] (x : PrimeSpectrum A) :
    Order.height x
      = Order.coheight (OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A x)) := by
  rw [← Order.height_orderIso (PrimeSpectrum.pointsEquivIrreducibleCloseds A) x,
      Order.coheight_ofDual]

/-- The closure of the generic point of `Spec A`, for `A` a domain, is the greatest irreducible
closed: it is the whole space `V(0)`. -/
theorem le_pointsEquiv_bot {A : Type u} [CommRing A] [IsDomain A]
    (z : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A)) :
    z ≤ OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A ⊥) := by
  set e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  have h1 : e ⊥ ≤ e (e.symm (OrderDual.toDual z)) := e.monotone bot_le
  rwa [e.apply_symm_apply] at h1

/-- The zero locus `V(P)` of a prime `P`, ordered by inclusion of primes, is antitone-isomorphic
to the down-set of irreducible closeds contained in the closure of `P`; both are cut out of
`PrimeSpectrum.pointsEquivIrreducibleCloseds A` by the condition `P ≤ ·`. -/
noncomputable def zeroLocusIsoIic {A : Type u} [CommRing A] (P : Ideal A) [hPp : P.IsPrime] :
    (↑(PrimeSpectrum.zeroLocus (P:Set A)))ᵒᵈ ≃o
      ↑(Set.Iic (OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A ⟨P, hPp⟩))) :=
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  let Pp : PrimeSpectrum A := ⟨P, hPp⟩
  have hmem : ∀ x : PrimeSpectrum A, x ∈ PrimeSpectrum.zeroLocus (P:Set A) ↔ Pp ≤ x := by
    intro x; rw [PrimeSpectrum.mem_zeroLocus]; exact Iff.rfl
  { toFun := fun x => ⟨OrderDual.ofDual (e (OrderDual.ofDual x).val), by
      have h2 : e Pp ≤ e (OrderDual.ofDual x).val :=
        e.monotone ((hmem _).mp (OrderDual.ofDual x).property)
      exact Set.mem_Iic.mpr h2⟩
    invFun := fun y => OrderDual.toDual ⟨e.symm (OrderDual.toDual y.val), by
      rw [hmem]
      have h2 : e.symm (OrderDual.toDual y.val) ≥ e.symm (e Pp) := e.symm.monotone y.property
      rwa [e.symm_apply_apply] at h2⟩
    left_inv := by
      intro x; apply OrderDual.ofDual.injective; apply Subtype.ext; simp [e.symm_apply_apply]
    right_inv := by intro y; apply Subtype.ext; simp [e.apply_symm_apply]
    map_rel_iff' := by
      intro x y
      change (OrderDual.ofDual (e (OrderDual.ofDual x).val)
          ≤ OrderDual.ofDual (e (OrderDual.ofDual y).val)) ↔ x ≤ y
      change (e (OrderDual.ofDual y).val ≤ e (OrderDual.ofDual x).val) ↔ x ≤ y
      rw [e.le_iff_le]; exact Iff.rfl }

/-- For primes `p ≤ q` of `A`, the codimension of the closure of `q` in the closure of `p` is the
height of `q` in the zero locus `V(p)`. -/
private theorem topCodim_pointsEquiv_eq_height_zeroLocus {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    (hq : q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) :
    IrreducibleClosedsCodim.topCodim
        (OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A q))
        (OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A p)) =
      Order.height (⟨q, hq⟩ : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) := by
  have hle : OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A q) ≤
      OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds A p) :=
    (PrimeSpectrum.pointsEquivIrreducibleCloseds A).monotone hpq
  rw [topCodim_eq_coheight_Iic _ _ hle]
  have hg := Order.coheight_orderIso (zeroLocusIsoIic p.asIdeal) (OrderDual.toDual ⟨q, hq⟩)
  rw [show (zeroLocusIsoIic p.asIdeal) (OrderDual.toDual ⟨q, hq⟩) = ⟨_, hle⟩ from rfl] at hg
  rw [hg, Order.coheight_toDual]

/-- For primes `p ≤ q` of `A`, the height of the image of `q` in `A ⧸ p` is the height of `q` in
the zero locus `V(p)`. -/
private theorem height_map_quotientMk_eq_height_zeroLocus {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p ≤ q)
    (hq : q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height =
      Order.height (⟨q, hq⟩ : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A))) := by
  have : (Ideal.map (Ideal.Quotient.mk p.asIdeal) q.asIdeal).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  set qP : PrimeSpectrum (A ⧸ p.asIdeal) :=
    ⟨Ideal.map (Ideal.Quotient.mk p.asIdeal) q.asIdeal, this⟩
  have himg : Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal qP = ⟨q, hq⟩ :=
    Subtype.ext (PrimeSpectrum.ext (Ideal.comap_map_mk hpq))
  rw [PrimeSpectrum.height_eq_orderHeight qP]
  change Order.height qP = _
  rw [← Order.height_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus p.asIdeal) qP, himg]

/-- For primes `p ⊆ q` of `A`, the codimension of the closure of `q` inside the closure of `p`
in `Spec A` is the height of the image of `q` in `A ⧸ p`, equivalently the dimension of the
local ring `(A ⧸ p)_q`. No Noetherian, catenary or domain hypothesis is needed: both sides count
the strictly increasing chains of primes from `p` to `q`, the left through the antitone
equivalence of `V(p)` with the irreducible closeds below the closure of `p`, the right through
the order isomorphism of `Spec (A ⧸ p)` with `V(p)`. -/
theorem topCodim_closureSingleton_eq_height_map_quotientMk {A : Type u} [CommRing A]
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    IrreducibleClosedsCodim.topCodim (TopologicalSpace.IrreducibleCloseds.closureSingleton q)
        (TopologicalSpace.IrreducibleCloseds.closureSingleton p) =
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have hQzero : q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]; exact hpq
  exact (topCodim_pointsEquiv_eq_height_zeroLocus p q hpq hQzero).trans
    (height_map_quotientMk_eq_height_zeroLocus p q hpq hQzero).symm

/-- In a catenary space, the codimension from `Y` to `Y'` adds along `Y ≤ Y'' ≤ Y'`. -/
@[ega "0 16.1.4" "partial, special case", ega "IV 10.7.2" "more general"]
theorem catenary_orderHeight_add
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (hcat : IsUniversallyCatenary A)
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q)
    (hQzero : (⟨Q, inferInstance⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (P : Set A)) :
    Order.height (⟨Q, inferInstance⟩ : PrimeSpectrum A)
      = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A)
        + Order.height (⟨⟨Q, inferInstance⟩, hQzero⟩
            : ↑(PrimeSpectrum.zeroLocus (P : Set A))) := by
  set e := PrimeSpectrum.pointsEquivIrreducibleCloseds A with he
  set Pp : PrimeSpectrum A := ⟨P, inferInstance⟩ with hPp
  set Qq : PrimeSpectrum A := ⟨Q, inferInstance⟩ with hQq
  set cP : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) := OrderDual.ofDual (e Pp) with hcP
  set cQ : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) := OrderDual.ofDual (e Qq) with hcQ
  set cB : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum A) := OrderDual.ofDual (e ⊥) with hcB
  have hPQ' : Pp ≤ Qq := hPQ
  have hcQP : cQ ≤ cP := e.monotone hPQ'
  have hcPB : cP ≤ cB := le_pointsEquiv_bot _
  have hcQB : cQ ≤ cB := le_pointsEquiv_bot _
  have hcatsp : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) :=
    hcat A inferInstance
  have hadd := topCodim_additive_of_catenary hcatsp cQ cP cB hcQP hcPB
  have h1 : IrreducibleClosedsCodim.topCodim cQ cB = Order.height Qq := by
    rw [topCodim_eq_coheight_of_isMax cQ cB le_pointsEquiv_bot,
      ← height_eq_coheight_irreducibleCloseds]
  have h2 : IrreducibleClosedsCodim.topCodim cP cB = Order.height Pp := by
    rw [topCodim_eq_coheight_of_isMax cP cB le_pointsEquiv_bot,
      ← height_eq_coheight_irreducibleCloseds]
  have h3 := topCodim_pointsEquiv_eq_height_zeroLocus Pp Qq hPQ' hQzero
  rw [h1, h2, h3] at hadd
  rw [hadd, add_comm]

/-- In a Noetherian universally catenary domain `A`, heights are additive along an inclusion
`P ≤ Q` of primes: `Q.height = P.height + (Q / P).height`, where `Q / P` is the image of `Q`
in `A ⧸ P`. -/
@[ega "0 16.1.4" "partial, special case", ega "IV 10.7.2" "more general"]
theorem catenary_height_add
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (hcat : IsUniversallyCatenary A)
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) :
    Q.height = P.height + (Ideal.map (Ideal.Quotient.mk P) Q).height := by
  have hQzero : (⟨Q, inferInstance⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (P : Set A) := by
    rw [PrimeSpectrum.mem_zeroLocus]; exact hPQ
  have hquot := height_map_quotientMk_eq_height_zeroLocus ⟨P, inferInstance⟩ ⟨Q, inferInstance⟩
    hPQ hQzero
  rw [PrimeSpectrum.height_eq_orderHeight ⟨Q, inferInstance⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨P, inferInstance⟩, hquot]
  exact catenary_orderHeight_add hcat P Q hPQ hQzero

/-- The field of rational functions over `K` has transcendence degree one over `K`. -/
theorem ratFunc_trdeg_eq_one (K : Type u) [Field K] :
    Algebra.trdeg K (RatFunc K) = 1 := by
  have hfaith : FaithfulSMul (Polynomial K) (RatFunc K) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact IsFractionRing.injective _ _
  have halg : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors (Polynomial K))
  have htower := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at htower
  exact htower.symm

/-- For `Q = P·A[X]` the constant-fibre prime over `P`, the residue field `κ(Q)` is the field
of rational functions `κ(P)(x)`, so its transcendence degree over `κ(P)` is one; in particular
it is at least one. -/
theorem const_fiber_residue_trdeg_pos {A : Type u} [CommRing A] [IsDomain A]
    (P : Ideal A) (Q : Ideal (Polynomial A)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    (hQeq : Q = Ideal.map (algebraMap A (Polynomial A)) P) :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    (1 : ℕ∞) ≤ (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
  have hQeqC : Q = Ideal.map Polynomial.C P := by
    rw [hQeq, Polynomial.algebraMap_eq]
  let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  have : Localization.AtPrime.IsLiesOverAlgebra P Q :=
    Localization.AtPrime.instIsLiesOverAlgebra P Q
  have e := Polynomial.residueFieldMapCAlgEquiv P Q hQeqC
  let ealg : Q.ResidueField ≃ₐ[P.ResidueField] RatFunc P.ResidueField :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) e.commutes
  have hfinal : Algebra.trdeg P.ResidueField Q.ResidueField = 1 :=
    (AlgEquiv.trdeg_eq ealg).trans (ratFunc_trdeg_eq_one P.ResidueField)
  have h2 : (1 : ℕ∞) ≤ ((Cardinal.toNat (1 : Cardinal)) : ℕ∞) := by
    rw [Cardinal.one_toNat, Nat.cast_one]
  exact hfinal ▸ h2

/-- A nonzero ideal of a domain has height at least one. -/
private theorem one_le_height_of_ne_bot {A : Type u} [CommRing A] [IsDomain A] {I : Ideal A}
    (h : I ≠ ⊥) : 1 ≤ I.height :=
  Order.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 h)

/-- The dimension-formula inequality for the polynomial extension `A ⊆ A[X]` of a Noetherian
universally catenary domain: `P.height + trdeg_A A[X] ≤ Q.height + trdeg_{κ(P)} κ(Q)` for `Q` a
prime of `A[X]` lying over `P`. Both fibre cases give equality, `height P + 1 = height Q +
trdeg_{κ(P)} κ(Q)`: over the constant fibre `Q = P·A[X]` the height is unchanged and the residue
degree is one, and over a closed fibre the height grows by one and the residue degree is zero. -/
private theorem single_generator_step_poly {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsDomain A]
    (P : Ideal A) (Q : Ideal (Polynomial A)) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    P.height + (Cardinal.toNat (Algebra.trdeg A (Polynomial A)) : ℕ∞)
      ≤ Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
  rw [Polynomial.trdeg_of_isDomain, map_one, Nat.cast_one]
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  set F : Ideal (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P) :=
    Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) Q with hF
  have hQh : Q.height = P.height + F.height :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q
  set t : ℕ∞ := (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) with ht
  rw [hQh, add_assoc]
  gcongr P.height + ?_
  have hPtilde_le : Ideal.map (algebraMap A (Polynomial A)) P ≤ Q := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (p := P) (P := Q))
  have hdomB : IsDomain (Polynomial A ⧸ Ideal.map (algebraMap A (Polynomial A)) P) := by
    rw [Polynomial.algebraMap_eq]
    exact Ideal.isDomain_map_C_quotient inferInstance
  have hFprime : F.IsPrime := by
    rw [hF]
    exact Ideal.isPrime_map_quotientMk_of_isPrime hPtilde_le
  by_cases hFbot : F = ⊥
  · -- Constant fiber: Q = P·A[X]; residue field κ(Q) = κ(P)(x), so trdeg = 1, t ≥ 1.
    rw [hFbot, Ideal.height_bot, zero_add]
    have hQeq : Q = Ideal.map (algebraMap A (Polynomial A)) P := by
      have hQle : Q ≤ Ideal.map (algebraMap A (Polynomial A)) P := by
        rw [hF] at hFbot
        intro x hx
        have : (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) x
            ∈ Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A (Polynomial A)) P)) Q :=
          Ideal.mem_map_of_mem _ hx
        rw [hFbot] at this
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa using this
      exact le_antisymm hQle hPtilde_le
    rw [ht]
    exact const_fiber_residue_trdeg_pos P Q hQeq
  · -- Closed fiber: F ≠ ⊥, so F.height ≥ 1.
    exact (one_le_height_of_ne_bot hFbot).trans le_self_add

/-- For `n` a height-one prime of `A[X]` with `n ∩ A = (0)`, the quotient `A[X] ⧸ n` is algebraic
over `A`, hence of transcendence degree zero: it is generated by the class of `X`, which is a
root of any nonzero element of `n`. -/
theorem trdeg_alg_quot_eq_zero {A : Type u} [CommRing A] [IsDomain A]
    (n : Ideal (Polynomial A)) [n.IsPrime] (hn1 : n.height = 1) :
    Algebra.trdeg A ((Polynomial A) ⧸ n) = 0 := by
  have hev : ∀ p : Polynomial A,
      Polynomial.aeval ((Ideal.Quotient.mk n) Polynomial.X) p = (Ideal.Quotient.mk n) p := by
    intro p
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ A n)
      (Polynomial.X : Polynomial A) p
    rwa [Polynomial.aeval_X_left_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  have hxalg : IsAlgebraic A ((Ideal.Quotient.mk n) Polynomial.X) := by
    have hne : n ≠ ⊥ := by
      rintro rfl; simp at hn1
    obtain ⟨g, hgn, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨g, hg0, by rwa [hev, Ideal.Quotient.eq_zero_iff_mem]⟩
  have htop : Algebra.adjoin A {(Ideal.Quotient.mk n) Polynomial.X} = ⊤ := by
    rw [_root_.eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hev p]
    exact Polynomial.aeval_mem_adjoin_singleton A (p := p) ((Ideal.Quotient.mk n) Polynomial.X)
  have halgsub : (Algebra.adjoin A {(Ideal.Quotient.mk n) Polynomial.X}).IsAlgebraic :=
    Algebra.isAlgebraic_adjoin_singleton_iff.mpr hxalg
  have : Algebra.IsAlgebraic A ((Polynomial A) ⧸ n) :=
    ⟨fun b => halgsub b (by rw [htop]; trivial)⟩
  exact trdeg_eq_zero

/-- `IsLocalRing.ResidueField.map` of a surjective local ring hom is surjective: the residue
map of the target is surjective, and it factors through the map of residue fields. -/
theorem isLocalRing_residueField_map_surjective
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Surjective (IsLocalRing.ResidueField.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨IsLocalRing.residue A a, IsLocalRing.ResidueField.map_residue f a⟩

/-- `Ideal.ResidueField.map` of a surjective base ring hom is surjective. -/
theorem residueField_map_surjective {R₀ : Type u} {S₀ : Type v} [CommRing R₀] [CommRing S₀]
    (I : Ideal R₀) [I.IsPrime] (J : Ideal S₀) [J.IsPrime] (f : R₀ →+* S₀)
    (hIJ : I = Ideal.comap f J) (hf : Function.Surjective f) :
    Function.Surjective (Ideal.ResidueField.map I J f hIJ) := by
  have hLocSurj : ∀ {R₁ : Type u} {P₁ : Type v} [CommRing R₁] [CommRing P₁]
      (I' : Ideal R₁) [I'.IsPrime]
      (J' : Ideal P₁) [J'.IsPrime] (f' : R₁ →+* P₁) (hIJ' : I' = Ideal.comap f' J'),
      Function.Surjective f' → Function.Surjective (Localization.localRingHom I' J' f' hIJ') := by
    intro R₁ P₁ _ _ I' _ J' _ f' hIJ' hf' y
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (J'.primeCompl) y
    obtain ⟨b', rfl⟩ := hf' b
    obtain ⟨s', hs'⟩ := hf' s.val
    have hs'mem : s' ∈ I'.primeCompl := by
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe]
      intro hc
      rw [hIJ', Ideal.mem_comap, hs'] at hc
      exact s.property hc
    refine ⟨IsLocalization.mk' (Localization.AtPrime I') b' ⟨s', hs'mem⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  unfold Ideal.ResidueField.map
  exact isLocalRing_residueField_map_surjective _ (hLocSurj I J f hIJ hf)

/-- Functoriality of `Ideal.ResidueField.map` under composition. -/
theorem residueField_map_comp {R₀ : Type u} {S₀ : Type v} {T₀ : Type w}
    [CommRing R₀] [CommRing S₀] [CommRing T₀]
    (I : Ideal R₀) [I.IsPrime] (J : Ideal S₀) [J.IsPrime] (K : Ideal T₀) [K.IsPrime]
    (f : R₀ →+* S₀) (g : S₀ →+* T₀) (hIJ : I = Ideal.comap f J) (hJK : J = Ideal.comap g K)
    (hIK : I = Ideal.comap (g.comp f) K) :
    (Ideal.ResidueField.map J K g hJK).comp (Ideal.ResidueField.map I J f hIJ)
      = Ideal.ResidueField.map I K (g.comp f) hIK := by
  unfold Ideal.ResidueField.map
  rw [← IsLocalRing.ResidueField.map_comp]
  congr 1
  rw [Localization.localRingHom_comp I J K f hIJ g hJK]

/-- `Ideal.ResidueField.map` depends only on the underlying ring hom. -/
theorem residueField_map_congr {R₀ : Type u} {S₀ : Type v} [CommRing R₀] [CommRing S₀]
    (I : Ideal R₀) [I.IsPrime] (J : Ideal S₀) [J.IsPrime] (f f' : R₀ →+* S₀)
    (hff : f = f') (h : I = Ideal.comap f J) (h' : I = Ideal.comap f' J) :
    Ideal.ResidueField.map I J f h = Ideal.ResidueField.map I J f' h' := by
  subst hff; rfl

/-- **Residue-field transcendence degree along a surjection.** For `f : C →+* A'` a surjective
`A`-algebra map and `Q` a prime of `A'` over `P`, the residue field of `Ideal.comap f Q` is
isomorphic to that of `Q` as a `κ(P)`-algebra, so the two have the same transcendence degree
over `κ(P)`. -/
theorem resfield_lift_trdeg_comap_eq {A : Type u} {C : Type v} {A' : Type w}
    [CommRing A] [CommRing C] [CommRing A']
    [Algebra A C] [Algebra A A'] (f : C →+* A') (hf : Function.Surjective f)
    (hcomp : f.comp (algebraMap A C) = algebraMap A A')
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    [(Ideal.comap f Q).LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    letI := Ideal.ResidueField.algebraOfLiesOver P (Ideal.comap f Q)
    Cardinal.lift.{w} (Algebra.trdeg P.ResidueField (Ideal.comap f Q).ResidueField)
      = Cardinal.lift.{v} (Algebra.trdeg P.ResidueField Q.ResidueField) := by
  set Qt : Ideal C := Ideal.comap f Q with hQtcomap
  let eRF : Qt.ResidueField ≃+* Q.ResidueField :=
    RingEquiv.ofBijective _
      ⟨RingHom.injective _, residueField_map_surjective Qt Q f hQtcomap hf⟩
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  let := Ideal.ResidueField.algebraOfLiesOver P Qt
  have hlin : ∀ x : P.ResidueField,
      eRF ((algebraMap P.ResidueField Qt.ResidueField) x)
        = (algebraMap P.ResidueField Q.ResidueField) x := by
    intro x
    change (Ideal.ResidueField.map Qt Q f hQtcomap)
        ((Ideal.ResidueField.map P Qt (algebraMap A C) Ideal.LiesOver.over) x)
      = (Ideal.ResidueField.map P Q (algebraMap A A') Ideal.LiesOver.over) x
    have hx := RingHom.congr_fun (residueField_map_comp P Qt Q (algebraMap A C) f
      Ideal.LiesOver.over hQtcomap (by rw [hcomp]; exact Ideal.LiesOver.over)) x
    simp only [RingHom.coe_comp, Function.comp_apply] at hx
    rw [hx]
    exact RingHom.congr_fun (residueField_map_congr P Q (f.comp (algebraMap A C))
      (algebraMap A A') hcomp (by rw [hcomp]; exact Ideal.LiesOver.over)
      Ideal.LiesOver.over) x
  exact AlgEquiv.lift_trdeg_eq (AlgEquiv.ofRingEquiv hlin)

/-- The same-universe form of residue-field transcendence degree invariance
under a surjective algebra map. -/
theorem resfield_trdeg_comap_eq {A : Type u} {C A' : Type v} [CommRing A] [CommRing C] [CommRing A']
    [Algebra A C] [Algebra A A'] (f : C →+* A') (hf : Function.Surjective f)
    (hcomp : f.comp (algebraMap A C) = algebraMap A A')
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P]
    [(Ideal.comap f Q).LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    letI := Ideal.ResidueField.algebraOfLiesOver P (Ideal.comap f Q)
    Algebra.trdeg P.ResidueField (Ideal.comap f Q).ResidueField
      = Algebra.trdeg P.ResidueField Q.ResidueField := by
  simpa only [Cardinal.lift_id] using resfield_lift_trdeg_comap_eq f hf hcomp P Q

/-- Residue-field transcendence degree is invariant under an `A`-algebra isomorphism
`e : C ≃ₐ[A] A'` pulling `Q` back to `Ideal.comap e Q`. -/
theorem resfield_trdeg_algEquiv_eq {A : Type u} {C A' : Type v}
    [CommRing A] [CommRing C] [CommRing A']
    [Algebra A C] [Algebra A A'] (e : C ≃ₐ[A] A') (P : Ideal A) (Q : Ideal A')
    [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] [(Ideal.comap (e : C →+* A') Q).LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    letI := Ideal.ResidueField.algebraOfLiesOver P (Ideal.comap (e : C →+* A') Q)
    Algebra.trdeg P.ResidueField (Ideal.comap (e : C →+* A') Q).ResidueField
      = Algebra.trdeg P.ResidueField Q.ResidueField :=
  resfield_trdeg_comap_eq _ e.surjective (by ext a; exact e.commutes a) P Q

-- the `simp` below needs to unfold the `Localization.AtPrime` residue-field abbreviations the
-- statement is phrased at.
set_option backward.isDefEq.respectTransparency false in
/-- The dimension-formula inequality for `A ⊆ A[X] ⧸ n` with `n` a height-one prime of `A[X]`
meeting `A` in `(0)`, so that the extension is generated by one algebraic element:
`P.height + trdeg_A (A[X] ⧸ n) ≤ Q.height + trdeg_{κ(P)} κ(Q)`. It is the polynomial step
applied to the lift `comap (mk n) Q`, whose height exceeds that of `Q` by `n.height = 1`. -/
private theorem single_generator_step_alg {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsDomain A]
    (hcat : IsUniversallyCatenary A)
    (n : Ideal (Polynomial A)) [n.IsPrime] (hn1 : n.height = 1)
    (P : Ideal A) (Q : Ideal ((Polynomial A) ⧸ n))
    [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    P.height + (Cardinal.toNat (Algebra.trdeg A ((Polynomial A) ⧸ n)) : ℕ∞)
      ≤ Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
  have hQtLO : (Ideal.comap (Ideal.Quotient.mk n) Q).LiesOver P :=
    Ideal.LiesOver.of_eq_comap P (Ideal.Quotient.mkₐ A n) rfl
  have htreq := resfield_trdeg_comap_eq (A := A) (Ideal.Quotient.mk n)
    Ideal.Quotient.mk_surjective rfl P Q
  set Qt : Ideal (Polynomial A) := Ideal.comap (Ideal.Quotient.mk n) Q with hQt
  have hnle : n ≤ Qt := by
    intro x hx
    rw [hQt, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  have hmapQt : Ideal.map (Ideal.Quotient.mk n) Qt = Q := by
    rw [hQt, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hadd := catenary_height_add hcat.trans n Qt hnle
  rw [hmapQt, hn1] at hadd
  have htr0 : Algebra.trdeg A ((Polynomial A) ⧸ n) = 0 := trdeg_alg_quot_eq_zero n hn1
  rw [htr0, map_zero, Nat.cast_zero, add_zero]
  have hpoly := single_generator_step_poly P Qt
  rw [Polynomial.trdeg_of_isDomain, map_one, hadd, htreq, Nat.cast_one] at hpoly
  refine (WithTop.add_le_add_iff_right (z := (1 : ℕ∞)) (by simp)).mp ?_
  refine hpoly.trans_eq ?_
  abel

/-- Height is invariant under a ring isomorphism: `(Ideal.comap e Q).height = Q.height` for
`e : A ≃+* B` and `Q` a prime of `B`. -/
theorem height_comap_ringEquiv {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) (Q : Ideal B) [hQ : Q.IsPrime] :
    (Ideal.comap (e : A →+* B) Q).height = Q.height := by
  have : (Ideal.comap (e : A →+* B) Q).IsPrime := Ideal.comap_isPrime (e : A →+* B) Q
  rw [PrimeSpectrum.height_eq_orderHeight ⟨Ideal.comap (e : A →+* B) Q, inferInstance⟩,
    PrimeSpectrum.height_eq_orderHeight ⟨Q, hQ⟩]
  change Order.height (⟨Ideal.comap (e : A →+* B) Q, inferInstance⟩ : PrimeSpectrum A)
      = Order.height (⟨Q, hQ⟩ : PrimeSpectrum B)
  have hpt : (PrimeSpectrum.comapEquiv e)
        (⟨Ideal.comap (e : A →+* B) Q, inferInstance⟩ : PrimeSpectrum A)
      = (⟨Q, hQ⟩ : PrimeSpectrum B) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (e.symm : B →+* A) (Ideal.comap (e : A →+* B) Q) = Q
    rw [Ideal.comap_comap,
      show (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B from by ext x; simp,
      Ideal.comap_id]
  rw [← Order.height_orderIso (PrimeSpectrum.comapEquiv e)
        (⟨Ideal.comap (e : A →+* B) Q, inferInstance⟩ : PrimeSpectrum A), hpt]

/-- A nonzero prime `n` of `A[X]`, for `A` a domain, contracting to `(0)` in `A` has height
exactly one: after localizing at the nonzero constants it becomes a nonzero prime of the
principal ideal domain `Frac(A)[X]`, hence a maximal one, so every prime strictly below `n`
already contracts to `(0)` and vanishes. -/
@[ega "IV 5.2.5" "more general", ega "IV 5.5.3" "special case"]
theorem height_one_of_comap_bot {A : Type u} [CommRing A] [IsDomain A]
    (n : Ideal (Polynomial A)) [hnp : n.IsPrime] (hnbot : n ≠ ⊥)
    (hncap : Ideal.comap (algebraMap A (Polynomial A)) n = ⊥) :
    n.height = 1 := by
  set M : Submonoid A := nonZeroDivisors A with hM
  set M' : Submonoid (Polynomial A) := Submonoid.map (Polynomial.C : A →+* Polynomial A) M with hM'
  have hloc : IsLocalization M' (Polynomial (FractionRing A)) := by
    rw [hM', hM]; exact Polynomial.isLocalization (nonZeroDivisors A) (FractionRing A)
  set f : Polynomial A →+* Polynomial (FractionRing A) :=
    algebraMap (Polynomial A) (Polynomial (FractionRing A)) with hf
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have hkerf : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hfinj
  have hdisj : ∀ (r : Ideal (Polynomial A)), Ideal.comap (algebraMap A (Polynomial A)) r = ⊥ →
      Disjoint (↑M' : Set (Polynomial A)) (↑r : Set (Polynomial A)) := by
    intro r hr
    rw [Set.disjoint_left]
    rintro y ⟨a, ha, rfl⟩ hyr
    have hac : a ∈ Ideal.comap (algebraMap A (Polynomial A)) r := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hyr
    rw [hr, Ideal.mem_bot] at hac
    rw [hac] at ha
    exact absurd ha (by simp [hM, nonZeroDivisors])
  have hdisjn : Disjoint (↑M' : Set (Polynomial A)) (↑n : Set (Polynomial A)) := hdisj n hncap
  have hnbar_p : (Ideal.map f n).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial (FractionRing A)) n hnp hdisjn
  have hcomap_n : Ideal.comap f (Ideal.map f n) = n := by
    have h := IsLocalization.under_map_of_isPrime_disjoint M' (Polynomial (FractionRing A)) hnp
        hdisjn
    rwa [Ideal.under_def] at h
  have hnbar_ne : Ideal.map f n ≠ ⊥ := by
    intro h; apply hnbot; rw [← hcomap_n, h, ← RingHom.ker_eq_comap_bot, hkerf]
  have hnbar_max : (Ideal.map f n).IsMaximal := IsPrime.to_maximal_ideal hnbar_ne
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from by norm_cast, Ideal.height_le_iff]
    intro q hqp hqn
    have := hqp
    have hqcap : Ideal.comap (algebraMap A (Polynomial A)) q = ⊥ := by
      rw [eq_bot_iff]
      calc Ideal.comap (algebraMap A (Polynomial A)) q
          ≤ Ideal.comap (algebraMap A (Polynomial A)) n := Ideal.comap_mono (le_of_lt hqn)
        _ = ⊥ := hncap
    have hdisjq : Disjoint (↑M' : Set (Polynomial A)) (↑q : Set (Polynomial A)) := hdisj q hqcap
    have hcomap_q : Ideal.comap f (Ideal.map f q) = q := by
      have h := IsLocalization.under_map_of_isPrime_disjoint M' (Polynomial (FractionRing A)) hqp
          hdisjq
      rwa [Ideal.under_def] at h
    have hqbar_p : (Ideal.map f q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M' (Polynomial (FractionRing A)) q hqp hdisjq
    have hqbar_lt : Ideal.map f q < Ideal.map f n := by
      refine lt_of_le_of_ne (Ideal.map_mono (le_of_lt hqn)) ?_
      intro h; apply ne_of_lt hqn; rw [← hcomap_q, ← hcomap_n, h]
    have hqbar_bot : Ideal.map f q = ⊥ := by
      by_contra hqbarne
      have hqm := IsPrime.to_maximal_ideal hqbarne
      exact (ne_of_lt hqbar_lt) (hqm.eq_of_le hnbar_max.ne_top (le_of_lt hqbar_lt))
    have hq_bot : q = ⊥ := by rw [← hcomap_q, hqbar_bot, ← RingHom.ker_eq_comap_bot, hkerf]
    rw [hq_bot, Ideal.height_bot]; exact zero_lt_one
  · exact one_le_height_of_ne_bot hnbot

/-- The dimension-formula inequality for a one-generator extension `A ⊆ A'` of domains with `A`
Noetherian and universally catenary: `P.height + trdeg_A A' ≤ Q.height + trdeg_{κ(P)} κ(Q)`.
Evaluation at the generator presents `A'` as `A[X] ⧸ n` with `n` prime and `n ∩ A = (0)`, which
is the polynomial extension when `n = (0)` and a one-generator algebraic extension otherwise. -/
theorem single_generator_step
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
    [IsNoetherianRing A] [Algebra.FiniteType A A'] [IsDomain A] [IsDomain A']
    (hinj : Function.Injective (algebraMap A A')) (hcat : IsUniversallyCatenary A)
    (hgen : ∃ x : A', Algebra.adjoin A {x} = ⊤)
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    P.height + (Cardinal.toNat (Algebra.trdeg A A') : ℕ∞)
      ≤ Q.height + (Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField) : ℕ∞) := by
  obtain ⟨x, htop⟩ := hgen
  have hsurj : Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] A') := by
    rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
  set n : Ideal (Polynomial A) :=
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] A').toRingHom with hn
  let e : (Polynomial A ⧸ n) ≃ₐ[A] A' := Ideal.quotientKerAlgEquivOfSurjective hsurj
  have hnp : n.IsPrime := RingHom.ker_isPrime _
  have hncap : Ideal.comap (algebraMap A (Polynomial A)) n = ⊥ := by
    rw [hn]; ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    constructor
    · intro h
      have hcc : (Polynomial.aeval x : Polynomial A →ₐ[A] A').toRingHom
            (algebraMap A (Polynomial A) a) = algebraMap A A' a := by
        rw [Polynomial.algebraMap_eq]; simp [Polynomial.aeval_C]
      rw [hcc] at h
      exact hinj (by rw [h, map_zero])
    · rintro rfl; simp
  set Q'' : Ideal (Polynomial A ⧸ n) := Ideal.comap (e : (Polynomial A ⧸ n) →+* A') Q with hQ''
  have hQ''p : Q''.IsPrime := Ideal.comap_isPrime (e : (Polynomial A ⧸ n) →+* A') Q
  have hcompmap : (e : (Polynomial A ⧸ n) →+* A').comp (algebraMap A (Polynomial A ⧸ n))
      = algebraMap A A' := by ext a; exact e.commutes a
  have hQ''LO : Q''.LiesOver P := Ideal.LiesOver.of_eq_comap P e rfl
  have hheight : Q.height = Q''.height :=
    (height_comap_ringEquiv (e : (Polynomial A ⧸ n) ≃+* A') Q).symm
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  let := Ideal.ResidueField.algebraOfLiesOver P Q''
  have htrdegA : Cardinal.toNat (Algebra.trdeg A A') =
      Cardinal.toNat (Algebra.trdeg A (Polynomial A ⧸ n)) := by
    simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat e.lift_trdeg_eq.symm
  have htres := congrArg Cardinal.toNat
    (resfield_lift_trdeg_comap_eq (e : (Polynomial A ⧸ n) →+* A')
      e.surjective hcompmap P Q)
  simp only [Cardinal.toNat_lift] at htres
  rw [htrdegA, hheight, ← htres]
  by_cases hnbot : n = ⊥
  · -- transcendental case: transport once more along A[X]/n ≅ A[X].
    let e3 : Polynomial A ≃ₐ[A] (Polynomial A ⧸ n) :=
      (AlgEquiv.quotientBot A (Polynomial A)).symm.trans (Ideal.quotientEquivAlgOfEq A hnbot).symm
    set Q''' : Ideal (Polynomial A) :=
      Ideal.comap (e3 : Polynomial A →+* (Polynomial A ⧸ n)) Q'' with hQ'''
    have hQ'''p : Q'''.IsPrime :=
      Ideal.comap_isPrime (e3 : Polynomial A →+* (Polynomial A ⧸ n)) Q''
    have hQ'''LO : Q'''.LiesOver P := Ideal.LiesOver.of_eq_comap P e3 rfl
    have hheight3 : Q''.height = Q'''.height :=
      (height_comap_ringEquiv (e3 : Polynomial A ≃+* (Polynomial A ⧸ n)) Q'').symm
    have htrdegA3 : Algebra.trdeg A (Polynomial A ⧸ n) = Algebra.trdeg A (Polynomial A) :=
      (AlgEquiv.trdeg_eq e3).symm
    have htres3 := resfield_trdeg_algEquiv_eq e3 P Q''
    rw [htrdegA3, hheight3, ← htres3]
    exact single_generator_step_poly P Q'''
  · -- algebraic case: n is a height-one generic-fiber prime.
    have hn1 : n.height = 1 := height_one_of_comap_bot n hnbot hncap
    exact single_generator_step_alg hcat n hn1 P Q''

/-- For `Q` a prime of `A'` lying over a prime `P` of `A`, the residue field extension and the
extension of quotient domains have the same transcendence degree,
`trdeg_{κ(P)} κ(Q) = trdeg_{A ⧸ P} (A' ⧸ Q)`: both `κ(P)` and `κ(Q)` are fraction fields, so
tower additivity along `A ⧸ P → κ(P) → κ(Q)` and `A ⧸ P → A' ⧸ Q → κ(Q)` identifies the two. -/
@[ega "IV 5.5.7" "more general"]
theorem resfield_trdeg_eq_quot_trdeg
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    Algebra.trdeg P.ResidueField Q.ResidueField = Algebra.trdeg (A ⧸ P) (A' ⧸ Q) := by
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  have hRP : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  have hSQ : IsDomain (A' ⧸ Q) := Ideal.Quotient.isDomain Q
  have hle : P ≤ Ideal.comap (algebraMap A A') Q := le_of_eq (Ideal.LiesOver.over (p:=P) (P:=Q))
  let f₀alg : Algebra (A ⧸ P) (A' ⧸ Q) := (Ideal.quotientMap Q (algebraMap A A') hle).toAlgebra
  let compAlg : Algebra (A ⧸ P) Q.ResidueField :=
    ((algebraMap (A' ⧸ Q) Q.ResidueField).comp (algebraMap (A ⧸ P) (A' ⧸ Q))).toAlgebra
  have tower2 : IsScalarTower (A ⧸ P) (A' ⧸ Q) Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have towerA : IsScalarTower A (A ⧸ P) (A' ⧸ Q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change (Ideal.Quotient.mk Q) (algebraMap A A' a)
        = (Ideal.quotientMap Q (algebraMap A A') hle) ((Ideal.Quotient.mk P) a)
    rw [Ideal.quotientMap_mk]
  have tower1 : IsScalarTower (A ⧸ P) P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hL : (algebraMap (A ⧸ P) P.ResidueField) ((Ideal.Quotient.mk P) r)
        = algebraMap A P.ResidueField r := by
      rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [hL]
    have hLHS : (algebraMap P.ResidueField Q.ResidueField) (algebraMap A P.ResidueField r)
        = algebraMap A' Q.ResidueField (algebraMap A A' r) := by
      change (Ideal.ResidueField.map P Q (algebraMap A A') Ideal.LiesOver.over)
          (algebraMap A P.ResidueField r) = _
      rw [Ideal.ResidueField.map_algebraMap P Q (algebraMap A A') Ideal.LiesOver.over r]
    have hRHS : (algebraMap (A ⧸ P) Q.ResidueField) ((Ideal.Quotient.mk P) r)
        = algebraMap A' Q.ResidueField (algebraMap A A' r) := by
      change (algebraMap (A' ⧸ Q) Q.ResidueField)
          ((algebraMap (A ⧸ P) (A' ⧸ Q)) ((Ideal.Quotient.mk P) r)) = _
      have hR1 : (algebraMap (A ⧸ P) (A' ⧸ Q)) ((Ideal.Quotient.mk P) r)
          = (Ideal.Quotient.mk Q) (algebraMap A A' r) := by
        change (Ideal.quotientMap Q (algebraMap A A') hle) ((Ideal.Quotient.mk P) r) = _
        rw [Ideal.quotientMap_mk]
      rw [hR1, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [hRHS, hLHS]
  have : FaithfulSMul (A ⧸ P) P.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact IsFractionRing.injective _ _
  have : FaithfulSMul (A' ⧸ Q) Q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact IsFractionRing.injective _ _
  have : FaithfulSMul P.ResidueField Q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact (algebraMap P.ResidueField Q.ResidueField).injective
  have : FaithfulSMul (A ⧸ P) (A' ⧸ Q) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Ideal.quotientMap_injective' (Ideal.LiesOver.over (p := P) (P := Q)).ge
  have hz1 : Algebra.trdeg (A ⧸ P) P.ResidueField = 0 := by
    have : Algebra.IsAlgebraic (A ⧸ P) P.ResidueField :=
      IsLocalization.isAlgebraic P.ResidueField (nonZeroDivisors (A ⧸ P))
    exact trdeg_eq_zero
  have hz2 : Algebra.trdeg (A' ⧸ Q) Q.ResidueField = 0 := by
    have : Algebra.IsAlgebraic (A' ⧸ Q) Q.ResidueField :=
      IsLocalization.isAlgebraic Q.ResidueField (nonZeroDivisors (A' ⧸ Q))
    exact trdeg_eq_zero
  have ht1 := lift_trdeg_add_eq (A ⧸ P) P.ResidueField Q.ResidueField
  have ht2 := trdeg_add_eq (A ⧸ P) (A' ⧸ Q) (A := Q.ResidueField)
  simp only [hz1, Cardinal.lift_zero, zero_add] at ht1
  rw [hz2, add_zero] at ht2
  exact Cardinal.lift_injective (ht1.trans (congrArg Cardinal.lift ht2.symm))

/-- For a finite-type extension of Noetherian domains `A ⊆ A'` and `Q` a prime lying over `P`,
the residue field extension `κ(Q)/κ(P)` has finite transcendence degree. -/
theorem resfield_trdeg_lt_aleph0_general
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [Algebra A A']
    [IsNoetherianRing A] [Algebra.FiniteType A A'] [IsDomain A] [IsDomain A']
    (P : Ideal A) (Q : Ideal A') [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    Algebra.trdeg P.ResidueField Q.ResidueField < Cardinal.aleph0 := by
  let := Ideal.ResidueField.algebraOfLiesOver P Q
  rw [resfield_trdeg_eq_quot_trdeg P Q]
  have : Algebra.FiniteType (A ⧸ P) (A' ⧸ Q) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ P) (A' ⧸ Q)
  exact trdeg_lt_aleph0_of_finiteType

end
