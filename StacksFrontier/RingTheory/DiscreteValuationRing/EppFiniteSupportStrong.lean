module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Etale.StandardEtale
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFiniteSupport

/-!
# Finite residue extensions with their embedding certificate retained

Epp's degree-prime argument needs more than an algebra map into the henselian overring: the
induced map on residue fields must have exactly the prescribed finite intermediate field as its
range.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Stacks.EppTheorem

universe u v

/-- A monogenic algebra with separable irreducible reduction is étale. -/
private theorem etale_adjoinRoot_of_separable_map_residue
    {A : Type u} [CommRing A] [IsLocalRing A] {P : A[X]}
    (hP : P.Monic) (hirr : Irreducible (P.map (residue A)))
    (hsep : (P.map (residue A)).Separable) [IsLocalRing (AdjoinRoot P)] :
    Algebra.Etale A (AdjoinRoot P) := by
  have hu : IsUnit (AdjoinRoot.mk P (derivative P)) := by
    by_contra hunit
    have hmem : AdjoinRoot.mk P (derivative P) ∈
        (maximalIdeal A).map (AdjoinRoot.of P) := by
      rw [← AdjoinRoot.maximalIdeal_eq_map_maximalIdeal hirr]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
    have hquot := AdjoinRoot.quotEquivQuotMap_apply_mk P (derivative P) (maximalIdeal A)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero] at hquot
    have hdvd : P.map (residue A) ∣ (derivative P).map (residue A) := by
      rw [← Ideal.mem_span_singleton]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hquot.symm
    have hcoprime : IsCoprime (P.map (residue A))
        (derivative (P.map (residue A))) := hsep
    rw [Polynomial.derivative_map] at hcoprime
    exact hirr.not_isUnit (hcoprime.isUnit_of_dvd' dvd_rfl hdvd)
  let Q : StandardEtalePair A :=
    ⟨P, hP, derivative P, ⟨1, 0, 1, by ring⟩⟩
  exact Algebra.Etale.of_equiv (Q.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit (AdjoinRoot P)
      (Localization.Away (AdjoinRoot.mk P (derivative P))) _ hu).restrictScalars A).symm)

/-- If `x` generates `S` as an `R`-algebra, every element of `S` is a polynomial in `x`. -/
private theorem exists_aeval_eq_of_adjoin_singleton_eq_top
    {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] {x : S}
    (h : Algebra.adjoin R {x} = ⊤) (z : S) : ∃ g : R[X], aeval x g = z := by
  rw [← AlgHom.mem_range, ← Algebra.adjoin_singleton_eq_range_aeval, h]
  exact Algebra.mem_top

/-- A finite separable intermediate residue field is realized by a finite étale extension, with
the induced residue-field range identified with that intermediate field. -/
theorem exists_finiteEtale_algebraMap_fieldRange_eq_intermediateField
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : Algebra.Etale A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange = E.toSubfield := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) E
  have hint : IsIntegral (ResidueField A) α := IsIntegral.of_finite (ResidueField A) α
  have hqsep : (minpoly (ResidueField A) α).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField A) α
  obtain ⟨P, hP, hPmap⟩ := exists_monic_lift_map_residue_eq A (minpoly.monic hint)
  have hirr : Irreducible (P.map (residue A)) := hPmap ▸ minpoly.irreducible hint
  have hd : 0 < P.natDegree := by
    rw [← hP.natDegree_map (residue A), hPmap]
    exact minpoly.natDegree_pos hint
  have hrootq : aeval (α : ResidueField B) (minpoly (ResidueField A) α) = 0 := by
    rw [← minpoly.algebraMap_eq (algebraMap E (ResidueField B)).injective α]
    exact minpoly.aeval _ _
  have hroot : aeval ((α : ResidueField B)) (P.map (residue A)) = 0 := by
    rwa [hPmap]
  have hsimple : aeval ((α : ResidueField B)) (derivative (P.map (residue A))) ≠ 0 := by
    rw [hPmap]
    exact hqsep.aeval_derivative_ne_zero hrootq
  have hlocal := AdjoinRoot.isLocalRing_of_irreducible_map_residue hP hirr
  have hdom := AdjoinRoot.isDomain_of_irreducible_map_residue hP hirr
  have hlh := AdjoinRoot.isLocalHom_of_monic_of_degree_pos (g := P) hP
    (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
  have hdvr := AdjoinRoot.isDiscreteValuationRing hP hirr hd
  have hetale : Algebra.Etale A (AdjoinRoot P) :=
    etale_adjoinRoot_of_separable_map_residue hP hirr (hPmap ▸ hqsep)
  have hext : IsDiscreteValuationRing.IsExtension A (AdjoinRoot P) :=
    { toFaithfulSMul := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hP
        (Polynomial.natDegree_pos_iff_degree_pos.mp hd)
      toIsLocalHom := hlh }
  obtain ⟨ψ, hψ⟩ :=
    AdjoinRoot.exists_algHom_residue_root_eq_of_henselian (A := A) (B := B) hP hroot hsimple
  let algψ : Algebra (AdjoinRoot P) B := (ψ : AdjoinRoot P →+* B).toAlgebra
  have hamap : algebraMap (AdjoinRoot P) B = (ψ : AdjoinRoot P →+* B) := rfl
  have htower : IsScalarTower A (AdjoinRoot P) B :=
    IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  have hlhψ : IsLocalHom (algebraMap (AdjoinRoot P) B) :=
    hamap ▸ AdjoinRoot.isLocalHom_of_algHom hirr ψ
  have hroot_res : algebraMap (ResidueField (AdjoinRoot P)) (ResidueField B)
      (residue (AdjoinRoot P) (AdjoinRoot.root P)) = (α : ResidueField B) := by
    rwa [ResidueField.algebraMap_residue, hamap]
  have htopE : Algebra.adjoin (ResidueField A) ({α} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hfr : (algebraMap (ResidueField (AdjoinRoot P))
      (ResidueField B)).fieldRange = E.toSubfield := by
    have hcalc : ∀ g : (ResidueField A)[X],
        algebraMap (ResidueField (AdjoinRoot P)) (ResidueField B)
            (aeval (residue (AdjoinRoot P) (AdjoinRoot.root P)) g) =
          E.val (aeval α g) := by
      intro g
      calc
        algebraMap (ResidueField (AdjoinRoot P)) (ResidueField B)
              (aeval (residue (AdjoinRoot P) (AdjoinRoot.root P)) g) =
            IsScalarTower.toAlgHom (ResidueField A) (ResidueField (AdjoinRoot P))
              (ResidueField B) (aeval (residue (AdjoinRoot P) (AdjoinRoot.root P)) g) := rfl
        _ = aeval (IsScalarTower.toAlgHom (ResidueField A)
              (ResidueField (AdjoinRoot P)) (ResidueField B)
              (residue (AdjoinRoot P) (AdjoinRoot.root P))) g :=
            (aeval_algHom_apply _ _ g).symm
        _ = aeval (E.val α) g := congrArg (aeval · g) hroot_res
        _ = E.val (aeval α g) := aeval_algHom_apply _ α g
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨z, rfl⟩ := RingHom.mem_fieldRange.mp hy
      have hz : z ∈ (aeval (R := ResidueField A)
          (residue (AdjoinRoot P) (AdjoinRoot.root P))).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval, AdjoinRoot.adjoin_residue_root_eq_top]
        exact Algebra.mem_top
      obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hz
      rw [hcalc g]
      exact (aeval α g).2
    · obtain ⟨g, hg⟩ := exists_aeval_eq_of_adjoin_singleton_eq_top htopE ⟨y, hy⟩
      refine RingHom.mem_fieldRange.mpr
        ⟨aeval (residue (AdjoinRoot P) (AdjoinRoot.root P)) g, ?_⟩
      rw [hcalc g, hg]
      rfl
  exact ⟨AdjoinRoot P, inferInstance, hdom, hdvr, inferInstance, hP.finite_adjoinRoot, hetale,
    hext, algψ, htower, hlhψ, AdjoinRoot.ramificationIdx_eq_one hP hirr hd, hfr⟩

/-- A finite separable intermediate residue field is realized by a finite weakly unramified
extension, with the induced residue-field range identified with that intermediate field. -/
theorem exists_isWeaklyUnramified_algebraMap_fieldRange_eq_intermediateField
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E] :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange = E.toSubfield := by
  obtain ⟨A₁, _, _, _, _, _, _, _, _, _, _, hweak, hfr⟩ :=
    exists_finiteEtale_algebraMap_fieldRange_eq_intermediateField E
  exact ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hweak, hfr⟩

/-- Every prescribed finite subset of the perfect core is absorbed by the residue field of a
finite étale base extension embedded in the henselian overring. -/
theorem EppCondition.exists_finiteEtale_algebraMap_absorbs_finset
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : Algebra.Etale A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∀ z ∈ s, z ∈ (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange := by
  obtain ⟨E, hfin, hsep, hsE, -⟩ := h.exists_finite_separable_subextension s hs
  obtain ⟨A₁, _, _, _, _, _, _, _, _, _, _, hweak, hfr⟩ :=
    exists_finiteEtale_algebraMap_fieldRange_eq_intermediateField E
  exact ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hweak,
    fun z hz => hfr ▸ hsE z hz⟩

/-- Under Epp's condition, a finite subset of the perfect core of `κ_B` lies in the image of the
residue field of some finite, weakly unramified extension `A₁ / A` inside `B`. -/
theorem EppCondition.exists_isWeaklyUnramified_algebraMap_absorbs_finset
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (s : Finset (ResidueField B))
    (hs : ∀ z ∈ s, z ∈ perfectCore (ResidueField B) p) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∀ z ∈ s, z ∈ (algebraMap (ResidueField A₁) (ResidueField B)).fieldRange := by
  obtain ⟨A₁, _, _, _, _, _, _, _, _, _, _, hweak, habs⟩ :=
    h.exists_finiteEtale_algebraMap_absorbs_finset s hs
  exact ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hweak, habs⟩

/-- Let `A → B` be a local homomorphism of discrete valuation rings with `B` henselian, let Epp's
condition hold, and fix a finite `S ⊆ κ_B` together with a depth `N`.  Then there is a finite
étale, weakly unramified `A₁ / A` sitting inside `B` over `A` such that for every `x ∈ S` lying in
`perfectCore κ_B p` there is `a : κ_{A₁}` with

  `(algebraMap κ_{A₁} κ_B a) ^ (p ^ N) = x`. -/
theorem EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (h : EppCondition A B p) (S : Finset (ResidueField B)) (N : ℕ) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : Algebra.Etale A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∀ x ∈ S, x ∈ perfectCore (ResidueField B) p →
          ∃ a : ResidueField A₁,
            algebraMap (ResidueField A₁) (ResidueField B) a ^ (p ^ N) = x := by
  classical
  choose! f hf using fun x (hx : x ∈ perfectCore (ResidueField B) p) =>
    exists_mem_perfectCore_pow_eq hx N
  -- Absorb the roots of the core part of `S`, not `S` itself.
  set T : Finset (ResidueField B) :=
    (S.filter fun x => x ∈ perfectCore (ResidueField B) p).image f
  have hTcore : ∀ z ∈ T, z ∈ perfectCore (ResidueField B) p := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (hf x (Finset.mem_filter.mp hx).2).1
  obtain ⟨A₁, _, hdom, hdvr, _, hmf, hetale, hext, algψ, htower, hlhψ, hweak, habs⟩ :=
    h.exists_finiteEtale_algebraMap_absorbs_finset T hTcore
  refine ⟨A₁, inferInstance, hdom, hdvr, inferInstance, hmf, hetale, hext, algψ, htower, hlhψ,
    hweak, fun x hxS hxcore => ?_⟩
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp
    (habs _ (Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨hxS, hxcore⟩)))
  exact ⟨a, by rw [ha, (hf x hxcore).2]⟩

/-- **The finite-étale re-entry: Epp's condition absorbed into the base residue field.**

Given a finite separable intermediate field `E` of `κ_A ⊆ κ_B` containing the whole perfect core,
there is a finite étale, weakly unramified `A₁ / A` sitting inside `B` over `A` whose residue field
contains every element of `perfectCore κ_B p`.

This is the hypothesis `exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le`
asks for, over `A₁` in place of `A`; so composing the two gives Epp's degree-`p` equal-
characteristic case over `A₁`.

**Why this composes.**  The layer returns a finite set `S` and a depth `N` under an existential,
so absorbing a finite set alone cannot be made to meet the layer's own antecedent without first
exposing `S` and `N`.  `perfectCore` absorption sidesteps that entirely: once
`perfectCore κ_B p ⊆ image κ_{A₁}`, the antecedent holds for *every* `S` and `N`, because a
`p ^ N`-th root of a core element is again a core element and so is itself in the image.

**What the hypothesis on `E` costs.**  Epp's condition says each element of the perfect core is
separable algebraic over `κ_A`, so `κ_A`-adjoining the core gives a separable `E` containing it
automatically; what is *not* automatic is that `E / κ_A` is finite, since the perfect core can be
infinite over `κ_A`.  Finiteness is exactly the content of the `hfin` hypothesis carried by
`Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_completion` in
`EppWildCaseReduction`; the finite-support results avoid it, since only the finitely many Laurent
coefficients of one Artin–Schreier parameter matter. -/
theorem EppCondition.exists_finiteEtale_forall_mem_perfectCore_mem_range
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (E : IntermediateField (ResidueField A) (ResidueField B))
    [Algebra.IsSeparable (ResidueField A) E] [FiniteDimensional (ResidueField A) E]
    (hE : ∀ x ∈ perfectCore (ResidueField B) p, x ∈ E) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : Algebra.Etale A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∀ x : ResidueField B, x ∈ perfectCore (ResidueField B) p →
          ∃ a : ResidueField A₁, algebraMap (ResidueField A₁) (ResidueField B) a = x := by
  obtain ⟨A₁, _, hdom, hdvr, _, hmf, hetale, hext, algψ, htower, hlhψ, hweak, hfr⟩ :=
    exists_finiteEtale_algebraMap_fieldRange_eq_intermediateField E
  exact ⟨A₁, inferInstance, hdom, hdvr, inferInstance, hmf, hetale, hext, algψ, htower, hlhψ,
    hweak, fun x hx => RingHom.mem_fieldRange.mp (hfr ▸ hE x hx)⟩

/-- **The finite-étale re-entry from Epp's condition itself.**

`exists_finiteEtale_forall_mem_perfectCore_mem_range` with the intermediate field constructed
rather than supplied: `E` is `κ_A`-adjoin of the perfect core, which contains the core by
`IntermediateField.subset_adjoin` and is separable over `κ_A` by
`IntermediateField.isSeparable_adjoin_iff_isSeparable` applied to Epp's condition, that condition
being precisely the statement that every generator is separable.

So the *only* hypothesis left beyond Epp's condition is `hfin`, finite-dimensionality of that
adjoin over `κ_A` — i.e. that the perfect core is finite over the base residue field.  Epp's
condition gives separable *algebraic*, which does not bound the degree, and the perfect core may
genuinely be infinite over `κ_A`; the finite-support machinery exists to avoid this hypothesis by
observing that only the finitely many Laurent coefficients of one Artin–Schreier parameter matter.
Composing this with
`IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le`
gives Epp's degree-`p` equal-characteristic case over `A₁` under `hepp` and `hfin` alone, with no
perfectness of any residue field and no appeal to Tag 09ET.

**Relation to the completion route.**
`Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_algHom_of_completion` in
`EppWildCaseReduction` is the same base change realised inside a *complete* `B'` dominating `B`,
where the extension lives inside `B'`, not inside `B`.  This theorem delivers the map `A₁ → B`
itself, at the price of assuming `B` henselian rather than passing to a completion, and it
additionally returns `Algebra.Etale A A₁`.  Complete discrete valuation rings are henselian, so the
henselian hypothesis holds for every complete `B`. -/
theorem EppCondition.exists_finiteEtale_forall_mem_perfectCore_mem_range_of_finiteDimensional
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {p : ℕ} [ExpChar (ResidueField B) p]
    (hepp : EppCondition A B p)
    (hfin : FiniteDimensional (ResidueField A)
      (IntermediateField.adjoin (ResidueField A)
        (perfectCore (ResidueField B) p : Set (ResidueField B)))) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsDiscreteValuationRing A₁)
      (_ : Algebra A A₁) (_ : Module.Finite A A₁)
      (_ : Algebra.Etale A A₁)
      (_ : IsDiscreteValuationRing.IsExtension A A₁) (_ : Algebra A₁ B)
      (_ : IsScalarTower A A₁ B) (_ : IsLocalHom (algebraMap A₁ B)),
      IsDiscreteValuationRing.IsWeaklyUnramified A A₁ ∧
        ∀ x : ResidueField B, x ∈ perfectCore (ResidueField B) p →
          ∃ a : ResidueField A₁, algebraMap (ResidueField A₁) (ResidueField B) a = x := by
  let E := IntermediateField.adjoin (ResidueField A)
    (perfectCore (ResidueField B) p : Set (ResidueField B))
  have : FiniteDimensional (ResidueField A) E := hfin
  have : Algebra.IsSeparable (ResidueField A) E :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable
      (ResidueField A) (ResidueField B)).mpr fun x hx => hepp x hx
  exact EppCondition.exists_finiteEtale_forall_mem_perfectCore_mem_range (p := p) E
    fun x hx => IntermediateField.subset_adjoin _ _ hx

end Stacks.EppTheorem

end
