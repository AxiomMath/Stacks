module

public import Mathlib
public import StacksCore.FieldTheory.AlgebraicClosure
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationII
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.SolutionTower
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.IntegralClosure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Eliminating ramification for an essentially finite type extension, given Epp's theorem

Let `A → B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, and suppose
`B` is essentially of finite type over `A`.  Stacks Tag 09II asserts that there is then a *finite*
extension `K₁ / K` which is a **solution** for `A → B` in the sense of Tag 09EN: the two integral
closures attached to `K₁` have formally smooth local homomorphisms at every maximal ideal
upstairs. This file develops the implication from Epp's theorem (Tag 09F9), keeping that theorem
as an explicit parameter so the large 09II construction is independent of its proof.

## Why Epp's theorem is a parameter here

The Stacks route through Tag 09ET cannot be used verbatim: its weak-solution clause (3) is false
(there is a counterexample). The replacement proof of 09F9 therefore lives in
separate modules. Keeping the target here as the implication

  Epp's theorem (09F9)  ⟹  elimination of ramification (09II),

makes the dependency boundary explicit and avoids an import cycle. `EppTheorem` is the statement
of 09F9, verbatim, as a `Prop`; `EliminateRamificationTheorem.lean` supplies its unconditional
provider and records the tagged 09II endpoint.

## What is proved

The proof of 09II splits into three cases according to the residue field `κ_A`.

* Residue characteristic zero, and more generally perfect `κ_A`: a weak solution is already a
  solution (Tag 09E7), so Epp's theorem applies directly.  **Both cases are proved here**, from
  `EppTheorem` alone, as `exists_finite_extension_isSolution_of_charZero` and
  `exists_finite_extension_isSolution_of_perfectField`.
* Positive residue characteristic with *imperfect* `κ_A` — the wild case.  The construction
  first passes to an algebraic extension with perfect residue field, solves the finitely many
  local problems there using Epp's theorem, and descends all finite data to one finite extension
  of `K`.

The machinery of the wild case is present in this file, ported in full and compiling:
the weakly unramified colimit construction producing an algebraic extension `E / K` whose integral
closure `A' = integralClosure A E` is a discrete valuation ring with algebraically closed — hence
perfect — residue field (`exists_algebraic_extension_isDiscreteValuationRing_integralClosure`); the
Dedekind, Noetherian, finite-spectrum and localization facts about the integral closure of `B` in
the reduced compositum `(L ⊗[K] E)ᵣₑd`; the merge of the finitely many local solutions into one
finite extension via Tag 0GLR (`exists_finite_extension_localSolutions_of_perfectField`); and the
transports of adic formal smoothness along ring equivalences, localizations and bijective base
changes that the finite-stage descent consumes; and the two final finite-stage assembly steps.

## Main definitions

* `Stacks.EliminateRamification.EppTheorem`: the statement of Epp's theorem (Tag 09F9) at four
  fixed universes, as
  a `Prop`. Its residue-field hypothesis is `Stacks.EppTheorem.EppCondition`.

## Main results

* `Stacks.EliminateRamification.exists_finite_extension_isSolution_of_charZero`: 09II in residue
  characteristic
  zero, from Epp's theorem.  The hypothesis that `B` is essentially of finite type is not used.
* `Stacks.EliminateRamification.exists_finite_extension_isSolution_of_perfectField`: 09II over a
  perfect residue
  field, from Epp's theorem.
* `Stacks.EliminateRamification.exists_finite_extension_isSolution_of_eppTheorem`: the exact
  conclusion of Tag
  09II from Epp's theorem at the two universe profiles used by the construction. The reusable
  implication remains untagged; `EliminateRamificationTheorem.lean` instantiates it and carries
  the tag.

## Implementation notes

The mathematics is the Stacks proof of 09II, ported from a `Card_*`-based development: every
reference to a `Card_*` namespace has been rewritten to the conceptual provider in this tree,
namely `IsDiscreteValuationRing.IsExtension`, `.IsWeaklyUnramified`, `.ramificationIndex` and
`.ramificationIndex_characterization` (Tag 09E4), `RingHom.FormallySmoothNAdic` (Tag 07NI),
`IsDiscreteValuationRing.IntegralClosureBaseChange` with its `IsWeakSolution` and `IsSolution`
(Tag 09EN), `IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension`
(Tag 09E7), the Tag 09IH provider
`IsDiscreteValuationRing.integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective`,
`IsDiscreteValuationRing.exists_isSolution_of_tower` (Tag 0GLR) and
`IsDiscreteValuationRing.integralClosures_after_finite_fraction_field_extension` (Tag 09EM).
Reductions of tensor products use the root-level `ReducedTensorTower` namespace.

The small declaration `smulLocalizationAtPrime` exists only to move a typeclass search out of a
proof with a large local instance context, where the default `synthInstance` budget does not
suffice, into a context with a handful of hypotheses, where it does.

## References

* [The Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [Epp, *Elimination of wild ramification*][epp1973]
* [de Jong, *Smoothness, semi-stability and alterations*, Lemma 2.13][alterations]
-/

/-! ## Contents of this part

Part 1 of the development of Stacks Tag 09II from Epp's theorem (Tag 09F9) in
`StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution`. It contains
the statement `EppTheorem` of Epp's theorem (Tag 09F9) as a `Prop`, finiteness and bijectivity
of prime spectra along integral maps, separability along directed unions, and the algebraic
extension `E / K` whose integral closure of `A` is a discrete valuation ring with algebraically
closed residue field (`exists_algebraic_extension_isDiscreteValuationRing_integralClosure`).
-/

@[expose] public section

universe uA uB uK uL v uK₁ uL₁ uA₁ uB₁

namespace Stacks.EliminateRamification

open IsLocalRing
open scoped TensorProduct

/-- The scalar action of a commutative ring on its localization at a prime, named so that it can
be supplied directly instead of being searched for. -/
private abbrev smulLocalizationAtPrime (R : Type*) [CommRing R] (q : Ideal R) [q.IsPrime] :
    SMul R (Localization.AtPrime q) := Algebra.toSMul

/-- **Epp's theorem (Stacks Tag 09F9) as an assumable statement.**

For every extension `A ⊂ B` of discrete valuation rings with fraction fields `K ⊂ L` such that,
whenever the residue characteristic of `A` is a prime `p`, every element of
`⋂_{n ≥ 1} κ_B^{p^n}` is separable algebraic over `κ_A`, there is a finite extension `K₁ / K`
which is a *weak* solution for `A → B` (Tag 09EN(1)): every maximal ideal of the integral closure
`B₁` of `B` in `(L ⊗[K] K₁)ᵣₑd` has ramification index one over the integral closure `A₁` of `A`
in `K₁`.

The residue-field hypothesis is `Stacks.EppTheorem.EppCondition A B p`, which is by definition
`∀ x ∈ perfectCore κ_B p, IsSeparable κ_A x`; `Stacks.EppTheorem.eppCondition_iff_forall_one_le`
  unfolds
it into the `⋂_{n ≥ 1} κ_B^{p^n}` form in which Tag 09F9 states it.  `ExpChar κ_B p` is taken as
an extra argument rather than derived, so that the statement mentions no instance that is not
already in scope; it is automatic from `p.Prime` and `CharP κ_A p`, since `κ_A → κ_B` is
injective, so this costs no generality.

This abbreviation keeps the statement usable as a parameter. The unconditional provider is
`Stacks.EppTheorem.eppTheorem_monomorphic` in `EppTheorem.lean`. -/
abbrev EppTheorem : Prop :=
  ∀ (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L],
    (∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ [ExpChar (IsLocalRing.ResidueField B) p], Stacks.EppTheorem.EppCondition A B p) →
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L K₁,
        D.IsWeakSolution

open IsLocalRing
open scoped TensorProduct

/-- A Noetherian integral algebra over a ring with finite spectrum has finite spectrum. -/
theorem finite_primeSpectrum_of_isIntegral_of_isNoetherianRing
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [IsNoetherianRing S] [Finite (PrimeSpectrum R)] :
    Finite (PrimeSpectrum S) := by
  let Q (p : PrimeSpectrum R) :=
    {q : Ideal S // q ∈ (p.asIdeal.map (algebraMap R S)).minimalPrimes}
  have (p : PrimeSpectrum R) : Finite (Q p) :=
    ((p.asIdeal.map (algebraMap R S)).finite_minimalPrimes_of_isNoetherianRing S).to_subtype
  let f (q : PrimeSpectrum S) : Σ p : PrimeSpectrum R, Q p :=
    ⟨PrimeSpectrum.comap (algebraMap R S) q, ⟨q.asIdeal,
      Ideal.IsIntegral.mem_minimalPrimes_map_under q.asIdeal⟩⟩
  exact Finite.of_injective f fun q r h =>
    PrimeSpectrum.ext (congrArg (fun z : Σ p : PrimeSpectrum R, Q p => z.2.val) h)

/-- The contraction maps from a finite spectrum into an increasing union of subrings
are eventually injective. -/
private theorem exists_primeSpectrum_comap_injective
    {R : Type*} [CommRing R] [Finite (PrimeSpectrum R)]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (S : ι → Subring R) (hS : Monotone S) (hcover : ∀ x : R, ∃ i, x ∈ S i) :
    ∃ i, ∀ j, i ≤ j → Function.Injective (PrimeSpectrum.comap (S j).subtype) := by
  classical
  have hsep (p q : PrimeSpectrum R) :
      ∃ i, ∀ j, i ≤ j →
        p.asIdeal.comap (S j).subtype = q.asIdeal.comap (S j).subtype → p = q := by
    by_cases hpq : p = q
    · exact ⟨Classical.arbitrary ι, fun _ _ _ => hpq⟩
    have hne : ¬ ∀ x : R, x ∈ p.asIdeal ↔ x ∈ q.asIdeal := fun h =>
      hpq (PrimeSpectrum.ext (Ideal.ext h))
    obtain ⟨x, hx⟩ := not_forall.mp hne
    obtain ⟨i, hxi⟩ := hcover x
    refine ⟨i, fun j hij he => False.elim (hx ?_)⟩
    let xj : S j := ⟨x, hS hij hxi⟩
    exact iff_of_eq (congrArg (fun I : Ideal (S j) => xj ∈ I) he)
  choose f hf using hsep
  obtain ⟨i, hi⟩ := Finite.exists_le (fun pq : PrimeSpectrum R × PrimeSpectrum R =>
    f pq.1 pq.2)
  refine ⟨i, fun j hij p q hpq => ?_⟩
  exact hf p q j ((hi (p, q)).trans hij) (congrArg PrimeSpectrum.asIdeal hpq)

/-- For an integral increasing union with finite spectrum, contraction is eventually bijective. -/
theorem exists_primeSpectrum_comap_bijective
    {R : Type*} [CommRing R] [Finite (PrimeSpectrum R)]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (S : ι → Subring R) (hS : Monotone S) (hcover : ∀ x : R, ∃ i, x ∈ S i)
    (hint : ∀ i, (S i).subtype.IsIntegral) :
    ∃ i, ∀ j, i ≤ j → Function.Bijective (PrimeSpectrum.comap (S j).subtype) := by
  obtain ⟨i, hi⟩ := exists_primeSpectrum_comap_injective S hS hcover
  exact ⟨i, fun j hij => ⟨hi j hij,
    RingHom.IsIntegral.comap_surjective (hint j) Subtype.val_injective⟩⟩

/-- In an algebraic field extension, the finite subextensions eventually distinguish
all primes of the integral closure, if that integral closure has finite spectrum. -/
private theorem exists_primeSpectrum_bijective_integralClosure_finite_stage
    (A K E : Type*) [CommRing A] [Field K] [Field E]
    [Algebra A K] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [Algebra.IsAlgebraic K E] [Finite (PrimeSpectrum (integralClosure A E))] :
    ∃ F : IntermediateField K E, Module.Finite K F ∧
      ∀ G : IntermediateField K E, Module.Finite K G → F ≤ G →
        Function.Bijective (PrimeSpectrum.comap
          (G.toSubalgebra.toSubring.comap (integralClosure A E).val.toRingHom).subtype) := by
  classical
  let ι := {F : IntermediateField K E // Module.Finite K F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  have : IsDirectedOrder ι := ⟨fun F G => by
    have := F.property
    have := G.property
    exact ⟨⟨F.val ⊔ G.val, inferInstance⟩,
      show F.val ≤ F.val ⊔ G.val from le_sup_left,
      show G.val ≤ F.val ⊔ G.val from le_sup_right⟩⟩
  let S (F : ι) : Subring (integralClosure A E) :=
    F.val.toSubalgebra.toSubring.comap (integralClosure A E).val.toRingHom
  have hS : Monotone S := fun _ _ h _ hx => h hx
  have hcover (x : integralClosure A E) : ∃ i, x ∈ S i := by
    let F := IntermediateField.adjoin K {(x : E)}
    have hfinite : Module.Finite K F :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (x : E))
    exact ⟨⟨F, hfinite⟩, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hint (F : ι) : (S F).subtype.IsIntegral := by
    let f : A →+* S F := (algebraMap A (integralClosure A E)).codRestrict (S F) (by
      intro a
      show algebraMap A E a ∈ F.val
      rw [IsScalarTower.algebraMap_apply A K E]
      exact F.val.algebraMap_mem (algebraMap A K a))
    apply RingHom.IsIntegral.tower_top f
    have he : (S F).subtype.comp f = algebraMap A (integralClosure A E) := by
      ext a
      rfl
    rw [he]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  obtain ⟨F, hF⟩ := exists_primeSpectrum_comap_bijective S hS hcover hint
  exact ⟨F.val, F.property, fun G hG hFG => hF ⟨G, hG⟩ hFG⟩

/-- The coefficients of a polynomial over a directed union occur at one stage. -/
private theorem exists_polynomial_map_subtype_eq
    {R : Type*} [CommRing R]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (S : ι → Subring R) (hS : Monotone S) (hcover : ∀ x : R, ∃ i, x ∈ S i)
    (p : Polynomial R) :
    ∃ i, ∀ j, i ≤ j → ∃ q : Polynomial (S j), q.map (S j).subtype = p := by
  classical
  choose f hf using fun x : p.coeffs => hcover (x : R)
  obtain ⟨i, hi⟩ := Finite.exists_le f
  refine ⟨i, fun j hij => ?_⟩
  have hp : (p.coeffs : Set R) ⊆ S j := by
    intro x hx
    exact hS ((hi ⟨x, hx⟩).trans hij) (hf ⟨x, hx⟩)
  exact ⟨p.toSubring (S j) hp, p.map_toSubring (S j) hp⟩

/-- Separable algebraicity of one element descends to a stage of an increasing union
of coefficient fields. -/
private theorem exists_isSeparable_of_directed_union
    {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (F : ι → Subfield K) (hF : Monotone F) (hcover : ∀ x : K, ∃ i, x ∈ F i)
    {x : L} (hx : IsSeparable K x) :
    ∃ i, ∀ j, i ≤ j →
      letI : Algebra (F j) L := ((algebraMap K L).comp (F j).subtype).toAlgebra
      IsSeparable (F j) x := by
  obtain ⟨i, hi⟩ := exists_polynomial_map_subtype_eq
    (fun j => (F j).toSubring) (fun _ _ h => hF h) hcover (minpoly K x)
  refine ⟨i, fun j hij => ?_⟩
  let : Algebra (F j) L := ((algebraMap K L).comp (F j).subtype).toAlgebra
  obtain ⟨q, hq⟩ := hi j hij
  have hsep : q.Separable := (Polynomial.separable_map (F j).subtype).mp (hq.symm ▸ hx)
  apply hsep.of_dvd
  apply minpoly.dvd
  show q.eval₂ ((algebraMap K L).comp (F j).subtype) x = 0
  rw [← Polynomial.eval₂_map]
  exact (congrArg (Polynomial.eval₂ (algebraMap K L) x) hq).trans (minpoly.aeval K x)

/-- A finite collection of separable elements is separable at a common coefficient stage. -/
private theorem exists_forall_isSeparable_of_directed_union
    {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (F : ι → Subfield K) (hF : Monotone F) (hcover : ∀ x : K, ∃ i, x ∈ F i)
    {κ : Type*} [Finite κ] (x : κ → L) (hx : ∀ a, IsSeparable K (x a)) :
    ∃ i, ∀ j, i ≤ j →
      letI : Algebra (F j) L := ((algebraMap K L).comp (F j).subtype).toAlgebra
      ∀ a, IsSeparable (F j) (x a) := by
  classical
  choose f hf using fun a => exists_isSeparable_of_directed_union F hF hcover (hx a)
  obtain ⟨i, hi⟩ := Finite.exists_le f
  exact ⟨i, fun j hij a => hf a j ((hi a).trans hij)⟩

/-- A prime of ramification index one in a flat tower has ramification index one below. -/
private theorem ramificationIdx_eq_one_of_tower
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [r.LiesOver q] [Module.Flat S T]
    (h : r.ramificationIdx R = 1) : q.ramificationIdx R = 1 :=
  Nat.eq_one_of_dvd_one ⟨r.ramificationIdx S, ((Ideal.ramificationIdx_tower q r).symm.trans h).symm⟩

/-- Irreducibility of the image of an element is preserved by an algebra isomorphism. -/
private theorem irreducible_algebraMap_iff_of_algEquiv
    {A S T : Type*} [CommSemiring A] [Semiring S] [Semiring T] [Algebra A S] [Algebra A T]
    (e : S ≃ₐ[A] T) (a : A) :
    Irreducible (algebraMap A S a) ↔ Irreducible (algebraMap A T a) := by
  rw [← e.commutes]
  exact (MulEquiv.irreducible_iff e).symm

/-- In an algebraically closed overfield, an integral extension of a discrete valuation
ring can be chosen with the same uniformizer and algebraically closed residue field. -/
private theorem exists_isAlgClosed_residueField_subalgebra
    (A Ω : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [FaithfulSMul A Ω]
    (π : A) (hπ : Irreducible π) :
    ∃ S : Subalgebra A Ω, S ≤ integralClosure A Ω ∧
      ∃ (_ : IsDiscreteValuationRing S),
        Irreducible (algebraMap A S π) ∧ IsAlgClosed (ResidueField S) := by
  classical
  let P (S : Subalgebra A Ω) : Prop := S ≤ integralClosure A Ω ∧
    ∃ (_ : IsDiscreteValuationRing S), Irreducible (algebraMap A S π)
  have hbot : P ⊥ := by
    let e := Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective A Ω)
    have hdvr : IsDiscreteValuationRing (⊥ : Subalgebra A Ω) :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
    refine ⟨bot_le, hdvr, ?_⟩
    exact (irreducible_algebraMap_iff_of_algEquiv e π).mpr hπ
  obtain ⟨S, _, hS⟩ := zorn_le_nonempty₀ {S | P S} (by
    intro c hcs hc y hy
    have hDVR (i : c) : IsDiscreteValuationRing i.val := (hcs i.property).2.choose
    have hirr (i : c) : Irreducible (algebraMap A i.val π) := (hcs i.property).2.choose_spec
    obtain ⟨hd, hi⟩ := IsDiscreteValuationRing.isDiscreteValuationRing_sSup_chain π c hc ⟨y, hy⟩
      (fun i hi => hDVR ⟨i, hi⟩) (fun i hi => hirr ⟨i, hi⟩)
    exact ⟨sSup c, ⟨sSup_le fun i hi => (hcs hi).1, hd, hi⟩,
      fun i hi => le_sSup hi⟩) ⊥ hbot
  obtain ⟨hSint, hSdvr, hπS⟩ := hS.prop
  have := hSdvr
  have : Algebra.IsIntegral A S := (Subalgebra.isIntegral_iff S).mpr hSint
  refine ⟨S, hSint, hSdvr, hπS, ?_⟩
  apply IsAlgClosed.of_exists_root
  intro p hp hpirr
  have hlift : p ∈ Polynomial.lifts (residue S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact residue_surjective _
  obtain ⟨q, hq, _, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  obtain ⟨hqdom, hqdvr, hqmax⟩ :=
    IsDiscreteValuationRing.adjoinRoot_isDiscreteValuationRing S q hqmonic (hq.symm ▸ hpirr)
  have := hqdom
  have := hqdvr
  have : Module.Finite S (AdjoinRoot q) := hqmonic.finite_adjoinRoot
  have : Module.Free S (AdjoinRoot q) := hqmonic.free_adjoinRoot
  have : Module.IsTorsionFree S (AdjoinRoot q) :=
    Module.Free.instIsTorsionFree S (AdjoinRoot q)
  have : IsScalarTower A S (AdjoinRoot q) := inferInstance
  let f : AdjoinRoot q →ₐ[S] Ω := IsAlgClosed.lift
  have hf : Function.Injective f := by
    let : Algebra (AdjoinRoot q) Ω := f.toRingHom.toAlgebra
    have : IsScalarTower S (AdjoinRoot q) Ω :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    exact Algebra.IsAlgebraic.injective_tower_top (AdjoinRoot q)
      (FaithfulSMul.algebraMap_injective S Ω)
  let T : Subalgebra A Ω := f.range.restrictScalars A
  let : Algebra S T := f.range.algebra
  let e : AdjoinRoot q ≃ₐ[S] T := AlgEquiv.ofInjective f hf
  have hTdvr : IsDiscreteValuationRing T :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hST : S ≤ T := by
    intro x hx
    exact ⟨algebraMap S (AdjoinRoot q) ⟨x, hx⟩, f.commutes _⟩
  have hπq : Irreducible (algebraMap A (AdjoinRoot q) π) := by
    apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    · show algebraMap S (AdjoinRoot q) (algebraMap A S π) ≠ 0
      simpa using (FaithfulSMul.algebraMap_injective S (AdjoinRoot q)).ne hπS.ne_zero
    · rw [← hqmax, hπS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
      rfl
  have hPT : P T := by
    refine ⟨?_, hTdvr, ?_⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact isIntegral_trans (R := A) _ ((Algebra.IsIntegral.isIntegral (R := S) y).map f)
    · have he : e (algebraMap A (AdjoinRoot q) π) = algebraMap A T π := by
        apply Subtype.ext
        show f (algebraMap S (AdjoinRoot q) (algebraMap A S π)) = algebraMap A Ω π
        exact f.commutes (algebraMap A S π)
      rw [← he]
      exact (MulEquiv.irreducible_iff e).mpr hπq
  have hTS : T ≤ S := hS.2 hPT hST
  let r : S := ⟨f (AdjoinRoot.root q), hTS ⟨AdjoinRoot.root q, rfl⟩⟩
  have hr : Polynomial.aeval r q = 0 := by
    apply Subtype.val_injective (p := fun x : Ω => x ∈ S)
    show algebraMap S Ω (Polynomial.aeval r q) = algebraMap S Ω 0
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply]
    show Polynomial.aeval (f (AdjoinRoot.root q)) q = 0
    rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  refine ⟨residue S r, ?_⟩
  rw [← hq, Polynomial.eval_map]
  simpa only [Polynomial.eval₂_at_apply, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id, RingHom.map_zero] using
    congrArg (residue S) hr

/-- The fraction field of a discrete valuation ring has an algebraic extension whose
normalization preserves a uniformizer and has perfect residue field. -/
theorem exists_algebraic_extension_isDiscreteValuationRing_integralClosure
    (A : Type uA) (K : Type uK)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] :
    ∃ (E : Type uK) (_ : Field E) (_ : Algebra K E) (_ : Algebra A E)
      (_ : IsScalarTower A K E) (_ : Algebra.IsAlgebraic K E),
      ∃ (_ : IsDiscreteValuationRing (integralClosure A E)),
        PerfectField (ResidueField (integralClosure A E)) ∧
        (maximalIdeal A).map (algebraMap A (integralClosure A E)) =
          maximalIdeal (integralClosure A E) := by
  classical
  let Ω := AlgebraicClosure K
  have : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).mpr (by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨S, hS, hdvr, hπS, hres⟩ :=
    exists_isAlgClosed_residueField_subalgebra A Ω π hπ
  have := hdvr
  have := hres
  have : Algebra.IsIntegral A S := (Subalgebra.isIntegral_iff S).mpr hS
  let E := FractionRing S
  let : Algebra K E :=
    (IsFractionRing.lift (K := K) (FaithfulSMul.algebraMap_injective A E)).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective A E) a).symm
  have : Algebra.IsAlgebraic A E :=
    (IsFractionRing.isAlgebraic_iff' A S E).mp inferInstance
  have : Algebra.IsAlgebraic K E := ⟨fun x =>
    (IsFractionRing.isAlgebraic_iff A K E).mp (Algebra.IsAlgebraic.isAlgebraic x)⟩
  have : IsIntegralClosure S A E := inferInstance
  let e : S ≃ₐ[A] integralClosure A E :=
    IsIntegralClosure.equiv A S E (integralClosure A E)
  have : IsDiscreteValuationRing (integralClosure A E) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmax := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  have hperfect : PerfectField (ResidueField (integralClosure A E)) :=
    PerfectField.of_ringEquiv (K := ResidueField S)
      (Ideal.quotientEquiv (maximalIdeal S) (maximalIdeal (integralClosure A E))
        e.toRingEquiv hmax.symm)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hperfect, ?_⟩
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  exact ((irreducible_algebraMap_iff_of_algEquiv e π).mp hπS).maximalIdeal_eq.symm

/-- An increasing union of discrete valuation subrings which is itself a discrete
valuation ring is eventually weakly unramified, provided every inclusion is local. -/
private theorem exists_isWeaklyUnramified_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (S : ι → Subring R) [∀ i, IsDiscreteValuationRing (S i)]
    [∀ i, IsDiscreteValuationRing.IsExtension (S i) R]
    (hS : Monotone S) (hcover : ∀ x : R, ∃ i, x ∈ S i) :
    ∃ i, ∀ j, i ≤ j → IsDiscreteValuationRing.IsWeaklyUnramified (S j) R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨i, hi⟩ := hcover π
  refine ⟨i, fun j hij => ?_⟩
  exact IsDiscreteValuationRing.isWeaklyUnramified_of_irreducible_algebraMap (S j) R
    ⟨π, hS hij hi⟩ hπ

/-- Residue fields at maximal ideals of an integral algebra over a local ring
with perfect residue field are perfect. -/
theorem perfectField_residueField_of_integral
    (A S : Type*) [CommRing A] [IsLocalRing A] [CommRing S]
    [Algebra A S] [Algebra.IsIntegral A S]
    [PerfectField (IsLocalRing.ResidueField A)]
    (q : Ideal S) [q.IsMaximal] : PerfectField q.ResidueField := by
  let p := IsLocalRing.maximalIdeal A
  have hpq : p = q.comap (algebraMap A S) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) q)).symm
  have : q.LiesOver p := ⟨hpq⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : PerfectField p.ResidueField :=
    Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField A)
  exact Algebra.IsAlgebraic.perfectField p.ResidueField

/-- Ramification index one says that the contracted prime generates the maximal ideal
of the localization upstairs. -/
theorem map_under_eq_maximalIdeal_of_ramificationIdx_eq_one
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] (h : q.ramificationIdx R = 1) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  exact h

end Stacks.EliminateRamification
