module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Catenary
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Localization.ClosedPointOfSpecialFibre
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
import StacksFrontier.RingTheory.Catenary.Saturated
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary

@[expose] public section

/-!
# Formally catenary local rings

A local ring is *formally catenary* when, after completion, the quotient by the extension of each
minimal prime has equidimensional spectrum. Formal catenarity is equivalent to universal
catenarity for Noetherian local rings; this is Ratliff's theorem, and both implications are proved
here.

## Main definitions

* `IsFormallyCatenary`: the formally catenary property for local rings.

## Main results

* `isUniversallyCatenary_of_isFormallyCatenary` (Stacks 0AW5): a formally catenary Noetherian
  local ring is universally catenary.
* `not_isUniversallyCatenary_of_not_isFormallyCatenary` (Stacks 0AW3): a Noetherian local ring
  which is not formally catenary is not universally catenary.
* `isUniversallyCatenary_iff_isFormallyCatenary` (Stacks 0AW6): Ratliff's theorem, that the two
  properties agree for a Noetherian local ring.

## Implementation notes

The completion is the adic completion at the maximal ideal. The source restricts the definition to
Noetherian local rings, but Noetherianity is not needed to *form* this condition and is therefore
left to the results that use it.

Equidimensionality is spelled topologically, as `TopologicalSpace.Equidimensional` of the prime
spectrum. This is the dominant convention in this repository and the one used by the results in
this section. `StacksFrontier.RingTheory.Equidimensional.FlatLocal`, which carries Stacks 0AW4,
states its two clauses with its own ring-theoretic `SpecEquidimensional`; the two agree by
`specEquidimensional_iff_equidimensional`, and Stacks 0AW5 consumes Stacks 0AW4 through that
file's `specEquidimensional_quotients_and_isCatenary_of_flat_local`, the topological packaging of
both clauses.

Stacks 0AW3 rests on Stacks 0ALR, the algebraization of a quotient of an adic completion whose
conormal module is annihilated by a power of the ideal; that is
`exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated` of
`StacksFrontier.RingTheory.AdicCompletion.Algebraization` and is used through the local
`exists_finiteType_algEquiv_adicCompletion_quotient`.

That completion at the maximal ideal leaves the Krull dimension of a Noetherian local ring
unchanged is Stacks 07NV, taken from `ringKrullDim_adicCompletion_maximalIdeal` in
`StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties`, where the tag is registered.

Completeness of a Noetherian local ring is expressed by precompleteness for its maximal ideal, as
in Stacks 07PJ and 07PX. That a complete Noetherian local ring is universally catenary is
Stacks 032C, and also part of Stacks 07QW, the standard classes of excellent rings; it is proved
here as `isUniversallyCatenary_of_isPrecomplete_maximalIdeal` from the Cohen structure theorem
(`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries`) and the
Cohen-Macaulay criterion `Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ`,
since excellence itself is not part of the conceptual tree.

## References

* [Stacks Project, Tag 0AW2](https://stacks.math.columbia.edu/tag/0AW2)
* [Stacks Project, Tag 0AW3](https://stacks.math.columbia.edu/tag/0AW3)
* [Stacks Project, Tag 0AW5](https://stacks.math.columbia.edu/tag/0AW5)
* [Stacks Project, Tag 0AW6](https://stacks.math.columbia.edu/tag/0AW6)
* [Stacks Project, Tag 032C](https://stacks.math.columbia.edu/tag/032C)
* [Ratliff]
-/

universe u

/-- A local ring `A` is formally catenary if, for every minimal prime `p` of `A`, the spectrum
of the quotient of its maximal-ideal-adic completion by the extension of `p` is
equidimensional. -/
@[stacks 0AW2, ega "IV 7.1.9"]
def IsFormallyCatenary (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ p ∈ minimalPrimes A,
    TopologicalSpace.Equidimensional
      (PrimeSpectrum
        (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸
          p.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))))

section FormallyCatenaryIsUniversallyCatenary

open TopologicalSpace IrreducibleClosedsCodim
open scoped TensorProduct

/-! ### Translating between the catenarity predicates -/

private theorem isUniversallyCatenary_iff_isUniversallyCatenaryRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    Ring.IsUniversallyCatenary R ↔ IsUniversallyCatenaryRing R := by
  constructor
  · intro h S _ _ hS
    have := hS
    exact Ring.isCatenary_iff_isCatenaryRing.mp (h S)
  · intro h S _ _ hS
    exact Ring.isCatenary_iff_isCatenaryRing.mpr (h S hS)

@[ega "IV 5.6.3" "(iii)"]
private theorem isUniversallyCatenary_of_quotient_minimalPrimes
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : ∀ p ∈ minimalPrimes R, Ring.IsUniversallyCatenary (R ⧸ p)) :
    Ring.IsUniversallyCatenary R := by
  apply isUniversallyCatenary_iff_isUniversallyCatenaryRing.mpr
  apply (isUniversallyCatenaryRing_iff_quotient_minimalPrimes R).mpr
  intro p hp
  exact isUniversallyCatenary_iff_isUniversallyCatenaryRing.mp (hR p hp)

/-- **The prime spectrum of a catenary ring is a catenary topological space.** This is the
forward half of [Stacks, Tag 02IH] in the `Ring.IsCatenary` encoding of catenarity; the tag
itself sits on `Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum`, which is stated for
the order-theoretic `Catenary.IsCatenaryRing`, and this is that equivalence composed with the
translation between the two encodings. -/
@[ega "IV 5.1.1" "(5.1.1.4)"]
theorem isCatenarySpace_of_isCatenary {R : Type*} [CommRing R]
    (hR : Ring.IsCatenary R) : IsCatenarySpace (PrimeSpectrum R) :=
  AlgebraicGeometry.catenarySpace_of_order
    ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mp
      (AlgebraicGeometry.catenaryOrder_of_ringIsCatenary hR))

/-- **A ring whose prime spectrum is a catenary topological space is catenary.** The converse
direction of `isCatenarySpace_of_isCatenary`, and the half that a scheme-theoretic hypothesis is
consumed through: a statement about the space `Spec R` is turned back into one about `R`. -/
@[ega "IV 5.1.1" "(5.1.1.4)"]
theorem isCatenary_of_isCatenarySpace {R : Type*} [CommRing R]
    (hR : IsCatenarySpace (PrimeSpectrum R)) : Ring.IsCatenary R :=
  AlgebraicGeometry.ringIsCatenary_of_catenaryOrder
    ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mpr
      (AlgebraicGeometry.catenaryOrder_of_catenarySpace hR))

/-! ### Catenarity along localizations -/

private theorem isCatenaryOrder_of_orderEmbedding {P Q : Type*}
    [PartialOrder P] [PartialOrder Q] (f : P ↪o Q) (hf : (Set.range f).OrdConnected)
    (hQ : Catenary.IsCatenaryOrder Q) : Catenary.IsCatenaryOrder P := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, heq⟩ := hQ (f p) (f q) (f.monotone hpq)
  refine ⟨⟨N, ?_⟩, ?_⟩
  · intro s hs ht
    exact hN (s.map f f.strictMono) (congrArg f hs) (congrArg f ht)
  · intro s t hs ht hs' ht'
    let map (s : RelSeries {(a, b) : P × P | a ⋖ b}) : RelSeries {(a, b) : Q × Q | a ⋖ b} :=
      ⟨s.length, f ∘ s.toFun, fun i => (hf.apply_covBy_apply_iff f).mpr (s.step i)⟩
    exact heq (map s) (map t) (congrArg f hs) (congrArg f ht) (congrArg f hs') (congrArg f ht')

@[ega "0 16.1.4"]
private theorem ringIsCatenary_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : Ring.IsCatenary R) : Ring.IsCatenary S := by
  apply AlgebraicGeometry.ringIsCatenary_of_catenaryOrder
  let e := IsLocalization.primeSpectrumOrderIso M S
  apply Catenary.isCatenaryOrder_of_orderIso e.symm
  apply isCatenaryOrder_of_orderEmbedding (OrderEmbedding.subtype _)
  · simp only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype]
    constructor
    intro p hp q hq r hr
    exact hq.mono_right hr.2
  · exact AlgebraicGeometry.catenaryOrder_of_ringIsCatenary hR

private theorem isCatenaryOrder_of_forall_Iic {P : Type*} [PartialOrder P]
    (hP : ∀ q : P, Catenary.IsCatenaryOrder (Set.Iic q)) :
    Catenary.IsCatenaryOrder P := by
  intro p q hpq
  let p' : Set.Iic q := ⟨p, hpq⟩
  let q' : Set.Iic q := ⟨q, le_rfl⟩
  obtain ⟨⟨N, hN⟩, heq⟩ := hP q p' q' hpq
  refine ⟨⟨N, ?_⟩, ?_⟩
  · intro s hs ht
    let t : LTSeries (Set.Iic q) :=
      ⟨s.length, fun i => ⟨s i, by
        simpa only [Set.mem_Iic, ← ht, RelSeries.last] using s.monotone (Fin.le_last i)⟩, s.step⟩
    exact hN t (Subtype.ext hs) (Subtype.ext ht)
  · intro s t hs ht hs' ht'
    let restrict (s : RelSeries {(a, b) : P × P | a ⋖ b}) (h : s.last = q) :
        RelSeries {(a, b) : Set.Iic q × Set.Iic q | a ⋖ b} :=
      let sl : LTSeries P := ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
      ⟨s.length, fun i => ⟨s i, by
        simpa only [Set.mem_Iic, ← h, RelSeries.last] using sl.monotone (Fin.le_last i)⟩,
        fun i => (s.step i).of_image (OrderEmbedding.subtype _)⟩
    exact heq (restrict s ht) (restrict t ht') (Subtype.ext hs) (Subtype.ext ht)
      (Subtype.ext hs') (Subtype.ext ht')

private theorem isCatenary_of_forall_localizationAtPrime {R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime], Ring.IsCatenary (Localization.AtPrime p)) :
    Ring.IsCatenary R := by
  apply AlgebraicGeometry.ringIsCatenary_of_catenaryOrder
  apply isCatenaryOrder_of_forall_Iic
  intro p
  exact Catenary.isCatenaryOrder_of_orderIso
    (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p.asIdeal) p.asIdeal)
    (AlgebraicGeometry.catenaryOrder_of_ringIsCatenary (hR p.asIdeal))

private theorem isCatenary_of_isLocalizationAtPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]
    (hR : Ring.IsCatenary R) : Ring.IsCatenary S := by
  apply AlgebraicGeometry.ringIsCatenary_of_catenaryOrder
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso S p
  apply Catenary.isCatenaryOrder_of_orderIso e.symm
  apply isCatenaryOrder_of_orderEmbedding (OrderEmbedding.subtype _)
  · simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
      using (Set.ordConnected_Iic : (Set.Iic (⟨p, inferInstance⟩ : PrimeSpectrum R)).OrdConnected)
  · exact AlgebraicGeometry.catenaryOrder_of_ringIsCatenary hR

/-! ### Complete Noetherian local rings are universally catenary

This is the part of Stacks 07QW that Stacks 0AW5 consumes, re-derived from the Cohen structure
theorem: a complete Noetherian local ring is a quotient of a power series ring over a field or a
Cohen ring, hence of a regular local ring, and a regular local ring is Cohen-Macaulay with full
support, so Stacks 00NM applies. -/

public theorem isUniversallyCatenary_of_forall_isMaximalCohenMacaulay
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p)) :
    Ring.IsUniversallyCatenary R := by
  apply Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ (M := R)
  · intro p _
    let e : LocalizedModule p.asIdeal.primeCompl R ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal :=
      (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
        (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
          p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    rw [Module.depth_eq_depth_of_linearEquiv _ e, Module.supportDim_eq_of_equiv e,
      Module.supportDim_self_eq_ringKrullDim]
    exact hR p.asIdeal
  · rw [Module.support_eq_zeroLocus,
      Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R),
      PrimeSpectrum.zeroLocus_bot]

@[ega "IV 5.6.4" "special case", ega "IV 7.1.11" "clause (i), special case"]
public theorem isUniversallyCatenary_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : Ring.IsUniversallyCatenary R :=
  isUniversallyCatenary_of_forall_isMaximalCohenMacaulay R fun p _ =>
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).2).of_isLocalization_atPrime p (Localization.AtPrime p)

/-- **Stacks Project, Tag 032C.** A Noetherian complete local ring is universally catenary.

By the Cohen structure theorem it is a quotient of a power series ring over a field or over a
Cohen ring, hence of a regular local ring; a regular local ring is Cohen-Macaulay with full
support, so [Stacks, Tag 00NM] applies, and universal catenarity passes to quotients.

Completeness is asked for as precompleteness for the maximal ideal, as in [Stacks, Tag 07PJ]; the
Hausdorff half is automatic for a Noetherian local ring, so a ring carrying
`IsAdicComplete (IsLocalRing.maximalIdeal R) R` satisfies the hypothesis by inference. -/
@[stacks 032C "universally catenary",
  ega "IV 5.2.5" "special case",
  ega "IV 5.6.4" "special case",
  ega "IV 7.1.11" "clause (i), special case",
  ega "IV 7.5.3" "more general"]
theorem isUniversallyCatenary_of_isPrecomplete_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (IsLocalRing.maximalIdeal R) R] : Ring.IsUniversallyCatenary R := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R := IsAdicComplete.mk
  obtain ⟨n, Λ, _, _, hΛ, f, hf⟩ :=
    (IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries R).2
      (Ideal.fg_of_isNoetherianRing _)
  have : IsRegularLocalRing Λ := by
    rcases hΛ with hΛ | hΛ
    · let : Field Λ := hΛ.toField
      infer_instance
    · have : IsCohenRing Λ := hΛ
      infer_instance
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := MvPowerSeries.isRegularLocalRing Λ n
  exact Ring.IsUniversallyCatenary.of_surjective hf
    (isUniversallyCatenary_of_isRegularLocalRing (MvPowerSeries (Fin n) Λ))

@[ega "IV 7.1.11" "clause (i), special case"]
private theorem isUniversallyCatenary_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    Ring.IsUniversallyCatenary R := by
  have : IsPrecomplete (IsLocalRing.maximalIdeal R) R :=
    IsAdicComplete.toIsPrecomplete
  exact isUniversallyCatenary_of_isPrecomplete_maximalIdeal R

/-! ### Completion of a quotient -/

private theorem isLocalization_maximalIdeal_self
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) :=
  IsLocalization.of_le_isUnit fun x hx => by
    exact IsLocalRing.notMem_maximalIdeal.mp hx

/-- A nontrivial quotient of a local ring is local. -/
private instance isLocalRing_quotient_of_nontrivial {R : Type*} [CommRing R] [IsLocalRing R]
    {I : Ideal R} [Nontrivial (R ⧸ I)] : IsLocalRing (R ⧸ I) :=
  .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

private theorem nonempty_ringEquiv_tensor_adicCompletion_of_finite_local
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Module.Finite R S] :
    Nonempty (S ⊗[R] AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  have hq (q : (IsLocalRing.maximalIdeal R).primesOver S) : q.val = IsLocalRing.maximalIdeal S := by
    have : q.val.IsPrime := q.property.1
    have : q.val.LiesOver (IsLocalRing.maximalIdeal R) := q.property.2
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.of_liesOver_isMaximal q.val (IsLocalRing.maximalIdeal R))
  have hm : (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  let : Unique ((IsLocalRing.maximalIdeal R).primesOver S) :=
    { default := ⟨IsLocalRing.maximalIdeal S, inferInstance, hm⟩
      uniq q := Subtype.ext (hq q) }
  have : IsLocalization.AtPrime R (IsLocalRing.maximalIdeal R) :=
    isLocalization_maximalIdeal_self R
  have (q : (IsLocalRing.maximalIdeal R).primesOver S) : IsLocalization.AtPrime S q.val := by
    apply IsLocalization.of_le_isUnit
    intro x hx
    apply IsLocalRing.notMem_maximalIdeal.mp
    change x ∉ q.val at hx
    simpa only [hq q] using hx
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver
    (R := R) (S := S) (IsLocalRing.maximalIdeal R) R (fun _ => S)
  exact ⟨e.toRingEquiv.trans (RingEquiv.piUnique _)⟩

/-- For a Noetherian local ring `R` and an ideal `I` such that `R ⧸ I` is local, the quotient of
the maximal-ideal-adic completion of `R` by the extension of `I` is the maximal-ideal-adic
completion of `R ⧸ I`. -/
theorem nonempty_ringEquiv_quotient_adicCompletion
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    Nonempty ((AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I)) := by
  have : IsLocalHom (algebraMap R (R ⧸ I)) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let T := AdicCompletion (IsLocalRing.maximalIdeal R) R
  obtain ⟨e⟩ := nonempty_ringEquiv_tensor_adicCompletion_of_finite_local R (R ⧸ I)
  let q := Algebra.TensorProduct.quotientTensorEquiv (R := R) R T R I
  let l := Algebra.TensorProduct.lid R T
  have he : I.map (algebraMap R T) =
      (I.map (algebraMap R (R ⊗[R] T))).map l.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    exact (l.commutes r).symm
  let g := Ideal.quotientEquivAlg _ _ l he
  exact ⟨g.symm.toRingEquiv.trans (q.symm.toRingEquiv.trans e)⟩

private theorem equidimensional_adicCompletion_quotient_iff
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R)
    [IsLocalRing (R ⧸ I)] :
    Equidimensional (PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal (R ⧸ I)) (R ⧸ I))) ↔
      Equidimensional (PrimeSpectrum
        (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
          I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_adicCompletion R I
  exact ⟨.of_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv e),
    .of_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv e.symm)⟩

private theorem equidimensional_adicCompletion_quotient_of_isFormallyCatenary
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsFormallyCatenary A) (p : Ideal A) (hp : p ∈ minimalPrimes A)
    [IsLocalRing (A ⧸ p)] :
    Equidimensional (PrimeSpectrum
      (AdicCompletion (IsLocalRing.maximalIdeal (A ⧸ p)) (A ⧸ p))) := by
  exact (equidimensional_adicCompletion_quotient_iff A p).mpr (hA p hp)

/-! ### Minimal primes and dimensions over a polynomial ring -/

private theorem isPrime_map_mvPolynomial_C {R : Type*} [CommRing R]
    (ι : Type*) (p : Ideal R) [p.IsPrime] :
    (p.map (MvPolynomial.C : R →+* MvPolynomial ι R)).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial p).symm.toRingEquiv.injective.isDomain
    (MvPolynomial.quotientEquivQuotientMvPolynomial p).symm.toRingEquiv

private theorem exists_minimalPrimes_map_mvPolynomial_C {R : Type*} [CommRing R]
    (ι : Type*) (q : Ideal (MvPolynomial ι R)) (hq : q ∈ minimalPrimes (MvPolynomial ι R)) :
    ∃ p ∈ minimalPrimes R, p.map (MvPolynomial.C : R →+* MvPolynomial ι R) = q := by
  have : q.IsPrime := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (J := q.comap (MvPolynomial.C : R →+* MvPolynomial ι R)) bot_le
  have : p.IsPrime := hp.1.1
  have hmap := Ideal.map_le_iff_le_comap.mpr hpq
  exact ⟨p, hp, le_antisymm hmap
    (hq.2 ⟨isPrime_map_mvPolynomial_C ι p, bot_le⟩ hmap)⟩

private theorem exists_minimalPrimes_map_mvPolynomial_localization {R : Type*} [CommRing R]
    (ι : Type*) (m : Ideal (MvPolynomial ι R)) [m.IsPrime]
    (q : Ideal (Localization.AtPrime m)) (hq : q ∈ minimalPrimes (Localization.AtPrime m)) :
    ∃ p ∈ minimalPrimes R, p.map (algebraMap R (Localization.AtPrime m)) = q := by
  have hc : q.under (MvPolynomial ι R) ∈ minimalPrimes (MvPolynomial ι R) := by
    rw [← Set.mem_preimage, ← IsLocalization.minimalPrimes_map m.primeCompl
      (Localization.AtPrime m), Ideal.map_bot]
    exact hq
  obtain ⟨p, hp, heq⟩ := exists_minimalPrimes_map_mvPolynomial_C ι _ hc
  refine ⟨p, hp, ?_⟩
  rw [IsScalarTower.algebraMap_eq R (MvPolynomial ι R) (Localization.AtPrime m),
    ← Ideal.map_map, show algebraMap R (MvPolynomial ι R) = MvPolynomial.C from rfl,
    heq, IsLocalization.map_under m.primeCompl (Localization.AtPrime m)]

private theorem height_mvPolynomial_of_liesOver_isMaximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] (n : ℕ) (p : Ideal R) [p.IsMaximal]
    (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal] [m.LiesOver p] :
    m.height = p.height + n := by
  let _ : Field (R ⧸ p) := Ideal.Quotient.field p
  let Q := m.map (Ideal.Quotient.mk (p.map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)))
  have hQ : Q.IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker, Ideal.map_le_iff_le_comap]
    exact (Ideal.LiesOver.over (P := m) (p := p)).le
  let e := (MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin n) p).symm.toRingEquiv
  have : (Q.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have h := mvpoly_maximal_height (R ⧸ p) n (Q.map e) inferInstance
  have hheight : Q.height = n := (RingEquiv.height_map e Q).symm.trans h
  exact (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m).trans
    (congrArg (fun h : ℕ∞ => p.height + h) hheight)

@[ega "IV 5.5.8" "special case"]
private theorem ringKrullDim_localization_mvPolynomial_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal]
    [m.LiesOver (IsLocalRing.maximalIdeal R)] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸ p.map (algebraMap R (Localization.AtPrime m))) =
      ringKrullDim (R ⧸ p) + n := by
  have : IsLocalHom (algebraMap R (R ⧸ p)) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let J := p.map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)
  have hJ : J ≤ m := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (IsLocalRing.le_maximalIdeal (show p ≠ ⊤ from Ideal.IsPrime.ne_top')).trans
      (Ideal.LiesOver.over (P := m) (p := IsLocalRing.maximalIdeal R)).le
  let Q := m.map (Ideal.Quotient.mk J)
  have hQ : Q.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hJ)
  have hQcomap : Q.comap (Ideal.Quotient.mk J) = m := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJ]
  have := isLocalization_atPrime_quotient m (Localization.AtPrime m) J Q hQcomap
  let e := (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).toRingEquiv
  let N := Q.comap e
  have hN : N.IsMaximal := Ideal.comap_isMaximal_of_surjective e e.surjective
  have hNover : N.LiesOver (IsLocalRing.maximalIdeal (R ⧸ p)) := by
    constructor
    apply Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top'
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : x ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.maximalIdeal_comap (algebraMap R (R ⧸ p))]
      exact hy
    change e (algebraMap R (MvPolynomial (Fin n) (R ⧸ p)) x) ∈ Q
    rw [show e (algebraMap R (MvPolynomial (Fin n) (R ⧸ p)) x) =
        algebraMap R (MvPolynomial (Fin n) R ⧸ J) x from
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin n) p).commutes x]
    apply Ideal.mem_map_of_mem
    change x ∈ m.under R
    rw [← Ideal.LiesOver.over (P := m) (p := IsLocalRing.maximalIdeal R)]
    exact hx
  have hdim := height_mvPolynomial_of_liesOver_isMaximal n
    (IsLocalRing.maximalIdeal (R ⧸ p)) N
  have hheight : Q.height = (IsLocalRing.maximalIdeal (R ⧸ p)).height + n :=
    (RingEquiv.height_comap e Q).symm.trans hdim
  have hmap : p.map (algebraMap R (Localization.AtPrime m)) =
      J.map (algebraMap (MvPolynomial (Fin n) R) (Localization.AtPrime m)) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R)]
    rfl
  have : IsLocalization.AtPrime (R ⧸ p) (IsLocalRing.maximalIdeal (R ⧸ p)) :=
    isLocalization_maximalIdeal_self (R ⧸ p)
  have hbase := IsLocalization.AtPrime.ringKrullDim_eq_height
    (IsLocalRing.maximalIdeal (R ⧸ p)) (R ⧸ p)
  rw [hmap, IsLocalization.AtPrime.ringKrullDim_eq_height Q
    (Localization.AtPrime m ⧸ J.map (algebraMap (MvPolynomial (Fin n) R)
      (Localization.AtPrime m))), hheight, WithBot.coe_add, ← hbase]
  simp

private theorem equidimensional_localization_mvPolynomial
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Equidimensional (PrimeSpectrum R)) (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal]
    [m.LiesOver (IsLocalRing.maximalIdeal R)] :
    Equidimensional (PrimeSpectrum (Localization.AtPrime m)) := by
  apply specEquidimensional_iff_equidimensional.mp
  intro q hq q' hq'
  obtain ⟨p, hp, rfl⟩ := exists_minimalPrimes_map_mvPolynomial_localization (Fin n) m q hq
  obtain ⟨p', hp', rfl⟩ := exists_minimalPrimes_map_mvPolynomial_localization (Fin n) m q' hq'
  have : p.IsPrime := hp.1.1
  have : p'.IsPrime := hp'.1.1
  rw [ringKrullDim_localization_mvPolynomial_quotient,
    ringKrullDim_localization_mvPolynomial_quotient,
    specEquidimensional_iff_equidimensional.mpr hR p hp p' hp']

/-! ### Descending catenarity along the completion -/

attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem flat_mvPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (ι : Type*) :
    (MvPolynomial.map (algebraMap R S) : MvPolynomial ι R →+* MvPolynomial ι S).Flat := by
  have e : MvPolynomial ι R ⊗[R] S ≃ₗ[MvPolynomial ι R] MvPolynomial ι S :=
    (Algebra.IsPushout.out (R := R) (S := MvPolynomial ι R) (R' := S)
      (S' := MvPolynomial ι S)).equiv
  have : Module.Flat (MvPolynomial ι R) (MvPolynomial ι S) :=
    Module.Flat.of_linearEquiv e.symm
  rw [← MvPolynomial.algebraMap_def, RingHom.flat_algebraMap_iff]
  infer_instance

private theorem isCatenary_localization_mvPolynomial_of_flat
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra A B] [Module.Flat A B]
    (hB : Ring.IsUniversallyCatenary B) (hequi : Equidimensional (PrimeSpectrum B))
    (n : ℕ) (m : Ideal (MvPolynomial (Fin n) A)) [m.IsPrime]
    (m' : Ideal (MvPolynomial (Fin n) B)) [m'.IsMaximal]
    [m'.LiesOver (IsLocalRing.maximalIdeal B)]
    (hm : m = m'.comap (MvPolynomial.map (algebraMap A B))) :
    Ring.IsCatenary (Localization.AtPrime m) := by
  let f := Localization.localRingHom m m' (MvPolynomial.map (algebraMap A B)) hm
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime m') := f.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime m) (Localization.AtPrime m')) :=
    Localization.isLocalHom_localRingHom m m' (MvPolynomial.map (algebraMap A B)) hm
  have : Module.Flat (Localization.AtPrime m) (Localization.AtPrime m') :=
    (flat_mvPolynomial_map (R := A) (S := B) (Fin n)).localRingHom m' m hm
  apply isCatenary_of_isCatenarySpace
  exact (specEquidimensional_quotients_and_isCatenary_of_flat_local
    (Localization.AtPrime m) (Localization.AtPrime m')
    (isCatenarySpace_of_isCatenary
      (isCatenary_of_isLocalizationAtPrime m' (hB (MvPolynomial (Fin n) B))))
    (equidimensional_localization_mvPolynomial hequi n m')).2.1

private theorem exists_isMaximal_mvPolynomial_comap_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hf : Function.Bijective (IsLocalRing.ResidueField.map f))
    (ι : Type*) (m : Ideal (MvPolynomial ι A)) [m.IsMaximal]
    (hm : m.comap MvPolynomial.C = IsLocalRing.maximalIdeal A) :
    ∃ m' : Ideal (MvPolynomial ι B), m'.IsMaximal ∧
      m'.comap MvPolynomial.C = IsLocalRing.maximalIdeal B ∧
      m'.comap (MvPolynomial.map f) = m := by
  let _ : Field (MvPolynomial ι A ⧸ m) := Ideal.Quotient.field m
  let k : IsLocalRing.ResidueField A →+* (MvPolynomial ι A ⧸ m) :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A)
      ((Ideal.Quotient.mk m).comp MvPolynomial.C) (by
        intro a ha
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change a ∈ m.comap MvPolynomial.C
        rwa [hm])
  let e := RingEquiv.ofBijective (IsLocalRing.ResidueField.map f) hf
  let c : B →+* (MvPolynomial ι A ⧸ m) :=
    k.comp (e.symm.toRingHom.comp (IsLocalRing.residue B))
  have hc (a : A) : c (f a) = Ideal.Quotient.mk m (MvPolynomial.C a) := by
    change k (e.symm (IsLocalRing.residue B (f a))) = _
    rw [← IsLocalRing.ResidueField.map_residue f]
    change k (e.symm (e (IsLocalRing.residue A a))) = _
    rw [e.symm_apply_apply]
    rfl
  let g : MvPolynomial ι B →+* (MvPolynomial ι A ⧸ m) :=
    MvPolynomial.eval₂Hom c (fun i => Ideal.Quotient.mk m (MvPolynomial.X i))
  have hg : g.comp (MvPolynomial.map f) = Ideal.Quotient.mk m := by
    ext a
    · simpa [g] using hc a
    · simp [g]
  have hgsurj : Function.Surjective g := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨MvPolynomial.map f p, RingHom.congr_fun hg p⟩
  refine ⟨RingHom.ker g, RingHom.ker_isMaximal_of_surjective g hgsurj, ?_, ?_⟩
  · ext b
    change g (MvPolynomial.C b) = 0 ↔ b ∈ IsLocalRing.maximalIdeal B
    simp only [g, MvPolynomial.eval₂Hom_C]
    change k (e.symm (IsLocalRing.residue B b)) = 0 ↔ _
    rw [map_eq_zero_iff k k.injective, map_eq_zero_iff e.symm e.symm.injective]
    exact Ideal.Quotient.eq_zero_iff_mem
  · ext p
    change g (MvPolynomial.map f p) = 0 ↔ p ∈ m
    rw [show g (MvPolynomial.map f p) = Ideal.Quotient.mk m p from RingHom.congr_fun hg p]
    exact Ideal.Quotient.eq_zero_iff_mem

private theorem isUniversallyCatenary_of_mvPolynomial
    (A : Type u) [CommRing A]
    (hA : ∀ n : ℕ, Ring.IsCatenary (MvPolynomial (Fin n) A)) :
    Ring.IsUniversallyCatenary A := by
  intro C _ _ _
  obtain ⟨n, f, hf⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A C›
  exact Ring.IsCatenary.of_surjective (f := f.toRingHom) hf (hA n)

@[ega "IV 7.1.11" "clause (i), special case",
  ega "IV 7.1.3" "(i), special case",
  ega "IV 7.1.4" "Clause (i)"]
private theorem isUniversallyCatenary_of_equidimensional_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hequi : Equidimensional
      (PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    Ring.IsUniversallyCatenary A := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  apply isUniversallyCatenary_of_mvPolynomial
  intro n
  apply isCatenary_of_forall_localizationAtPrime
  intro p hp
  obtain ⟨n', m, hm, hmover, g, _, hg⟩ := exists_isLocalizationOfQuotientMap_mvPolynomial_atMaximal
    A (Localization.AtPrime p)
  obtain ⟨m', hm', hm'over, hm'comap⟩ := exists_isMaximal_mvPolynomial_comap_eq
    (algebraMap A B) (AdicCompletion.residueField_map_bijective A) (Fin n') m hmover
  have : m'.LiesOver (IsLocalRing.maximalIdeal B) := ⟨hm'over.symm⟩
  have hcat : Ring.IsCatenary (Localization.AtPrime m) :=
    isCatenary_localization_mvPolynomial_of_flat
      (isUniversallyCatenary_of_isAdicComplete B) hequi n' m m' hm'comap.symm
  obtain ⟨I, f, T, _, hf⟩ := hg
  let : Algebra (Localization.AtPrime m ⧸ I) (Localization.AtPrime p) := f.toAlgebra
  have : IsLocalization T (Localization.AtPrime p) := hf
  exact ringIsCatenary_of_isLocalization T
    (Ring.IsCatenary.of_surjective (Ideal.Quotient.mk_surjective (I := I)) hcat)

/-- **Stacks 0AW5.** A formally catenary Noetherian local ring is universally catenary. -/
@[stacks 0AW5, ega "IV 7.1.11" "(i)"]
theorem isUniversallyCatenary_of_isFormallyCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsFormallyCatenary A) : Ring.IsUniversallyCatenary A := by
  apply isUniversallyCatenary_of_quotient_minimalPrimes
  intro p hp
  have : p.IsPrime := hp.1.1
  exact isUniversallyCatenary_of_equidimensional_adicCompletion (A ⧸ p)
    (equidimensional_adicCompletion_quotient_of_isFormallyCatenary A hA p hp)

end FormallyCatenaryIsUniversallyCatenary

section UniversalCatenarityImpliesFormalCatenarity

open IsLocalRing

/-! ### Reduction to a local domain with a nonequidimensional completion -/

private theorem exists_domain_not_equidimensional_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ¬ IsFormallyCatenary A) (huc : Ring.IsUniversallyCatenary A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
      (_ : IsDomain B), Ring.IsUniversallyCatenary B ∧
      ¬ TopologicalSpace.Equidimensional (PrimeSpectrum (AdicCompletion (maximalIdeal B) B)) := by
  classical
  simp only [IsFormallyCatenary, not_forall] at hA
  obtain ⟨p, hp, hbad⟩ := hA
  have : p.IsPrime := hp.1.1
  refine ⟨A ⧸ p, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective huc
  · exact fun hequi => hbad ((equidimensional_adicCompletion_quotient_iff A p).mp hequi)

/-- The kernel of the map from `R` to a quotient `S ⧸ q` is the preimage of `q`. -/
private theorem ker_algebraMap_quotient {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) : RingHom.ker (algebraMap R (S ⧸ q)) = q.comap (algebraMap R S) := by
  rw [IsScalarTower.algebraMap_eq R S (S ⧸ q), ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq,
    Ideal.mk_ker]

private theorem comap_eq_bot_of_mem_minimalPrimes_of_hasGoingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Algebra.HasGoingDown R S]
    (p : Ideal S) (hp : p ∈ minimalPrimes S) :
    p.comap (algebraMap R S) = ⊥ := by
  have : p.IsPrime := hp.1.1
  have : p.LiesOver (p.under R) := ⟨rfl⟩
  obtain ⟨q, hqp, hq, hqbot⟩ :=
    p.exists_ideal_le_liesOver_of_le (p := ⊥) (q := p.under R) bot_le
  have heq : q = p := le_antisymm hqp (hp.2 ⟨hq, bot_le⟩ hqp)
  subst q
  exact hqbot.over.symm

private theorem algebraMap_quotient_injective_of_mem_minimalPrimes
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Algebra.HasGoingDown R S]
    (p : Ideal S) (hp : p ∈ minimalPrimes S) :
    Function.Injective (algebraMap R (S ⧸ p)) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [ker_algebraMap_quotient]
  exact comap_eq_bot_of_mem_minimalPrimes_of_hasGoingDown p hp

private theorem ringKrullDim_quotient_pow
    {R : Type*} [CommRing R] (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    ringKrullDim (R ⧸ I ^ n) = ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_pow I hn]

@[ega "IV 5.1.1"]
private theorem equidimensional_iff_ringKrullDim_quotient_minimalPrimes
    {R : Type*} [CommRing R] :
    TopologicalSpace.Equidimensional (PrimeSpectrum R) ↔
      ∀ p ∈ minimalPrimes R, ∀ q ∈ minimalPrimes R,
        ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸ q) :=
  specEquidimensional_iff_equidimensional.symm

/-! ### Dimensions of the components of a spectrum -/

/-- In a nonequidimensional Noetherian local spectrum, a component of smallest dimension
has positive dimension strictly less than that of the whole spectrum. -/
private theorem exists_minimalPrime_ringKrullDim_quotient_min
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ¬ TopologicalSpace.Equidimensional (PrimeSpectrum R)) :
    ∃ p ∈ minimalPrimes R, ∃ d : ℕ,
      0 < d ∧ ringKrullDim (R ⧸ p) = d ∧ (d : WithBot ℕ∞) < ringKrullDim R ∧
        ∀ q ∈ minimalPrimes R, (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := by
  classical
  have : Nonempty (minimalPrimes R) := Ideal.nonempty_minimalPrimes bot_ne_top
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  obtain ⟨p, hmin⟩ := Finite.exists_min (fun p : minimalPrimes R => ringKrullDim (R ⧸ p.val))
  obtain ⟨q, hpq⟩ : ∃ q : minimalPrimes R,
      ringKrullDim (R ⧸ p.val) < ringKrullDim (R ⧸ q.val) := by
    by_contra! h
    apply hR
    apply equidimensional_iff_ringKrullDim_quotient_minimalPrimes.mpr
    intro a ha b hb
    exact (le_antisymm (hmin ⟨a, ha⟩) (h ⟨a, ha⟩)).symm.trans
      (le_antisymm (hmin ⟨b, hb⟩) (h ⟨b, hb⟩))
  have : p.val.IsPrime := p.property.1.1
  have : q.val.IsPrime := q.property.1.1
  let P : PrimeSpectrum R := ⟨p.val, inferInstance⟩
  have hP : IsMin P := PrimeSpectrum.isMin_iff.mpr p.property
  have hne : P ≠ ⊤ := by
    intro heq
    have hqp : (⟨q.val, inferInstance⟩ : PrimeSpectrum R) = P :=
      hP.eq_of_le (heq ▸ le_top)
    have heq' : q.val = p.val := congrArg PrimeSpectrum.asIdeal hqp
    rw [heq'] at hpq
    exact (lt_irrefl _) hpq
  have hfinite : Order.coheight P ≠ ⊤ := (Order.coheight_lt_top P).ne
  let d := (Order.coheight P).toNat
  have hd : (d : ℕ∞) = Order.coheight P := ENat.natCast_toNat hfinite
  have hdim : ringKrullDim (R ⧸ p.val) = d :=
    (coheight_eq_ringKrullDim_quotient P).symm.trans
      (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hd.symm)
  refine ⟨p.val, p.property, d, ?_, hdim, ?_, ?_⟩
  · have hpos := Order.coheight_pos_of_lt_top (lt_top_iff_ne_top.mpr hne)
    rw [← hd] at hpos
    exact_mod_cast hpos
  · rw [← hdim]
    exact hpq.trans_le (ringKrullDim_quotient_le q.val)
  · intro q hq
    rw [← hdim]
    exact hmin ⟨q, hq⟩

private theorem exists_minimalPrime_adicCompletion_ringKrullDim_quotient_min
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ¬ TopologicalSpace.Equidimensional
      (PrimeSpectrum (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    ∃ p ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A), ∃ d : ℕ,
      0 < d ∧ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p) = d ∧
        (d : WithBot ℕ∞) < ringKrullDim A ∧
        ∀ q ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A),
          (d : WithBot ℕ∞) ≤
            ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ q) := by
  rw [_root_.ringKrullDim_adicCompletion_maximalIdeal]
  exact exists_minimalPrime_ringKrullDim_quotient_min _ hA

/-! ### Algebraizing a one-dimensional component of the completion -/

private theorem exists_pow_map_eq_bot_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R)
    (hp : p ∈ minimalPrimes R) :
    ∃ n : ℕ, 0 < n ∧
      (p ^ n).map (algebraMap R (Localization.AtPrime p (hp := hp.1.1))) = ⊥ := by
  have : p.IsPrime := hp.1.1
  let S := Localization.AtPrime p
  have hr := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := S) p ⊥ hp
  simp only [Ideal.map_bot] at hr
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical S
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [Ideal.map_pow, ← hr, pow_succ]
  change nilradical S ^ n * nilradical S = ⊥
  rw [hn, zero_mul]
  rfl

private theorem cotangent_notMem_support_of_map_eq_bot
    {R : Type*} [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : J.map (algebraMap R (Localization.AtPrime p)) = ⊥) :
    (⟨p, inferInstance⟩ : PrimeSpectrum R) ∉ Module.support R J.Cotangent := by
  apply Module.notMem_support_iff'.mpr
  intro x
  obtain ⟨y, rfl⟩ := J.toCotangent_surjective x
  have hy : algebraMap R (Localization.AtPrime p) y = 0 := by
    have h := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) y.property
    rwa [hJ, Ideal.mem_bot] at h
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) y).mp hy
  refine ⟨s, s.property, ?_⟩
  rw [← map_smul]
  have hzero : (s.val • y : J) = 0 := Subtype.ext hs
  rw [hzero, map_zero]

private theorem exists_pow_smul_eq_bot_of_support_subset_singleton
    {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (hm : (IsLocalRing.maximalIdeal R).FG)
    (hM : Module.support R M ⊆ {(⊤ : PrimeSpectrum R)}) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥ := by
  have hle : IsLocalRing.maximalIdeal R ≤ (Module.annihilator R M).radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro p ⟨hle, hp⟩
    have hmem : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr hle
    have htop := hM hmem
    change (⟨p, hp⟩ : PrimeSpectrum R) = ⊤ at htop
    have heq := congrArg PrimeSpectrum.asIdeal htop
    exact heq.ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle hm
  refine ⟨n, Submodule.le_annihilator_iff.mp ?_⟩
  simpa only [Submodule.annihilator_top] using hn

/-- A suitable power of a one-dimensional minimal prime has conormal module supported
only at the closed point. -/
private theorem exists_pow_cotangent_smul_eq_bot_of_mem_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (hdim : ringKrullDim (R ⧸ p) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ,
      IsLocalRing.maximalIdeal R ^ c • (⊤ : Submodule R (p ^ n).Cotangent) = ⊥ := by
  have : p.IsPrime := hp.1.1
  obtain ⟨n, hn, hmap⟩ := exists_pow_map_eq_bot_of_mem_minimalPrimes p hp
  have : Module.Finite R ↥(p ^ n) := Module.Finite.of_fg (IsNoetherian.noetherian _)
  have : Module.Finite R (p ^ n).Cotangent :=
    Module.Finite.of_surjective (p ^ n).toCotangent (p ^ n).toCotangent_surjective
  refine ⟨n, hn, exists_pow_smul_eq_bot_of_support_subset_singleton
    (IsNoetherian.noetherian _) ?_⟩
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hnot := cotangent_notMem_support_of_map_eq_bot p (p ^ n) hmap
  have hco : Order.coheight P = 1 := by
    apply WithBot.coe_injective
    exact (coheight_eq_ringKrullDim_quotient ⟨p, inferInstance⟩).trans hdim
  intro Q hQ
  have hle : p ≤ Q.asIdeal := by
    intro x hx
    apply Q.isPrime.mem_of_pow_mem n
    apply Module.annihilator_le_of_mem_support hQ
    apply Module.mem_annihilator.mpr
    exact fun y => Ideal.Cotangent.smul_eq_zero_of_mem (Ideal.pow_mem_pow hx n) y
  have hlt : P < Q := lt_of_le_of_ne hle (by
    intro heq
    apply hnot
    change P ∈ Module.support R (p ^ n).Cotangent
    rw [heq]
    exact hQ)
  have h := Order.coheight_add_one_le hlt
  rw [hco] at h
  have hz : Order.coheight Q ≤ 0 :=
    (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (by simpa using h)
  exact Set.mem_singleton_iff.mpr
    (isMax_iff_eq_top.mp (Order.coheight_eq_zero.mp (le_antisymm hz bot_le)))

private theorem exists_finiteType_algEquiv_adicCompletion_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (J : Ideal (AdicCompletion I A)) (c : ℕ)
    (hJ : I ^ c • (⊤ : Submodule A J.Cotangent) = ⊥) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.FiniteType A B ∧
        Nonempty ((AdicCompletion I A ⧸ J) ≃ₐ[A]
          AdicCompletion (I.map (algebraMap A B)) B) := by
  have aux (K : Ideal A) (hK : I.map (algebraMap A A) = K)
      (J : Ideal (AdicCompletion K A)) (c : ℕ)
      (hJ : I ^ c • (⊤ : Submodule A J.Cotangent) = ⊥) :
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Algebra.FiniteType A B ∧ Nonempty ((AdicCompletion K A ⧸ J) ≃ₐ[A]
          AdicCompletion (I.map (algebraMap A B)) B) := by
    subst K
    apply exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated
      A A _ I (Ideal.Quotient.mkₐ A J) (Ideal.Quotient.mkₐ_surjective A J) c
    exact Eq.mpr (congrArg (fun L : Ideal (AdicCompletion (I.map (algebraMap A A)) A) =>
      I ^ c • (⊤ : Submodule A L.Cotangent) = ⊥) (Ideal.Quotient.mkₐ_ker A J)) hJ
  exact aux I (by simp) J c hJ

private theorem exists_finiteType_algEquiv_adicCompletion_quotient_pow
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hp : p ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hdim : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p) = 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Algebra.FiniteType A B ∧
        Nonempty ((AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p ^ n) ≃ₐ[A]
          AdicCompletion ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) B) := by
  obtain ⟨n, hn, c, hc⟩ := exists_pow_cotangent_smul_eq_bot_of_mem_minimalPrimes p hp hdim
  refine ⟨n, hn, exists_finiteType_algEquiv_adicCompletion_quotient
    A (IsLocalRing.maximalIdeal A) (p ^ n) c ?_⟩
  have h := congrArg (Submodule.restrictScalars A) hc
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.smul_restrictScalars] at h
  simpa only [Submodule.restrictScalars_top, Submodule.restrictScalars_bot] using h

/-! ### Cutting a deficient component down to dimension one -/

/-- The quotient of `R` by the preimage of an ideal `Q` of `R ⧸ I` has the dimension of the
quotient of `R ⧸ I` by `Q`. -/
private theorem ringKrullDim_quotient_comap_mk {R : Type*} [CommRing R] (I : Ideal R)
    (Q : Ideal (R ⧸ I)) :
    ringKrullDim (R ⧸ Q.comap (Ideal.Quotient.mk I)) = ringKrullDim ((R ⧸ I) ⧸ Q) := by
  rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE
    (Ideal.mk_ker.ge.trans (Ideal.ker_le_comap _) : I ≤ Q.comap (Ideal.Quotient.mk I))),
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- A finite-dimensional ring has an irreducible component of full dimension. -/
public theorem exists_mem_minimalPrimes_ringKrullDim_quotient_eq
    (R : Type*) [CommRing R] [Nontrivial R] [FiniteRingKrullDim R] :
    ∃ p ∈ minimalPrimes R, ringKrullDim (R ⧸ p) = ringKrullDim R := by
  let c := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨p, hp, hpc⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := c.head.asIdeal) bot_le
  have : p.IsPrime := hp.1.1
  refine ⟨p, hp, le_antisymm (ringKrullDim_quotient_le p) ?_⟩
  rw [← coheight_eq_ringKrullDim_quotient (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R)]
  change Order.krullDim (PrimeSpectrum R) ≤ _
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
  exact WithBot.coe_le_coe.mpr ((Order.length_le_coheight_head (p := c)).trans
    (Order.coheight_anti hpc))

/-- A finite family of nonclosed primes can be avoided by an element of the maximal
ideal when the closed fibre is a point. -/
private theorem exists_mem_maximalIdeal_notMem_primes
    {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [Algebra A R] (hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (s : Set (Ideal R)) (hs : s.Finite)
    (hp : ∀ p ∈ s, p.IsPrime) (hne : ∀ p ∈ s, p ≠ maximalIdeal R) :
    ∃ f ∈ maximalIdeal A, ∀ p ∈ s, algebraMap A R f ∉ p := by
  classical
  by_contra! h
  have hcover : (maximalIdeal A : Set A) ⊆
      ⋃ p ∈ s, (p.comap (algebraMap A R) : Set A) := by
    intro f hf
    obtain ⟨p, hps, hfp⟩ := h f hf
    exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hps, hfp⟩⟩
  obtain ⟨p, hps, hle⟩ :=
    (Ideal.subset_union_prime_finite hs (⊥ : Ideal R) ⊥
      (fun p hp' _ _ => by
        have : p.IsPrime := hp p hp'
        exact Ideal.comap_isPrime (algebraMap A R) p)).mp hcover
  have hmp : maximalIdeal R ≤ p := by
    rw [← hm]
    exact Ideal.map_le_iff_le_comap.mpr hle
  have : p.IsPrime := hp p hps
  exact hne p hps (le_antisymm (le_maximalIdeal (hp p hps).ne_top) hmp)

/-- A prime minimal over a principal extension of a prime covers that prime. -/
private theorem covBy_of_mem_minimalPrimes_sup_span
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) [p.IsPrime] {f : R} (hf : f ∉ p)
    (hq : q ∈ (p ⊔ Ideal.span {f}).minimalPrimes) :
    (⟨p, inferInstance⟩ : PrimeSpectrum R) ⋖ ⟨q, hq.isPrime⟩ := by
  have hpq : p ≤ q := le_sup_left.trans hq.le
  have hlt : p < q := lt_of_le_of_ne hpq (by
    intro heq
    exact hf (heq ▸ hq.le
      ((show Ideal.span {f} ≤ p ⊔ Ideal.span {f} from le_sup_right)
        (Ideal.mem_span_singleton_self f))))
  refine ⟨hlt, ?_⟩
  intro t hpt htq
  let e := p.primeSpectrumQuotientOrderIsoZeroLocus.symm
  let P : PrimeSpectrum (R ⧸ p) := e ⟨⟨p, inferInstance⟩, by exact (le_rfl : p ≤ p)⟩
  let T : PrimeSpectrum (R ⧸ p) := e ⟨t, hpt.le⟩
  let Q : PrimeSpectrum (R ⧸ p) := e ⟨⟨q, hq.isPrime⟩, hpq⟩
  have hPQ : 1 < Order.height Q := Order.one_lt_height_iff.mpr
    ⟨T, P, e.strictMono hpt, e.strictMono htq⟩
  have hQ : Q.asIdeal = q.map (Ideal.Quotient.mk p) := rfl
  have hle : Order.height Q ≤ 1 := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hQ]
    exact Ideal.map_height_le_one_of_mem_minimalPrimes hq
  exact (not_lt_of_ge hle) hPQ

/-- Avoiding the intersections with the other components makes every nonclosed
component of the principal section a component of the section of the whole spectrum. -/
private theorem mem_minimalPrimes_span_of_avoid_intersections
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) {f : R} (hf : f ∉ p)
    (havoid : ∀ r ∈ minimalPrimes R, r ≠ p →
      ∀ t ∈ (p ⊔ r).minimalPrimes, t ≠ maximalIdeal R → f ∉ t)
    (q : Ideal R) (hq : q ∈ (p ⊔ Ideal.span {f}).minimalPrimes)
    (hqne : q ≠ maximalIdeal R) : q ∈ (Ideal.span {f}).minimalPrimes := by
  have : p.IsPrime := hp.isPrime
  have : q.IsPrime := hq.isPrime
  have hpq : p ≤ q := le_sup_left.trans hq.le
  have hcov := covBy_of_mem_minimalPrimes_sup_span p q hf hq
  have huniq (r : Ideal R) (hr : r ∈ minimalPrimes R) (hrq : r ≤ q) : r = p := by
    by_contra hrne
    obtain ⟨t, ht, htq⟩ := Ideal.exists_minimalPrimes_le (sup_le hpq hrq)
    have : t.IsPrime := ht.isPrime
    have hpt : p < t := lt_of_le_of_ne (le_sup_left.trans ht.le) (by
      intro hpt
      have hrp : r ≤ p := hpt ▸ le_sup_right.trans ht.le
      exact hrne (le_antisymm hrp (hp.2 ⟨hr.isPrime, bot_le⟩ hrp)))
    have htqeq : t = q := by
      apply le_antisymm htq
      by_contra hn
      exact hcov.2 (c := (⟨t, inferInstance⟩ : PrimeSpectrum R)) hpt (lt_of_le_not_ge htq hn)
    exact havoid r hr hrne t ht (htqeq ▸ hqne)
      (htqeq ▸ hq.le
        ((show Ideal.span {f} ≤ p ⊔ Ideal.span {f} from le_sup_right)
          (Ideal.mem_span_singleton_self f)))
  refine ⟨⟨hq.isPrime, le_sup_right.trans hq.le⟩, ?_⟩
  intro t ht htq
  have : t.IsPrime := ht.1
  obtain ⟨r, hr, hrt⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := t) bot_le
  have hrp := huniq r hr (hrt.trans htq)
  subst r
  exact hq.2 ⟨ht.1, sup_le hrt ht.2⟩ htq

/-- A principal section of an irreducible component has a component whose dimension
is one less. -/
private theorem exists_minimalPrimes_sup_span_ringKrullDim
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime] {f : R} (hf : f ∉ p) (hfm : f ∈ maximalIdeal R) :
    ∃ q ∈ (p ⊔ Ideal.span {f}).minimalPrimes,
      ringKrullDim (R ⧸ q) + 1 = ringKrullDim (R ⧸ p) := by
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hf0 : Ideal.Quotient.mk p f ≠ 0 := by
    intro h
    exact hf (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hfmax : Ideal.Quotient.mk p f ∈ maximalIdeal (R ⧸ p) :=
    by
    change f ∈ (maximalIdeal (R ⧸ p)).comap (Ideal.Quotient.mk p)
    rwa [IsLocalRing.maximalIdeal_comap]
  have hdim := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (show Ideal.Quotient.mk p f ∈ nonZeroDivisors (R ⧸ p) by simpa using hf0) hfmax
  have hmap : (Ideal.span {f}).map (Ideal.Quotient.mk p) =
      Ideal.span {Ideal.Quotient.mk p f} := by rw [Ideal.map_span, Set.image_singleton]
  rw [← hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {f}))]
    at hdim
  let I := p ⊔ Ideal.span {f}
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    (sup_le (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨q, hq, hqdim⟩ := exists_mem_minimalPrimes_ringKrullDim_quotient_eq (R ⧸ I)
  let Q := q.comap (Ideal.Quotient.mk I)
  have hQ : Q ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q, hq, rfl⟩
  refine ⟨Q, hQ, ?_⟩
  rw [ringKrullDim_quotient_comap_mk, hqdim]
  exact hdim

/-- Over a local map with point closed fibre, a component of dimension at least two
admits a principal section which remains a component of the whole section. -/
private theorem exists_mem_maximalIdeal_minimalPrimes_span_ringKrullDim
    {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing A] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra A R]
    (hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (hdim : 1 < ringKrullDim (R ⧸ p)) :
    ∃ f ∈ maximalIdeal A, algebraMap A R f ∉ p ∧
      ∃ q ∈ (Ideal.span {algebraMap A R f}).minimalPrimes,
        ringKrullDim (R ⧸ q) + 1 = ringKrullDim (R ⧸ p) := by
  classical
  have : p.IsPrime := hp.isPrime
  let s : Set (Ideal R) := {p} ∪
    ((⋃ r ∈ minimalPrimes R, (p ⊔ r).minimalPrimes) \ {maximalIdeal R})
  have hs : s.Finite := Set.finite_singleton p |>.union <|
    ((minimalPrimes.finite_of_isNoetherianRing R).biUnion fun r _ =>
      Ideal.finite_minimalPrimes_of_isNoetherianRing R (p ⊔ r)).sdiff
  have hz (r : Ideal R) (hr : r = maximalIdeal R) : ringKrullDim (R ⧸ r) = 0 := by
    have : r.IsMaximal := hr ▸ maximalIdeal.isMaximal R
    exact ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp ‹_›)
  have hpne : p ≠ maximalIdeal R := by
    intro heq
    rw [hz p heq] at hdim
    norm_num at hdim
  have hsprime : ∀ q ∈ s, q.IsPrime := by
    rintro q (hq | ⟨hq, _⟩)
    · simpa only [Set.mem_singleton_iff.mp hq] using hp.isPrime
    · obtain ⟨r, hr, hqr⟩ := Set.mem_iUnion₂.mp hq
      exact hqr.isPrime
  have hsne : ∀ q ∈ s, q ≠ maximalIdeal R := by
    rintro q (hq | ⟨_, hq⟩)
    · exact Set.mem_singleton_iff.mp hq ▸ hpne
    · exact hq
  obtain ⟨f, hfm, hf⟩ := exists_mem_maximalIdeal_notMem_primes hm s hs hsprime hsne
  have hfp : algebraMap A R f ∉ p := hf p (Or.inl rfl)
  have hfmax : algebraMap A R f ∈ maximalIdeal R :=
    hm ▸ Ideal.mem_map_of_mem (algebraMap A R) hfm
  obtain ⟨q, hq, hqdim⟩ := exists_minimalPrimes_sup_span_ringKrullDim p hfp hfmax
  have hqne : q ≠ maximalIdeal R := by
    intro heq
    rw [hz q heq, zero_add] at hqdim
    exact (ne_of_lt hdim) hqdim
  refine ⟨f, hfm, hfp, q, ?_, hqdim⟩
  apply mem_minimalPrimes_span_of_avoid_intersections p hp hfp _ q hq hqne
  intro r hr _ t ht htne
  exact hf t (Or.inr ⟨Set.mem_iUnion₂.mpr ⟨r, hr, ht⟩, htne⟩)

@[ega "IV 5.1.1" "5.1.1.5"]
private theorem ringKrullDim_quotient_minimalPrime_eq_of_equidimensional
    {R : Type*} [CommRing R] [Nontrivial R] [FiniteRingKrullDim R]
    (hR : TopologicalSpace.Equidimensional (PrimeSpectrum R))
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  obtain ⟨q, hq, hdim⟩ := exists_mem_minimalPrimes_ringKrullDim_quotient_eq R
  exact (equidimensional_iff_ringKrullDim_quotient_minimalPrimes.mp hR p hp q hq).trans hdim

/-- For an equidimensional local ring, formal catenarity makes the completion
itself equidimensional. -/
private theorem equidimensional_adicCompletion_of_isFormallyCatenary
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsFormallyCatenary A)
    (hequi : TopologicalSpace.Equidimensional (PrimeSpectrum A)) :
    TopologicalSpace.Equidimensional (PrimeSpectrum (AdicCompletion (maximalIdeal A) A)) := by
  let C := AdicCompletion (maximalIdeal A) A
  suffices h : ∀ q ∈ minimalPrimes C, ringKrullDim (C ⧸ q) = ringKrullDim A by
    exact equidimensional_iff_ringKrullDim_quotient_minimalPrimes.mpr
      (fun q hq r hr => (h q hq).trans (h r hr).symm)
  intro q hq
  have : q.IsPrime := hq.isPrime
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (I := ⊥) (J := q.comap (algebraMap A C)) bot_le
  have : p.IsPrime := hp.isPrime
  let I := p.map (algebraMap A C)
  have hIq : I ≤ q := Ideal.map_le_iff_le_comap.mpr hpq
  have hqI : q ∈ I.minimalPrimes :=
    ⟨⟨hq.isPrime, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, bot_le⟩ hrq⟩
  have : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹_›) hIq)
  obtain ⟨Q, hQ, heq⟩ := (Ideal.minimalPrimes_eq_comap (I := I) ▸ hqI)
  have hdim : ringKrullDim (C ⧸ q) = ringKrullDim (C ⧸ I) := by
    rw [← heq, ringKrullDim_quotient_comap_mk]
    exact ringKrullDim_quotient_minimalPrime_eq_of_equidimensional (hA p hp) Q hQ
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_adicCompletion A p
  calc
    ringKrullDim (C ⧸ q) = ringKrullDim (C ⧸ I) := hdim
    _ = ringKrullDim (AdicCompletion (maximalIdeal (A ⧸ p)) (A ⧸ p)) :=
      ringKrullDim_eq_of_ringEquiv e
    _ = ringKrullDim (A ⧸ p) := _root_.ringKrullDim_adicCompletion_maximalIdeal.symm
    _ = ringKrullDim A := ringKrullDim_quotient_minimalPrime_eq_of_equidimensional hequi p hp

/-- In a catenary local domain all components of a nonzero principal section
have codimension one. -/
private theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes_span
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {f : R} (hf : f ≠ 0)
    (p : Ideal R) (hp : p ∈ (Ideal.span {f}).minimalPrimes) :
    ringKrullDim (R ⧸ p) + 1 = ringKrullDim R := by
  have hcov := covBy_of_mem_minimalPrimes_sup_span (⊥ : Ideal R) p
    (by simpa using hf) (by simpa using hp)
  have hstep := coheight_covby_of_catenary
    (_root_.isCatenaryRingSaturated_of_isCatenary hcat) (⊥ : PrimeSpectrum R)
      (⟨p, hp.isPrime⟩ : PrimeSpectrum R) hcov
  have hcast := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hstep
  rw [WithBot.coe_add, Order.coheight_bot_eq_krullDim,
    coheight_eq_ringKrullDim_quotient] at hcast
  exact hcast.symm

private theorem equidimensional_quotient_span_of_isCatenary
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {f : R} (hf : f ≠ 0) :
    TopologicalSpace.Equidimensional (PrimeSpectrum (R ⧸ Ideal.span {f})) := by
  let I := Ideal.span {f}
  have h (q : Ideal (R ⧸ I)) (hq : q ∈ minimalPrimes (R ⧸ I)) :
      ringKrullDim ((R ⧸ I) ⧸ q) + 1 = ringKrullDim R := by
    let Q := q.comap (Ideal.Quotient.mk I)
    have hQ : Q ∈ I.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]
      exact ⟨q, hq, rfl⟩
    rw [← ringKrullDim_quotient_comap_mk]
    exact ringKrullDim_quotient_add_one_of_mem_minimalPrimes_span hcat hf Q hQ
  exact equidimensional_iff_ringKrullDim_quotient_minimalPrimes.mpr
    (fun q hq r hr => ENat.WithBot.add_one_cancel.mp ((h q hq).trans (h r hr).symm))

/-- A deficient component of dimension greater than one gives a non-formally-catenary
principal quotient of a catenary local domain. -/
private theorem exists_not_isFormallyCatenary_quotient_span
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hcat : Ring.IsCatenary A)
    (p : Ideal (AdicCompletion (maximalIdeal A) A))
    (hp : p ∈ minimalPrimes (AdicCompletion (maximalIdeal A) A))
    (hpdim : 1 < ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p))
    (hlt : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p) < ringKrullDim A) :
    ∃ f ∈ maximalIdeal A, f ≠ 0 ∧ ∃ (_ : IsLocalRing (A ⧸ Ideal.span {f})),
      ¬ IsFormallyCatenary (A ⧸ Ideal.span {f}) := by
  let C := AdicCompletion (maximalIdeal A) A
  obtain ⟨f, hfm, hfp, q, hq, hqdim⟩ :=
    exists_mem_maximalIdeal_minimalPrimes_span_ringKrullDim
      (A := A) AdicCompletion.maximalIdeal_eq_map.symm p hp hpdim
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hfp (by simp)
  let I : Ideal A := Ideal.span {f}
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm))
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  refine ⟨f, hfm, hf0, inferInstance, ?_⟩
  intro hformal
  have hequi := equidimensional_adicCompletion_of_isFormallyCatenary (A ⧸ I) hformal
    (equidimensional_quotient_span_of_isCatenary hcat hf0)
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_adicCompletion A I
  let J := I.map (algebraMap A C)
  have hJ : J = Ideal.span {algebraMap A C f} := by
    dsimp [J, I]
    rw [Ideal.map_span, Set.image_singleton]
  have hqJ : q ∈ J.minimalPrimes := hJ ▸ hq
  have hCJ : TopologicalSpace.Equidimensional (PrimeSpectrum (C ⧸ J)) :=
    (equidimensional_adicCompletion_quotient_iff A I).mp hequi
  have : Nontrivial (C ⧸ J) := e.toMulEquiv.nontrivial
  obtain ⟨Q, hQ, heq⟩ := Ideal.minimalPrimes_eq_comap (I := J) ▸ hqJ
  have hdimq : ringKrullDim (C ⧸ q) = ringKrullDim (C ⧸ J) := by
    rw [← heq, ringKrullDim_quotient_comap_mk]
    exact ringKrullDim_quotient_minimalPrime_eq_of_equidimensional hCJ Q hQ
  have hdimquot : ringKrullDim (C ⧸ J) = ringKrullDim (A ⧸ I) :=
    (ringKrullDim_eq_of_ringEquiv e).trans
      _root_.ringKrullDim_adicCompletion_maximalIdeal.symm
  have hsum := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (show f ∈ nonZeroDivisors A by simpa using hf0) hfm
  rw [hdimq, hdimquot] at hqdim
  exact (ne_of_lt hlt) (hqdim.symm.trans hsum)

/-- A counterexample of least ambient dimension has a one-dimensional deficient
component in its completion. -/
private theorem exists_domain_minimalPrime_completion_dim_one
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ¬ IsFormallyCatenary A) (huc : Ring.IsUniversallyCatenary A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
      (_ : IsDomain B), Ring.IsUniversallyCatenary B ∧
      ∃ p ∈ minimalPrimes (AdicCompletion (maximalIdeal B) B),
        ringKrullDim (AdicCompletion (maximalIdeal B) B ⧸ p) = 1 ∧ 1 < ringKrullDim B := by
  classical
  let P (n : ℕ) : Prop :=
    ∃ (B : Type u) (_ : CommRing B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
      (_ : IsDomain B), Ring.IsUniversallyCatenary B ∧
      ¬ TopologicalSpace.Equidimensional (PrimeSpectrum (AdicCompletion (maximalIdeal B) B)) ∧
      ringKrullDim B = n
  have hex : ∃ n, P n := by
    obtain ⟨B, _, _, _, _, hB, hbad⟩ :=
      exists_domain_not_equidimensional_adicCompletion A hA huc
    exact ⟨(LTSeries.longestOf (PrimeSpectrum B)).length, B, inferInstance, inferInstance,
      inferInstance, inferInstance, hB, hbad, Order.krullDim_eq_length_of_finiteDimensionalOrder⟩
  obtain ⟨B, _, _, _, _, hB, hbad, hBdim⟩ := Nat.find_spec hex
  obtain ⟨p, hp, d, hdpos, hdim, hdlt, _⟩ :=
    exists_minimalPrime_adicCompletion_ringKrullDim_quotient_min B hbad
  by_cases hd : d = 1
  · subst d
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, hB, p, hp,
      by simpa using hdim, by simpa using hdlt⟩
  have hdgt : 1 < d := by omega
  obtain ⟨f, hfm, hf0, _, hf⟩ := exists_not_isFormallyCatenary_quotient_span B (hB B) p hp
    (by rw [hdim]; exact_mod_cast hdgt) (by rwa [hdim])
  have hquot : Ring.IsUniversallyCatenary (B ⧸ Ideal.span {f}) :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hB
  simp only [IsFormallyCatenary, not_forall] at hf
  obtain ⟨r, hr, hrf⟩ := hf
  have : r.IsPrime := hr.isPrime
  let E := (B ⧸ Ideal.span {f}) ⧸ r
  have : IsLocalRing E :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk r) Ideal.Quotient.mk_surjective
  have hE : Ring.IsUniversallyCatenary E :=
    Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective hquot
  have hEbad : ¬ TopologicalSpace.Equidimensional
      (PrimeSpectrum (AdicCompletion (maximalIdeal E) E)) := by
    intro hequi
    exact hrf ((equidimensional_adicCompletion_quotient_iff (B ⧸ Ideal.span {f}) r).mp hequi)
  let k := (LTSeries.longestOf (PrimeSpectrum E)).length
  have hk : ringKrullDim E = k := Order.krullDim_eq_length_of_finiteDimensionalOrder
  have hPk : P k := ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hE, hEbad, hk⟩
  have hmin := Nat.find_min' hex hPk
  have hsum := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (show f ∈ nonZeroDivisors B by simpa using hf0) hfm
  have hdimle : (k : WithBot ℕ∞) + 1 ≤ (Nat.find hex : WithBot ℕ∞) := by
    rw [← hk, ← hBdim, ← hsum]
    simpa only [add_comm] using add_le_add_right (ringKrullDim_quotient_le r) 1
  have : k + 1 ≤ Nat.find hex := by exact_mod_cast hdimle
  omega

/-! ### Heights along a dominant finite-type map -/

private theorem surjective_residue_comp_of_surjective
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra A R] [Algebra A S]
    (f : R →ₐ[A] S) (hf : Function.Surjective f)
    (hR : Function.Surjective ((residue R).comp (algebraMap A R))) :
    Function.Surjective ((residue S).comp (algebraMap A S)) := by
  have : IsLocalHom f.toRingHom := IsLocalHom.of_surjective _ hf
  intro x
  obtain ⟨s, rfl⟩ := residue_surjective x
  obtain ⟨r, rfl⟩ := hf s
  obtain ⟨a, ha⟩ := hR (residue R r)
  refine ⟨a, ?_⟩
  have h := congrArg (IsLocalRing.ResidueField.map f.toRingHom) ha
  simp only [IsLocalRing.ResidueField.map_residue] at h
  change residue S (f (algebraMap A R a)) = residue S (f r) at h
  rwa [f.commutes] at h

private theorem surjective_residue_comp_adicCompletion
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    Function.Surjective ((residue (AdicCompletion (maximalIdeal A) A)).comp
      (algebraMap A (AdicCompletion (maximalIdeal A) A))) := by
  rw [← IsLocalRing.ResidueField.map_comp_residue]
  exact (AdicCompletion.residueField_map_bijective A).surjective.comp residue_surjective

private theorem height_le_comap_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (q : Ideal S) [q.IsPrime] :
    q.height ≤ (q.comap f).height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum S),
    PrimeSpectrum.height_eq_orderHeight (⟨q.comap f, inferInstance⟩ : PrimeSpectrum R)]
  exact Order.height_le_height_apply_of_strictMono (PrimeSpectrum.comap f)
    (RingHom.strictMono_comap_of_surjective hf) _

/-- Algebraization produces a finite-type domain with a rational closed point of
height at most one and dominant structural map. -/
private theorem exists_finiteType_domain_prime_height_le_one
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (p : Ideal (AdicCompletion (maximalIdeal A) A))
    (hp : p ∈ minimalPrimes (AdicCompletion (maximalIdeal A) A))
    (hdim : ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸ p) = 1) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D) (_ : IsDomain D),
      Algebra.FiniteType A D ∧ Function.Injective (algebraMap A D) ∧
      ∃ q : Ideal D, q.IsMaximal ∧ q.height ≤ 1 ∧
        Function.Surjective (algebraMap A (D ⧸ q)) := by
  have : p.IsPrime := hp.isPrime
  obtain ⟨n, hn, B, _, _, hB, ⟨e⟩⟩ :=
    exists_finiteType_algEquiv_adicCompletion_quotient_pow A p hp hdim
  have : Algebra.FiniteType A B := hB
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let R := AdicCompletion (maximalIdeal A) A
  let C := AdicCompletion ((maximalIdeal A).map (algebraMap A B)) B
  let T := R ⧸ p ^ n
  have hpn : p ^ n ≠ ⊤ := ne_top_of_le_ne_top (hp.isPrime.ne_top) (Ideal.pow_le_self hn.ne')
  have : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hpn
  have : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (p ^ n)) Ideal.Quotient.mk_surjective
  have : Nontrivial C := e.symm.toMulEquiv.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have hCdim : ringKrullDim C = 1 :=
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans
      ((ringKrullDim_quotient_pow p hn.ne').trans hdim)
  let g : R →ₐ[A] C := e.toAlgHom.comp (Ideal.Quotient.mkₐ A (p ^ n))
  have hg : Function.Surjective g := e.surjective.comp (Ideal.Quotient.mkₐ_surjective A _)
  have hresA : Function.Surjective ((residue C).comp (algebraMap A C)) :=
    surjective_residue_comp_of_surjective g hg (surjective_residue_comp_adicCompletion A)
  let φ : B →+* ResidueField C := (residue C).comp (algebraMap B C)
  have hφA (a : A) : φ (algebraMap A B a) = residue C (algebraMap A C a) :=
    congrArg (residue C) (IsScalarTower.algebraMap_apply A B C a).symm
  have hφ : Function.Surjective φ := fun x =>
    let ⟨a, ha⟩ := hresA x
    ⟨algebraMap A B a, (hφA a).trans ha⟩
  let m := RingHom.ker φ
  have hm : m = (maximalIdeal C).comap (algebraMap B C) := by
    change RingHom.ker ((residue C).comp (algebraMap B C)) = _
    rw [← RingHom.comap_ker, ker_residue]
  have : m.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hφ
  have hmh : m.height ≤ 1 := by
    have : (maximalIdeal C).LiesOver m := ⟨hm⟩
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m (maximalIdeal C)
    have hle : m.height ≤ (maximalIdeal C).height := by rw [h]; exact le_self_add
    have hch : (maximalIdeal C).height = 1 := by
      apply WithBot.coe_injective
      exact maximalIdeal_height_eq_ringKrullDim.trans hCdim
    exact hle.trans_eq hch
  let f : B →ₐ[A] (R ⧸ p) :=
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_self hn.ne')).comp
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B C))
  let K := RingHom.ker f.toRingHom
  have : K.IsPrime := RingHom.ker_isPrime f.toRingHom
  have hKm : K ≤ m := by
    intro b hb
    have hb' : e.symm (algebraMap B C b) ∈
        p.map (Ideal.Quotient.mk (p ^ n)) := by
      rw [← Ideal.Quotient.factor_ker (Ideal.pow_le_self hn.ne')]
      exact hb
    have hpm : p.map (Ideal.Quotient.mk (p ^ n)) ≤ maximalIdeal T :=
      le_maximalIdeal (Ideal.isPrime_map_quotientMk_of_isPrime (Ideal.pow_le_self hn.ne')).ne_top
    have hbmax := hpm hb'
    have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
    have hemax := IsLocalRing.maximalIdeal_comap e.symm.toRingHom
    have hbC : algebraMap B C b ∈ maximalIdeal C := by
      change algebraMap B C b ∈ (maximalIdeal T).comap e.symm.toRingHom at hbmax
      rwa [hemax] at hbmax
    exact hm ▸ hbC
  let D := B ⧸ K
  let q := m.map (Ideal.Quotient.mk K)
  have hq : q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by simpa using hKm)
  have hqcomap : q.comap (Ideal.Quotient.mk K) = m := Ideal.comap_map_mk hKm
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ?_, q, hq, ?_, ?_⟩
  · apply (RingHom.injective_iff_ker_eq_bot _).mpr
    rw [ker_algebraMap_quotient]
    change RingHom.ker (f.toRingHom.comp (algebraMap A B)) = ⊥
    have hf : f.toRingHom.comp (algebraMap A B) = algebraMap A (R ⧸ p) :=
      RingHom.ext f.commutes
    rw [hf]
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (algebraMap_quotient_injective_of_mem_minimalPrimes p hp)
  · have : q.IsPrime := hq.isPrime
    exact (height_le_comap_of_surjective _ Ideal.Quotient.mk_surjective q).trans
      (hqcomap ▸ hmh)
  · intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a, ha⟩ := hresA (φ b)
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B (D ⧸ q), IsScalarTower.algebraMap_apply B D (D ⧸ q)]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_map_of_mem
    change φ (algebraMap A B a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact (hφA a).trans ha

private theorem covBy_of_length_eq_height {α : Type*} [PartialOrder α]
    (s : LTSeries α) (hs : (s.length : ℕ∞) = Order.height s.last) (i : Fin s.length) :
    s i.castSucc ⋖ s i.succ := by
  refine ⟨s.step i, fun z hz₁ hz₂ => ?_⟩
  have h₁ := Order.height_add_one_le hz₁
  have h₂ := Order.height_add_one_le hz₂
  rw [Order.height_eq_index_of_length_eq_height_last hs i.castSucc] at h₁
  rw [Order.height_eq_index_of_length_eq_height_last hs i.succ] at h₂
  have h := (add_le_add h₁ (le_refl (1 : ℕ∞))).trans h₂
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h
  norm_cast at h
  omega

private theorem exists_covChain_bot_length_eq_height
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (p : Ideal R) [p.IsPrime] :
    ∃ s : CovChain R, s.head = ⊥ ∧ s.last.asIdeal = p ∧ (s.length : ℕ∞) = p.height := by
  obtain ⟨s, hs, hlen⟩ := p.exists_ltSeries_length_eq_height
  have hh : (s.length : ℕ∞) = Order.height s.last := by
    rw [← PrimeSpectrum.height_eq_orderHeight, hs]
    exact hlen
  refine ⟨⟨s.length, s.toFun, covBy_of_length_eq_height s hh⟩, ?_,
    congrArg PrimeSpectrum.asIdeal hs, hlen⟩
  have hz : Order.height s.head = 0 := by
    simpa only [RelSeries.head, Fin.val_zero, Nat.cast_zero] using
      Order.height_eq_index_of_length_eq_height_last hh 0
  exact isMin_iff_eq_bot.mp (Order.height_eq_zero.mp hz)

private theorem covBy_comap_quotient {R : Type*} [CommRing R] (I : Ideal R)
    {p q : PrimeSpectrum (R ⧸ I)} (hpq : p ⋖ q) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) p ⋖ PrimeSpectrum.comap (Ideal.Quotient.mk I) q := by
  let e := I.primeSpectrumQuotientOrderIsoZeroLocus
  have h := (apply_covBy_apply_iff e).mpr hpq
  refine ⟨h.1, fun r hr₁ hr₂ => ?_⟩
  have hr : r ∈ PrimeSpectrum.zeroLocus (I : Set R) :=
    (show I ≤ (e p).val.asIdeal from (e p).property).trans hr₁.le
  exact h.2 (c := ⟨r, hr⟩) hr₁ hr₂

private theorem height_eq_add_one_of_height_one_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    (hp : p.height = 1) (hpq : p ≤ q) :
    q.height = (q.map (Ideal.Quotient.mk p)).height + 1 := by
  have hcov : (⊥ : PrimeSpectrum R) ⋖ (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    refine ⟨bot_lt_iff_ne_bot.mpr (fun h => Ideal.ne_bot_of_height_eq_one hp
      (congrArg PrimeSpectrum.asIdeal h)), ?_⟩
    intro t hbt htp
    have h := Order.one_lt_height_iff.mpr ⟨t, ⊥, hbt, htp⟩
    rw [← PrimeSpectrum.height_eq_orderHeight, hp] at h
    exact (lt_irrefl _) h
  have : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨s, hsh, hsl, hslen⟩ := exists_covChain_bot_length_eq_height (q.map (Ideal.Quotient.mk p))
  let t : CovChain R :=
    ⟨s.length, fun i => PrimeSpectrum.comap (Ideal.Quotient.mk p) (s i),
      fun i => covBy_comap_quotient p (s.step i)⟩
  have hth : t.head = (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
    change PrimeSpectrum.comap (Ideal.Quotient.mk p) s.head = _
    rw [hsh]
    apply PrimeSpectrum.ext
    exact Ideal.mk_ker
  have htl : t.last = (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    change (s.last.asIdeal).comap (Ideal.Quotient.mk p) = q
    rw [hsl, Ideal.comap_map_mk hpq]
  let t' := t.cons ⊥ (hth.symm ▸ hcov)
  obtain ⟨v, hvh, hvl, hvlen⟩ := exists_covChain_bot_length_eq_height q
  have heq := (_root_.isCatenaryRingSaturated_of_isCatenary hcat ⊥ ⟨q, inferInstance⟩ bot_le).2
    t' v (by simp [t']) (by simpa [t'] using htl) hvh (PrimeSpectrum.ext hvl)
  rw [← hvlen, ← heq]
  simpa [t', t, Nat.cast_add, Nat.cast_one] using hslen

private theorem height_le_one_of_comap_polynomial_eq_bot
    {R : Type*} [CommRing R] [IsDomain R]
    (p : Ideal (Polynomial R)) [p.IsPrime]
    (hp : p.comap (algebraMap R (Polynomial R)) = ⊥) : p.height ≤ 1 := by
  let M := (nonZeroDivisors R).map (Polynomial.C : R →+* Polynomial R)
  let S := Polynomial (FractionRing R)
  let : Algebra (Polynomial R) S := Polynomial.algebra R (FractionRing R)
  have : IsLocalization M S := Polynomial.isLocalization (nonZeroDivisors R) (FractionRing R)
  have hdisj : Disjoint (M : Set (Polynomial R)) (p : Set (Polynomial R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hap
    have hmem : a ∈ p.comap (algebraMap R (Polynomial R)) := hap
    rw [hp, Ideal.mem_bot] at hmem
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) hmem
  let P := p.map (algebraMap (Polynomial R) S)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S p inferInstance hdisj
  rw [← IsLocalization.height_map_of_disjoint (S := S) M p hdisj]
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
    ⟨⟨inferInstance, le_rfl⟩, fun q hq _ => hq.2⟩

private theorem height_le_height_of_surjective_quotient_of_single_generator
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S]
    (hinj : Function.Injective (algebraMap R S))
    (hcat : Ring.IsCatenary (Polynomial R))
    (hgen : ∃ b : S, Algebra.adjoin R {b} = ⊤)
    (q : Ideal S) [q.IsPrime]
    (hres : Function.Surjective (algebraMap R (S ⧸ q))) :
    (q.comap (algebraMap R S)).height ≤ q.height := by
  obtain ⟨b, hb⟩ := hgen
  let f := Polynomial.aeval (R := R) b
  have hf : Function.Surjective f := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
    exact hb
  let K := RingHom.ker f.toRingHom
  let Q := q.comap f.toRingHom
  let p := q.comap (algebraMap R S)
  have : Q.IsPrime := Ideal.comap_isPrime _ q
  have : K.IsPrime := RingHom.ker_isPrime _
  have hfcomp : f.toRingHom.comp (algebraMap R (Polynomial R)) = algebraMap R S :=
    RingHom.ext f.commutes
  have hQp : Q.comap (algebraMap R (Polynomial R)) = p := by
    change q.comap (f.toRingHom.comp (algebraMap R (Polynomial R))) = p
    rw [hfcomp]
  have : Q.LiesOver p := ⟨hQp.symm⟩
  have hK : K.comap (algebraMap R (Polynomial R)) = ⊥ := by
    change RingHom.ker (f.toRingHom.comp (algebraMap R (Polynomial R))) = ⊥
    rw [hfcomp]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hmaple : p.map (algebraMap R (Polynomial R)) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr hQp.symm.le
  obtain ⟨a, ha⟩ := hres (Ideal.Quotient.mk q b)
  have hbQ : Polynomial.X - Polynomial.C a ∈ Q := by
    change f (Polynomial.X - Polynomial.C a) ∈ q
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_sub, sub_eq_zero]
    exact ha.symm
  have hbnot : Polynomial.X - Polynomial.C a ∉ p.map (algebraMap R (Polynomial R)) := by
    rw [Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    intro h
    have h1 := h 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      one_ne_zero, ↓reduceIte, sub_zero] at h1
    exact (inferInstance : p.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  let F := Q.map (Ideal.Quotient.mk (p.map (algebraMap R (Polynomial R))))
  have : F.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hmaple
  have : IsDomain (Polynomial R ⧸ p.map (algebraMap R (Polynomial R))) := by
    rw [Polynomial.algebraMap_eq]
    exact Ideal.isDomain_map_C_quotient inferInstance
  have hF : F ≠ ⊥ := by
    intro hF
    have hqeq : Q = p.map (algebraMap R (Polynomial R)) := by
      have h := congrArg (Ideal.comap (Ideal.Quotient.mk
        (p.map (algebraMap R (Polynomial R))))) hF
      change (Q.map (Ideal.Quotient.mk (p.map (algebraMap R (Polynomial R))))).comap _ = _ at h
      rw [Ideal.comap_map_mk hmaple, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h
      exact h
    exact hbnot (hqeq ▸ hbQ)
  have hFpos : 1 ≤ F.height := Order.one_le_iff_ne_zero.mpr
    (fun h => hF (Ideal.height_eq_zero_iff_eq_bot.mp h))
  have hlow : p.height + 1 ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q]
    exact add_le_add le_rfl hFpos
  let e : (Polynomial R ⧸ K) ≃+* S :=
    RingHom.quotientKerEquivOfSurjective (f := f.toRingHom) hf
  have hKQ : K ≤ Q := fun x hx => by
    change f x = 0 at hx
    change f x ∈ q
    rw [hx]
    exact q.zero_mem
  have hmapQ : Q.map (Ideal.Quotient.mk K) = q.comap e.toRingHom := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_mk hKQ, Ideal.comap_comap]
    rfl
  by_cases hK0 : K = ⊥
  · have hf' : Function.Injective f := (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr hK0
    let e' := RingEquiv.ofBijective f.toRingHom ⟨hf', hf⟩
    have hheight : Q.height = q.height := e'.height_comap q
    exact le_self_add.trans (hlow.trans_eq hheight)
  · have hK1 : K.height = 1 := le_antisymm
      (height_le_one_of_comap_polynomial_eq_bot K hK)
      (Order.one_le_iff_ne_zero.mpr (fun h => hK0 (Ideal.height_eq_zero_iff_eq_bot.mp h)))
    have hadd := height_eq_add_one_of_height_one_quotient hcat K Q hK1 hKQ
    have heheight : (q.comap e.toRingHom).height = q.height := e.height_comap q
    rw [hmapQ, heheight] at hadd
    rw [hadd] at hlow
    exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hlow

private theorem adjoin_insert_isOneGenerator
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq S] (a : S) (T : Finset S)
    [Algebra ↥(Algebra.adjoin R (↑T : Set S)) ↥(Algebra.adjoin R (↑(insert a T) : Set S))]
    [IsScalarTower ↥(Algebra.adjoin R (↑T : Set S))
      ↥(Algebra.adjoin R (↑(insert a T) : Set S)) S] :
    ∃ x : ↥(Algebra.adjoin R (↑(insert a T) : Set S)),
      Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) {x} = ⊤ := by
  have haB' : a ∈ Algebra.adjoin R (↑(insert a T) : Set S) := by
    apply Algebra.subset_adjoin; simp
  refine ⟨⟨a, haB'⟩, ?_⟩
  have hB'eq : Algebra.adjoin R (↑(insert a T) : Set S)
      = Subalgebra.restrictScalars R
        (Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) ({a} : Set S)) := by
    have hu : (↑(insert a T) : Set S) = (↑T : Set S) ∪ {a} := by
      rw [Finset.coe_insert]; ext z; simp
    rw [hu, Algebra.adjoin_union_eq_adjoin_adjoin]
  have hmem : ∀ x : S, x ∈ Algebra.adjoin R (↑(insert a T) : Set S)
      ↔ x ∈ Algebra.adjoin ↥(Algebra.adjoin R (↑T : Set S)) ({a} : Set S) := by
    intro x; rw [hB'eq]; rfl
  let j : ↥(Algebra.adjoin R (↑(insert a T) : Set S))
      →ₐ[↥(Algebra.adjoin R (↑T : Set S))] S :=
    IsScalarTower.toAlgHom ↥(Algebra.adjoin R (↑T : Set S))
      ↥(Algebra.adjoin R (↑(insert a T) : Set S)) S
  have hjinj : Function.Injective j := Subtype.val_injective
  apply Subalgebra.map_injective hjinj
  rw [AlgHom.map_adjoin]
  have himg : (j : ↥(Algebra.adjoin R (↑(insert a T) : Set S)) → S)
      '' {(⟨a, haB'⟩ : ↥(Algebra.adjoin R (↑(insert a T) : Set S)))} = {a} := by
    exact Set.image_singleton
  rw [himg, Algebra.map_top]
  apply SetLike.ext
  intro x
  rw [AlgHom.mem_range]
  constructor
  · intro hx; exact ⟨⟨x, (hmem _).mpr hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩; exact (hmem _).mp y.property

/-- A dominant finite-type map over a universally catenary domain cannot lower the
height at a point whose residue quotient is generated by constants. -/
private theorem height_le_height_of_surjective_quotient
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsDomain R] [IsDomain S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (hcat : Ring.IsUniversallyCatenary R)
    (q : Ideal S) [q.IsPrime]
    (hres : Function.Surjective (algebraMap R (S ⧸ q))) :
    (q.comap (algebraMap R S)).height ≤ q.height := by
  classical
  have main (T : Finset S) :
      (q.under R).height ≤ (q.under ↥(Algebra.adjoin R (T : Set S))).height := by
    induction T using Finset.induction_on with
    | empty =>
      let B := Algebra.adjoin R (↑(∅ : Finset S) : Set S)
      let e : R ≃ₐ[R] B :=
        ((Subalgebra.equivOfEq _ _ (by simp [B] : B = ⊥)).trans
          (Algebra.botEquivOfInjective hinj)).symm
      have he : e.toRingHom = algebraMap R B := by
        apply RingHom.ext
        intro r
        simpa using e.commutes r
      have hp : (q.under B).comap e.toRingHom = q.under R := by
        rw [he, Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      have hheight : ((q.under B).comap e.toRingHom).height = (q.under B).height :=
        e.toRingEquiv.height_comap (q.under B)
      rw [hp] at hheight
      exact hheight.le
    | insert b T hb ih =>
      let B := Algebra.adjoin R (T : Set S)
      let B' := Algebra.adjoin R (↑(insert b T) : Set S)
      have hBB' : B ≤ B' := Algebra.adjoin_mono (by intro x hx; exact Finset.mem_insert_of_mem hx)
      let : Algebra B B' := (Subalgebra.inclusion hBB').toAlgebra
      have : IsScalarTower B B' S := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : Algebra.FiniteType R B :=
        (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
      have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
      have : Algebra.FiniteType R B' :=
        (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset (insert b T))
      have : Algebra.FiniteType R (Polynomial B) :=
        Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R B)
          (inferInstance : Algebra.FiniteType B (Polynomial B))
      have hres' : Function.Surjective (algebraMap B (B' ⧸ q.under B')) := by
        intro x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨a, ha⟩ := hres (Ideal.Quotient.mk q x.val)
        refine ⟨algebraMap R B a, ?_⟩
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        change algebraMap R S a - x.val ∈ q
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_sub, sub_eq_zero]
        exact ha
      have hstep := height_le_height_of_surjective_quotient_of_single_generator
        (Subalgebra.inclusion_injective hBB') (hcat (Polynomial B))
        (adjoin_insert_isOneGenerator (R := R) b T) (q.under B') hres'
      have heq : (q.under B').comap (algebraMap B B') = q.under B := rfl
      rw [heq] at hstep
      exact ih.trans hstep
  obtain ⟨G, hG⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  let e : Algebra.adjoin R (G : Set S) ≃ₐ[R] S :=
    (Subalgebra.equivOfEq _ _ hG).trans Subalgebra.topEquiv
  have hheight : (q.under ↥(Algebra.adjoin R (G : Set S))).height = q.height :=
    e.toRingEquiv.height_comap q
  exact (main G).trans_eq hheight

/-! ### Stacks 0AW3 and Ratliff's equivalence -/

/-- **Stacks 0AW3.** A Noetherian local ring which is not formally catenary is not universally
catenary. -/
@[stacks 0AW3]
theorem not_isUniversallyCatenary_of_not_isFormallyCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ¬ IsFormallyCatenary A) : ¬ Ring.IsUniversallyCatenary A := by
  intro huc
  obtain ⟨B, _, _, _, _, hB, p, hp, hdim, hdlt⟩ :=
    exists_domain_minimalPrime_completion_dim_one A hA huc
  obtain ⟨D, _, _, _, hD, hinj, q, hq, hheight, hres⟩ :=
    exists_finiteType_domain_prime_height_le_one B p hp hdim
  have : Algebra.FiniteType B D := hD
  have : q.IsPrime := hq.isPrime
  have hle := height_le_height_of_surjective_quotient hinj hB q hres
  have hmax : q.comap (algebraMap B D) = maximalIdeal B := by
    have : (q.comap (algebraMap B D)).IsMaximal := by
      have : q.IsMaximal := hq
      let := Ideal.Quotient.field q
      exact ker_algebraMap_quotient (R := B) q ▸
        RingHom.ker_isMaximal_of_surjective (algebraMap B (D ⧸ q)) hres
    exact eq_maximalIdeal inferInstance
  rw [hmax] at hle
  have hdimB : ringKrullDim B ≤ 1 := by
    rw [← maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr (hle.trans hheight)
  exact (not_le_of_gt hdlt) hdimB

/-- **Ratliff's theorem (Stacks 0AW6).** A Noetherian local ring is universally catenary if and
only if it is formally catenary. -/
@[stacks 0AW6, ega "IV 7.1.11" "(i)"]
theorem isUniversallyCatenary_iff_isFormallyCatenary
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    Ring.IsUniversallyCatenary A ↔ IsFormallyCatenary A := by
  constructor
  · intro hA
    by_contra h
    exact not_isUniversallyCatenary_of_not_isFormallyCatenary A h hA
  · exact isUniversallyCatenary_of_isFormallyCatenary A

end UniversalCatenarityImpliesFormalCatenarity
