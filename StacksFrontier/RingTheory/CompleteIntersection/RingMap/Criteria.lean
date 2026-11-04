module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Quotient
public meta import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MvPolynomial.FiberAtPrime
public import StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import StacksFrontier.RingTheory.Koszul.H1BaseChange
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.Regular.Ideal
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Syntomic.Defs
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksFrontier.RingTheory.Koszul.H1RegularRingEquiv

@[expose] public section

/-!
# Criteria for a ring map to be a local complete intersection

Two criteria for `RingHom.IsLocalCompleteIntersection`, and the characterization of syntomic ring
maps that the second one yields. The first is that the property is local on the target: it may be
checked after localizing at every member of a finite family generating the unit ideal. The second
identifies the relations of a relative global complete intersection presentation
`S = R[x₁, …, x_n] / (f₁, …, f_c)` (Definition 00SP,
`Algebra.IsRelativeGlobalCompleteIntersection`) as Koszul-regular, which is what makes the
syntomic ring maps precisely the flat local complete intersections.

## Main results

* `RingHom.isLocalCompleteIntersection_of_localization_away`: the local complete intersection
  property can be checked on a finite cover by principal localizations of the target.
* `RingHom.isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection`: the relations
  `f₁, …, f_c` of a relative global complete intersection presentation form a Koszul-regular
  sequence in the polynomial ring `R[xᵢ]`.
* `RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection`: a ring homomorphism is syntomic
  exactly when it is flat and a local complete intersection.

## Implementation notes

The two halves are kept in separate `section`s, `LocalOnTarget` and `SyntomicCriterion`, each
carrying its own universe variables, `open`s and options.

### Locality on the target (tag 07D1)

The family `g₁, ..., gₘ` is represented by a function `g : Fin m → S`, and generation of the unit
ideal by `Ideal.span (Set.range g) = ⊤`. Each `S_{g_j}` is the canonical localization
`Localization.Away (g j)`.

The finite-type half of the conclusion is local on the target already in Mathlib
(`Algebra.FiniteType.of_span_eq_top_target`). For the Koszul-regularity half, choose any finite
presentation `p : R[x₁, …, x_n] → S`, which exists once finite type is known, and fix a prime `q`
of `R[x₁, …, x_n]` containing `I = ker p`. Lifting the `g j` to polynomials `h j` along `p`, some
`h j` avoids `q`, because the `g j` generate the unit ideal and so cannot all lie in the prime
`(q)·p`. Localizing that variable away turns `p` into a presentation
`R[x₁, …, x_n][T] → S_{g j}` of the localized algebra, whose kernel `J` is Koszul-regular by
hypothesis together with `RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial` (tag 07CZ),
which makes Koszul-regularity of a presentation ideal independent of the presentation.

Descending from `J` back to `I` is the substance of the argument, and is carried out by
`exists_koszulRegular_of_map_presentation_away`. The ideal `J` contains the localization relation
`t = C h * T - 1` and maps onto the extension of `I`, so it suffices to move `t` to the front of a
local Koszul-regular generating sequence for `J` and divide it out. That `t` really does occur
with a unit coefficient is detected by a derivation: `∂/∂T` kills none of the relation, and
extends from `R[x₁, …, x_n][T]` to any of its localizations because those are formally étale
(`Algebra.FormallyEtale.of_isLocalization`), so it can be evaluated in the residue field of the
prime at hand. Reordering the generators is then
`Koszul.regularity_of_generators_of_eq_span_range` (tag 066A) and dividing `t` out is
`Koszul.koszulRegular_quotient_of_koszulRegular_append` (tag 068M). Flat base change
(`KoszulC.isKoszulRegular_baseChange`, tag 062H) transports Koszul-regularity along the
localization maps that appear along the way, and the various localizations away from different
elements are identified through `IsLocalization.Away.mul_of_associated`.

### Koszul-regular relations and the syntomic criterion (tags 07D2, 07D3)

Koszul regularity of the relations is checked one maximal ideal of `R[xᵢ]` at a time
(`isKoszulRegular_of_forall_atPrime`); flat base change of Koszul homology
(`KoszulC.homology_baseChange_linearEquiv`) makes that local check sufficient. At a maximal ideal
`q` not containing the relation ideal some `f_j` becomes a unit, and wedge multiplication by the
corresponding basis vector contracts the Koszul complex (`isKoszulRegular_of_isUnit`). At a
maximal ideal containing the relation ideal the fibre dimension condition of the presentation is
used instead: the fibre ring of `(R[xᵢ])_q` over the residue field of `p = q ∩ R` is a
localization of `κ(p)[xᵢ]` (the `Fibre` section builds that identification by hand, as
`ψ : κ(p)[xᵢ] → F`), where Cohen–Macaulayness of polynomial rings over a field turns the
dimension bound into regularity of the relations (Stacks 00R9); flatness of
`(R[xᵢ])_q` over `R_p` together with essential finite presentation then lifts regularity from the
fibre to the local ring, and `Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular` (Stacks
062F) converts it to Koszul regularity.

The polynomial variables may be indexed by any finite type. The relations remain indexed by
`Fin c`, matching the finite-sequence representation used by the Koszul complex.

For the characterization of syntomic ring maps, the two implications are proved separately. A
flat local complete intersection is of finite presentation (a Koszul-regular ideal is locally
generated by a finite sequence, hence finitely generated) and its fibres over the residue fields
of the base are local complete intersections, because a locally `H₁`-regular ideal with flat
quotient stays locally `H₁`-regular after arbitrary base change (Stacks 0CEP) and, over a field,
a polynomial presentation with locally `H₁`-regular kernel is a local complete intersection
(via Stacks 09CC in the local ring at a prime of the presentation). Conversely a syntomic ring
map is, in a principal neighborhood of every prime, a relative global complete intersection
(Stacks tag 00SY), and `RingHom.isLocalCompleteIntersection_of_localization_away` (Stacks 07D1)
glues the resulting local complete intersections.

## References

* [Stacks Project, Tag 07D1](https://stacks.math.columbia.edu/tag/07D1)
* [Stacks Project, Tag 07D2](https://stacks.math.columbia.edu/tag/07D2)
* [Stacks Project, Tag 07D3](https://stacks.math.columbia.edu/tag/07D3)
-/

namespace RingHom

section LocalOnTarget

universe u v w x

open CategoryTheory
open scoped TensorProduct

set_option maxRecDepth 4096

/-- Finite type is local on the target: it is enough to check it after localizing away from each
member of a family generating the unit ideal. -/
private theorem finiteType_of_localization_away
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} (g : ι → S) (hspan : Ideal.span (Set.range g) = ⊤)
    (hlocal : ∀ j, ((algebraMap S (Localization.Away (g j))).comp f).FiniteType) :
    f.FiniteType := by
  let := f.toAlgebra
  change Algebra.FiniteType R S
  apply Algebra.FiniteType.of_span_eq_top_target (Set.range g) hspan
  rintro _ ⟨j, rfl⟩
  exact (RingHom.finiteType_algebraMap).mp (hlocal j)

/-- If a derivation does not kill `t = ∑ i, c i * f i` while every `f i` dies in `K`, then some
coefficient `c i` survives in `K`. -/
private theorem exists_coeff_notMem_of_derivation
    {R A K : Type*} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    {ι : Type*} [Fintype ι] (D : Derivation R A K)
    (f c : ι → A) (t : A) (ht : t = ∑ i, c i * f i)
    (hf : ∀ i, algebraMap A K (f i) = 0) (hD : D t ≠ 0) :
    ∃ i, algebraMap A K (c i) ≠ 0 := by
  by_contra! h
  apply hD
  rw [ht, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp [D.leibniz, Algebra.smul_def, hf i, h i]

/-- If a derivation does not kill `t = ∑ i, c i * f i` while every `f i` dies in `K`, then some
coefficient `c i` survives in `K`. -/
private alias exists_coeff_map_ne_zero_of_derivation := exists_coeff_notMem_of_derivation

/-- Replacing `f i` by a combination `t = ∑ j, c j * f j` in which `c i` is a unit does not change
the generated ideal. -/
private theorem span_range_update_eq_of_isUnit
    {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f c : ι → R) (t : R) (ht : ∑ j, c j * f j = t) (i : ι)
    (hc : IsUnit (c i)) :
    Ideal.span (Set.range (Function.update f i t)) = Ideal.span (Set.range f) := by
  let J := Ideal.span (Set.range (Function.update f i t))
  have hmem (j : ι) (hji : j ≠ i) : f j ∈ J := by
    apply Ideal.subset_span
    exact ⟨j, Function.update_of_ne hji _ _⟩
  have hi : f i ∈ J := by
    apply (J.unit_mul_mem_iff_mem hc).mp
    have heq : c i * f i = t - ∑ j ∈ Finset.univ.erase i, c j * f j := by
      rw [← ht, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_right]
    rw [heq]
    apply J.sub_mem
    · exact Ideal.subset_span ⟨i, Function.update_self _ _ _⟩
    · apply J.sum_mem
      intro j hj
      exact J.mul_mem_left _ (hmem j (Finset.ne_of_mem_erase hj))
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨c, ht⟩
    · rw [Function.update_of_ne hji]
      exact Ideal.subset_span ⟨j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact hmem j hji

/-- A derivation into `K` extends along a formally étale algebra map. -/
theorem exists_derivation_of_formallyEtale
    {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing K]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R K] [Algebra A K] [Algebra B K]
    [IsScalarTower R A K] [IsScalarTower R B K] [IsScalarTower A B K]
    [Algebra.FormallyEtale A B] (D : Derivation R A K) :
    ∃ D' : Derivation R B K, ∀ x, D' (algebraMap A B x) = D x := by
  let L : KaehlerDifferential R B →ₗ[B] K :=
    D.liftKaehlerDifferential.liftBaseChange B ∘ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap
  refine ⟨Derivation.llcomp L (KaehlerDifferential.D R B), ?_⟩
  intro x
  simp [L, Derivation.llcomp,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

/-- Reindexing a Koszul-regular sequence along an equality of lengths. -/
private theorem isKoszulRegular_cast
    {R : Type*} [CommRing R] {n m : ℕ} (h : n = m) (f : Fin n → R)
    (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i : Fin m ↦ f (Fin.cast h.symm i)) := by
  subst m
  simpa using hf

/-- If `t = ∑ j, c j * f j` with `c i` a unit and `f` is Koszul-regular, then `t` can be put at the
front of a Koszul-regular sequence generating the same ideal as `f`. -/
private theorem exists_koszulRegular_append_of_isUnit
    {R : Type*} [CommRing R] {r : ℕ} (f c : Fin (r + 1) → R) (t : R)
    (ht : ∑ j, c j * f j = t) (i : Fin (r + 1)) (hc : IsUnit (c i))
    (hf : Koszul.IsKoszulRegular f) :
    ∃ g : Fin r → R, Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 ↦ t) g) ∧
      Ideal.span (Set.range (Fin.append (fun _ : Fin 1 ↦ t) g)) =
        Ideal.span (Set.range f) := by
  let g := i.removeNth f
  have hspan : Ideal.span (Set.range (Fin.append (fun _ : Fin 1 ↦ t) g)) =
      Ideal.span (Set.range f) := by
    have hrange : Set.range (Fin.append (fun _ : Fin 1 ↦ t) g) =
        Set.range (Function.update f i t) := by
      calc
        _ = insert t (Set.range g) := by
          rw [Fin.append_left_eq_cons,
            (Fin.rightInverse_cast (Nat.add_comm 1 r)).surjective.range_comp, Fin.range_cons]
        _ = Set.range (i.insertNth t g) := (Fin.range_insertNth i t g).symm
        _ = _ := congrArg Set.range (Fin.insertNth_removeNth i t f)
    rw [hrange]
    exact span_range_update_eq_of_isUnit f c t ht i hc
  refine ⟨g, ?_, hspan⟩
  apply (Koszul.regularity_of_generators_of_eq_span_range _ _ hspan).2.2
  refine ⟨fun j : Fin (1 + r) ↦ f (Fin.cast (Nat.add_comm 1 r) j), ?_, ?_⟩
  · exact (Fin.rightInverse_cast (Nat.add_comm 1 r)).surjective.range_comp f ▸ rfl
  · exact isKoszulRegular_cast (Nat.add_comm r 1) f hf

/-- A Koszul-regular sequence stays Koszul-regular along a ring isomorphism. -/
private theorem isKoszulRegular_map_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] (e : R →+* S)
    (he : Function.Bijective e) {r : ℕ} (f : Fin r → R)
    (hf : Koszul.IsKoszulRegular f) : Koszul.IsKoszulRegular (fun i ↦ e (f i)) := by
  let := e.toAlgebra
  have : Module.Flat R S := RingHom.Flat.of_bijective he
  exact Koszul.isKoszulRegular_map_of_flat f hf

/-- Transport a Koszul-regular generating sequence from an arbitrary model of a principal
localization to the canonical one. -/
private theorem exists_koszulRegular_of_isLocalizationAway
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsLocalization.Away a S] (I : Ideal R)
    {r : ℕ} (f : Fin r → S) (hf : Koszul.IsKoszulRegular f)
    (hI : I.map (algebraMap R S) = Ideal.span (Set.range f)) :
    ∃ g : Fin r → Localization.Away a, Koszul.IsKoszulRegular g ∧
      I.map (algebraMap R (Localization.Away a)) = Ideal.span (Set.range g) := by
  let e := IsLocalization.algEquiv (Submonoid.powers a) S (Localization.Away a)
  refine ⟨fun i ↦ e (f i), isKoszulRegular_map_of_bijective e.toRingHom e.bijective f hf, ?_⟩
  have he : e.toRingHom.comp (algebraMap R S) =
      algebraMap R (Localization.Away a) := by ext; exact e.commutes _
  rw [← he, ← Ideal.map_map, hI, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Dividing out a combination with a unit coefficient from a Koszul-regular sequence leaves a
Koszul-regular sequence generating the image ideal. -/
private theorem exists_koszulRegular_quotient_of_isUnit
    {R : Type u} [CommRing R] {r : ℕ} (f c : Fin (r + 1) → R) (t : R)
    (ht : ∑ j, c j * f j = t) (i : Fin (r + 1)) (hc : IsUnit (c i))
    (hf : Koszul.IsKoszulRegular f)
    (htreg : Koszul.IsKoszulRegular (fun _ : Fin 1 ↦ t)) :
    ∃ g : Fin r → R ⧸ Ideal.span {t}, Koszul.IsKoszulRegular g ∧
      (Ideal.span (Set.range f)).map (Ideal.Quotient.mk (Ideal.span {t})) =
        Ideal.span (Set.range g) := by
  obtain ⟨g, hg, hspan⟩ := exists_koszulRegular_append_of_isUnit f c t ht i hc hf
  refine ⟨fun j ↦ Ideal.Quotient.mk (Ideal.span {t}) (g j), ?_, ?_⟩
  · have h := Koszul.koszulRegular_quotient_of_koszulRegular_append
      (fun _ : Fin 1 ↦ t) g htreg hg
    have heq : Ideal.span (Set.range (fun _ : Fin 1 ↦ t)) = Ideal.span {t} :=
      congrArg Ideal.span Set.range_const
    rw [heq] at h
    exact h
  · rw [← hspan, Ideal.map_span, ← Set.range_comp]
    have hrange : Set.range (fun j ↦ Ideal.Quotient.mk (Ideal.span {t})
        (Fin.append (fun _ : Fin 1 ↦ t) g j)) =
        insert 0 (Set.range (fun j ↦ Ideal.Quotient.mk (Ideal.span {t}) (g j))) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        induction j using Fin.addCases with
        | left j => simp [Fin.append_left, Ideal.Quotient.eq_zero_iff_mem]
        | right j => exact Set.mem_insert_of_mem _ ⟨j, by simp⟩
      · rintro (rfl | ⟨j, rfl⟩)
        · exact ⟨Fin.castAdd r 0, by simp⟩
        · exact ⟨Fin.natAdd 1 j, by simp⟩
    change Ideal.span (Set.range (fun j ↦ Ideal.Quotient.mk (Ideal.span {t})
      (Fin.append (fun _ : Fin 1 ↦ t) g j))) = _
    rw [hrange, Ideal.span_insert_zero]

/-- Every element of a localization is associated to the image of an element of the base ring. -/
private theorem exists_integer_associated_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (s : S) :
    ∃ z : R, Associated (algebraMap R S z) s := by
  obtain ⟨⟨z, d⟩, hd⟩ := IsLocalization.surj M s
  refine ⟨z, ?_⟩
  rw [← hd]
  exact associated_mul_unit_left _ _ (IsLocalization.map_units S d)

/-- If the image of `z` is associated to an element outside the extension of `p`, then `z ∉ p`. -/
private theorem notMem_of_associated_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} {z : R} {s : S}
    (hz : Associated (algebraMap R S z) s) (hs : s ∉ p.map (algebraMap R S)) : z ∉ p := by
  intro hzp
  apply hs
  obtain ⟨d, hd⟩ := hz.dvd
  rw [hd]
  exact Ideal.mul_mem_right d _ (Ideal.mem_map_of_mem _ hzp)

/-- The extension of a prime avoiding `a` to the principal localization at `a` is prime and
contracts back to the original prime. -/
private theorem isPrime_map_and_comap_away
    {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {a : R}
    [IsLocalization.Away a S] {p : Ideal R} [p.IsPrime] (ha : a ∉ p) :
    (p.map (algebraMap R S)).IsPrime ∧ (p.map (algebraMap R S)).comap (algebraMap R S) = p := by
  have hd : Disjoint (Submonoid.powers a : Set R) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr ha
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) S p ‹_› hd,
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) S ‹_› hd⟩

/-- A Koszul-regular generating sequence of the extension of `I` to `S_s`, where `s` lies outside
the extension of a prime `p` to a principal localization `S` of `R`, descends to a principal
localization of `R` away from `p`. -/
private theorem exists_koszulRegular_of_associated_away
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsLocalization.Away a S] (I : Ideal R) (p : PrimeSpectrum R) (ha : a ∉ p.asIdeal)
    {s : S} (hs : s ∉ p.asIdeal.map (algebraMap R S)) {r : ℕ}
    (f : Fin r → Localization.Away s) (hf : Koszul.IsKoszulRegular f)
    (hspan : I.map (algebraMap R (Localization.Away s)) = Ideal.span (Set.range f)) :
    ∃ b : R, b ∉ p.asIdeal ∧ ∃ g : Fin r → Localization.Away b, Koszul.IsKoszulRegular g ∧
      I.map (algebraMap R (Localization.Away b)) = Ideal.span (Set.range g) := by
  obtain ⟨z, hz⟩ := exists_integer_associated_of_isLocalization (Submonoid.powers a) s
  have : IsLocalization.Away (a * z) (Localization.Away s) :=
    IsLocalization.Away.mul_of_associated a z s hz
  obtain ⟨g, hg, hspan'⟩ := exists_koszulRegular_of_isLocalizationAway (a * z) I f hf hspan
  exact ⟨a * z, fun h ↦ (p.isPrime.mem_or_mem h).elim ha (notMem_of_associated_algebraMap hz hs),
    g, hg, hspan'⟩

/-- Koszul-regularity of the extension of `I` to a principal localization `S` of `R` gives a
Koszul-regular generating sequence for `I` in a principal localization of `R` itself. -/
private theorem exists_koszulRegular_of_isKoszulRegularIdeal_map
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (a : R) [IsLocalization.Away a S] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) (ha : a ∉ p.asIdeal)
    (hI : Ideal.IsKoszulRegular (I.map (algebraMap R S))) :
    ∃ b : R, b ∉ p.asIdeal ∧
      ∃ (r : ℕ) (f : Fin r → Localization.Away b), Koszul.IsKoszulRegular f ∧
        I.map (algebraMap R (Localization.Away b)) = Ideal.span (Set.range f) := by
  let q : PrimeSpectrum S := ⟨p.asIdeal.map (algebraMap R S), (isPrime_map_and_comap_away S ha).1⟩
  obtain ⟨s, hs, r, f, hf, hspan⟩ := hI q (Ideal.map_mono hp)
  have hspan' : I.map (algebraMap R (Localization.Away s)) = Ideal.span (Set.range f) := by
    rw [IsScalarTower.algebraMap_eq R S (Localization.Away s), ← Ideal.map_map]
    exact hspan
  obtain ⟨b, hb, f', hf', hspan''⟩ :=
    exists_koszulRegular_of_associated_away a I p ha hs f hf hspan'
  exact ⟨b, hb, r, f', hf', hspan''⟩

/-- Koszul-regularity of an ideal is preserved by a ring isomorphism. -/
private theorem isKoszulRegularIdeal_map_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R)
    (hI : Ideal.IsKoszulRegular I) :
    Ideal.IsKoszulRegular (I.map e.toRingHom) := by
  let := e.symm.toRingHom.toAlgebra
  have : IsLocalization.Away (1 : S) R :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.symm.bijective
  intro p hp
  apply exists_koszulRegular_of_isKoszulRegularIdeal_map (S := R) 1 _ p hp
    p.isPrime.one_notMem
  convert hI using 1
  rw [Ideal.map_map]
  change I.map (e.symm.toRingHom.comp e.toRingHom) = I
  simp

/-- An element `t` of a Koszul-regularly generated ideal which a derivation does not kill can,
after localizing at a suitable element, be moved to the front of a Koszul-regular generating
sequence. -/
private theorem exists_koszulRegular_append_localization_of_derivation
    {R A K : Type u} [CommRing R] [CommRing A] [CommRing K]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
    {n : ℕ} (f : Fin n → A) (hf : Koszul.IsKoszulRegular f) (t : A)
    (ht : t ∈ Ideal.span (Set.range f)) (D : Derivation R A K)
    (hzero : ∀ i, algebraMap A K (f i) = 0) (hDt : D t ≠ 0) :
    ∃ c : A, algebraMap A K c ≠ 0 ∧
      ∃ (r : ℕ) (g : Fin r → Localization.Away c),
        Koszul.IsKoszulRegular
          (Fin.append (fun _ : Fin 1 ↦ algebraMap A (Localization.Away c) t) g) ∧
        Ideal.span (Set.range
            (Fin.append (fun _ : Fin 1 ↦ algebraMap A (Localization.Away c) t) g)) =
          (Ideal.span (Set.range f)).map (algebraMap A (Localization.Away c)) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht
  obtain ⟨i, hi⟩ := exists_coeff_map_ne_zero_of_derivation D f c t hc.symm hzero hDt
  cases n with
  | zero => exact i.elim0
  | succ r =>
    let φ := algebraMap A (Localization.Away (c i))
    have hrel : ∑ j, φ (c j) * φ (f j) = φ t := by
      simpa only [map_sum, map_mul] using congrArg φ hc
    have hunit : IsUnit (φ (c i)) :=
      IsLocalization.map_units (Localization.Away (c i)) ⟨c i, Submonoid.mem_powers _⟩
    obtain ⟨g, hg, hspan⟩ := exists_koszulRegular_append_of_isUnit
      (fun j ↦ φ (f j)) (fun j ↦ φ (c j)) (φ t) hrel i hunit
      (Koszul.isKoszulRegular_map_of_flat f hf)
    refine ⟨c i, hi, r, g, hg, ?_⟩
    rw [hspan, Ideal.map_span, ← Set.range_comp]
    rfl

/-- If the kernel of a surjection `φ` is generated by `t` and `t` heads a Koszul-regular sequence,
then the image of the tail is Koszul-regular. -/
private theorem isKoszulRegular_map_of_ker_eq_span
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ) (t : A) (hker : RingHom.ker φ = Ideal.span {t})
    (ht : Koszul.IsKoszulRegular (fun _ : Fin 1 ↦ t))
    {r : ℕ} (g : Fin r → A)
    (hg : Koszul.IsKoszulRegular (Fin.append (fun _ : Fin 1 ↦ t) g)) :
    Koszul.IsKoszulRegular (fun j ↦ φ (g j)) := by
  have h := Koszul.koszulRegular_quotient_of_koszulRegular_append
    (fun _ : Fin 1 ↦ t) g ht hg
  have heq : Ideal.span (Set.range (fun _ : Fin 1 ↦ t)) = RingHom.ker φ :=
    (congrArg Ideal.span Set.range_const).trans hker.symm
  rw [heq] at h
  let e := φ.quotientKerEquivOfSurjective hφ
  simpa [e, RingHom.quotientKerEquivOfSurjective_apply_mk] using
    isKoszulRegular_map_of_bijective e.toRingHom e.bijective
      (fun j ↦ Ideal.Quotient.mk (RingHom.ker φ) (g j)) h

/-- For a local complete intersection, the kernel of any finite polynomial presentation is
Koszul-regular. -/
private theorem isKoszulRegularIdeal_ker_of_isLocalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type w} [_root_.Finite ι] (p : MvPolynomial ι R →ₐ[R] S)
    (hp : Function.Surjective p)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap R S)) :
    Ideal.IsKoszulRegular (RingHom.ker p.toRingHom) := by
  rw [RingHom.IsLocalCompleteIntersection, _root_.toAlgebra_algebraMap] at h
  obtain ⟨_, n, q, hq, hI⟩ := h
  exact RingHom.isKoszulRegularIdeal_ker_of_surjective_mvPolynomial q hq hI p hp

/-- The same statement for a presentation by a polynomial ring over a polynomial ring. -/
private theorem isKoszulRegularIdeal_ker_mvPolynomial_mvPolynomial
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type w} {κ : Type x} [_root_.Finite ι] [_root_.Finite κ]
    (p : MvPolynomial ι (MvPolynomial κ R) →ₐ[R] S)
    (hp : Function.Surjective p)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap R S)) :
    Ideal.IsKoszulRegular (RingHom.ker p.toRingHom) := by
  let e := MvPolynomial.sumAlgEquiv R ι κ
  have hreg := isKoszulRegularIdeal_ker_of_isLocalCompleteIntersection
    (p.comp e.toAlgHom) (hp.comp e.surjective) h
  have hmap := isKoszulRegularIdeal_map_ringEquiv' e.toRingEquiv hreg
  change Ideal.IsKoszulRegular
    ((RingHom.ker (p.toRingHom.comp e.toRingEquiv.toRingHom)).map e.toRingEquiv.toRingHom) at hmap
  rwa [← RingHom.comap_ker,
    Ideal.map_comap_of_surjective e.toRingEquiv.toRingHom e.surjective] at hmap

/-- Localizing a polynomial presentation `p` away from `h` presents the localization
`S_{p h}` by `P[T]`, and the kernel of the localized presentation maps onto the extension of
`ker p`. -/
private theorem map_ker_localization_presentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (p : MvPolynomial (Fin n) R →ₐ[R] S)
    (h : MvPolynomial (Fin n) R) :
    let P := MvPolynomial (Fin n) R
    let α : MvPolynomial Unit P →ₐ[P] Localization.Away h :=
      MvPolynomial.aeval (fun _ ↦ IsLocalization.Away.invSelf h)
    let β := (IsLocalization.Away.mapₐ (Localization.Away h)
      (Localization.Away (p h)) p h).comp (α.restrictScalars R)
    (RingHom.ker β.toRingHom).map α.toRingHom =
      (RingHom.ker p.toRingHom).map (algebraMap P (Localization.Away h)) := by
  dsimp only
  let α : MvPolynomial Unit (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R]
      Localization.Away h := MvPolynomial.aeval (fun _ ↦ IsLocalization.Away.invSelf h)
  have hα : Function.Surjective α :=
    (Algebra.Generators.localizationAway (Localization.Away h) h).aeval_val_surjective
  change (RingHom.ker ((Localization.awayMap p.toRingHom h).comp α.toRingHom)).map
    α.toRingHom = _
  rw [← RingHom.comap_ker, Ideal.map_comap_of_surjective α.toRingHom hα]
  exact IsLocalization.ker_map (Localization.Away (p h)) p.toRingHom
    (Submonoid.map_powers p.toRingHom h)

/-- The localization relation `h * T - 1` is a Koszul-regular element of `R[T]`. -/
private theorem isKoszulRegular_singleton_C_mul_X_sub_one
    {R : Type u} [CommRing R] (h : R) :
    Koszul.IsKoszulRegular
      (fun _ : Fin 1 ↦ MvPolynomial.C h * MvPolynomial.X () - (1 : MvPolynomial Unit R)) := by
  let t : MvPolynomial Unit R := MvPolynomial.C h * MvPolynomial.X () - 1
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  have ht : e t = Polynomial.C h * Polynomial.X - 1 := by
    simp [e, t, MvPolynomial.uniqueAlgEquiv_apply]
  have hreg : IsRegular (e t) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
    simpa [ht] using (isUnit_neg_one : IsUnit (-1 : R)).mem_nonZeroDivisors
  have hsmul : IsSMulRegular (MvPolynomial Unit R) t := by
    intro x y hxy
    apply e.injective
    apply hreg.left
    simpa only [smul_eq_mul, map_mul] using congrArg e hxy
  apply (Koszul.isKoszulRegularOn_self_iff _).mp
  apply Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
  simpa only [List.ofFn_const, List.replicate_succ, List.replicate_zero] using
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff (MvPolynomial Unit R) t).mpr hsmul

/-- If a family generating the unit ideal is the image of `h` under a surjection, some `h i` avoids
a given prime containing the kernel. -/
private theorem exists_notMem_of_span_range_eq_top
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (p : PrimeSpectrum R) (hp : RingHom.ker f ≤ p.asIdeal)
    {ι : Type*} (g : ι → S) (hspan : Ideal.span (Set.range g) = ⊤)
    (h : ι → R) (hh : ∀ i, f (h i) = g i) : ∃ i, h i ∉ p.asIdeal := by
  have hprime : (p.asIdeal.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hp
  have hex : ∃ i, g i ∉ p.asIdeal.map f := by
    by_contra! hn
    apply hprime.ne_top
    apply top_unique
    rw [← hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hn i
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, fun hmem ↦ hi ?_⟩
  rw [← hh i]
  exact Ideal.mem_map_of_mem f hmem

open MvPolynomial in
/-- If `J ⊆ P[T]` is Koszul-regular, contains `h * T - 1`, and maps to the extension of `I` in
`P_h`, then `I` is Koszul-regular locally at every prime containing it and not containing `h`. -/
private theorem exists_koszulRegular_of_map_presentation_away
    {P : Type u} [CommRing P] (I : Ideal P) (q : PrimeSpectrum P) (hIq : I ≤ q.asIdeal)
    (h : P) (hh : h ∉ q.asIdeal) (J : Ideal (MvPolynomial Unit P))
    (hJ : Ideal.IsKoszulRegular J) (hJt : C h * X () - 1 ∈ J)
    (hmap : J.map (MvPolynomial.aeval (fun _ ↦ IsLocalization.Away.invSelf h) :
      MvPolynomial Unit P →ₐ[P] Localization.Away h).toRingHom =
        I.map (algebraMap P (Localization.Away h))) :
    ∃ b : P, b ∉ q.asIdeal ∧
      ∃ (r : ℕ) (f : Fin r → Localization.Away b), Koszul.IsKoszulRegular f ∧
        I.map (algebraMap P (Localization.Away b)) = Ideal.span (Set.range f) := by
  classical
  let A := MvPolynomial Unit P
  let Ph := Localization.Away h
  let α : A →ₐ[P] Ph := MvPolynomial.aeval (fun _ ↦ IsLocalization.Away.invSelf h)
  have hα : Function.Surjective α :=
    (Algebra.Generators.localizationAway Ph h).aeval_val_surjective
  have hker : RingHom.ker α.toRingHom = Ideal.span {C h * X () - 1} :=
    Algebra.Generators.ker_localizationAway (S := Ph) h
  let q' : Ideal Ph := q.asIdeal.map (algebraMap P Ph)
  obtain ⟨hq', hq'c⟩ := isPrime_map_and_comap_away Ph hh (p := q.asIdeal)
  let Q : PrimeSpectrum A := ⟨q'.comap α.toRingHom, Ideal.comap_isPrime _ _⟩
  have hJQ : J ≤ Q.asIdeal := by
    refine le_trans (Ideal.le_comap_map (f := α.toRingHom)) (Ideal.comap_mono ?_)
    rw [hmap]
    exact Ideal.map_mono hIq
  have hCh : (C h : A) ∉ Q.asIdeal := by
    intro hmem
    apply hh
    rw [← hq'c]
    change algebraMap P Ph h ∈ q'
    have hmem' : α (C h) ∈ q' := hmem
    rwa [MvPolynomial.aeval_C] at hmem'
  obtain ⟨s, hs, r, f, hf, hspan⟩ := hJ Q hJQ
  let As := Localization.Away s
  let Qs : Ideal As := Q.asIdeal.map (algebraMap A As)
  obtain ⟨_, hQs⟩ := isPrime_map_and_comap_away As hs (p := Q.asIdeal)
  let K := Qs.ResidueField
  let D0 : Derivation P A K := (Algebra.linearMap A K).compDer (pderiv ())
  have : Algebra.FormallyEtale A As := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
  obtain ⟨D, hD⟩ := exists_derivation_of_formallyEtale (R := P) (A := A) (B := As) (K := K) D0
  let t : A := C h * X () - 1
  have htmem : algebraMap A As t ∈ Ideal.span (Set.range f) := by
    rw [← hspan]; exact Ideal.mem_map_of_mem _ hJt
  have hzero : ∀ i, algebraMap As K (f i) = 0 := by
    intro i
    rw [Ideal.algebraMap_residueField_eq_zero]
    have : f i ∈ J.map (algebraMap A As) := hspan ▸ Ideal.subset_span ⟨i, rfl⟩
    exact Ideal.map_mono hJQ this
  have hDt : D (algebraMap A As t) ≠ 0 := by
    rw [hD]
    have h0 : D0 t = algebraMap A K (C h) := by
      simp only [D0, t, Derivation.coe_comp, LinearMap.coe_comp, Function.comp_apply, map_sub,
        Derivation.map_one_eq_zero, sub_zero]
      have hp : pderiv () (C h * X () : A) = C h := by
        rw [pderiv_C_mul, pderiv_X_self, mul_one]
      exact congrArg (algebraMap A K) hp
    rw [h0, IsScalarTower.algebraMap_apply A As K, Ne, Ideal.algebraMap_residueField_eq_zero,
      ← Ideal.mem_comap, hQs]
    exact hCh
  obtain ⟨c, hc, r', g, hg, hgspan⟩ :=
    exists_koszulRegular_append_localization_of_derivation f hf _ htmem D hzero hDt
  obtain ⟨c0, hc0⟩ := exists_integer_associated_of_isLocalization (Submonoid.powers s) c
  have hc0Q : c0 ∉ Q.asIdeal :=
    notMem_of_associated_algebraMap hc0 fun hm ↦ hc (Ideal.algebraMap_residueField_eq_zero.mpr hm)
  let w := s * c0
  have hwQ : w ∉ Q.asIdeal := fun hmem ↦ (Q.isPrime.mem_or_mem hmem).elim hs hc0Q
  have : IsLocalization.Away w (Localization.Away c) :=
    IsLocalization.Away.mul_of_associated s c0 c hc0
  let Lc := Localization.Away c
  let Pw := Localization.Away (α w)
  let ψ : Lc →+* Pw := IsLocalization.Away.map Lc Pw α.toRingHom w
  have hψ : Function.Surjective ψ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective (Aₚ := Lc) (Bₚ := Pw) (f := α) w hα
  have hψker : RingHom.ker ψ = Ideal.span {algebraMap A Lc t} := by
    have := IsLocalization.ker_map (M := Submonoid.powers w) (S := Lc) Pw α.toRingHom
      (Submonoid.map_powers α.toRingHom w)
    change RingHom.ker (IsLocalization.map Pw α.toRingHom _) = _
    rw [this, hker, Ideal.map_span, Set.image_singleton]
  have ht' : Koszul.IsKoszulRegular (fun _ : Fin 1 ↦ algebraMap A Lc t) :=
    Koszul.isKoszulRegular_map_of_flat (fun _ : Fin 1 ↦ t)
      (isKoszulRegular_singleton_C_mul_X_sub_one h)
  have htc : algebraMap As Lc (algebraMap A As t) = algebraMap A Lc t :=
    (IsScalarTower.algebraMap_apply A As Lc t).symm
  rw [htc] at hg hgspan
  have hψker' : RingHom.ker ψ =
      Ideal.span (Set.range (fun _ : Fin 1 ↦ algebraMap A Lc t)) := by
    rw [hψker, Set.range_const]
  have hreg := isKoszulRegular_map_of_ker_eq_span' ψ hψ _ g hψker' ht' hg
  have hJL : J.map (algebraMap A Lc) =
      Ideal.span (Set.range (Fin.append (fun _ : Fin 1 ↦ algebraMap A Lc t) g)) := by
    rw [hgspan, ← hspan, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hψcomp : ψ.comp (algebraMap A Lc) = (algebraMap Ph Pw).comp α.toRingHom :=
    IsLocalization.map_comp _
  have hIPw : I.map (algebraMap P Pw) = Ideal.span (Set.range (fun j ↦ ψ (g j))) := by
    have h1 : I.map (algebraMap P Pw) = (J.map (algebraMap A Lc)).map ψ := by
      rw [Ideal.map_map, hψcomp, ← Ideal.map_map, hmap, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [h1, hJL, Ideal.map_span, ← Set.range_comp]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j =>
        have : ψ (algebraMap A Lc t) = 0 := by
          rw [← RingHom.mem_ker, hψker]; exact Ideal.mem_span_singleton_self _
        simp [Fin.append_left, this]
      | right j => exact Ideal.subset_span ⟨j, by simp⟩
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨Fin.natAdd 1 j, by simp⟩
  obtain ⟨b, hb, f', hf', hspan'⟩ :=
    exists_koszulRegular_of_associated_away h I q hh (s := α w) hwQ _ hreg hIPw
  exact ⟨b, hb, r', f', hf', hspan'⟩

/-- **Stacks 07D1.** If finitely many elements `g j` generate the unit ideal of `S` and every
composite from `R` to the localization `S_{g j}` is a local complete intersection, then the
original ring homomorphism `R → S` is a local complete intersection. -/
@[stacks 07D1]
public theorem isLocalCompleteIntersection_of_localization_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    {m : ℕ} (g : Fin m → S) (hspan : Ideal.span (Set.range g) = ⊤)
    (hlocal : ∀ j, RingHom.IsLocalCompleteIntersection
      ((algebraMap S (Localization.Away (g j))).comp f)) :
    RingHom.IsLocalCompleteIntersection f := by
  have hft : f.FiniteType := finiteType_of_localization_away f g hspan (fun j ↦ (hlocal j).1)
  refine ⟨hft, ?_⟩
  let := f.toAlgebra
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  refine ⟨n, p, hp, ?_⟩
  choose h hh using fun j ↦ hp (g j)
  intro q hq
  obtain ⟨j, hj⟩ := exists_notMem_of_span_range_eq_top p.toRingHom hp q hq _ hspan h hh
  let P := MvPolynomial (Fin n) R
  let α : MvPolynomial Unit P →ₐ[P] Localization.Away (h j) :=
    MvPolynomial.aeval (fun _ ↦ IsLocalization.Away.invSelf (h j))
  have hα : Function.Surjective α :=
    (Algebra.Generators.localizationAway (Localization.Away (h j)) (h j)).aeval_val_surjective
  let μ := IsLocalization.Away.mapₐ (Localization.Away (h j)) (Localization.Away (p (h j))) p (h j)
  let β := μ.comp (α.restrictScalars R)
  have hβ : Function.Surjective β :=
    (IsLocalization.Away.mapₐ_surjective_of_surjective (Aₚ := Localization.Away (h j))
      (Bₚ := Localization.Away (p (h j))) (f := p) (h j) hp).comp hα
  have hloc : RingHom.IsLocalCompleteIntersection
      (algebraMap R (Localization.Away (p (h j)))) := by
    have h1 := hlocal j
    rw [← hh j] at h1
    exact h1
  have hJ := isKoszulRegularIdeal_ker_mvPolynomial_mvPolynomial β hβ hloc
  have hJt : MvPolynomial.C (h j) * MvPolynomial.X () - 1 ∈ RingHom.ker β.toRingHom := by
    have hmem : MvPolynomial.C (h j) * MvPolynomial.X () - 1 ∈ RingHom.ker α.toRingHom := by
      have hk : RingHom.ker α.toRingHom = _ :=
        Algebra.Generators.ker_localizationAway (S := Localization.Away (h j)) (h j)
      rw [hk]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hmem ⊢
    change μ (α _) = 0
    rw [show α _ = 0 from hmem, map_zero]
  exact exists_koszulRegular_of_map_presentation_away (RingHom.ker p.toRingHom) q hq (h j) hj
    _ hJ hJt (map_ker_localization_presentation p (h j))

end LocalOnTarget

section SyntomicCriterion

universe u v w

open MvPolynomial TensorProduct CategoryTheory

/-! ## Tag 07D2: the relations of a relative global complete intersection are Koszul-regular -/

/-! ### The fibre over a field: the relations are a regular sequence (Stacks 00R9) -/

/-- Let `k` be a field and `f₁, …, f_c ∈ k[xᵢ]` (finitely many variables) cut out a closed subset
of dimension at most `n - c`, `n` the number of variables. Then the `fⱼ` form a regular sequence
in the local ring of `k[xᵢ]` at any prime containing them. -/
private lemma isRegular_of_ringKrullDim_le {k : Type*} [Field k] {ι : Type*} [_root_.Finite ι]
    {c : ℕ} (f : Fin c → MvPolynomial ι k)
    (hdim :
      ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) + (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞))
    (q : Ideal (MvPolynomial ι k)) [q.IsPrime] (hq : Ideal.span (Set.range f) ≤ q) (Sq : Type*)
    [CommRing Sq] [Algebra (MvPolynomial ι k) Sq] [IsLocalization.AtPrime Sq q] :
    RingTheory.Sequence.IsRegular Sq ((List.ofFn f).map (algebraMap (MvPolynomial ι k) Sq)) := by
  have hk :
    ∀ (p : Ideal k) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun _ _ => isMaximalCohenMacaulay_self_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hS :
    ∀ (p : Ideal (MvPolynomial ι k)) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun p _ =>
    Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial hk p
      (Localization.AtPrime p)
  have hd : ringKrullDim (MvPolynomial ι k) = ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Semifield.toIsField k), zero_add]
  have hlen : (List.ofFn f).length = c := List.length_ofFn
  have hne : Ideal.ofList (List.ofFn f) ≠ ⊤ := by
    rw [Ideal.ofList_ofFn]
    exact fun h => Ideal.IsPrime.ne_top ‹q.IsPrime› (top_le_iff.mp (h ▸ hq))
  refine
    (Module.IsMaximalCohenMacaulay.ringKrullDim_quotient_add_length_eq_and_isRegular (k := k) hS
          (TopologicalSpace.Equidimensional.of_preirreducibleSpace _) (Nat.card ι) hd
          (List.ofFn f) hne ?_).2
      q (by rwa [Ideal.ofList_ofFn]) Sq
  rw [Ideal.ofList_ofFn, hlen]
  exact hdim

/-! ### Descent to a finite type `ℤ`-subalgebra -/

/-- A finite family of polynomials is defined over a Noetherian subalgebra of the
coefficient ring.  The subalgebra is generated by the finitely many coefficients. -/
private lemma exists_noetherian_model {R : Type*} [CommRing R] {ι α : Type*}
    [_root_.Finite α] (g : α → MvPolynomial ι R) :
    ∃ (R₀ : Subalgebra ℤ R) (g₀ : α → MvPolynomial ι R₀),
      IsNoetherianRing R₀ ∧ ∀ i, MvPolynomial.map (algebraMap R₀ R) (g₀ i) = g i := by
  classical
  let _ := Fintype.ofFinite α
  let T : Finset R :=
    Finset.univ.biUnion fun i : α =>
      (g i).support.image fun d => MvPolynomial.coeff d (g i)
  let R₀ : Subalgebra ℤ R := Algebra.adjoin ℤ (T : Set R)
  have hmem (i : α) (d : ι →₀ ℕ) (hd : d ∈ (g i).support) :
      MvPolynomial.coeff d (g i) ∈ R₀ := by
    apply Algebra.subset_adjoin
    simp only [Finset.mem_coe, T, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_image_of_mem _ hd⟩
  have hpre (i : α) :
      ∃ p : MvPolynomial ι R₀, MvPolynomial.map (algebraMap R₀ R) p = g i := by
    refine ⟨∑ d ∈ (g i).support,
      MvPolynomial.monomial d
        (if h : d ∈ (g i).support then
          (⟨MvPolynomial.coeff d (g i), hmem i d h⟩ : R₀) else 0), ?_⟩
    rw [map_sum]
    conv_rhs => rw [(g i).as_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [MvPolynomial.map_monomial]
    simp [hd]
  choose g₀ hg₀ using hpre
  have : Algebra.FiniteType ℤ R₀ := Algebra.FiniteType.adjoin_of_finite T.finite_toSet
  exact ⟨R₀, g₀, Algebra.FiniteType.isNoetherianRing ℤ R₀, hg₀⟩

private lemma map_noetherian_model_injective {R : Type*} [CommRing R]
    (R₀ : Subalgebra ℤ R) {ι : Type*} :
    Function.Injective
      (MvPolynomial.map (algebraMap R₀ R) : MvPolynomial ι R₀ → MvPolynomial ι R) :=
  MvPolynomial.map_injective _ fun _ _ h => Subtype.ext (by simpa using h)

/-- The dimension condition of a relative presentation, expressed for its relation ideal. -/
private lemma relation_fiber_dimension {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) (p : Ideal R) [p.IsPrime]
    [Nontrivial (p.Fiber S)] :
    ringKrullDim
          (MvPolynomial ι p.ResidueField ⧸
            Ideal.span (Set.range fun i ↦
              MvPolynomial.map (algebraMap R p.ResidueField) (P.relation i))) +
        (c : WithBot ℕ∞) = ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_fiber_eq_quotient P p]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    hP.ringKrullDim_fiber_add_card_eq_card p inferInstance

/-! ### The fibre ring of a localized polynomial algebra is a localization of `κ(p₀)[x]` -/

/-! ### The heart: the relations are a regular sequence in the local ring, over a Noetherian base
-/

/-- The local ring of a polynomial ring at a prime `q` is a flat local extension of the local ring
of the coefficients at the contraction of `q`. -/
private lemma isLocalHom_and_flat_localization_atPrime
    {R : Type*} [CommRing R] {ι : Type*} (q : Ideal (MvPolynomial ι R)) [q.IsPrime] :
    let := Localization.AtPrime.algebraOfLiesOver (Ideal.under R q) q
    IsLocalHom (algebraMap (Localization.AtPrime (Ideal.under R q)) (Localization.AtPrime q)) ∧
      Module.Flat (Localization.AtPrime (Ideal.under R q)) (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver (Ideal.under R q) q
  refine ⟨?_, ?_⟩
  · rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  · exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (Ideal.under R q))
      (Ideal.under R q).primeCompl (Localization.AtPrime q)).2
      (Module.Flat.trans R (MvPolynomial ι R) _)

/-- The dimension bound on the fibre makes the relations a regular sequence modulo the extension
of the contracted prime. -/
private lemma isRegular_quotient_map_under_of_ringKrullDim_le
    {R : Type*} [CommRing R] {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (f : Fin c → MvPolynomial ι R) (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Ideal.under R q).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Ideal.under R q).ResidueField) (f i))) +
          (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular
      (Localization.AtPrime q ⧸
        Ideal.map (algebraMap R (Localization.AtPrime q)) (Ideal.under R q))
      (((List.ofFn f).map (algebraMap (MvPolynomial ι R) (Localization.AtPrime q))).map
        (Ideal.Quotient.mk
          (Ideal.map (algebraMap R (Localization.AtPrime q)) (Ideal.under R q)))) := by
  let := MvPolynomial.FiberAtPrime.algebra q
  have := MvPolynomial.FiberAtPrime.isLocalization q
  have h := isRegular_of_ringKrullDim_le
    (fun i ↦ MvPolynomial.FiberAtPrime.residueMap q (f i)) hdim
    (MvPolynomial.FiberAtPrime.basePrime q)
    (Ideal.span_le.2
      (by
        rintro x ⟨i, rfl⟩
        exact MvPolynomial.FiberAtPrime.residueMap_mem_basePrime q
          (hq (Ideal.subset_span ⟨i, rfl⟩))))
    (MvPolynomial.FiberAtPrime q)
  simp only [List.map_ofFn, Function.comp_def, RingHom.algebraMap_toAlgebra,
    MvPolynomial.FiberAtPrime.ofResidueField_residueMap, MvPolynomial.FiberAtPrime.mk_apply] at h ⊢
  exact h

section Heart

variable {R₀ : Type*} [CommRing R₀] [IsNoetherianRing R₀] {ι : Type*} [_root_.Finite ι] {c : ℕ}

open MvPolynomial.FiberAtPrime (mk residueMap basePrime algebra isLocalization
  residueMap_mem_basePrime ofResidueField_residueMap) in
private lemma isRegular_localization (f : Fin c → MvPolynomial ι R₀)
    (Q : Ideal (MvPolynomial ι R₀)) [Q.IsPrime] (hQ : Ideal.span (Set.range f) ≤ Q) (p₀ : Ideal R₀)
    [p₀.IsPrime] (hp₀ : p₀ = Ideal.under R₀ Q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι p₀.ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦ MvPolynomial.map (algebraMap R₀ p₀.ResidueField) (f i))) +
          (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime Q)
      ((List.ofFn f).map (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime Q))) := by
  subst hp₀
  classical
  let : Algebra (Localization.AtPrime (Ideal.under R₀ Q)) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under R₀ Q) Q
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl (Localization.AtPrime Q) inferInstance
  have : IsNoetherianRing (Localization.AtPrime (Ideal.under R₀ Q)) :=
    IsLocalization.isNoetherianRing (Ideal.under R₀ Q).primeCompl
      (Localization.AtPrime (Ideal.under R₀ Q)) inferInstance
  obtain ⟨hlh, hflat⟩ := isLocalHom_and_flat_localization_atPrime Q
  refine
    (Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal (R :=
        Localization.AtPrime (Ideal.under R₀ Q)) ?_).1
  refine
    isRegular_quotient_congr (J₂ :=
      Ideal.map (algebraMap R₀ (Localization.AtPrime Q)) (Ideal.under R₀ Q)) ?_ _ ?_
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  · exact isRegular_quotient_map_under_of_ringKrullDim_le f Q hQ hdim

end Heart

/-! ### Dimension transfer along a change of base ring -/

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private lemma ringKrullDim_quotient_map_eq {k K : Type*} [Field k] [Field K] [Algebra k K]
    {ι : Type*} [_root_.Finite ι] {c : ℕ} (f : Fin c → MvPolynomial ι k) :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) =
      ringKrullDim
        (MvPolynomial ι K ⧸
          Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap k K) (f i))) := by
  have h1 :
    ringKrullDim (MvPolynomial ι k ⧸ Ideal.span (Set.range f)) =
      ringKrullDim (K ⊗[k] (MvPolynomial ι k ⧸ Ideal.span (Set.range f))) :=
    Algebra.IsPushout.ringKrullDim_eq k K
      (MvPolynomial ι k ⧸ Ideal.span (Set.range f))
      (K ⊗[k] (MvPolynomial ι k ⧸ Ideal.span (Set.range f)))
  obtain ⟨e⟩ := nonempty_algEquiv_tensor_quotient (R := k) K f
  rw [h1, ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

private lemma ringKrullDim_fiber_le_of_algebraMap {R₀ R : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] {ι : Type*} [_root_.Finite ι] {c : ℕ} (f₀ : Fin c → MvPolynomial ι R₀)
    (p : Ideal R) [p.IsPrime]
    (hdim :
      ringKrullDim
            (MvPolynomial ι p.ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map ((algebraMap R p.ResidueField).comp (algebraMap R₀ R))
                    (f₀ i))) +
          (c : WithBot ℕ∞) =
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    ringKrullDim
          (MvPolynomial ι (Ideal.under R₀ p).ResidueField ⧸
            Ideal.span
              (Set.range fun i ↦
                MvPolynomial.map (algebraMap R₀ (Ideal.under R₀ p).ResidueField) (f₀ i))) +
        (c : WithBot ℕ∞) ≤
      ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  let : Algebra (Ideal.under R₀ p).ResidueField p.ResidueField :=
    (Ideal.ResidueField.map (Ideal.under R₀ p) p (algebraMap R₀ R) rfl).toAlgebra
  have hcomp :
    (algebraMap (Ideal.under R₀ p).ResidueField p.ResidueField).comp
        (algebraMap R₀ (Ideal.under R₀ p).ResidueField) =
      (algebraMap R p.ResidueField).comp (algebraMap R₀ R) := by
    refine RingHom.ext fun r ↦ ?_
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      RingHom.comp_apply]
  have hmain :=
    ringKrullDim_quotient_map_eq (k := (Ideal.under R₀ p).ResidueField) (K := p.ResidueField)
      (fun i ↦ MvPolynomial.map (algebraMap R₀ _) (f₀ i))
  have hfam :
    (fun i ↦
        MvPolynomial.map (algebraMap (Ideal.under R₀ p).ResidueField p.ResidueField)
          (MvPolynomial.map (algebraMap R₀ (Ideal.under R₀ p).ResidueField) (f₀ i))) =
      fun i ↦ MvPolynomial.map ((algebraMap R p.ResidueField).comp (algebraMap R₀ R)) (f₀ i) := by
    funext i
    rw [MvPolynomial.map_map, hcomp]
  rw [hfam] at hmain
  rw [hmain]
  exact le_of_eq hdim

end BaseChange

/-- A Noetherian model inherits the required dimension bound from the fibre
over the original base.  Its relations are therefore regular at the contracted
prime. -/
private lemma isRegular_localization_noetherian_model
    {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]
    [IsNoetherianRing R₀] {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (f₀ : Fin c → MvPolynomial ι R₀)
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span
      (Set.range fun i ↦ MvPolynomial.map (algebraMap R₀ R) (f₀ i)) ≤ q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Ideal.under R q).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map
                    ((algebraMap R (Ideal.under R q).ResidueField).comp
                      (algebraMap R₀ R)) (f₀ i))) +
          (c : WithBot ℕ∞) = ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    let q₀ := q.comap (MvPolynomial.map (algebraMap R₀ R))
    RingTheory.Sequence.IsRegular (Localization.AtPrime q₀)
      ((List.ofFn f₀).map
        (algebraMap (MvPolynomial ι R₀) (Localization.AtPrime q₀))) := by
  set q₀ : Ideal (MvPolynomial ι R₀) :=
    q.comap (MvPolynomial.map (algebraMap R₀ R)) with hq₀def
  have : q₀.IsPrime := Ideal.comap_isPrime _ q
  have hq₀ : Ideal.span (Set.range f₀) ≤ q₀ := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hq (Ideal.subset_span ⟨i, rfl⟩)
  have hunder : Ideal.under R₀ (Ideal.under R q) = Ideal.under R₀ q₀ := by
    rw [Ideal.under, Ideal.under, Ideal.under, hq₀def, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun r ↦ ?_
    simp [MvPolynomial.algebraMap_eq]
  have hle := _root_.ringKrullDim_fiber_le_of_algebraMap' f₀ (Ideal.under R q) hdim
  exact isRegular_localization f₀ q₀ hq₀ _ hunder hle

/-- A prime containing the relation ideal gives a point in the corresponding fibre. -/
private lemma nontrivial_fiber_of_prime_over_relations
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c))
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span (Set.range P.relation) ≤ q) :
    Nontrivial ((Ideal.under R q).Fiber S) := by
  let f : P.Ring →+* S := algebraMap P.Ring S
  let m : Ideal S := q.map f
  have hker : RingHom.ker f ≤ q := by
    change P.ker ≤ q
    rw [← P.span_range_relation_eq_ker]
    exact hq
  have hm : m.IsPrime := by
    dsimp [m]
    exact @Ideal.map_isPrime_of_surjective P.Ring S (P.Ring →+* S)
      inferInstance inferInstance inferInstance inferInstance f
      P.toExtension.algebraMap_surjective q ‹q.IsPrime› hker
  have hcomap : m.comap f = q := by
    change (q.map f).comap f = q
    calc
      (q.map f).comap f = q ⊔ RingHom.ker f :=
        Ideal.comap_map_of_surjective' f P.toExtension.algebraMap_surjective q
      _ = q := sup_eq_left.mpr hker
  have hunder : Ideal.under R m = Ideal.under R q := by
    change m.comap (algebraMap R S) = q.comap (algebraMap R P.Ring)
    calc
      m.comap (algebraMap R S) =
          (m.comap f).comap (algebraMap R P.Ring) := by
            rw [Ideal.comap_comap, IsScalarTower.algebraMap_eq R P.Ring S]
      _ = q.comap (algebraMap R P.Ring) := by rw [hcomap]
  have hnt : Nontrivial ((Ideal.under R m).Fiber S) :=
    PrimeSpectrum.nonempty_iff_nontrivial.1
      ⟨PrimeSpectrum.primesOverOrderIsoFiber R S (Ideal.under R m)
        ⟨m, ⟨hm, ⟨rfl⟩⟩⟩⟩
  simpa only [← hunder] using hnt

/-- At a prime of a polynomial presentation over a Noetherian base, the fibre dimension
criterion makes the defining relations a regular sequence after localization. -/
private lemma relation_regular_at_prime_of_noetherian
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span (Set.range P.relation) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn P.relation).map
        (algebraMap (MvPolynomial ι R) (Localization.AtPrime q))) := by
  let _ : Nontrivial ((Ideal.under R q).Fiber S) :=
    nontrivial_fiber_of_prime_over_relations P q hq
  exact isRegular_localization P.relation q hq (Ideal.under R q) rfl
    (le_of_eq (relation_fiber_dimension P hP (Ideal.under R q)))

/-! ### Essential finite presentation of a localized polynomial algebra -/

/-- A local polynomial algebra is essentially of finite presentation over the corresponding
localization of its coefficient ring. -/
@[ega "IV 1.3.10" "special case"]
private lemma essentiallyOfFinitePresentation_atPrime_mvPolynomial
    {R : Type*} [CommRing R] {ι : Type*} [_root_.Finite ι]
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime] :
    let p := Ideal.under R q
    let := Localization.AtPrime.algebraOfLiesOver p q
    (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime q)).EssentiallyOfFinitePresentation := by
  let p := Ideal.under R q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := R) (S := Localization.AtPrime p)
  have htower : IsScalarTower R (Localization.AtPrime p)
      (MvPolynomial ι (Localization.AtPrime p)) := inferInstance
  have hfp : Algebra.FinitePresentation (Localization.AtPrime p)
      (MvPolynomial ι (Localization.AtPrime p)) := inferInstance
  let M : Submonoid (MvPolynomial ι R) :=
    (p.primeCompl).map (MvPolynomial.C : R →+* MvPolynomial ι R)
  have hM : M ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr
  have hloc : IsLocalization M (MvPolynomial ι (Localization.AtPrime p)) := inferInstance
  let ψ : MvPolynomial ι (Localization.AtPrime p) →+* Localization.AtPrime q :=
    MvPolynomial.eval₂Hom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (fun i => algebraMap (MvPolynomial ι R) (Localization.AtPrime q) (X i))
  let : Algebra (MvPolynomial ι (Localization.AtPrime p)) (Localization.AtPrime q) :=
    RingHom.toAlgebra' ψ (fun _ _ => mul_comm _ _)
  have : IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (Localization.AtPrime p))
      (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change (algebraMap (MvPolynomial ι R) (Localization.AtPrime q)) x =
      ψ ((algebraMap (MvPolynomial ι R) (MvPolynomial ι (Localization.AtPrime p))) x)
    have h : ψ.comp (algebraMap (MvPolynomial ι R)
        (MvPolynomial ι (Localization.AtPrime p))) =
        algebraMap (MvPolynomial ι R) (Localization.AtPrime q) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C,
          ψ, MvPolynomial.eval₂Hom_C]
        rw [← MvPolynomial.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply R (MvPolynomial ι R) (Localization.AtPrime q)]
        exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
          (Localization.AtPrime q) r).symm
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.algebraMap_def,
          MvPolynomial.map_X, ψ, MvPolynomial.eval₂Hom_X']
    exact (RingHom.congr_fun h x).symm
  have : IsScalarTower (Localization.AtPrime p) (MvPolynomial ι (Localization.AtPrime p))
      (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [MvPolynomial.algebraMap_eq,
      RingHom.algebraMap_toAlgebra' ψ (fun _ _ => mul_comm _ _)]
    exact (MvPolynomial.eval₂Hom_C _ _ x).symm
  have : IsLocalization (q.primeCompl.map
      (algebraMap (MvPolynomial ι R) (MvPolynomial ι (Localization.AtPrime p))))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le
      (MvPolynomial ι (Localization.AtPrime p)) (Localization.AtPrime q) M q.primeCompl hM
  change ∃ (A : Type _), ∃ (_ : CommRing A) (_ : Algebra (Localization.AtPrime p) A)
    (_ : Algebra A (Localization.AtPrime q))
    (_ : IsScalarTower (Localization.AtPrime p) A (Localization.AtPrime q))
    (_ : Algebra.FinitePresentation (Localization.AtPrime p) A) (T : Submonoid A),
    IsLocalization T (Localization.AtPrime q)
  exact ⟨MvPolynomial ι (Localization.AtPrime p), inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    q.primeCompl.map (algebraMap (MvPolynomial ι R)
      (MvPolynomial ι (Localization.AtPrime p))), inferInstance⟩

/-! ### Regularity at a prime over an arbitrary base -/

private lemma isRegular_quotient_smul_top
    {A : Type*} [CommRing A] (J : Ideal A) (fs : List A)
    (h : RingTheory.Sequence.IsRegular (A ⧸ J) (fs.map (Ideal.Quotient.mk J))) :
    RingTheory.Sequence.IsRegular (A ⧸ (J • (⊤ : Submodule A A))) fs := by
  have hJ : J • (⊤ : Submodule A A) = J := by
    rw [Ideal.smul_top_eq_map]
    simp
  let e : (A ⧸ (J • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotEquivOfEq _ _ hJ
  have hregA : RingTheory.Sequence.IsRegular (A ⧸ J) fs :=
    ((AddEquiv.refl (A ⧸ J)).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul (A ⧸ J) r).mp h
  exact (e.isRegular_congr fs).mpr hregA

open MvPolynomial.FiberAtPrime (mk residueMap basePrime algebra isLocalization
  residueMap_mem_basePrime ofResidueField_residueMap) in
private lemma isRegular_localization_general
    {R : Type*} [CommRing R] {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (f : Fin c → MvPolynomial ι R)
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q)
    (hdim :
      ringKrullDim
            (MvPolynomial ι (Ideal.under R q).ResidueField ⧸
              Ideal.span
                (Set.range fun i ↦
                  MvPolynomial.map (algebraMap R (Ideal.under R q).ResidueField) (f i))) +
          (c : WithBot ℕ∞) ≤
        ((Nat.card ι : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn f).map (algebraMap (MvPolynomial ι R) (Localization.AtPrime q))) := by
  classical
  let p := Ideal.under R q
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  obtain ⟨hlh, hflat⟩ := isLocalHom_and_flat_localization_atPrime q
  have hEFP : (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime q)).EssentiallyOfFinitePresentation :=
    essentiallyOfFinitePresentation_atPrime_mvPolynomial q
  refine
    (Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
      (R := Localization.AtPrime p) hEFP _ ?_).1
  have hJ : Ideal.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
      Ideal.map (algebraMap R (Localization.AtPrime q)) p := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  apply isRegular_quotient_smul_top
  exact isRegular_quotient_congr hJ _ (isRegular_quotient_map_under_of_ringKrullDim_le f q hq hdim)

private lemma relation_regular_at_prime
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [_root_.Finite ι] {c : ℕ}
    (P : Algebra.Presentation R S ι (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection)
    (q : Ideal (MvPolynomial ι R)) [q.IsPrime]
    (hq : Ideal.span (Set.range P.relation) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn P.relation).map
        (algebraMap (MvPolynomial ι R) (Localization.AtPrime q))) := by
  let _ : Nontrivial ((Ideal.under R q).Fiber S) :=
    nontrivial_fiber_of_prime_over_relations P q hq
  exact isRegular_localization_general P.relation q hq
    (le_of_eq (relation_fiber_dimension P hP (Ideal.under R q)))

/-! ### Koszul acyclicity and descent from localizations -/

/-- If one entry of a sequence is a unit, wedge multiplication by its basis vector contracts
the Koszul complex. -/
private lemma isKoszulRegular_of_isUnit {A : Type*} [CommRing A] {c : ℕ}
    (f : Fin c → A) (j : Fin c) (hj : IsUnit (f j)) : Koszul.IsKoszulRegular f := by
  rcases hj with ⟨u, hu⟩
  intro i hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g, Koszul.seqComplex_d]
  change LinearMap.ker (Koszul.d (Koszul.seqDual f) n) ≤
    LinearMap.range (Koszul.d (Koszul.seqDual f) (n + 1))
  intro x hx
  let v : Fin c → A := Pi.single j 1
  have hv : ExteriorAlgebra.ι A v ∈ ⋀[A]^1 (Fin c → A) := Koszul.ι_mem_one v
  have hmul : ExteriorAlgebra.ι A v * (x : ExteriorAlgebra A (Fin c → A)) ∈
      ⋀[A]^(n + 2) (Fin c → A) := by
    simpa only [show 1 + (n + 1) = n + 2 by omega] using
      (SetLike.mul_mem_graded hv x.property)
  let y : ⋀[A]^(n + 2) (Fin c → A) :=
    ⟨(↑u⁻¹ : A) • (ExteriorAlgebra.ι A v * (x : ExteriorAlgebra A (Fin c → A))),
      Submodule.smul_mem _ _ hmul⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  have hcycle : Koszul.contraction (Koszul.seqDual f) (x : ExteriorAlgebra A (Fin c → A))
      = 0 := by
    simpa only [Koszul.d_apply_coe, Submodule.coe_zero] using congrArg Subtype.val hx
  change Koszul.contraction (Koszul.seqDual f)
    ((↑u⁻¹ : A) • (ExteriorAlgebra.ι A v * (x : ExteriorAlgebra A (Fin c → A)))) = x
  rw [map_smul, CliffordAlgebra.contractLeft_ι_mul, hcycle, mul_zero, sub_zero]
  change (↑u⁻¹ : A) • (Koszul.seqDual f v • (x : ExteriorAlgebra A (Fin c → A))) = x
  simp [v, Koszul.seqDual_single, smul_smul, ← hu]

/-- Koszul regularity can be checked after localization at every maximal ideal. -/
private lemma isKoszulRegular_of_forall_atPrime {A : Type*} [CommRing A] {c : ℕ}
    (f : Fin c → A)
    (h : ∀ (q : Ideal A) [q.IsMaximal],
      Koszul.IsKoszulRegular (fun j => algebraMap A (Localization.AtPrime q) (f j))) :
    Koszul.IsKoszulRegular f := by
  apply (Koszul.isKoszulRegularOn_self_iff f).mp
  intro i hi
  rw [ModuleCat.isZero_iff_subsingleton]
  let H := (Koszul.seqComplexTensor f A).homology i
  refine Module.subsingleton_of_localization_maximal
    (fun q [q.IsMaximal] => Localization.AtPrime q ⊗[A] H)
    (fun q [q.IsMaximal] => TensorProduct.mk A (Localization.AtPrime q) H 1) ?_
  intro q hq
  let L := Localization.AtPrime q
  let g : Fin c → L := fun j => algebraMap A L (f j)
  have hL : Koszul.IsKoszulRegular g := h q
  have hOnL : Koszul.IsKoszulRegularOn g L :=
    (Koszul.isKoszulRegularOn_self_iff g).mpr hL
  have hCoeff : Limits.IsZero ((Koszul.seqComplexTensor g (L ⊗[A] A)).homology i) := by
    let e : (L ⊗[A] A) ≃ₗ[L] L := AlgebraTensorModule.rid A L L
    exact (hOnL i hi).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso (Koszul.seqComplexTensorCongr g e))
  obtain ⟨e⟩ := KoszulC.homology_baseChange_linearEquiv (S := L) f A i
  have : Subsingleton ((Koszul.seqComplexTensor g (L ⊗[A] A)).homology i) :=
    (ModuleCat.isZero_iff_subsingleton).mp hCoeff
  exact e.symm.toEquiv.subsingleton

/-- The relations in a polynomial presentation of a relative global complete intersection form a
Koszul-regular sequence in the polynomial ring. -/
@[stacks 07D2]
public theorem isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type w} [_root_.Finite ι] {c : ℕ} (P : Algebra.Presentation R S ι (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Koszul.IsKoszulRegular P.relation := by
  refine isKoszulRegular_of_forall_atPrime P.relation ?_
  intro q hq
  have : q.IsPrime := hq.isPrime
  by_cases hrel : Ideal.span (Set.range P.relation) ≤ q
  · have hreg := relation_regular_at_prime P hP q hrel
    exact (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (M := Localization.AtPrime q)
      (f := fun j => algebraMap (MvPolynomial ι R) (Localization.AtPrime q) (P.relation j))).2.2
      (by simpa only [List.map_ofFn, Function.comp_def] using hreg)
  · have hj : ∃ j, P.relation j ∉ q := by
      by_contra hn
      apply hrel
      apply Ideal.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact not_not.mp (not_exists.mp hn j)
    obtain ⟨j, hj⟩ := hj
    exact isKoszulRegular_of_isUnit _ j
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q
        (P.relation j)).mpr (by simpa [Ideal.primeCompl] using hj))

/-! ## Tag 07D3: the syntomic ring maps are the flat local complete intersections -/

/-! ### Finite presentation of a local complete intersection -/

/-- An ideal is finitely generated if it is finitely generated on a principal neighborhood
of every prime containing it. -/
private theorem fg_of_localization_away_at_primes
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      ∃ g : R, g ∉ p.asIdeal ∧ (I.map (algebraMap R (Localization.Away g))).FG) :
    I.FG := by
  let t : Set R := {g | (I.map (algebraMap R (Localization.Away g))).FG}
  apply Ideal.fg_of_localizationSpan t _ (fun g => g.property)
  by_contra ht
  obtain ⟨m, hm, htm⟩ := Ideal.exists_le_maximal (Ideal.span t) ht
  have := hm
  have hIm : I ≤ m := by
    intro x hx
    apply htm
    apply Ideal.subset_span
    change (I.map (algebraMap R (Localization.Away x))).FG
    have htop : I.map (algebraMap R (Localization.Away x)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hx)
        (IsLocalization.Away.algebraMap_isUnit x)
    rw [htop]
    exact Ideal.fg_top _
  obtain ⟨g, hgm, hg⟩ := hI ⟨m, inferInstance⟩ hIm
  exact hgm (htm (Ideal.subset_span hg))

/-- Koszul-regular ideals are finitely generated. -/
private theorem fg_of_isKoszulRegularIdeal
    {R : Type u} [CommRing R] {I : Ideal R}
    (hI : Ideal.IsKoszulRegular I) : I.FG := by
  apply fg_of_localization_away_at_primes I
  intro p hp
  obtain ⟨g, hgp, r, f, _, hf⟩ := hI p hp
  exact ⟨g, hgp, hf.symm ▸ Submodule.fg_span (Set.finite_range f)⟩

/-- Local complete intersection ring maps are of finite presentation. -/
private theorem finitePresentation_of_isLocalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : RingHom.IsLocalCompleteIntersection f) :
    let := f.toAlgebra
    Algebra.FinitePresentation R S := by
  let := f.toAlgebra
  obtain ⟨_, n, p, hp, hker⟩ := hf
  exact Algebra.FinitePresentation.of_surjective hp (fg_of_isKoszulRegularIdeal hker)

/-! ### Transport of Koszul regularity along flat maps and ring isomorphisms -/

/-- Changing the coefficient module preserves Koszul homology, including across universes. -/
theorem seqComplexTensor_homology_congr
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {c : ℕ} (f : Fin c → A) (e : M ≃ₗ[A] N) (i : ℕ) :
    Nonempty ((Koszul.seqComplexTensor f M).homology i ≃ₗ[A]
      (Koszul.seqComplexTensor f N).homology i) := by
  apply KoszulC.homologyTransport_of_degreewiseEquiv
    (fun n => TensorProduct.congr (LinearEquiv.refl A (⋀[A]^n (Fin c → A))) e) _ i
  intro n m
  by_cases h : m + 1 = n
  · subst n
    rw [Koszul.seqComplexTensor_d, Koszul.seqComplexTensor_d]
    intro x
    change (TensorProduct.map LinearMap.id e.toLinearMap)
        ((LinearMap.rTensor M (Koszul.d (Koszul.seqDual f) m)) x) =
      (LinearMap.rTensor N (Koszul.d (Koszul.seqDual f) m))
        ((TensorProduct.map LinearMap.id e.toLinearMap) x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · rw [HomologicalComplex.shape _ n m h, HomologicalComplex.shape _ n m h]
    intro x
    exact (TensorProduct.congr (LinearEquiv.refl A _) e).map_zero

/-- Flat extension of scalars preserves Koszul regularity of a sequence in the ring. -/
theorem isKoszulRegular_algebraMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {r : ℕ} (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular (fun i => algebraMap R S (f i)) := by
  have h := KoszulC.isKoszulRegular_baseChange (S := S) f R
    ((Koszul.isKoszulRegularOn_self_iff f).2 hf)
  apply (Koszul.isKoszulRegularOn_self_iff _).1
  intro i hi
  obtain ⟨e⟩ := seqComplexTensor_homology_congr (fun j => algebraMap R S (f j))
    (TensorProduct.AlgebraTensorModule.rid R S S) i
  have hz := h i hi
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  have := hz
  exact e.symm.toEquiv.subsingleton

/-- Ring isomorphisms preserve locally H₁-regular ideals. -/
private theorem isH1RegularIdeal_map_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R)
    (hI : Ideal.IsH1Regular I) :
    Ideal.IsH1Regular (I.map e.toRingHom) := by
  intro p hp
  let q := PrimeSpectrum.comap e.toRingHom p
  obtain ⟨g, hg, r, f, hf, hspan⟩ := hI q (Ideal.map_le_iff_le_comap.mp hp)
  let e' := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers g) (T := Submonoid.powers (e g))
    (Localization.Away g) (Localization.Away (e g)) e
    (Submonoid.map_powers e.toMonoidHom g)
  refine ⟨e g, hg, r, (fun i => e' (f i)), isH1Regular_map_ringEquiv e' f hf, ?_⟩
  have he : e'.toRingHom.comp (algebraMap R (Localization.Away g)) =
      (algebraMap S (Localization.Away (e g))).comp e.toRingHom := by
    ext x
    exact IsLocalization.ringEquivOfRingEquiv_eq
      (M := Submonoid.powers g) (T := Submonoid.powers (e g))
      (S := Localization.Away g) (Q := Localization.Away (e g)) (j := e)
      (Submonoid.map_powers e.toMonoidHom g) x
  rw [Ideal.map_map, ← he, ← Ideal.map_map, hspan, Ideal.map_span, ← Set.range_comp]
  rfl

/-- An ideal generated by a Koszul-regular sequence is Koszul-regular locally. -/
theorem isKoszulRegularIdeal_span
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (hf : Koszul.IsKoszulRegular f) :
    Ideal.IsKoszulRegular (Ideal.span (Set.range f)) := by
  intro p _
  refine ⟨1, p.isPrime.one_notMem, r,
    (fun i => algebraMap R (Localization.Away (1 : R)) (f i)),
    isKoszulRegular_algebraMap f hf, ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-! ### Local complete intersections assembled from principal neighborhoods -/

/-- A relative global complete intersection is a local complete intersection ring map. -/
private theorem isLocalCompleteIntersection_of_isRelativeGlobalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsRelativeGlobalCompleteIntersection R S) :
    RingHom.IsLocalCompleteIntersection (algebraMap R S) := by
  obtain ⟨n, c, P, hP⟩ := h.out
  have := P.finitePresentation_of_isFinite
  rw [RingHom.IsLocalCompleteIntersection, _root_.toAlgebra_algebraMap]
  refine ⟨RingHom.finiteType_algebraMap.mpr inferInstance,
    n, MvPolynomial.aeval P.val, P.aeval_val_surjective, ?_⟩
  change Ideal.IsKoszulRegular (RingHom.ker (MvPolynomial.aeval (R := R) P.val))
  rw [← P.ker_eq_ker_aeval_val]
  rw [← P.span_range_relation_eq_ker]
  exact isKoszulRegularIdeal_span P.relation
    (isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection P hP)

/-- Local complete intersection neighborhoods at every prime suffice. -/
private theorem isLocalCompleteIntersection_of_forall_exists_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (h : ∀ p : PrimeSpectrum S, ∃ g ∉ p.asIdeal,
      RingHom.IsLocalCompleteIntersection
        ((algebraMap S (Localization.Away g)).comp f)) :
    RingHom.IsLocalCompleteIntersection f := by
  classical
  let t : Set S := {g | RingHom.IsLocalCompleteIntersection
    ((algebraMap S (Localization.Away g)).comp f)}
  have ht : Ideal.span t = ⊤ := by
    by_contra ht
    obtain ⟨m, hm, htm⟩ := Ideal.exists_le_maximal (Ideal.span t) ht
    have := hm
    obtain ⟨g, hgm, hg⟩ := h ⟨m, inferInstance⟩
    exact hgm (htm (Ideal.subset_span hg))
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite t).mp ht
  let g : Fin s.card → S := fun i => (s.equivFin.symm i).val
  have hg : Set.range g = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).property
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [g]⟩
  exact isLocalCompleteIntersection_of_localization_away f g
    (hg ▸ hspan) (fun i => hs (hg ▸ Set.mem_range_self i))

/-! ### The fibres of a flat local complete intersection -/

/-- A H₁-regular ideal in a Noetherian ring is generated by a regular sequence
after localization at any prime containing it. -/
private theorem exists_isRegular_of_isH1RegularIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : Ideal.IsH1Regular I) (p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ fs : List (Localization.AtPrime p),
      RingTheory.Sequence.IsRegular (Localization.AtPrime p) fs ∧
        Ideal.ofList fs = I.map (algebraMap R (Localization.AtPrime p)) := by
  obtain ⟨g, hgp, r, f, hf, hspan⟩ := hI ⟨p, inferInstance⟩ hp
  let A := Localization.Away g
  let B := Localization.AtPrime p
  have hle : Submonoid.powers g ≤ p.primeCompl :=
    Submonoid.powers_le.mpr hgp
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A B _ _ hle
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A B _ _ hle
  have := IsLocalization.isLocalization_of_submonoid_le A B _ _ hle
  have : Module.Flat A B := IsLocalization.flat B (p.primeCompl.map (algebraMap R A))
  let f' : Fin r → B := fun i => algebraMap A B (f i)
  have hspan' : Ideal.span (Set.range f') = I.map (algebraMap R B) := by
    rw [IsScalarTower.algebraMap_eq R A B, ← Ideal.map_map, hspan,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hmem (i : Fin r) : f' i ∈ IsLocalRing.maximalIdeal B := by
    have h := Ideal.map_mono hp (f := algebraMap R B)
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal p B] at h
    exact h (hspan' ▸ Ideal.subset_span (Set.mem_range_self i))
  refine ⟨List.ofFn f', ?_, ?_⟩
  · exact ((Koszul.regular_koszulRegular_h1Regular_quasiRegular_tfae
      (M := B) f' hmem).2.out 3 1).mp (Koszul.isH1Regular_map_of_flat (S := B) f hf)
  · rw [Ideal.ofList, show {x | x ∈ List.ofFn f'} = Set.range f' by
      ext x; exact List.mem_ofFn' f' x]
    exact hspan'

/-- A polynomial presentation with locally H₁-regular kernel defines a local
complete intersection over a field. -/
private theorem isLocalCompleteIntersection_of_isH1RegularIdeal
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    {n : ℕ} (P : Algebra.Generators k S (Fin n))
    (hP : Ideal.IsH1Regular P.ker) :
    _root_.IsLocalCompleteIntersection k S := by
  let t : Set S := {g | _root_.IsGlobalCompleteIntersection k (Localization.Away g)}
  refine ⟨t, ?_, fun g hg => hg⟩
  by_contra ht
  obtain ⟨q, hq, htq⟩ := Ideal.exists_le_maximal (Ideal.span t) ht
  have := hq
  let p := q.comap (algebraMap P.Ring S)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : P.ker ≤ p := Ideal.ker_le_comap _
  obtain ⟨c, hc⟩ := P.exists_height_comap_eq q
  obtain ⟨g, hgq, hg⟩ := P.exists_isGlobalCompleteIntersection_away_of_exists_isRegular
    k S q c hc (Localization.AtPrime p)
    (exists_isRegular_of_isH1RegularIdeal hP p hp)
  exact hgq (htq (Ideal.subset_span hg))

/-- A flat quotient remains flat after localizing the ambient ring. -/
private theorem flat_localization_quotient
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal B) [Module.Flat R (B ⧸ I)] (g : B) :
    Module.Flat R ((Localization.Away g) ⧸ I.map (algebraMap B (Localization.Away g))) := by
  let Q := (Localization.Away g) ⧸ I.map (algebraMap B (Localization.Away g))
  have : Module.Flat (B ⧸ I) Q :=
    IsLocalization.flat Q (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers g))
  have : IsScalarTower R (B ⧸ I) Q :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  exact Module.Flat.trans R (B ⧸ I) Q

/-- Arbitrary base change preserves locally H₁-regular ideals with flat quotient. -/
private theorem isH1RegularIdeal_baseChange
    {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K] (I : Ideal B) [Module.Flat R (B ⧸ I)]
    (hI : Ideal.IsH1Regular I) :
    Ideal.IsH1Regular
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) := by
  intro p hp
  let inc : B →+* K ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
  let q : PrimeSpectrum B := PrimeSpectrum.comap inc p
  have hIq : I ≤ q.asIdeal := (Ideal.map_le_iff_le_comap).mp hp
  obtain ⟨g, hg, r, f, hf, hspan⟩ := hI q hIq
  let A := Localization.Away g
  let T := K ⊗[R] B
  let L := Localization.Away (inc g)
  let e : (A ⊗[R] K) ≃+* L :=
    (Algebra.TensorProduct.comm R A K).toRingEquiv.trans
      (IsLocalization.Away.tensorProductEquivTMulRight R K g A).toRingEquiv
  have hflat : Module.Flat R (A ⧸ Ideal.span (Set.range f)) := by
    have := flat_localization_quotient (R := R) I g
    exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlgOfEq R hspan).symm.toLinearEquiv
  have hreg :=
    (Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat
      (A := R) (A' := K) f hflat).2 hf
  let f' : Fin r → L := fun i => e (KoszulH1.fp (A := R) (A' := K) f i)
  refine ⟨inc g, hg, r, f', isH1Regular_map_ringEquiv e _ hreg, ?_⟩
  let j : A →+* L := e.toRingHom.comp
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := K)).toRingHom
  have hj : j.comp (algebraMap B A) = (algebraMap T L).comp inc := by
    apply RingHom.ext
    intro x
    change (IsLocalization.Away.tensorProductEquivTMulRight R K g A)
      (1 ⊗ₜ[R] algebraMap B A x) = algebraMap T L (1 ⊗ₜ[R] x)
    exact IsLocalization.Away.tensorProductEquivTMulRight_tmul
      (R := R) (S := K) (g := g) (B := A) (x := 1) (a := x)
  change Ideal.map (algebraMap T L) (Ideal.map inc I) = _
  rw [Ideal.map_map, ← hj, ← Ideal.map_map, hspan, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Base change of a polynomial presentation carries its kernel to the new kernel. -/
private theorem map_ker_baseChange
    {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] {ι : Type*} (P : Algebra.Generators R S ι) :
    P.ker.map (MvPolynomial.map (algebraMap R K)) = (P.baseChange K).ker := by
  let Q : Algebra.Presentation R S ι P.ker :=
    { toGenerators := P
      relation := Subtype.val
      span_range_relation_eq_ker := by simp }
  rw [← Q.span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
  exact (Q.baseChange K).span_range_relation_eq_ker

/-- The fibres of a flat local complete intersection ring map are local complete
intersections over the corresponding fields. -/
private theorem isLocalCompleteIntersection_baseChange_field
    {R : Type u} {S : Type v} {k : Type*} [CommRing R] [CommRing S] [Field k]
    [Algebra R S] [Algebra R k] [Module.Flat R S]
    (h : RingHom.IsLocalCompleteIntersection (algebraMap R S)) :
    _root_.IsLocalCompleteIntersection k (k ⊗[R] S) := by
  rw [RingHom.IsLocalCompleteIntersection, _root_.toAlgebra_algebraMap] at h
  obtain ⟨_, n, f, hf, hker⟩ := h
  let P := Algebra.Generators.ofAlgHom f hf
  have hP : Ideal.IsH1Regular P.ker := by
    rw [Algebra.Generators.ker_ofAlgHom]
    intro p hp
    obtain ⟨g, hg, r, a, ha, hspan⟩ := hker p hp
    exact ⟨g, hg, r, a, ha.isH1Regular, hspan⟩
  have : Module.Flat R (P.Ring ⧸ P.ker) :=
    Module.Flat.of_linearEquiv
      (Ideal.quotientKerAlgEquivOfSurjective P.aeval_val_surjective).toLinearEquiv
  have ht := isH1RegularIdeal_baseChange (R := R) (K := k) P.ker hP
  let e := MvPolynomial.algebraTensorAlgEquiv R k (σ := Fin n)
  have he : (P.baseChange k).ker.map e.symm.toRingHom =
      P.ker.map (Algebra.TensorProduct.includeRight (R := R) (A := k)) := by
    rw [← map_ker_baseChange P, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro x
    change e.symm (MvPolynomial.map (algebraMap R k) x) = 1 ⊗ₜ[R] x
    apply e.injective
    simp [e]
  apply isLocalCompleteIntersection_of_isH1RegularIdeal (P.baseChange k)
  rw [← he] at ht
  have hreg := isH1RegularIdeal_map_ringEquiv e.toRingEquiv _ ht
  have he' : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ :=
    RingHom.ext fun x => e.apply_symm_apply x
  rwa [Ideal.map_map, he', Ideal.map_id] at hreg

/-! ### Syntomicity -/

/-- A flat local complete intersection ring map is syntomic. -/
private theorem syntomic_of_flat_and_isLocalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (hflat : f.Flat) (hlci : RingHom.IsLocalCompleteIntersection f) :
    let := f.toAlgebra
    Algebra.Syntomic R S := by
  let := f.toAlgebra
  have : Module.Flat R S := hflat
  have := finitePresentation_of_isLocalCompleteIntersection f hlci
  refine ⟨inferInstance, inferInstance, fun p _ => ?_⟩
  exact isLocalCompleteIntersection_baseChange_field hlci

/-- Relative global complete intersection neighborhoods imply the ring-map property. -/
private theorem isLocalCompleteIntersection_of_relative_neighborhoods
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ p : PrimeSpectrum S, ∃ g ∉ p.asIdeal,
      Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g)) :
    RingHom.IsLocalCompleteIntersection (algebraMap R S) := by
  apply isLocalCompleteIntersection_of_forall_exists_away
  intro p
  obtain ⟨g, hg, hreg⟩ := h p
  refine ⟨g, hg, ?_⟩
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  exact isLocalCompleteIntersection_of_isRelativeGlobalCompleteIntersection hreg

/-- Syntomicity is preserved by an isomorphism of algebras. -/
public theorem syntomic_of_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) [Algebra.Syntomic R S] :
    Algebra.Syntomic R T where
  flat := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  finitePresentation := Algebra.FinitePresentation.equiv e
  isLocalCompleteIntersection_fiber p _ :=
    _root_.lci_transport p.ResidueField
      (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
        p.ResidueField) e)
      (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)

/-- **Stacks 07D3.** A ring homomorphism is syntomic if and only if it is flat and a local
complete intersection. -/
@[stacks 07D3]
public theorem syntomic_iff_flat_and_isLocalCompleteIntersection
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    letI := f.toAlgebra
    Algebra.Syntomic R S ↔ f.Flat ∧ RingHom.IsLocalCompleteIntersection f := by
  let := f.toAlgebra
  constructor
  · intro h
    let := h
    refine ⟨h.flat, ?_⟩
    apply isLocalCompleteIntersection_of_relative_neighborhoods
    intro q
    apply ((Algebra.exists_notMem_syntomic_tfae (q.asIdeal.under R) q.asIdeal).out 1 2).mp
    refine ⟨1, q.isPrime.one_notMem, ?_⟩
    exact syntomic_of_algEquiv
      ((IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars R)
  · rintro ⟨hflat, hlci⟩
    exact syntomic_of_flat_and_isLocalCompleteIntersection f hflat hlci

end SyntomicCriterion

end RingHom

end
