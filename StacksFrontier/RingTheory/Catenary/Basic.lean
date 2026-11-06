module

public import StacksFrontier.RingTheory.Catenary.Defs
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Catenary and universally catenary rings

A commutative ring `R` is *catenary* if for every pair of primes `p ⊆ q` the lengths of the chains
of primes from `p` to `q` are bounded and all maximal such chains have the same length. A
Noetherian ring is *universally catenary* if every algebra of finite type over it is catenary.

## Main definitions

* `IsCatenaryRing`: catenarity, phrased with `PrimeChain`.
* `IsUniversallyCatenaryRing`: every finite-type algebra over a Noetherian ring satisfies
  `IsCatenaryRing`.
* `Ring.IsCatenary`: catenarity, phrased with `LTSeries` and covering pairs.
* `Ring.IsUniversallyCatenary`: every finite-type algebra satisfies `Ring.IsCatenary`.

## Main results

* `isCatenaryRing_iff_quotient_minimalPrimes`,
  `isUniversallyCatenaryRing_iff_quotient_minimalPrimes`: a Noetherian ring is (universally)
  catenary if and only if its quotients by its minimal primes are.
* `localization_isUniversallyCatenary`: a localization of a Noetherian universally catenary ring
  is universally catenary.
* `catenary_iff_isDimensionFunction`: a Noetherian local ring `A` is catenary if and only if
  `p ↦ dim(A ⧸ p)` is a dimension function on its spectrum.
* `catenary_tfae`, `universallyCatenary_tfae`: a ring is (universally) catenary if and only if
  all its localizations at primes are, if and only if all its localizations at maximal ideals are.
* `universally_catenary`: an algebra essentially of finite type over a Noetherian universally
  catenary ring is universally catenary.
* `Ring.isCatenary_and_isUniversallyCatenary_of_surjective`: catenarity and universal catenarity
  pass to the target of a surjective ring map.
-/

@[expose] public section

@[expose] public section

universe u

/-! ## Main Definitions -/

namespace PrimeChain

variable {R : Type u} [CommRing R] {p q : PrimeSpectrum R}

end PrimeChain

/-- A commutative ring `R` is *catenary* if for every pair of primes `p ⊆ q` the lengths of all
finite chains of primes from `p` to `q` are bounded above, and any two maximal chains of primes
from `p` to `q` have the same length. -/
@[ega "0 16.1.4"]
def IsCatenaryRing (R : Type u) [CommRing R] : Prop :=
  ∀ p q : PrimeSpectrum R, p ≤ q →
    (∃ n : ℕ, ∀ c : PrimeChain R p q, c.length ≤ n) ∧
    (∀ c d : PrimeChain R p q, c.IsMaximal → d.IsMaximal → c.length = d.length)

/-- A Noetherian ring `R` is *universally catenary* if every `R`-algebra of finite type, in the
universe of `R`, is catenary. -/
@[ega "IV 5.6.2"]
def IsUniversallyCatenaryRing (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A], Algebra.FiniteType R A → IsCatenaryRing A

/-! ## Transfer of chains along quotient maps -/

/-- The catenary condition between a fixed pair of primes `a ≤ b`: the lengths of the chains from
`a` to `b` are bounded, and the maximal chains from `a` to `b` have equal length. -/
def LocalCatenary {R : Type u} [CommRing R] (a b : PrimeSpectrum R) : Prop :=
  (∃ n : ℕ, ∀ c : PrimeChain R a b, c.length ≤ n) ∧
    (∀ c d : PrimeChain R a b, c.IsMaximal → d.IsMaximal → c.length = d.length)

/-- `IsCatenaryRing R` says exactly that `LocalCatenary a b` holds for every pair of primes
`a ≤ b`. -/
theorem isCatenaryRing_iff_localCatenary (R : Type u) [CommRing R] :
    IsCatenaryRing R ↔ ∀ a b : PrimeSpectrum R, a ≤ b → LocalCatenary a b := by
  rfl

/-- For two primes `x, y` in `zeroLocus I`, covering in the subtype is equivalent to covering in
`PrimeSpectrum R`. -/
theorem covBy_subtype_zeroLocus_iff {R : Type u} [CommRing R] (I : Ideal R)
    (x y : ↥(PrimeSpectrum.zeroLocus (I : Set R))) :
    (x ⋖ y) ↔ ((x : PrimeSpectrum R) ⋖ (y : PrimeSpectrum R)) := by
  constructor
  · rintro ⟨hlt, hnb⟩
    refine ⟨Subtype.coe_lt_coe.mpr hlt, ?_⟩
    intro w hxw hwy
    have hxmem : I ≤ (x : PrimeSpectrum R).asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp x.property
    have hwmem : w ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [PrimeSpectrum.mem_zeroLocus]; exact le_trans hxmem (le_of_lt hxw)
    refine hnb (c := (⟨w, hwmem⟩ : ↥(PrimeSpectrum.zeroLocus (I:Set R))))
      (Subtype.coe_lt_coe.mp hxw) ?_
    exact Subtype.coe_lt_coe.mp
      (show (⟨w, hwmem⟩ : ↥(PrimeSpectrum.zeroLocus (I:Set R))).val < (y:PrimeSpectrum R) from hwy)
  · rintro ⟨hlt, hnb⟩
    refine ⟨Subtype.coe_lt_coe.mp hlt, ?_⟩
    intro w hxw hwy
    exact hnb (Subtype.coe_lt_coe.mpr hxw) (Subtype.coe_lt_coe.mpr hwy)

/-- Lift an `LTSeries` on `PrimeSpectrum R`, all of whose terms lie in `zeroLocus I`,
to an `LTSeries` on the subtype `↥(zeroLocus I)`. -/
noncomputable def liftSeries {R : Type u} [CommRing R] (I : Ideal R)
    (s : LTSeries (PrimeSpectrum R))
    (hmem : ∀ i, s.toFun i ∈ PrimeSpectrum.zeroLocus (I : Set R)) :
    LTSeries ↥(PrimeSpectrum.zeroLocus (I : Set R)) where
  length := s.length
  toFun i := ⟨s.toFun i, hmem i⟩
  step i := s.step i

/-- A prime chain from `a` to `b` in `R`, where `I ≤ a`, as a prime chain between the
corresponding primes of `R ⧸ I`. -/
noncomputable def forwardChain {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (c : PrimeChain R a b) :
    PrimeChain (R ⧸ I)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨a, hIa⟩)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨b, le_trans hIa hab⟩) := by
  set e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus I with he
  have hmem : ∀ i, c.series.toFun i ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro i
    rw [PrimeSpectrum.mem_zeroLocus]
    have hh : c.series.head ≤ c.series.toFun i := c.series.head_le i
    rw [c.head_eq] at hh
    exact le_trans hIa hh
  refine ⟨(liftSeries I c.series hmem).map e.symm e.symm.strictMono, ?_, ?_⟩
  · rw [LTSeries.head_map]; congr 1; apply Subtype.ext; exact c.head_eq
  · rw [LTSeries.last_map]; congr 1; apply Subtype.ext; exact c.last_eq

/-- `forwardChain` preserves the length of a chain. -/
theorem forwardChain_length {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (c : PrimeChain R a b) :
    (forwardChain I a b hIa hab c).length = c.length := rfl

/-- Every prime in a chain starting at `a ≥ I` lies in `zeroLocus I`. -/
private theorem chain_mem_zeroLocus {R : Type u} [CommRing R] (I : Ideal R)
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (c : PrimeChain R a b) (i : Fin (c.length + 1)) :
    c.series.toFun i ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [PrimeSpectrum.mem_zeroLocus]
  have hh : c.series.head ≤ c.series.toFun i := c.series.head_le i
  rw [c.head_eq] at hh
  exact le_trans hIa hh

/-- `forwardChain` sends maximal chains to maximal chains. -/
theorem forwardChain_isMaximal {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (c : PrimeChain R a b) (hc : c.IsMaximal) :
    (forwardChain I a b hIa hab c).IsMaximal := by
  intro i
  have key := hc i
  set e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus I with he
  rw [show (forwardChain I a b hIa hab c).series.toFun i.castSucc =
      e.symm ⟨c.series.toFun i.castSucc, chain_mem_zeroLocus I a b hIa c _⟩ from rfl,
      show (forwardChain I a b hIa hab c).series.toFun i.succ =
      e.symm ⟨c.series.toFun i.succ, chain_mem_zeroLocus I a b hIa c _⟩ from rfl]
  rw [apply_covBy_apply_iff e.symm, covBy_subtype_zeroLocus_iff]
  exact key

/-- A prime chain between the primes of `R ⧸ I` corresponding to `a` and `b`, as a prime chain
from `a` to `b` in `R`. -/
noncomputable def backwardChain {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (d : PrimeChain (R ⧸ I)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨a, hIa⟩)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨b, le_trans hIa hab⟩)) :
    PrimeChain R a b := by
  set e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus I with he
  refine ⟨d.series.map (fun p => (e p : PrimeSpectrum R))
    ((Subtype.strictMono_coe _).comp e.strictMono), ?_, ?_⟩
  · rw [LTSeries.head_map, d.head_eq, OrderIso.apply_symm_apply]
  · rw [LTSeries.last_map, d.last_eq, OrderIso.apply_symm_apply]

/-- `backwardChain` preserves the length of a chain. -/
theorem backwardChain_length {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (d : PrimeChain (R ⧸ I)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨a, hIa⟩)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨b, le_trans hIa hab⟩)) :
    (backwardChain I a b hIa hab d).length = d.length := rfl

/-- `backwardChain` sends maximal chains to maximal chains. -/
theorem backwardChain_isMaximal {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b)
    (d : PrimeChain (R ⧸ I)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨a, hIa⟩)
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨b, le_trans hIa hab⟩))
    (hd : d.IsMaximal) :
    (backwardChain I a b hIa hab d).IsMaximal := by
  intro i
  have key := hd i
  refine (covBy_subtype_zeroLocus_iff I _ _).mp ?_
  exact (apply_covBy_apply_iff (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)).mpr key

/-- A length-preserving, maximality-preserving map of chains transfers `LocalCatenary` back along
the map. -/
private theorem localCatenary_of_chain_map {R S : Type u} [CommRing R] [CommRing S]
    {a b : PrimeSpectrum R} {a' b' : PrimeSpectrum S} (φ : PrimeChain S a' b' → PrimeChain R a b)
    (hlen : ∀ c, (φ c).length = c.length) (hmax : ∀ c, c.IsMaximal → (φ c).IsMaximal) :
    LocalCatenary a b → LocalCatenary a' b' := by
  rintro ⟨⟨n, hn⟩, heq⟩
  refine ⟨⟨n, fun c => ?_⟩, fun c d hc hd => ?_⟩
  · rw [← hlen]; exact hn _
  · rw [← hlen c, ← hlen d]; exact heq _ _ (hmax c hc) (hmax d hd)

/-- Let `I` be a prime ideal of `R` and `a ≤ b` primes of `R` with `I ≤ a`. The catenary condition
between `a` and `b` in `R` is equivalent to the catenary condition between the corresponding primes
of `R ⧸ I`. -/
theorem localCatenary_quotient_iff {R : Type u} [CommRing R] (I : Ideal R) [I.IsPrime]
    (a b : PrimeSpectrum R) (hIa : I ≤ a.asIdeal) (hab : a ≤ b) :
    LocalCatenary a b ↔
      LocalCatenary
        ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨a, hIa⟩)
        ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).symm ⟨b, le_trans hIa hab⟩) := by
  exact ⟨localCatenary_of_chain_map (backwardChain I a b hIa hab)
      (backwardChain_length I a b hIa hab) (backwardChain_isMaximal I a b hIa hab),
    localCatenary_of_chain_map (forwardChain I a b hIa hab) (forwardChain_length I a b hIa hab)
      (forwardChain_isMaximal I a b hIa hab)⟩

/-! ## Quotients by minimal primes -/

/-- A Noetherian ring `R` is catenary if and only if `R ⧸ p` is catenary for every minimal prime
`p` of `R`. -/
@[stacks 0AUP "(1)", ega "0 16.1.4" "special case"]
theorem isCatenaryRing_iff_quotient_minimalPrimes
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsCatenaryRing R ↔
      ∀ p : Ideal R, (hp : p ∈ minimalPrimes R) →
        haveI : p.IsPrime := hp.1.1
        IsCatenaryRing (R ⧸ p) := by
  rw [isCatenaryRing_iff_localCatenary]
  constructor
  · intro hR p hp
    have : p.IsPrime := hp.left.left
    rw [isCatenaryRing_iff_localCatenary]
    intro qa qb hqab
    set e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus p with he
    have ha : p ≤ ((e qa : PrimeSpectrum R)).asIdeal := (e qa).property
    have hb : p ≤ ((e qb : PrimeSpectrum R)).asIdeal := (e qb).property
    have hab : (e qa : PrimeSpectrum R) ≤ (e qb : PrimeSpectrum R) :=
      Subtype.coe_le_coe.mpr (e.monotone hqab)
    have key := (localCatenary_quotient_iff p (e qa) (e qb) ha hab).mp (hR _ _ hab)
    have eqa : (⟨(e qa : PrimeSpectrum R), ha⟩ : ↥(PrimeSpectrum.zeroLocus (p : Set R))) = e qa :=
      Subtype.ext rfl
    have eqb : (⟨(e qb : PrimeSpectrum R), hb⟩ : ↥(PrimeSpectrum.zeroLocus (p : Set R))) = e qb :=
      Subtype.ext rfl
    rwa [eqa, eqb, OrderIso.symm_apply_apply, OrderIso.symm_apply_apply] at key
  · intro hQ a b hab
    obtain ⟨p, hp, hpa⟩ := Ideal.exists_minimalPrimes_le (J := a.asIdeal) bot_le
    have : p.IsPrime := hp.left.left
    rw [localCatenary_quotient_iff p a b hpa hab]
    exact hQ p hp _ _
      ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus p).symm.monotone (Subtype.mk_le_mk.mpr hab))

/-- A Noetherian ring `R` is universally catenary if and only if `R ⧸ p` is universally catenary
for every minimal prime `p` of `R`. -/
@[stacks 0AUP "(2)", ega "IV 5.6.3"]
theorem isUniversallyCatenaryRing_iff_quotient_minimalPrimes
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCatenaryRing R ↔
      ∀ p : Ideal R, (hp : p ∈ minimalPrimes R) →
        haveI : p.IsPrime := hp.1.1
        haveI : IsNoetherianRing (R ⧸ p) := inferInstance
        IsUniversallyCatenaryRing (R ⧸ p) := by
  constructor
  · intro hR p hp
    have : p.IsPrime := hp.left.left
    intro B _ _ hB
    let : Algebra R B := ((algebraMap (R ⧸ p) B).comp (algebraMap R (R ⧸ p))).toAlgebra
    have : IsScalarTower R (R ⧸ p) B :=
      IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _).symm
    have hRp : Algebra.FiniteType R (R ⧸ p) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R p)
        Ideal.Quotient.mk_surjective
    have hRB : Algebra.FiniteType R B := Algebra.FiniteType.trans hRp hB
    exact hR B hRB
  · intro hQ A _ _ hA
    have : Algebra.FiniteType R A := hA
    have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    rw [isCatenaryRing_iff_quotient_minimalPrimes A]
    intro q hq
    have : q.IsPrime := hq.left.left
    obtain ⟨p₀, hp₀, hp₀q⟩ :=
      Ideal.exists_minimalPrimes_le (J := (q.comap (algebraMap R A))) bot_le
    have : p₀.IsPrime := hp₀.left.left
    have hker : ∀ x ∈ p₀, (Ideal.Quotient.mk q).comp (algebraMap R A) x = 0 := fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hp₀q hx
    let f : R ⧸ p₀ →+* A ⧸ q :=
      Ideal.Quotient.lift p₀ ((Ideal.Quotient.mk q).comp (algebraMap R A)) hker
    let : Algebra (R ⧸ p₀) (A ⧸ q) := f.toAlgebra
    have : IsScalarTower R (R ⧸ p₀) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.FiniteType R (A ⧸ q) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R q)
        Ideal.Quotient.mk_surjective
    have : Algebra.FiniteType (R ⧸ p₀) (A ⧸ q) :=
      Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ p₀) (A ⧸ q)
    exact hQ p₀ hp₀ (A ⧸ q) inferInstance

/-! ## Localization -/

private theorem image_ssubset_of_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) {s t : Set α} (h : s ⊂ t) : f '' s ⊂ f '' t := by
  rw [Set.ssubset_iff_subset_ne] at h ⊢
  exact ⟨Set.image_mono h.left, fun he => h.right ((Set.image_eq_image hf).mp he)⟩

/-- Membership-aware transport of a `List.IsChain` along a relation implication
that is only known to hold between list members. -/
private theorem isChain_imp_mem {α : Type*} {Rr Ss : α → α → Prop} :
    ∀ {l : List α}, List.IsChain Rr l →
      (∀ a ∈ l, ∀ b ∈ l, Rr a b → Ss a b) → List.IsChain Ss l := by
  intro l
  induction l with
  | nil => intro _ _; exact List.IsChain.nil
  | cons x t ih =>
    intro hchain H
    cases t with
    | nil => exact List.IsChain.singleton x
    | cons y t' =>
      rw [List.isChain_cons] at hchain
      obtain ⟨hxy, htail⟩ := hchain
      have hxyrel : Rr x y := hxy y (by simp)
      refine List.IsChain.cons_cons (H x (by simp) y (by simp) hxyrel) ?_
      exact ih htail fun a ha b hb hab => H a (by simp [ha]) b (by simp [hb]) hab

/-- Catenarity is a topological property: it transfers across a homeomorphism. -/
theorem isCatenary_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hX : IrreducibleClosedsCodim.IsCatenarySpace X) :
    IrreducibleClosedsCodim.IsCatenarySpace Y := by
  rw [IrreducibleClosedsCodim.isCatenarySpace_iff_isIrreducibleChain] at hX ⊢
  intro T T' hT hTc hT' hT'c hTT'
  have himg : ∀ S : Set Y, IsIrreducible S → IsClosed S →
      IsIrreducible (e.symm '' S) ∧ IsClosed (e.symm '' S) := fun S hS hSc =>
    ⟨hS.image e.symm e.symm.continuous.continuousOn, (e.symm.isClosed_image).mpr hSc⟩
  obtain ⟨n, hle, hmax⟩ := hX (e.symm '' T) (e.symm '' T') (himg T hT hTc).1 (himg T hT hTc).2
    (himg T' hT' hT'c).1 (himg T' hT' hT'c).2 (Set.image_mono hTT')
  set f : Set Y → Set X := fun S => e.symm '' S with hf
  have chainX : ∀ c : List (Set Y), TopologicalSpace.IsIrreducibleChain T T' c →
      TopologicalSpace.IsIrreducibleChain (e.symm '' T) (e.symm '' T') (c.map f) := by
    rintro c ⟨hchain, hmem, hhead, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.isChain_map]
      exact hchain.imp fun a b hab => image_ssubset_of_injective e.symm.injective hab
    · intro S hS
      rw [List.mem_map] at hS
      obtain ⟨W, hW, rfl⟩ := hS
      exact himg W (hmem W hW).1 (hmem W hW).2
    · rw [List.head?_map, hhead]; rfl
    · rw [List.getLast?_map, hlast]; rfl
  refine ⟨n, fun c hc => ?_, fun c hc hcmax => ?_⟩
  · have := hle _ (chainX c hc); rwa [List.length_map] at this
  · have hmaxX : TopologicalSpace.IsIrreducibleChain.IsMaximal (c.map f) := by
      have hcmax' := hcmax
      unfold TopologicalSpace.IsIrreducibleChain.IsMaximal at hcmax' ⊢
      rw [List.isChain_map]
      refine hcmax'.imp fun A B hAB => ?_
      rintro ⟨S, hSi, hSc, hAS, hSB⟩
      refine hAB ⟨e '' S, hSi.image e e.continuous.continuousOn, (e.isClosed_image).mpr hSc, ?_, ?_⟩
      · have h := image_ssubset_of_injective e.injective hAS
        simpa [hf, Set.image_image] using h
      · have h := image_ssubset_of_injective e.injective hSB
        simpa [hf, Set.image_image] using h
    have := hmax _ (chainX c hc) hmaxX; rwa [List.length_map] at this

namespace CatenaryTransport

open Topology

variable {X : Type*} [TopologicalSpace X] {Y : Set X}

/-- The "up" transport of a subset of `Y` to `X`: closure of its image. -/
def up (C : Set ↥Y) : Set X := closure ((Subtype.val : ↥Y → X) '' C)

/-- `up C` is a closed subset of `X`. -/
lemma isClosed_up (C : Set ↥Y) : IsClosed (up C) := isClosed_closure

/-- The `up` transport of an irreducible subset of `Y` is irreducible in `X`. -/
lemma isIrreducible_up {C : Set ↥Y} (hC : IsIrreducible C) : IsIrreducible (up C) :=
  (hC.image _ (by fun_prop)).closure

/-- For a closed `C ⊆ Y`, `C = val⁻¹ (up C)`. -/
lemma preimage_up_of_isClosed {C : Set ↥Y} (hC : IsClosed C) :
    (Subtype.val : ↥Y → X) ⁻¹' up C = C := by
  rw [up, ← IsInducing.subtypeVal.closure_eq_preimage_closure_image C, hC.closure_eq]

/-- `up` is monotone for inclusion. -/
lemma up_mono {C D : Set ↥Y} (h : C ⊆ D) : up C ⊆ up D :=
  closure_mono (Set.image_mono h)

/-- Strict monotonicity of `up` on closed sets. -/
lemma up_strictMono {C D : Set ↥Y} (hCcl : IsClosed C) (hDcl : IsClosed D)
    (h : C ⊂ D) : up C ⊂ up D := by
  refine ⟨up_mono h.subset, ?_⟩
  intro hcontra
  apply h.not_subset
  have : (Subtype.val : ↥Y → X) ⁻¹' up D ⊆ (Subtype.val : ↥Y → X) ⁻¹' up C :=
    Set.preimage_mono hcontra
  rw [preimage_up_of_isClosed hCcl, preimage_up_of_isClosed hDcl] at this
  exact this

/-- The generic point of `up C` lies in `Y` when `Y` is stable under generalization. -/
lemma exists_genericPoint_up_mem [QuasiSober X]
    (hY : StableUnderGeneralization Y) {C : Set ↥Y} (hC : IsIrreducible C) :
    ∃ ξ, ξ ∈ Y ∧ IsGenericPoint ξ (up C) := by
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_up hC) (isClosed_up C)
  refine ⟨ξ, ?_, hξ⟩
  obtain ⟨c, hc⟩ := hC.nonempty
  have hmem : (c : X) ∈ up C := subset_closure (Set.mem_image_of_mem _ hc)
  rw [← hξ, ← specializes_iff_mem_closure] at hmem
  exact hY hmem c.property

/-- Given an irreducible closed `S` in `X` whose generic point `ξ` lies in `Y`, the preimage
`val⁻¹ S` is irreducible closed in `Y` with generic point `⟨ξ⟩` and `up (val⁻¹ S) = S`. -/
lemma down_of_genericPoint_mem {S : Set X} (hScl : IsClosed S) {ξ : X} (hξY : ξ ∈ Y)
    (hgen : IsGenericPoint ξ S) :
    IsIrreducible ((Subtype.val : ↥Y → X) ⁻¹' S) ∧ IsClosed ((Subtype.val : ↥Y → X) ⁻¹' S)
      ∧ IsGenericPoint (⟨ξ, hξY⟩ : ↥Y) ((Subtype.val : ↥Y → X) ⁻¹' S)
      ∧ up ((Subtype.val : ↥Y → X) ⁻¹' S) = S := by
  set p : ↥Y := ⟨ξ, hξY⟩ with hp
  have hgp : IsGenericPoint p ((Subtype.val : ↥Y → X) ⁻¹' S) := by
    unfold IsGenericPoint
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image {p}]
    have h1 : (Subtype.val : ↥Y → X) '' {p} = {ξ} := by simp [hp]
    rw [h1, hgen]
  refine ⟨?_, hScl.preimage_val, hgp, ?_⟩
  · rw [← hgp]; exact isIrreducible_singleton.closure
  · apply subset_antisymm
    · rw [up]; rw [hScl.closure_subset_iff]
      rintro x ⟨y, hy, rfl⟩; exact hy
    · rw [up]; nth_rewrite 1 [← hgen]
      apply closure_minimal _ isClosed_closure
      rw [Set.singleton_subset_iff]
      exact subset_closure ⟨p, hgen.mem, rfl⟩

/-- Transport of an irreducible chain `c` in `Y` to the mapped chain `c.map up` in `X`. -/
lemma isChain_map_up {c : List (Set ↥Y)} (hcl : ∀ C ∈ c, IsClosed C)
    (hch : List.IsChain (fun A B => A ⊂ B) c) :
    List.IsChain (fun A B => A ⊂ B) (c.map up) := by
  induction hch with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.isChain_singleton _
  | @cons_cons a b l hab hbl ih =>
      simp only [List.map_cons]
      apply List.IsChain.cons_cons
      · exact up_strictMono (hcl a (by simp)) (hcl b (by simp)) hab
      · exact ih (fun C hC => hcl C (by simp [hC]))

/-- Reflection of "no refinement between consecutive sets" from `Y` to `X`. -/
lemma no_refine_up [QuasiSober X] (hY : StableUnderGeneralization Y)
    {A B : Set ↥Y} (hAirr : IsIrreducible A) (hAcl : IsClosed A) (hBcl : IsClosed B)
    (hmax : ¬∃ S : Set ↥Y, IsIrreducible S ∧ IsClosed S ∧ A ⊂ S ∧ S ⊂ B) :
    ¬∃ S : Set X, IsIrreducible S ∧ IsClosed S ∧ up A ⊂ S ∧ S ⊂ up B := by
  rintro ⟨S, hSirr, hScl, hAS, hSB⟩
  apply hmax
  obtain ⟨η, hηY, hηgen⟩ := exists_genericPoint_up_mem hY hAirr
  have hηupA : η ∈ up A := hηgen.mem
  have hηS : η ∈ S := hAS.subset hηupA
  obtain ⟨ξ, hξgen⟩ := QuasiSober.sober hSirr hScl
  have hspec : ξ ⤳ η := by rw [specializes_iff_mem_closure, hξgen]; exact hηS
  have hξY : ξ ∈ Y := hY hspec hηY
  obtain ⟨hSYirr, hSYcl, hSYgen, hupSY⟩ := down_of_genericPoint_mem hScl hξY hξgen
  have hpreA : (Subtype.val : ↥Y → X) ⁻¹' up A = A := preimage_up_of_isClosed hAcl
  have hpreB : (Subtype.val : ↥Y → X) ⁻¹' up B = B := preimage_up_of_isClosed hBcl
  refine ⟨(Subtype.val : ↥Y → X) ⁻¹' S, hSYirr, hSYcl, ?_, ?_⟩
  · rw [← hpreA]
    refine ⟨Set.preimage_mono hAS.subset, ?_⟩
    intro hc
    have heq : (Subtype.val : ↥Y → X) ⁻¹' up A = (Subtype.val : ↥Y → X) ⁻¹' S :=
      Set.Subset.antisymm (Set.preimage_mono hAS.subset) hc
    apply hAS.ne
    calc up A = up ((Subtype.val : ↥Y → X) ⁻¹' up A) := by rw [hpreA]
      _ = up ((Subtype.val : ↥Y → X) ⁻¹' S) := by rw [heq]
      _ = S := hupSY
  · rw [← hpreB]
    refine ⟨Set.preimage_mono hSB.subset, ?_⟩
    intro hc
    have heq : (Subtype.val : ↥Y → X) ⁻¹' S = (Subtype.val : ↥Y → X) ⁻¹' up B :=
      Set.Subset.antisymm (Set.preimage_mono hSB.subset) hc
    apply hSB.ne
    calc S = up ((Subtype.val : ↥Y → X) ⁻¹' S) := hupSY.symm
      _ = up ((Subtype.val : ↥Y → X) ⁻¹' up B) := by rw [heq]
      _ = up B := by rw [hpreB]

/-- Transport of maximality of a chain from `Y` to `X`. -/
lemma maximal_map_up [QuasiSober X] (hY : StableUnderGeneralization Y)
    {c : List (Set ↥Y)} (hirrcl : ∀ C ∈ c, IsIrreducible C ∧ IsClosed C)
    (hmax : TopologicalSpace.IsIrreducibleChain.IsMaximal c) :
    TopologicalSpace.IsIrreducibleChain.IsMaximal (c.map up) := by
  unfold TopologicalSpace.IsIrreducibleChain.IsMaximal at *
  induction hmax with
  | nil => exact List.IsChain.nil
  | singleton a => exact List.isChain_singleton _
  | @cons_cons a b l hab hbl ih =>
      simp only [List.map_cons]
      apply List.IsChain.cons_cons
      · exact no_refine_up hY (hirrcl a (by simp)).left (hirrcl a (by simp)).right
          (hirrcl b (by simp)).right hab
      · exact ih (fun C hC => hirrcl C (by simp [hC]))

/-- A generization-stable subset of a quasi-sober catenary space is catenary. -/
theorem isCatenary_of_stableUnderGeneralization
    {X : Type*} [TopologicalSpace X] [QuasiSober X] (Y : Set X)
    (hY : StableUnderGeneralization Y)
    (hX : IrreducibleClosedsCodim.IsCatenarySpace X) :
    IrreducibleClosedsCodim.IsCatenarySpace (↥Y) := by
  rw [IrreducibleClosedsCodim.isCatenarySpace_iff_isIrreducibleChain] at hX ⊢
  intro T T' hTirr hTcl hT'irr hT'cl hTT'
  obtain ⟨n, hbound, hmaxlen⟩ :=
    hX (up T) (up T') (isIrreducible_up hTirr) (isClosed_up T)
      (isIrreducible_up hT'irr) (isClosed_up T') (up_mono hTT')
  have hmap : ∀ c, TopologicalSpace.IsIrreducibleChain T T' c →
      TopologicalSpace.IsIrreducibleChain (up T) (up T') (c.map up) := by
    rintro c ⟨hchain, hirrcl, hhead, hlast⟩
    refine ⟨isChain_map_up (fun C hC => (hirrcl C hC).right) hchain, ?_, ?_, ?_⟩
    · intro Sset hS
      rw [List.mem_map] at hS
      obtain ⟨A, hA, rfl⟩ := hS
      exact ⟨isIrreducible_up (hirrcl A hA).left, isClosed_up A⟩
    · rw [List.head?_map, hhead]; rfl
    · rw [List.getLast?_map, hlast]; rfl
  refine ⟨n, fun c hc => ?_, fun c hc hcmax => ?_⟩
  · simpa using hbound _ (hmap c hc)
  · simpa using hmaxlen _ (hmap c hc) (maximal_map_up hY hc.2.1 hcmax)

/-- Let `Y` be stable under generalization and let `S ⊇ T` be irreducible closed, where `T` meets
`Y`. Then the preimage of `S` in `Y` is irreducible and closed, and `up` recovers `S` from it. -/
lemma preimage_of_subset [QuasiSober X] (hY : StableUnderGeneralization Y) {T S : Set X}
    {y : X} (hyY : y ∈ Y) (hyT : y ∈ T) (hSirr : IsIrreducible S) (hScl : IsClosed S)
    (hTS : T ⊆ S) :
    IsIrreducible ((Subtype.val : ↥Y → X) ⁻¹' S) ∧ IsClosed ((Subtype.val : ↥Y → X) ⁻¹' S)
      ∧ up ((Subtype.val : ↥Y → X) ⁻¹' S) = S := by
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hSirr hScl
  have hξy : ξ ⤳ y := by rw [specializes_iff_mem_closure, hξ]; exact hTS hyT
  obtain ⟨h1, h2, -, h4⟩ := down_of_genericPoint_mem hScl (hY hξy hyY) hξ
  exact ⟨h1, h2, h4⟩

/-- Let `Y` be a generization-stable catenary subset of a quasi-sober space `X`, and `T ⊆ T'`
irreducible closed subsets of `X` with `T` meeting `Y`. Then the chains of irreducible closed
subsets from `T` to `T'` have bounded length and the maximal ones have a common length. -/
theorem exists_isIrreducibleChain_of_mem [QuasiSober X] (hY : StableUnderGeneralization Y)
    (hYc : IrreducibleClosedsCodim.IsCatenarySpace ↥Y) {T T' : Set X} (hTirr : IsIrreducible T)
    (hTcl : IsClosed T) (hT'irr : IsIrreducible T') (hT'cl : IsClosed T') (hTT' : T ⊆ T')
    {y : X} (hyY : y ∈ Y) (hyT : y ∈ T) :
    ∃ n : ℕ,
      (∀ c : List (Set X), TopologicalSpace.IsIrreducibleChain T T' c → c.length ≤ n + 1) ∧
      (∀ c : List (Set X), TopologicalSpace.IsIrreducibleChain T T' c →
        TopologicalSpace.IsIrreducibleChain.IsMaximal c → c.length = n + 1) := by
  set f : Set X → Set ↥Y := fun S => (Subtype.val : ↥Y → X) ⁻¹' S with hf
  have key := fun {S : Set X} => preimage_of_subset hY hyY hyT (S := S)
  obtain ⟨hTYi, hTYc, -⟩ := key hTirr hTcl subset_rfl
  obtain ⟨hT'Yi, hT'Yc, -⟩ := key hT'irr hT'cl hTT'
  rw [IrreducibleClosedsCodim.isCatenarySpace_iff_isIrreducibleChain] at hYc
  obtain ⟨n, hb, hm⟩ := hYc (f T) (f T') hTYi hTYc hT'Yi hT'Yc (Set.preimage_mono hTT')
  have hmem : ∀ c : List (Set X), TopologicalSpace.IsIrreducibleChain T T' c →
      ∀ S ∈ c, IsIrreducible S ∧ IsClosed S ∧ T ⊆ S := by
    rintro (_ | ⟨a, l⟩) ⟨hch, hirr, hhead, -⟩ S hS
    · simp at hS
    · obtain rfl : a = T := by simpa using hhead
      refine ⟨(hirr S hS).1, (hirr S hS).2, ?_⟩
      rcases List.mem_cons.1 hS with rfl | hS
      · exact subset_rfl
      · exact (List.pairwise_cons.1 hch.pairwise).1 S hS |>.subset
  have hchain : ∀ c : List (Set X), (hc : TopologicalSpace.IsIrreducibleChain T T' c) →
      TopologicalSpace.IsIrreducibleChain (f T) (f T') (c.map f) := by
    intro c hc
    refine ⟨?_, ?_, by rw [List.head?_map, hc.2.2.1]; rfl, by rw [List.getLast?_map, hc.2.2.2]; rfl⟩
    · rw [List.isChain_map]
      refine isChain_imp_mem hc.1 fun A hA B hB hAB => ⟨Set.preimage_mono hAB.subset, fun hBA => ?_⟩
      obtain ⟨hAi, hAc, hTA⟩ := hmem c hc A hA
      obtain ⟨hBi, hBc, hTB⟩ := hmem c hc B hB
      refine hAB.ne ?_
      rw [← (key hAi hAc hTA).2.2, ← (key hBi hBc hTB).2.2,
        Set.Subset.antisymm (Set.preimage_mono hAB.subset) hBA]
    · intro S hS
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hS
      obtain ⟨hAi, hAc, hTA⟩ := hmem c hc A hA
      exact ⟨(key hAi hAc hTA).1, (key hAi hAc hTA).2.1⟩
  refine ⟨n, fun c hc => ?_, fun c hc hcmax => ?_⟩
  · simpa using hb _ (hchain c hc)
  · suffices hmax : TopologicalSpace.IsIrreducibleChain.IsMaximal (c.map f) by
      simpa using hm _ (hchain c hc) hmax
    unfold TopologicalSpace.IsIrreducibleChain.IsMaximal at hcmax ⊢
    rw [List.isChain_map]
    refine isChain_imp_mem hcmax fun A hA B hB hAB => ?_
    rintro ⟨S, hSi, hSc, hAS, hSB⟩
    obtain ⟨hAi, hAc, hTA⟩ := hmem c hc A hA
    obtain ⟨hBi, hBc, hTB⟩ := hmem c hc B hB
    refine hAB ⟨up S, isIrreducible_up hSi, isClosed_up S, ?_, ?_⟩
    · simpa [hf, (key hAi hAc hTA).2.2] using up_strictMono (key hAi hAc hTA).2.1 hSc hAS
    · simpa [hf, (key hBi hBc hTB).2.2] using up_strictMono hSc (key hBi hBc hTB).2.1 hSB

end CatenaryTransport

/-- The primes disjoint from a submonoid `S` form a generization-stable subset of `Spec R`. -/
theorem stableUnderGeneralization_primesDisjointFrom (R : Type u) [CommRing R] (S : Submonoid R) :
    StableUnderGeneralization {p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal} :=
  fun _ _ hxy hx => Set.disjoint_left.2 fun _ haS hay =>
    Set.disjoint_left.1 hx haS ((PrimeSpectrum.le_iff_specializes _ _).2 hxy hay)

/-- If `Spec R` is catenary, so is the subspace of primes disjoint from `S`
(a generization-stable subspace of `Spec R`). -/
theorem isCatenary_primesDisjointFrom
    (R : Type u) [CommRing R] (S : Submonoid R)
    (h : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R)) :
    IrreducibleClosedsCodim.IsCatenarySpace
      (↥{p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal}) :=
  CatenaryTransport.isCatenary_of_stableUnderGeneralization _
    (stableUnderGeneralization_primesDisjointFrom R S) h

/-- A localization of a catenary ring is catenary. -/
@[ega "0 16.1.4", ega "IV 5.1.5" "special case", ega "IV 5.6.3"]
theorem localization_isCatenary
    (R : Type u) [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (h : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R)) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) := by
  have e : PrimeSpectrum A ≃ₜ ↥{p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal} :=
    (PrimeSpectrum.localization_comap_isEmbedding A S).toHomeomorph.trans
      (Homeomorph.setCongr (PrimeSpectrum.localization_comap_range A S))
  exact isCatenary_of_homeomorph e.symm (isCatenary_primesDisjointFrom R S h)

/-- For a localization `A = S⁻¹R`, catenarity of `Spec A` is catenarity of the subspace of
primes of `R` disjoint from `S`. -/
theorem isCatenary_primesDisjointFrom_of_isLocalization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (h : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A)) :
    IrreducibleClosedsCodim.IsCatenarySpace
      (↥{p : PrimeSpectrum R | Disjoint (S : Set R) p.asIdeal}) :=
  isCatenary_of_homeomorph ((PrimeSpectrum.localization_comap_isEmbedding A S).toHomeomorph.trans
    (Homeomorph.setCongr (PrimeSpectrum.localization_comap_range A S))) h

/-- A finite-type algebra over a localization is itself a localization of a
finite-type algebra over the base ring. -/
theorem exists_finiteType_localization_of_finiteType_over_localization
    (R : Type u) [CommRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (hC : Algebra.FiniteType A C) :
    ∃ (B : Subalgebra R C) (T : Submonoid ↥B),
      Algebra.FiniteType R (↥B) ∧ IsLocalization T C := by
  obtain ⟨gens, hgens⟩ := hC
  set B : Subalgebra R C := Algebra.adjoin R (↑gens : Set C) with hBdef
  have : IsScalarTower R ↥B C := IsScalarTower.subalgebra' R C C B
  refine ⟨B, S.map (algebraMap R ↥B), Algebra.FiniteType.adjoin_of_finite gens.finite_toSet, ?_⟩
  have hmap : ∀ r : R, (algebraMap (↥B) C) ((algebraMap R ↥B) r) = (algebraMap R C) r := by
    intro r; rw [← IsScalarTower.algebraMap_apply R ↥B C]
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, s, hsS, rfl⟩
    dsimp only
    rw [hmap, IsScalarTower.algebraMap_apply R A C]
    exact (IsLocalization.map_units A ⟨s, hsS⟩).map (algebraMap A C)
  · intro z
    have hP : ∀ w : C, w ∈ Algebra.adjoin A (↑gens : Set C) →
        ∃ (b : ↥B) (s : S), w * (algebraMap R C) ↑s = (algebraMap (↥B) C) b := by
      intro w hw
      induction hw using Algebra.adjoin_induction with
      | mem x hx => exact ⟨⟨x, Algebra.subset_adjoin hx⟩, 1, by simp⟩
      | algebraMap a =>
        obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj S a
        refine ⟨(algebraMap R ↥B) r, t, ?_⟩
        rw [hmap]
        have := congrArg (algebraMap A C) ht
        rw [map_mul, ← IsScalarTower.algebraMap_apply R A C,
          ← IsScalarTower.algebraMap_apply R A C] at this
        exact this
      | add x y hx hy ihx ihy =>
        obtain ⟨b₁, s₁, h₁⟩ := ihx
        obtain ⟨b₂, s₂, h₂⟩ := ihy
        refine ⟨b₁ * (algebraMap R ↥B) s₂ + b₂ * (algebraMap R ↥B) s₁, s₁ * s₂, ?_⟩
        rw [map_add, map_mul, map_mul, hmap, hmap, Submonoid.coe_mul, map_mul]
        calc (x + y) * ((algebraMap R C) ↑s₁ * (algebraMap R C) ↑s₂)
            = (x * (algebraMap R C) ↑s₁) * (algebraMap R C) ↑s₂
              + (y * (algebraMap R C) ↑s₂) * (algebraMap R C) ↑s₁ := by ring
          _ = (algebraMap (↥B) C) b₁ * (algebraMap R C) ↑s₂
              + (algebraMap (↥B) C) b₂ * (algebraMap R C) ↑s₁ := by rw [h₁, h₂]
      | mul x y hx hy ihx ihy =>
        obtain ⟨b₁, s₁, h₁⟩ := ihx
        obtain ⟨b₂, s₂, h₂⟩ := ihy
        refine ⟨b₁ * b₂, s₁ * s₂, ?_⟩
        rw [map_mul, Submonoid.coe_mul, map_mul]
        calc x * y * ((algebraMap R C) ↑s₁ * (algebraMap R C) ↑s₂)
            = (x * (algebraMap R C) ↑s₁) * (y * (algebraMap R C) ↑s₂) := by ring
          _ = (algebraMap (↥B) C) b₁ * (algebraMap (↥B) C) b₂ := by rw [h₁, h₂]
    obtain ⟨b, s, hbs⟩ := hP z (hgens ▸ Algebra.mem_top)
    refine ⟨⟨b, ⟨(algebraMap R ↥B) s, ⟨s, s.property, rfl⟩⟩⟩, ?_⟩
    simp only
    rw [hmap]
    exact hbs
  · intro x y hxy
    exact ⟨1, by rw [Subtype.val_injective hxy]⟩

/-- A localization of a Noetherian universally catenary ring is universally catenary. -/
@[stacks 00NJ, ega "IV 10.7.2" "more general", ega "IV 5.6.3", ega "IV 7.8.2" "partial"]
theorem localization_isUniversallyCatenary
    (R : Type u) [CommRing R] [IsNoetherianRing R] (S : Submonoid R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (h : IsUniversallyCatenary R) :
    IsUniversallyCatenary A := by
  intro C _ _ hC
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨B, T, hBft, hBloc⟩ :=
    exists_finiteType_localization_of_finiteType_over_localization R S A C hC
  have hBcat : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum (↥B)) := h (↥B) hBft
  exact localization_isCatenary (↥B) T C hBcat

/-- A finite-type algebra over a universally catenary ring, in an arbitrary universe, has catenary
spectrum. -/
theorem IsUniversallyCatenary.isCatenarySpace {R : Type u} [CommRing R]
    (h : IsUniversallyCatenary R) (C : Type*) [CommRing C] [Algebra R C]
    (hC : Algebra.FiniteType R C) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum C) := by
  let : Small.{u} C := Algebra.FiniteType.small (R := R)
  have hcat := h (Shrink.{u} C)
    (Algebra.FiniteType.of_surjective (Shrink.algEquiv R C).symm.toAlgHom
      (Shrink.algEquiv R C).symm.surjective)
  exact isCatenary_of_homeomorph
    (PrimeSpectrum.homeomorphOfRingEquiv (Shrink.ringEquiv C)) hcat

/-- For `R : Type u` and any universe `v`, `R` is universally catenary if and only if every
finite-type `R`-algebra in `Type (max u v)` has catenary spectrum. -/
theorem isUniversallyCatenary_iff_forall_max.{v} {R : Type u} [CommRing R] :
    IsUniversallyCatenary R ↔
      ∀ (C : Type (max u v)) [CommRing C] [Algebra R C], Algebra.FiniteType R C →
        IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum C) := by
  refine ⟨fun h C _ _ hC => h.isCatenarySpace C hC, fun h C _ _ hC => ?_⟩
  have hcat := h (ULift.{v} C)
    (Algebra.FiniteType.of_surjective (ULift.algEquiv (R := R)).symm.toAlgHom
      (ULift.algEquiv (R := R)).symm.surjective)
  exact isCatenary_of_homeomorph
    (PrimeSpectrum.homeomorphOfRingEquiv (ULift.ringEquiv : ULift.{v} C ≃+* C)) hcat

/-- A finite-type algebra over a universally catenary ring is universally catenary. -/
theorem IsUniversallyCatenary.trans {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (h : IsUniversallyCatenary A) : IsUniversallyCatenary B := by
  intro C _ _ hC
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact h.isCatenarySpace C (Algebra.FiniteType.trans inferInstance hC)

/-! ## Catenary Noetherian local rings and dimension functions -/

@[expose] public section

open Order TopologicalSpace

/-- A *saturated* chain of primes: a `RelSeries` for the covering relation `⋖` on
`PrimeSpectrum A`. -/
@[ega "0 14.3.1" "Prime spectra"]
abbrev CovChain (A : Type*) [CommRing A] :=
  RelSeries {(a, b) : PrimeSpectrum A × PrimeSpectrum A | a ⋖ b}

/-- A ring `A` is *catenary* if for every pair of primes `p ≤ q` the lengths of the chains of
primes (`LTSeries`) from `p` to `q` are bounded, and all saturated chains (`CovChain`) from `p` to
`q` have the same length. -/
@[ega "0 16.1.4"]
def IsCatenaryRingSaturated (A : Type*) [CommRing A] : Prop :=
  ∀ p q : PrimeSpectrum A, p ≤ q →
    (∃ N : ℕ, ∀ l : LTSeries (PrimeSpectrum A),
        l.head = p → l.last = q → l.length ≤ N) ∧
    (∀ s t : CovChain A,
        s.head = p → s.last = q → t.head = p → t.last = q → s.length = t.length)

/-- A map `δ : X → ℤ` on a topological space `X` is a *dimension function* if `δ y < δ x` whenever
`x ⤳ y` and `x ≠ y`, and `δ x = δ y + 1` for every immediate specialization `x ⤳ y`. -/
@[sga "6 X 1.6"]
def IsDimensionFunctionProp {X : Type*} [TopologicalSpace X] (δ : X → ℤ) : Prop :=
  (∀ x y : X, x ⤳ y → x ≠ y → δ y < δ x) ∧
  (∀ x y : X, TopologicalSpace.IsImmediateSpecialization x y → δ x = δ y + 1)

/-- The Krull dimension `dim(A ⧸ p)`, as the natural number `coheight p` in `PrimeSpectrum A`. -/
noncomputable def dimQuotient {A : Type*} [CommRing A] (p : PrimeSpectrum A) : ℕ :=
  (Order.coheight p).toNat

/-- The candidate dimension function `delta(p) = dim(A/p)`, valued in `Z`. -/
@[sga "2 XIV 2.1" "special case"]
noncomputable def deltaDim {A : Type*} [CommRing A] (p : PrimeSpectrum A) : ℤ :=
  (dimQuotient p : ℤ)

/-- In a Noetherian local ring every prime has finite coheight. -/
theorem coheight_lt_top_of_noetherianLocal {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (p : PrimeSpectrum A) : Order.coheight p < ⊤ := by
  have hle : (Order.coheight p : WithBot ℕ∞) ≤ ringKrullDim A := Order.coheight_le_krullDim p
  have hfin : ringKrullDim A < ⊤ := ringKrullDim_lt_top
  have h : (Order.coheight p : WithBot ℕ∞) < (⊤ : WithBot ℕ∞) := lt_of_le_of_lt hle hfin
  rw [← WithBot.coe_top, WithBot.coe_lt_coe] at h
  exact h

/-- In a Noetherian local ring, if `x ⤳ y` and `x ≠ y` then `deltaDim y < deltaDim x`. -/
@[sga "6 X 1.4" "(i), special case"]
theorem deltaDim_lt_of_specializes {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (x y : PrimeSpectrum A) (h : x ⤳ y) (hne : x ≠ y) : deltaDim y < deltaDim x := by
  rw [← PrimeSpectrum.le_iff_specializes] at h
  have hlt : x < y := lt_of_le_of_ne h hne
  have hco : Order.coheight y < Order.coheight x :=
    Order.coheight_strictAnti hlt (coheight_lt_top_of_noetherianLocal y)
  have hxt : Order.coheight x ≠ ⊤ := (coheight_lt_top_of_noetherianLocal x).ne
  have hyt : Order.coheight y ≠ ⊤ := (coheight_lt_top_of_noetherianLocal y).ne
  have htn : (Order.coheight y).toNat < (Order.coheight x).toNat := by
    lift Order.coheight x to ℕ using hxt with a
    lift Order.coheight y to ℕ using hyt with b
    simpa using hco
  unfold deltaDim dimQuotient
  exact_mod_cast htn

/-- In `PrimeSpectrum A`, immediate specialization is the covering relation `⋖`. -/
theorem immediateSpec_iff_covby {A : Type*} [CommRing A] (x y : PrimeSpectrum A) :
    TopologicalSpace.IsImmediateSpecialization x y ↔ x ⋖ y := by
  unfold TopologicalSpace.IsImmediateSpecialization
  simp only [← PrimeSpectrum.le_iff_specializes]
  constructor
  · rintro ⟨hle, hne, hmid⟩
    refine ⟨lt_of_le_of_ne hle hne, ?_⟩
    intro z hxz hzy
    rcases hmid z (le_of_lt hxz) (le_of_lt hzy) with h | h
    · exact absurd hxz (by rw [h]; exact lt_irrefl x)
    · exact absurd hzy (by rw [h]; exact lt_irrefl y)
  · rintro ⟨hlt, hmid⟩
    refine ⟨le_of_lt hlt, ne_of_lt hlt, ?_⟩
    intro z hxz hzy
    rcases eq_or_lt_of_le hxz with h | h
    · exact Or.inl h.symm
    rcases eq_or_lt_of_le hzy with h2 | h2
    · exact Or.inr h2
    · exact absurd h2 (hmid h)

/-- In a Noetherian local ring, `deltaDim x = deltaDim y + 1` if and only if
`coheight x = coheight y + 1`. -/
theorem deltaDim_eq_iff_coheight {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (x y : PrimeSpectrum A) :
    deltaDim x = deltaDim y + 1 ↔ Order.coheight x = Order.coheight y + 1 := by
  have hxt : Order.coheight x ≠ ⊤ := (coheight_lt_top_of_noetherianLocal x).ne
  have hyt : Order.coheight y ≠ ⊤ := (coheight_lt_top_of_noetherianLocal y).ne
  unfold deltaDim dimQuotient
  lift Order.coheight x to ℕ using hxt with a ha
  lift Order.coheight y to ℕ using hyt with b hb
  rw [ENat.toNat_natCast, ENat.toNat_natCast,
      show ((b : ℕ∞) + 1) = ((b + 1 : ℕ) : ℕ∞) by push_cast; ring, Nat.cast_inj]
  constructor
  · intro h
    have : (a : ℤ) = (b : ℤ) + 1 := by exact_mod_cast h
    omega
  · intro h; subst h; push_cast; ring

/-- A saturated chain, as an `LTSeries` with the same entries. -/
noncomputable def covToLT {α : Type*} [PartialOrder α] (s : RelSeries {(a, b) : α × α | a ⋖ b}) :
    LTSeries α :=
  LTSeries.mk s.length s.toFun (by
    rw [Fin.strictMono_iff_lt_succ]; intro i; exact (s.step i).lt)

/-- `covToLT` preserves the head of the chain. -/
lemma covToLT_head {α : Type*} [PartialOrder α] (s : RelSeries {(a, b) : α × α | a ⋖ b}) :
    (covToLT s).head = s.head := rfl
/-- `covToLT` preserves the length of the chain. -/
lemma covToLT_length {α : Type*} [PartialOrder α] (s : RelSeries {(a, b) : α × α | a ⋖ b}) :
    (covToLT s).length = s.length := rfl
/-- `covToLT` leaves each entry of the chain unchanged. -/
lemma covToLT_apply {α : Type*} [PartialOrder α] (s : RelSeries {(a, b) : α × α | a ⋖ b})
    (j : Fin (s.length + 1)) : (covToLT s) j = s j := rfl

/-- In a Noetherian local ring, for every prime `p` there is a saturated chain from `p` to the
maximal ideal `⊤` whose length is `coheight p`. -/
lemma exists_covchain_top {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : PrimeSpectrum A) :
    ∃ s : CovChain A, s.head = p ∧ s.last = ⊤ ∧ (s.length : ℕ∞) = Order.coheight p := by
  have : WellFoundedGT (PrimeSpectrum A) := by
    apply WellFounded.onFun (f := PrimeSpectrum.asIdeal) (r := (· > ·))
    exact (wellFounded_gt : WellFounded (· > · : Ideal A → Ideal A → Prop))
  have hfd : FiniteDimensionalOrder (PrimeSpectrum A) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
    exact ⟨(Order.bot_lt_krullDim).ne', ringKrullDim_lt_top.ne⟩
  have : WellFoundedLT (PrimeSpectrum A) :=
    SetRel.IsWellFounded.of_finiteDimensional {(a, b) : PrimeSpectrum A × PrimeSpectrum A | a < b}
  have hfin : Order.coheight p < ⊤ := coheight_lt_top_of_noetherianLocal p
  set n := (Order.coheight p).toNat with hndef
  have hn : Order.coheight p = (n : ℕ∞) := by rw [hndef]; exact (ENat.natCast_toNat hfin.ne).symm
  obtain ⟨q0, hq0head, hq0len⟩ := exists_series_of_coheight_eq_coe p hn
  obtain ⟨t, i, hti, hi0, hilast⟩ := LTSeries.exists_relSeries_covBy q0
  have hthead : t.head = p := by
    have h2 : t (i 0) = q0 0 := by rw [← Function.comp_apply (f := t) (g := i), hti]
    rw [hi0] at h2
    rw [RelSeries.head, h2, ← RelSeries.head]; exact hq0head
  have hge : q0.length ≤ t.length := by
    have hcard := Fintype.card_le_of_injective i i.injective
    simp only [Fintype.card_fin] at hcard
    omega
  have hub : (t.length : ℕ∞) ≤ Order.coheight p := by
    have := Order.length_le_coheight_head (p := covToLT t)
    rw [covToLT_length, covToLT_head, hthead] at this
    exact this
  have hlen : t.length = n := by
    have h1 : n ≤ t.length := by omega
    rw [hn] at hub
    have : (t.length : ℕ∞) = n := le_antisymm hub (by exact_mod_cast h1)
    exact_mod_cast this
  refine ⟨t, hthead, ?_, by rw [hlen, hn]⟩
  have hidx : (covToLT t).length = Order.coheight (covToLT t).head := by
    rw [covToLT_length, covToLT_head, hthead, hlen, hn]
  have hc := Order.coheight_eq_index_of_length_eq_head_coheight hidx (Fin.last _)
  rw [Fin.rev_last] at hc
  have hlast : (covToLT t) (Fin.last (covToLT t).length) = t.last := covToLT_apply t _
  rw [hlast] at hc
  exact IsMax.eq_top (Order.coheight_eq_zero.mp hc)

/-- In a catenary Noetherian local ring, `coheight x = coheight y + 1` for every covering pair
`x ⋖ y`. -/
theorem coheight_covby_of_catenary {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcat : IsCatenaryRingSaturated A) (x y : PrimeSpectrum A) (hxy : x ⋖ y) :
    Order.coheight x = Order.coheight y + 1 := by
  obtain ⟨sy, syhead, sylast, sylen⟩ := exists_covchain_top y
  obtain ⟨sx, sxhead, sxlast, sxlen⟩ := exists_covchain_top x
  have hcons : (x, sy.head) ∈ {(a, b) : PrimeSpectrum A × PrimeSpectrum A | a ⋖ b} := by
    simpa [syhead] using hxy
  set sx' : CovChain A := sy.cons x hcons with hsx'
  have hx'head : sx'.head = x := RelSeries.head_cons _ _ _
  have hx'last : sx'.last = ⊤ := by rw [hsx', RelSeries.last_cons]; exact sylast
  have hx'len : sx'.length = sy.length + 1 := RelSeries.cons_length _ _ _
  have hcat2 := (hcat x ⊤ le_top).right sx sx' sxhead sxlast hx'head hx'last
  have hlens : (sx.length : ℕ∞) = (sx'.length : ℕ∞) := by rw [hcat2]
  rw [sxlen, hx'len] at hlens
  rw [hlens]; push_cast; rw [sylen]

/-- A Noetherian local ring in which `coheight x = coheight y + 1` for every covering pair `x ⋖ y`
is catenary. -/
theorem catenary_of_coheight_covby {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hcov : ∀ x y : PrimeSpectrum A, x ⋖ y → Order.coheight x = Order.coheight y + 1) :
    IsCatenaryRingSaturated A := by
  have tele : ∀ s : CovChain A,
      (Order.coheight s.head : ℕ∞) = Order.coheight s.last + s.length := by
    intro s
    induction s using RelSeries.inductionOn with
    | singleton x =>
      rw [RelSeries.head_singleton, RelSeries.last_singleton, RelSeries.singleton_length]
      simp
    | cons p x hx ih =>
      have hcover : x ⋖ p.head := hx
      have hstep : Order.coheight x = Order.coheight p.head + 1 := hcov x p.head hcover
      rw [RelSeries.head_cons, RelSeries.last_cons, RelSeries.cons_length, hstep, ih]
      push_cast
      ring
  intro p q hpq
  refine ⟨⟨(Order.coheight p).toNat, ?_⟩, ?_⟩
  · intro l hlhead _
    have hub : (l.length : ℕ∞) ≤ Order.coheight l.head := Order.length_le_coheight_head
    rw [hlhead] at hub
    have hpfin : Order.coheight p ≠ ⊤ := (coheight_lt_top_of_noetherianLocal p).ne
    have hcoe : Order.coheight p = ((Order.coheight p).toNat : ℕ∞) :=
      (ENat.natCast_toNat hpfin).symm
    rw [hcoe] at hub
    exact_mod_cast hub
  · intro s t shead slast thead tlast
    have hs := tele s
    have ht := tele t
    rw [shead, slast] at hs
    rw [thead, tlast] at ht
    have hqfin : Order.coheight q ≠ ⊤ := (coheight_lt_top_of_noetherianLocal q).ne
    have heq : (Order.coheight q + (s.length : ℕ∞)) = Order.coheight q + (t.length : ℕ∞) := by
      rw [← hs, ← ht]
    exact ENat.natCast_inj.mp (WithTop.add_left_cancel hqfin heq)

/-- A Noetherian local ring `A` is catenary if and only if `p ↦ dim(A ⧸ p)` is a dimension function
on `PrimeSpectrum A`. -/
@[stacks 0ECF]
theorem catenary_iff_isDimensionFunction
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRingSaturated A ↔ IsDimensionFunctionProp (X := PrimeSpectrum A) deltaDim := by
  constructor
  · intro hcat
    refine ⟨deltaDim_lt_of_specializes, ?_⟩
    intro x y himm
    have hxy : x ⋖ y := (immediateSpec_iff_covby x y).mp himm
    exact (deltaDim_eq_iff_coheight x y).mpr (coheight_covby_of_catenary hcat x y hxy)
  · intro hdim
    apply catenary_of_coheight_covby
    intro x y hxy
    have himm : TopologicalSpace.IsImmediateSpecialization x y :=
      (immediateSpec_iff_covby x y).mpr hxy
    have hstep : deltaDim x = deltaDim y + 1 := hdim.right x y himm
    exact (deltaDim_eq_iff_coheight x y).mp hstep

/-! ## Catenarity is detected by localizations -/

@[expose] public section

open Ring

/-- A localization of a catenary ring is catenary. -/
@[ega "0 16.1.4", ega "IV 5.1.5" "special case", ega "IV 5.6.3"]
theorem isCatenary_of_isLocalization
    (R : Type u) [CommRing R] (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] (h : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R)) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum S) :=
  localization_isCatenary R M S h

/-- If the localization `R_m` is catenary at every maximal ideal `m`, then `R` is catenary. -/
@[ega "0 16.1.4" "partial", ega "IV 5.1.5" "special case"]
theorem isCatenary_of_forall_isMaximal
    (R : Type u) [CommRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum (Localization.AtPrime m))) :
    IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R) := by
  rw [IrreducibleClosedsCodim.isCatenarySpace_iff_isIrreducibleChain]
  intro T T' hTirr hTcl hT'irr hT'cl hTT'
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hTirr hTcl
  obtain ⟨m, hm, hξm⟩ := Ideal.exists_le_maximal ξ.asIdeal ξ.isPrime.ne_top
  refine CatenaryTransport.exists_isIrreducibleChain_of_mem
    (stableUnderGeneralization_primesDisjointFrom R m.primeCompl)
    (isCatenary_primesDisjointFrom_of_isLocalization R m.primeCompl _ (h m))
    hTirr hTcl hT'irr hT'cl hTT' ?_ hξ.mem
  exact Set.disjoint_left.2 fun a ha haξ => ha (hξm haξ)

/-- A localization of a Noetherian universally catenary ring is universally catenary. -/
@[ega "IV 10.7.2" "more general", ega "IV 5.6.3", ega "IV 7.8.2" "partial"]
theorem isUniversallyCatenary_of_isLocalization
    (R : Type u) [CommRing R] [IsNoetherianRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S]
    [IsLocalization M S] (h : IsUniversallyCatenary R) :
    IsUniversallyCatenary S :=
  localization_isUniversallyCatenary R M S h

/-- If `R` is Noetherian and the localization `R_m` is universally catenary at every maximal ideal
`m`, then `R` is universally catenary. -/
@[ega "IV 5.6.3" "(i)", ega "IV 7.8.2" "partial", ega "IV 7.8.3" "(i)"]
theorem isUniversallyCatenary_of_forall_isMaximal
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], IsUniversallyCatenary (Localization.AtPrime m)) :
    IsUniversallyCatenary R := by
  intro C _ _ hCFT
  apply isCatenary_of_forall_isMaximal C
  intro n _
  set p : Ideal R := n.comap (algebraMap R C) with hp
  have hpp : p.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hpp.ne_top
  have : m.IsMaximal := hm
  have hRp : IsUniversallyCatenary (Localization.AtPrime p) := by
    have hle : m.primeCompl ≤ p.primeCompl := by
      intro x hx
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe] at hx ⊢
      exact fun hxp => hx (hpm hxp)
    let : Algebra (Localization.AtPrime m) (Localization.AtPrime p) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime m)
        (Localization.AtPrime p) m.primeCompl p.primeCompl hle
    have : IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime p) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime m)
        (Localization.AtPrime p) m.primeCompl p.primeCompl hle
    have : IsLocalization
        (Submonoid.map (algebraMap R (Localization.AtPrime m)) p.primeCompl)
        (Localization.AtPrime p) :=
      IsLocalization.isLocalization_of_submonoid_le (Localization.AtPrime m)
        (Localization.AtPrime p) m.primeCompl p.primeCompl hle
    exact localization_isUniversallyCatenary (Localization.AtPrime m)
      (Submonoid.map (algebraMap R (Localization.AtPrime m)) p.primeCompl)
      (Localization.AtPrime p) (h m)
  have hS' : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum
      (Localization (Submonoid.map (algebraMap R C) p.primeCompl))) := by
    have hfin : (algebraMap R C).FiniteType := by
      have heq : (algebraMap R C).toAlgebra = ‹Algebra R C› :=
        Algebra.algebra_ext _ _ (fun r => rfl)
      rw [RingHom.FiniteType, heq]; exact hCFT
    have hmapFT := RingHom.finiteType_localizationPreserves (algebraMap R C) p.primeCompl
      (Localization.AtPrime p) (Localization (Submonoid.map (algebraMap R C) p.primeCompl)) hfin
    let : Algebra (Localization.AtPrime p)
        (Localization (Submonoid.map (algebraMap R C) p.primeCompl)) :=
      (IsLocalization.map (Localization (Submonoid.map (algebraMap R C) p.primeCompl))
        (algebraMap R C) (Submonoid.le_comap_map p.primeCompl)).toAlgebra
    have hAFT : Algebra.FiniteType (Localization.AtPrime p)
        (Localization (Submonoid.map (algebraMap R C) p.primeCompl)) := hmapFT
    exact hRp (Localization (Submonoid.map (algebraMap R C) p.primeCompl)) hAFT
  set N₁ : Submonoid C := Submonoid.map (algebraMap R C) p.primeCompl with hN1
  have hle : N₁ ≤ n.primeCompl := by
    rintro x ⟨a, ha, rfl⟩
    simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe] at ha ⊢
    intro hxn
    exact ha (by rw [hp]; exact hxn)
  let : Algebra (Localization N₁) (Localization.AtPrime n) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization N₁) (Localization.AtPrime n)
      N₁ n.primeCompl hle
  have : IsScalarTower C (Localization N₁) (Localization.AtPrime n) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization N₁)
      (Localization.AtPrime n) N₁ n.primeCompl hle
  have : IsLocalization (Submonoid.map (algebraMap C (Localization N₁)) n.primeCompl)
      (Localization.AtPrime n) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization N₁) (Localization.AtPrime n)
      N₁ n.primeCompl hle
  exact isCatenary_of_isLocalization (Localization N₁)
    (Submonoid.map (algebraMap C (Localization N₁)) n.primeCompl)
    (Localization.AtPrime n) hS'

/-- For a commutative ring `R` the following are equivalent:
1. `R` is catenary;
2. the localization `R_p` is catenary for every prime ideal `p`;
3. the localization `R_m` is catenary for every maximal ideal `m`. -/
@[stacks 0AUN "catenary",
  ega "0 16.1.4",
  ega "IV 5.1.5" "special case",
  ega "IV 5.6.3" "(i), special case"]
theorem catenary_tfae (R : Type u) [CommRing R] :
    [ IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum R),
      ∀ (p : Ideal R) [p.IsPrime],
        IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum (Localization.AtPrime p)),
      ∀ (m : Ideal R) [m.IsMaximal],
        IrreducibleClosedsCodim.IsCatenarySpace
          (PrimeSpectrum (Localization.AtPrime m)) ].TFAE := by
  tfae_have 1 → 2 := by
    intro h p _
    exact isCatenary_of_isLocalization R p.primeCompl (Localization.AtPrime p) h
  tfae_have 2 → 3 := by
    intro h m _
    exact h m
  tfae_have 3 → 1 := by
    intro h
    exact isCatenary_of_forall_isMaximal R h
  tfae_finish

/-- For a Noetherian commutative ring `R` the following are equivalent:
1. `R` is universally catenary;
2. the localization `R_p` is universally catenary for every prime ideal `p`;
3. the localization `R_m` is universally catenary for every maximal ideal `m`. -/
@[stacks 0AUN "universally catenary",
  ega "IV 10.7.2" "more general",
  ega "IV 5.6.3",
  ega "IV 7.8.2",
  ega "IV 7.8.3" "(i)"]
theorem universallyCatenary_tfae (R : Type u) [CommRing R] [IsNoetherianRing R] :
    [ IsUniversallyCatenary R,
      ∀ (p : Ideal R) [p.IsPrime], IsUniversallyCatenary (Localization.AtPrime p),
      ∀ (m : Ideal R) [m.IsMaximal], IsUniversallyCatenary (Localization.AtPrime m) ].TFAE := by
  tfae_have 1 → 2 := by
    intro h p _
    exact isUniversallyCatenary_of_isLocalization R p.primeCompl (Localization.AtPrime p) h
  tfae_have 2 → 3 := by
    intro h m _
    exact h m
  tfae_have 3 → 1 := by
    intro h
    exact isUniversallyCatenary_of_forall_isMaximal R h
  tfae_finish

/-! ## Algebras essentially of finite type over a universally catenary ring -/

@[expose] public section

/-- Let `A` be a Noetherian ring such that every finite-type `A`-algebra has catenary spectrum.
Then every `A`-algebra `S` essentially of finite type is Noetherian, and every finite-type
`S`-algebra has catenary spectrum. -/
@[stacks 0ECE,
  ega "IV 10.6.1" "(i)",
  ega "IV 10.7.2" "more general",
  ega "IV 10.7.3" "partial",
  ega "IV 5.6.3",
  ega "IV 7.8.2" "partial"]
theorem universally_catenary
    (A : Type*) [CommRing A] [IsNoetherianRing A]
    (hA : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B],
            IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum B))
    (S : Type*) [CommRing S] [Algebra A S] [Algebra.EssFiniteType A S] :
    IsNoetherianRing S ∧
    (∀ (C : Type u) [CommRing C] [Algebra S C] [Algebra.FiniteType S C],
       IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum C)) := by
  refine ⟨?_, ?_⟩
  · exact Algebra.EssFiniteType.isNoetherianRing A S
  · intro C _ _ _
    let : Algebra A C := ((algebraMap S C).comp (algebraMap A S)).toAlgebra
    have : IsScalarTower A S C :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : Algebra.EssFiniteType S C := Algebra.EssFiniteType.of_finiteType S C
    have : Algebra.EssFiniteType A C := Algebra.EssFiniteType.comp A S C
    obtain ⟨C₀, M, hC₀ft, hloc⟩ :=
      (Algebra.essFiniteType_iff_exists_subalgebra A C).mp inferInstance
    have : Algebra.FiniteType A C₀ := hC₀ft
    have hC₀ : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum C₀) := hA C₀
    exact localization_isCatenary C₀ M C hC₀

/-! ## Catenarity passes to the target of a surjection -/

@[expose] public section

namespace Stacks.Catenary.SurjectiveImage

open PrimeSpectrum Set

/-- `IsCatenaryAt p q`, for two elements of a preorder: the chains from `p` to `q` have bounded
length, and the non-refinable ones (all of whose steps are covering pairs `⋖`) have one and the
same length. -/
public def IsCatenaryAt {α : Type*} [Preorder α] (p q : α) : Prop :=
  (∃ N : ℕ, ∀ s : LTSeries α, s.head = p → s.last = q → s.length ≤ N) ∧
    ∃ n : ℕ, ∀ s : LTSeries α, s.head = p → s.last = q →
      (∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) → s.length = n

/-- Catenarity at a pair transfers backwards along an order embedding with order-connected
range. -/
public theorem IsCatenaryAt.of_image {α β : Type*} [Preorder α] [Preorder β] (e : α ↪o β)
    (he : (range e).OrdConnected) {p q : α} (h : IsCatenaryAt (e p) (e q)) : IsCatenaryAt p q := by
  obtain ⟨⟨N, hN⟩, n, hn⟩ := h
  refine ⟨⟨N, fun s hs hl => ?_⟩, n, fun s hs hl hcov => ?_⟩
  · simpa using hN (s.map e e.strictMono) (by simp [hs]) (by simp [hl])
  · simpa using hn (s.map e e.strictMono) (by simp [hs]) (by simp [hl])
      fun i => (hcov i).image e he

/-- A zero locus is an upper set of the prime spectrum: a prime containing `s` still contains `s`
after growing. -/
private theorem isUpperSet_zeroLocus {R : Type*} [CommSemiring R] (s : Set R) :
    IsUpperSet (zeroLocus s) := fun _ _ hpq hp => by
  rw [mem_zeroLocus] at hp ⊢; exact hp.trans hpq

section Surjective

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)

include f hf in
/-- For a surjective ring map `f : A →+* B`, taking preimages of primes is an order embedding
`Spec(B) ↪o Spec(A)`. -/
private noncomputable def comapOrderEmbedding : PrimeSpectrum B ↪o PrimeSpectrum A :=
  (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj f hf rfl).toOrderEmbedding.trans
    (OrderEmbedding.subtype _)

/-- `comapOrderEmbedding f hf` is `PrimeSpectrum.comap f`. -/
private theorem coe_comapOrderEmbedding :
    (comapOrderEmbedding f hf : PrimeSpectrum B → PrimeSpectrum A) = comap f := rfl

/-- The range of `comapOrderEmbedding f hf` is the zero locus of `ker f`: the primes of `A`
containing `ker f` are exactly the preimages of the primes of `B`. -/
private theorem range_comapOrderEmbedding :
    range (comapOrderEmbedding f hf) = zeroLocus (RingHom.ker f) := by
  rw [coe_comapOrderEmbedding]; exact range_comap_of_surjective B f hf

/-- The range of `comapOrderEmbedding f hf` is order-connected: a prime of `A` squeezed between
two primes containing `ker f` again contains `ker f`, hence is a preimage. -/
private theorem ordConnected_range_comapOrderEmbedding :
    (range (comapOrderEmbedding f hf)).OrdConnected :=
  range_comapOrderEmbedding f hf ▸ (isUpperSet_zeroLocus _).ordConnected

end Surjective

end Stacks.Catenary.SurjectiveImage

end

/-! ## Catenarity in terms of `LTSeries` -/

@[expose] public section

/-- A commutative ring `R` is **catenary** if for every pair of prime ideals `p ⊆ q` there is an
integer bounding the lengths of the finite chains of primes from `p` to `q`, and all non-refinable
such chains have the same length. Chains are `LTSeries` in `PrimeSpectrum R`, and
non-refinability of a chain with fixed endpoints is the condition that each of its steps be a
covering pair `⋖`. -/
@[stacks 00NI, ega "0 16.1.4" "catenary ring def"]
public def Ring.IsCatenary (R : Type*) [CommRing R] : Prop :=
  ∀ p q : PrimeSpectrum R, p ≤ q →
    (∃ N : ℕ, ∀ s : LTSeries (PrimeSpectrum R), s.head = p → s.last = q → s.length ≤ N) ∧
    ∃ n : ℕ, ∀ s : LTSeries (PrimeSpectrum R), s.head = p → s.last = q →
      (∀ i : Fin s.length, s i.castSucc ⋖ s i.succ) → s.length = n

/-- A commutative ring `R` is **universally catenary** if every `R`-algebra of finite type is
catenary. -/
@[stacks 00NL, ega "IV 5.6.2"]
public def Ring.IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], Ring.IsCatenary C

/-- `Ring.IsCatenary`, phrased with `LTSeries` and covering pairs, agrees with `IsCatenaryRing`,
phrased with `PrimeChain`. -/
public theorem Ring.isCatenary_iff_isCatenaryRing {R : Type*} [CommRing R] :
    Ring.IsCatenary R ↔ IsCatenaryRing R := by
  classical
  constructor
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, n, hn⟩ := h p q hpq
    refine ⟨⟨N, fun c => hN c.series c.head_eq c.last_eq⟩, ?_⟩
    intro c d hc hd
    exact (hn c.series c.head_eq c.last_eq hc).trans
      (hn d.series d.head_eq d.last_eq hd).symm
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, heq⟩ := h p q hpq
    refine ⟨⟨N, fun s hs ht => hN ⟨s, hs, ht⟩⟩, ?_⟩
    by_cases hex : ∃ c : PrimeChain R p q, c.IsMaximal
    · obtain ⟨c, hc⟩ := hex
      exact ⟨c.length, fun s hs ht hsat => heq ⟨s, hs, ht⟩ c hsat hc⟩
    · exact ⟨0, fun s hs ht hsat => (hex ⟨⟨s, hs, ht⟩, hsat⟩).elim⟩

/-- If `f : A →+* B` is surjective, then `B` is catenary if `A` is, and `B` is universally catenary
if `A` is. -/
@[stacks 00NK, ega "0 16.1.4", ega "IV 5.6.3" "partial"]
public theorem Ring.isCatenary_and_isUniversallyCatenary_of_surjective {A B : Type u} [CommRing A]
    [CommRing B] {f : A →+* B} (hf : Function.Surjective f) :
    (Ring.IsCatenary A → Ring.IsCatenary B) ∧
      (Ring.IsUniversallyCatenary A → Ring.IsUniversallyCatenary B) := by
  constructor
  · intro hA p q hpq
    exact Stacks.Catenary.SurjectiveImage.IsCatenaryAt.of_image
      (Stacks.Catenary.SurjectiveImage.comapOrderEmbedding f hf)
      (Stacks.Catenary.SurjectiveImage.ordConnected_range_comapOrderEmbedding f hf)
      (hA _ _ ((Stacks.Catenary.SurjectiveImage.comapOrderEmbedding f hf).monotone hpq))
  · intro hA C _ _ _
    let : Algebra A C := ((algebraMap B C).comp f).toAlgebra
    have : Algebra.FiniteType A C :=
      (RingHom.finiteType_algebraMap.2 ‹Algebra.FiniteType B C›).comp (.of_surjective f hf)
    exact hA C

/-- If `f : A →+* B` is surjective and `A` is catenary, then so is `B`. -/
@[stacks 00NK]
public theorem Ring.IsCatenary.of_surjective {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Surjective f) (hA : Ring.IsCatenary A) : Ring.IsCatenary B :=
  (Ring.isCatenary_and_isUniversallyCatenary_of_surjective hf).1 hA

/-- If `f : A →+* B` is surjective and `A` is universally catenary, then so is `B`. -/
@[stacks 00NK]
public theorem Ring.IsUniversallyCatenary.of_surjective {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : Function.Surjective f) (hA : Ring.IsUniversallyCatenary A) :
    Ring.IsUniversallyCatenary B :=
  (Ring.isCatenary_and_isUniversallyCatenary_of_surjective hf).2 hA
