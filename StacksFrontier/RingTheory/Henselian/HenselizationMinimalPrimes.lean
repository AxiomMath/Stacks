module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic fields after henselization

Let `A` be a Noetherian local ring and let `B` be a henselization or a strict henselization
of `A`. Then `B` is Noetherian, and its minimal primes are exactly the primes lying over
minimal primes of `A`. Base changing the product of the generic residue fields of `A` to `B`
gives the product of the generic residue fields of `B`.

## Main definitions

* `StacksDraft.adicCompletionLinearEquivMap` compares the `I`-adic completion of an
  `R`-algebra `U` as an `R`-module with its `I·U`-adic completion as a `U`-module.

## Main results

* `IsLocalRing.isNoetherianRing_of_isHenselization` says that a henselization of a
  Noetherian local ring is Noetherian.
* `IsLocalRing.mem_minimalPrimes_iff_liesOver_minimalPrime_of_isHenselization` identifies
  its minimal primes.
* `IsLocalRing.nonempty_algEquiv_tensor_pi_residueField_minimalPrimes_of_isHenselization`
  identifies the base change of the product of the generic residue fields.

Supporting results of independent interest:

* `StacksDraft.isNoetherianRing_of_indEtale`: an ind-étale local algebra over a Noetherian
  local ring, with local structure map, is Noetherian.
* `StacksDraft.minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero`: over a flat algebra with
  zero-dimensional fibres the minimal primes are exactly the primes over minimal primes.
* `StacksDraft.nonempty_tensor_residue_algEquiv`: for an ind-étale algebra the fibre at a
  prime `p` decomposes, `S`-linearly, as the product of the residue fields at the primes
  over `p`.

## Implementation notes

Both henselizations and strict henselizations are expressed by
`IsLocalRing.IsHenselization A L B`: in the first case `L` is the residue field of `A`, and
in the second it is a chosen separable closure. The statements hold uniformly for every
residue-field extension admitted by this predicate, so `L` is a genuine parameter and lives
in its own universe `v`, independent of the universes `u` of `A` and `w` of `B`.

The three main results are in the `IsLocalRing` namespace because the root name
`isNoetherianRing_of_isHenselization` is already taken, by the weaker `L = ResidueField A`
form in `StacksFrontier.RingTheory.Branches.Completion`; the present form subsumes it. The
supporting layer is in `StacksDraft` for the same reason, matching the `StacksDraft.IndEtale`
API it is built on.

Noetherianness of `B` is proved through `StacksDraft.isNoetherianRing_of_indEtale`, which is
stated for a single universe. The three universes are reconciled by `ULift`ing `A` and `B`
into `Type (max u w)` rather than by narrowing the statement;
`StacksDraft.indEtale_of_equiv` transports the ind-étale hypothesis across those lifts.

`Ideal.nonempty_fiber_residue_algEquiv` already provides the comparison
`p.Fiber B ⧸ P ≃ₐ[κ(p)] κ(q)` over the residue field of `p`. The last result needs it over
`B` instead, so `StacksDraft.nonempty_fiber_residue_algEquiv_right` reproves it with the
`B`-algebra structure coming from `Algebra.TensorProduct.rightAlgebra`; the `κ(p)`-linear
form does not imply the `B`-linear one.

The finite families of minimal primes in the source are represented intrinsically by the
subtypes `minimalPrimes A` and `minimalPrimes B` rather than by an indexing of a list. The
last result is an equivalence of `B`-algebras, so it is the canonical equivalence: its maps
out of `B` are the residue maps, and their kernels distinguish the factors.

## References

* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ)
* [Stacks Project, Tag 0AH1](https://stacks.math.columbia.edu/tag/0AH1)
-/

@[expose] public section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace StacksDraft

/-- An ind-étale local algebra `S` over a Noetherian local ring `R`, whose structure map is
local, is Noetherian.

The completion `S^∧` at the maximal ideal of `S` is a complete local ring whose maximal ideal
is finitely generated, hence Noetherian; it is faithfully flat over `S` because it is flat and
the structure map is local; and Noetherianness descends along a faithfully flat map. -/
theorem isNoetherianRing_of_indEtale
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing R]
    (hi : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    IsNoetherianRing S := by
  have : Module.Flat R S := CommAlgCat.flat_of_ind_etale hi
  have hm := CommAlgCat.map_maximalIdeal_of_ind_etale hi
  have hfg : (IsLocalRing.maximalIdeal S).FG :=
    hm ▸ (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing.map _
  have : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) S) :=
    _root_.adicCompletion_flat_of_flat _ _
  have : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
    rw [← hm]
    exact Module.Flat.of_linearEquiv (adicCompletionLinearEquivMap _ _).symm
  have : Module.Flat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    CommAlgCat.flat_of_ind_etale_restrictScalars hi
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  have : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    complete_local_ring_noetherian _ (AdicCompletion.isAdicComplete_of_fg hfg)
      (AdicCompletion.maximalIdeal_eq_map_of_fg hfg ▸ hfg.map _)
  have : Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact descent_noetherian (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) inferInstance

/-- Every fibre of an ind-étale algebra is reduced and of Krull dimension at most zero.

The fibre `p.Fiber S` is ind-étale over the residue field `κ(p)`, after lifting the latter to
the universe of `S`, and an ind-étale algebra over a field is a filtered colimit of étale
algebras, hence reduced and zero-dimensional. -/
theorem fiber_reduced_and_krullDimLE_zero
    {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    (hi : StacksDraft.IndEtale R S) (p : Ideal R) [p.IsPrime] :
    IsReduced (p.Fiber S) ∧ Ring.KrullDimLE 0 (p.Fiber S) := by
  let K := ULift.{w} p.ResidueField
  let : Algebra K (p.Fiber S) := ULift.algebra' p.ResidueField _
  have h : StacksDraft.IndEtale K (p.Fiber S) := StacksDraft.indEtale_of_equiv
    ULift.ringEquiv.symm (RingEquiv.refl _) (fun _ => rfl)
    (StacksDraft.indEtale_tensorProduct p.ResidueField hi)
  have hc := Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind K (p.Fiber S)
    (StacksDraft.indEtale_iff.mp h)
  exact ⟨hc.isReduced, hc.krullDimLE_zero⟩

/-- Over a flat algebra all of whose fibres are zero-dimensional, the minimal primes of `S` are
exactly the primes of `S` lying over a minimal prime of `R`.

Flatness gives going down, so the contraction of a minimal prime is minimal and every prime
below a prime over `p` is itself over `p`; zero-dimensionality of the fibre over `p` then
forces any two comparable primes over `p` to coincide. -/
theorem minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (hdim : ∀ (p : Ideal R) [p.IsPrime], Ring.KrullDimLE 0 (p.Fiber S))
    (q : Ideal S) :
    q ∈ minimalPrimes S ↔
      (q.IsPrime ∧ ∃ p : Ideal R, p ∈ minimalPrimes R ∧ q.LiesOver p) := by
  constructor
  · intro hq
    have : q.IsPrime := hq.1.1
    refine ⟨inferInstance, q.under R, ⟨⟨inferInstance, bot_le⟩, fun p hp hpq => ?_⟩, inferInstance⟩
    have : p.IsPrime := hp.1
    obtain ⟨P, hPq, hP, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q.under R) q hpq
    obtain rfl : P = q := le_antisymm hPq (hq.2 ⟨hP, bot_le⟩ hPq)
    exact hlo.over.symm.le
  · rintro ⟨hq, p, hp, hlo⟩
    have : p.IsPrime := hp.1.1
    refine ⟨⟨hq, bot_le⟩, fun Q hQ hQq => ?_⟩
    have : Q.IsPrime := hQ.1
    have hQq' : Q.under R ≤ p := hlo.over ▸ Ideal.comap_mono hQq
    have : Q.LiesOver p := ⟨(le_antisymm hQq' (hp.2 ⟨inferInstance, bot_le⟩ hQq')).symm⟩
    let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
    have hle : e ⟨Q, inferInstance, inferInstance⟩ ≤ e ⟨q, hq, hlo⟩ :=
      e.monotone hQq
    have he := ((Ring.krullDimLE_zero_iff.mp (hdim p)) _ inferInstance).eq_of_le
      (e ⟨q, hq, hlo⟩).isPrime.ne_top hle
    exact (show Q = q from congrArg Subtype.val (e.injective (PrimeSpectrum.ext he))).ge

/-- The `B`-linear form of `Ideal.nonempty_fiber_residue_algEquiv`: if a maximal ideal `P` of
the fibre `p.Fiber B` corresponds to a prime `q` of `B` over `p`, then `p.Fiber B ⧸ P` is
`B`-algebra isomorphic to the residue field of `q`, where `p.Fiber B` carries the `B`-algebra
structure of `Algebra.TensorProduct.rightAlgebra`.

The map is the lift `Φ` of the residue map `κ(p) → κ(q)` and of `B → κ(q)`. Its kernel is `P`
by construction, and it is surjective: its image is a subring which is a field, because it is
isomorphic to the field `p.Fiber B ⧸ P`, and which contains the image of `B ⧸ q`, hence
contains every fraction of such elements. -/
theorem nonempty_fiber_residue_algEquiv_right {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (p : Ideal A) [p.IsPrime]
    {P : PrimeSpectrum (p.Fiber B)} [P.asIdeal.IsMaximal]
    (q : p.primesOver B) (hq : PrimeSpectrum.primesOverOrderIsoFiber A B p q = P) :
    let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
    Nonempty ((p.Fiber B ⧸ P.asIdeal) ≃ₐ[B] (q : Ideal B).ResidueField) := by
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let hlo : (q : Ideal B).LiesOver p := Ideal.primesOver.liesOver p q
  let φ1 : p.ResidueField →ₐ[A] (q:Ideal B).ResidueField :=
    Ideal.ResidueField.mapₐ p (q:Ideal B) (Algebra.ofId A B) hlo.over
  let φ2 : B →ₐ[A] (q:Ideal B).ResidueField := IsScalarTower.toAlgHom A B (q:Ideal B).ResidueField
  let Φ_A : p.ResidueField ⊗[A] B →ₐ[A] (q:Ideal B).ResidueField :=
    Algebra.TensorProduct.lift φ1 φ2 (fun x y => mul_comm _ _)
  have hker : P.asIdeal = RingHom.ker Φ_A.toRingHom := by rw [← hq]; rfl
  let Φ : p.Fiber B →ₐ[B] (q : Ideal B).ResidueField :=
    { Φ_A.toRingHom with
      commutes' := by
        intro b
        change φ1 1 * φ2 b = _
        rw [map_one, one_mul]
        rfl }
  set R : Subring (q:Ideal B).ResidueField := Φ_A.toRingHom.range
  have hfield : IsField R :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivRange _)).symm.toMulEquiv
  have hBmem : ∀ b : B, algebraMap B (q:Ideal B).ResidueField b ∈ R :=
    fun b => ⟨Algebra.TensorProduct.includeRight b, Φ.commutes b⟩
  have hQmem : ∀ c : B ⧸ (q:Ideal B),
      algebraMap (B ⧸ (q:Ideal B)) (q:Ideal B).ResidueField c ∈ R := by
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact hBmem b
  have hsurjA : Function.Surjective Φ_A := by
    rw [← AlgHom.range_eq_top, eq_top_iff]
    rintro y -
    obtain ⟨x, d, hd, hxd⟩ := IsFractionRing.div_surjective (A := B ⧸ (q:Ideal B)) y
    have hadne : algebraMap (B ⧸ (q:Ideal B)) (q:Ideal B).ResidueField d ≠ 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).not.mpr (nonZeroDivisors.ne_zero hd)
    rw [← hxd, div_eq_mul_inv]
    exact R.mul_mem (hQmem x) (Subring.inv_mem_of_isField hfield (hQmem d) hadne)
  exact ⟨(hker.symm : RingHom.ker Φ = P.asIdeal) ▸
    Ideal.quotientKerAlgEquivOfSurjective (f := Φ) hsurjA⟩

/-- For an ind-étale algebra `S` over `R` with `S` Noetherian, the fibre at a prime `p` is
`S`-algebra isomorphic to the product of the residue fields at the primes of `S` over `p`.

The fibre is Noetherian, reduced and zero-dimensional, hence Artinian, so it is the product of
its localizations at its maximal ideals; those maximal ideals are the primes over `p`, and the
corresponding factors are their residue fields by
`nonempty_fiber_residue_algEquiv_right`. -/
theorem nonempty_tensor_residue_algEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    (hi : StacksDraft.IndEtale R S) (p : Ideal R) [p.IsPrime] :
    Nonempty ((S ⊗[R] p.ResidueField) ≃ₐ[S]
      (∀ q : p.primesOver S, (q : Ideal S).ResidueField)) := by
  classical
  let C := p.Fiber S
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  obtain ⟨hred, hdim⟩ := fiber_reduced_and_krullDimLE_zero hi p
  have : IsNoetherianRing C := p.isNoetherianRing_fiber S
  have : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let e : p.primesOver S ≃ MaximalSpectrum C :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S p).toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum
  let ec : (S ⊗[R] p.ResidueField) ≃ₐ[S] C :=
    { (Algebra.TensorProduct.comm R S p.ResidueField).toRingEquiv with
      commutes' := fun s => by
        change (Algebra.TensorProduct.comm R S p.ResidueField) (s ⊗ₜ[R] 1) = 1 ⊗ₜ[R] s
        simp }
  let ek : ∀ q : p.primesOver S,
      (C ⧸ (e q).asIdeal) ≃ₐ[S] (q : Ideal S).ResidueField := fun q => by
    have : (PrimeSpectrum.primesOverOrderIsoFiber R S p q).asIdeal.IsMaximal :=
      (Ring.krullDimLE_zero_iff.mp hdim) _ inferInstance
    exact (nonempty_fiber_residue_algEquiv_right p q rfl).some
  exact ⟨ec.trans (((IsArtinianRing.equivPi C).restrictScalars S).trans
    (((AlgEquiv.piCongrLeft S (fun m : MaximalSpectrum C => C ⧸ m.asIdeal) e).symm).trans
      (AlgEquiv.piCongrRight ek)))⟩

end StacksDraft

namespace IsLocalRing

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] [IsLocalRing A]
  [IsLocalRing B] [Algebra A B] (L : Type v) [Field L]
  [Algebra (IsLocalRing.ResidueField A) L]
  [IsLocalRing.IsHenselization A L B]

include L in
/-- A henselization or strict henselization of a Noetherian local ring is Noetherian. -/
@[ega "IV 18.6.6" "(v)",
  ega "IV 18.8.8" "(iv)",
  sga "4 VIII 4.1" "more general",
  sga "4 VIII 4.4" "more general"]
theorem isNoetherianRing_of_isHenselization [IsNoetherianRing A] :
    IsNoetherianRing B := by
  let A' := ULift.{w} A
  let B' := ULift.{u} B
  let : Algebra A' B' := ULift.algebra' A B'
  have : IsLocalRing A' := ULift.ringEquiv.symm.isLocalRing
  have : IsLocalRing B' := ULift.ringEquiv.symm.isLocalRing
  have : IsNoetherianRing A' := isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  have : IsLocalHom (algebraMap A B) := IsLocalRing.IsHenselization.isLocalHom (L := L)
  have : IsLocalHom (algebraMap A' B') := ⟨fun a ha =>
    (isUnit_of_map_unit (algebraMap A B) a.down (ha.map (ULift.ringEquiv : B' ≃+* B).toRingHom)).map
      (ULift.ringEquiv : A' ≃+* A).symm.toRingHom⟩
  have hi : StacksDraft.IndEtale A' B' := StacksDraft.indEtale_of_equiv
    ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ => rfl)
    (IsLocalRing.IsHenselization.ind_etale (R := A) (L := L) (Rh := B))
  have : IsNoetherianRing B' :=
    StacksDraft.isNoetherianRing_of_indEtale (StacksDraft.indEtale_iff.mp hi)
  exact isNoetherianRing_of_ringEquiv B' ULift.ringEquiv

include L in
/-- The minimal primes of a henselization or strict henselization are exactly the prime ideals
lying over minimal primes of the original local ring. -/
theorem mem_minimalPrimes_iff_liesOver_minimalPrime_of_isHenselization
    [IsNoetherianRing A] (q : Ideal B) :
    q ∈ minimalPrimes B ↔
      (q.IsPrime ∧ ∃ p : Ideal A, p ∈ minimalPrimes A ∧ q.LiesOver p) := by
  have : Module.Flat A B := IsLocalRing.IsHenselization.flat (L := L)
  exact StacksDraft.minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero
    (fun p _ => (StacksDraft.fiber_reduced_and_krullDimLE_zero
      (IsLocalRing.IsHenselization.ind_etale (L := L)) p).2) q

include L in
/-- After base change to a henselization or strict henselization, the product of the residue
fields at the minimal primes is the product of the residue fields at the minimal primes
upstairs. -/
theorem nonempty_algEquiv_tensor_pi_residueField_minimalPrimes_of_isHenselization
    [IsNoetherianRing A] :
    Nonempty
      ((B ⊗[A] (∀ p : minimalPrimes A,
          @Ideal.ResidueField A _ p.1 p.2.1.1)) ≃ₐ[B]
        (∀ q : minimalPrimes B,
          @Ideal.ResidueField B _ q.1 q.2.1.1)) := by
  classical
  have : IsNoetherianRing B := isNoetherianRing_of_isHenselization (A := A) L
  have : ∀ p : minimalPrimes A, p.1.IsPrime := fun p => p.2.1.1
  have : ∀ q : minimalPrimes B, q.1.IsPrime := fun q => q.2.1.1
  let : Fintype (minimalPrimes A) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := A)).fintype
  let T := Σ p : minimalPrimes A, p.1.primesOver B
  let f : T → minimalPrimes B := fun t => ⟨t.2.1,
    (mem_minimalPrimes_iff_liesOver_minimalPrime_of_isHenselization L t.2.1).2
      ⟨t.2.2.1, t.1.1, t.1.2, t.2.2.2⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, fun q => ?_⟩
    · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ h
      obtain rfl : q = q' := congrArg Subtype.val h
      obtain rfl : p = p' := hq.2.over.trans hq'.2.over.symm
      rfl
    · obtain ⟨_, p, hp, hlo⟩ :=
        (mem_minimalPrimes_iff_liesOver_minimalPrime_of_isHenselization (A := A) L q.1).1 q.2
      exact ⟨⟨⟨p, hp⟩, ⟨q.1, q.2.1.1, hlo⟩⟩, rfl⟩
  let e : T ≃ minimalPrimes B := Equiv.ofBijective f hf
  let ek : ∀ p : minimalPrimes A,
      (B ⊗[A] p.1.ResidueField) ≃ₐ[B]
        (∀ q : p.1.primesOver B, (q : Ideal B).ResidueField) := fun p =>
    (StacksDraft.nonempty_tensor_residue_algEquiv
      (IsLocalRing.IsHenselization.ind_etale (R := A) (L := L) (Rh := B)) p.1).some
  let ec : (∀ t : T, (t.2 : Ideal B).ResidueField) ≃ₐ[B]
      (∀ p : minimalPrimes A, ∀ q : p.1.primesOver B, (q : Ideal B).ResidueField) :=
    { __ := LinearEquiv.piCurry B (fun (p : minimalPrimes A) (q : p.1.primesOver B) =>
          (q : Ideal B).ResidueField)
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  exact ⟨(Algebra.TensorProduct.piRight A B B (fun p : minimalPrimes A => p.1.ResidueField)).trans
    ((AlgEquiv.piCongrRight ek).trans (ec.symm.trans
      (AlgEquiv.piCongrLeft B (fun q : minimalPrimes B => q.1.ResidueField) e)))⟩

end IsLocalRing

end
