module

public import Mathlib
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHomProperties
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuasiFinite
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase

@[expose] public section

/-!
# Fibre properties and localization

Stacks Project, Chapter 15 "More on Algebra", Tag 0BK8.

A property of homomorphisms from fields to Noetherian rings which can be checked after
localizing at every prime can likewise be checked on the fibres of a ring map either before
localization, after localization at every prime above a prime, or after localization at every
maximal ideal.

## Main definitions

* `FibersHaveProperty` says that a property holds on every fibre of a ring map.
* `IsLocalForLocalization` is property (B): the property can be checked at all
  prime localizations of its target.
* `RespectsIsomorphisms` says that a property is invariant under isomorphisms
  of the source field and target ring.

## Main results

* `fibersHaveProperty_iff_localizations_at_primes_and_maximals` gives the three
  equivalent ways to check a fibre property.

## Implementation notes

A property is represented as a predicate on ring homomorphisms whose source is a field.
Such a property is required to respect isomorphisms, as is implicit for properties of ring maps.
For a prime of the target, its contraction is used as the prime below it; this is equivalent
to quantifying over pairs of primes with the target prime lying over the source prime.

## References

* [Stacks Project, Tag 0BK8](https://stacks.math.columbia.edu/tag/0BK8)

-/

/-! ### Stacks Tag 0BK8 -/

section

section

universe u v

/-! A *property of ring homomorphisms whose source is a field* is spelled out inline below, as
`∀ {k : Type _} {S : Type _} [Field k] [CommRing S], (k →+* S) → Prop`, rather than abbreviated.
A `Sort`-valued abbreviation for it would carry two universe parameters that can only ever appear
inside a single `max` in its own type, which `checkUnivs` rightly reports; and the two universes
cannot be merged, since the fibre statements below instantiate the shape at `u` and at `max u v`
simultaneously. Inlining keeps both universes and needs no linter exemption. -/

/-- A property of maps from fields respects isomorphisms if it is preserved by changing
either the source field or the target ring along a ring equivalence. -/
public abbrev RespectsIsomorphisms
    (P : ∀ {k : Type u} {S : Type v} [Field k] [CommRing S], (k →+* S) → Prop) : Prop :=
  (∀ {k : Type u} {S T : Type v} [Field k] [CommRing S] [CommRing T]
      (f : k →+* S) (e : S ≃+* T), P f → P (e.toRingHom.comp f)) ∧
    ∀ {k l : Type u} {S : Type v} [Field k] [Field l] [CommRing S]
      (f : k →+* S) (e : l ≃+* k), P f → P (f.comp e.toRingHom)

/-- A property of maps from fields is local for localization if it holds for a map to a
Noetherian ring exactly when it holds after localizing the target at every prime. This is
property (B) in the Stacks Project. -/
public abbrev IsLocalForLocalization
    (P : ∀ {k : Type u} {S : Type v} [Field k] [CommRing S], (k →+* S) → Prop) : Prop :=
  ∀ {k : Type u} {S : Type v} [Field k] [CommRing S] [IsNoetherianRing S] (f : k →+* S),
    P f ↔
      letI : Algebra k S := f.toAlgebra
      ∀ (p : Ideal S) [p.IsPrime], P (algebraMap k (Localization.AtPrime p))

/-- A property holds on the fibres of `A → B` if it holds for the canonical map from the
residue field at every prime of `A` to the corresponding fibre ring. -/
public abbrev FibersHaveProperty
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], P (algebraMap p.ResidueField (p.Fiber B))

end

section

set_option backward.isDefEq.respectTransparency false
open TensorProduct PrimeSpectrum

universe u v

section FiberLocalization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)]

private noncomputable abbrev toFiberLocalization :
    p.Fiber S →ₐ[p.ResidueField] p.Fiber (Localization.AtPrime q) :=
  Algebra.TensorProduct.lTensor _ (IsScalarTower.toAlgHom R S (Localization.AtPrime q))

@[instance_reducible]
private noncomputable def fiberLocalizationAlgebra :
    Algebra (p.Fiber S) (p.Fiber (Localization.AtPrime q)) :=
  (toFiberLocalization p q).toRingHom.toAlgebra

attribute [local instance] fiberLocalizationAlgebra

omit [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] in
private lemma algebraMap_fiberLocalization_apply (x : p.Fiber S) :
    algebraMap (p.Fiber S) (p.Fiber (Localization.AtPrime q)) x =
      toFiberLocalization p q x := rfl

omit [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q)] in
private lemma isScalarTower_fiberLocalization :
    IsScalarTower p.ResidueField (p.Fiber S) (p.Fiber (Localization.AtPrime q)) :=
  IsScalarTower.of_algHom (toFiberLocalization p q)

attribute [local instance] isScalarTower_fiberLocalization

private noncomputable abbrev toResidueField : p.Fiber S →ₐ[p.ResidueField] q.ResidueField :=
  Algebra.TensorProduct.lift (Algebra.ofId p.ResidueField q.ResidueField)
    (IsScalarTower.toAlgHom R S q.ResidueField) fun _ _ ↦ .all _ _

private noncomputable abbrev qbar : Ideal (p.Fiber S) := RingHom.ker (toResidueField p q)

private instance : (qbar p q).IsPrime := RingHom.ker_isPrime _

private abbrev fiberPoint :
    ↥(comap (algebraMap R S) ⁻¹' {(⟨p, ‹_›⟩ : PrimeSpectrum R)}) :=
  ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩

private lemma preimageEquivFiber_fiberPoint :
    PrimeSpectrum.preimageEquivFiber R S (⟨p, ‹_›⟩ : PrimeSpectrum R) (fiberPoint p q) =
      ⟨qbar p q, inferInstance⟩ := by
  refine PrimeSpectrum.ext ?_
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]
  congr 1
  ext x <;> simp

private lemma one_tmul_mem_qbar_iff (s : S) :
    (1 : p.ResidueField) ⊗ₜ[R] s ∈ qbar p q ↔ s ∈ q := by
  simp [RingHom.mem_ker, Ideal.algebraMap_residueField_eq_zero]

private lemma isUnit_algebraMap_of_notMem {T : Type*} [CommRing T] [Algebra R T] {r : R}
    (hr : r ∉ p) : IsUnit (algebraMap R (p.Fiber T) r) := by
  rw [IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber T)]
  exact (isUnit_iff_ne_zero.mpr
    fun h ↦ hr (Ideal.algebraMap_residueField_eq_zero.mp h)).map _

private lemma isUnit_algebraMap_of_notMem_qbar {x : p.Fiber S} (hx : x ∉ qbar p q) :
    IsUnit (algebraMap (p.Fiber S) (p.Fiber (Localization.AtPrime q)) x) := by
  obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul (S := S) p x
  have hru : IsUnit (algebraMap R (p.Fiber S) r) := isUnit_algebraMap_of_notMem p hr
  have hsq : s ∉ q := by
    rw [← one_tmul_mem_qbar_iff p q, ← e, Algebra.smul_def, mul_comm,
      Ideal.mul_unit_mem_iff_mem _ hru]
    exact hx
  refine isUnit_of_mul_isUnit_right (x := algebraMap (p.Fiber S)
    (p.Fiber (Localization.AtPrime q)) (algebraMap R (p.Fiber S) r)) ?_
  have key : algebraMap (p.Fiber S) (p.Fiber (Localization.AtPrime q))
        (algebraMap R (p.Fiber S) r) *
      algebraMap (p.Fiber S) (p.Fiber (Localization.AtPrime q)) x =
        (1 : p.ResidueField) ⊗ₜ[R] algebraMap S (Localization.AtPrime q) s := by
    rw [← map_mul, ← Algebra.smul_def, e]
    simp [algebraMap_fiberLocalization_apply]
  rw [key]
  simpa using (IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
    ⟨s, hsq⟩).map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)
      (B := Localization.AtPrime q))

private lemma isLocalization_atPrime_qbar :
    IsLocalization.AtPrime (p.Fiber (Localization.AtPrime q)) (qbar p q) := by
  set M := q.primeCompl.map (Algebra.TensorProduct.includeRight
    (R := R) (A := p.ResidueField) (B := S)) with hM
  have hL : IsLocalization M (p.Fiber (Localization.AtPrime q)) :=
    IsLocalization.tensorProduct_tensorProduct_right R p.ResidueField q.primeCompl
      (Localization.AtPrime q) (by ext x; simp [algebraMap_fiberLocalization_apply])
  refine IsLocalization.of_le (M := M) _ ?_ fun x hx ↦ isUnit_algebraMap_of_notMem_qbar p q hx
  rintro x ⟨s, hs, rfl⟩
  simpa [hM, Ideal.primeCompl, one_tmul_mem_qbar_iff] using hs

end FiberLocalization

/-- A property respecting isomorphisms transfers along an equivalence of targets compatible
with the structure maps. -/
private lemma property_of_ringEquiv
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P) {k : Type u} {S T : Type (max u v)} [Field k] [CommRing S]
    [CommRing T] {f : k →+* S} {g : k →+* T} (e : S ≃+* T) (he : ∀ x, e (f x) = g x)
    (h : P f) : P g :=
  (RingHom.ext he : e.toRingHom.comp f = g) ▸ hPiso.1 _ e h

section Pointwise

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing B]

private abbrev PointProperty
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (q : Ideal B)
    [q.IsPrime] : Prop :=
  letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver (q.under A) q
  P (algebraMap (q.under A).ResidueField
    ((q.under A).Fiber (Localization.AtPrime q)))

private theorem fiberIsNoetherian (p : Ideal A) [p.IsPrime] :
    IsNoetherianRing (p.Fiber B) := by
  let Sp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  let pSp := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
    (algebraMap (Localization.AtPrime p) Sp)
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let : IsNoetherianRing Sp :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid B p.primeCompl) Sp inferInstance
  let : IsNoetherianRing (Sp ⧸ pSp) :=
    isNoetherianRing_of_surjective Sp _ (Ideal.Quotient.mk pSp)
      Ideal.Quotient.mk_surjective
  exact isNoetherianRing_of_ringEquiv (Sp ⧸ pSp)
    (Ideal.Fiber.algEquivQuotient (S := B) p).symm.toRingEquiv

private lemma fiberProperty_congr_base
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    {T : Type v} [CommRing T] [Algebra A T]
    (p p' : Ideal A) [p.IsPrime] [p'.IsPrime] (e : p = p')
    (h : P (algebraMap p.ResidueField (p.Fiber T))) :
    P (algebraMap p'.ResidueField (p'.Fiber T)) := by
  subst p'
  exact h

private lemma fibersHaveProperty_iff_pointProperty
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P)
    (hP : IsLocalForLocalization P) :
    FibersHaveProperty P A B ↔
      ∀ (q : Ideal B) [q.IsPrime], PointProperty (A := A) (B := B) P q := by
  constructor
  · intro h q _
    let p := q.under A
    let : IsNoetherianRing (p.Fiber B) := fiberIsNoetherian p
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let : Algebra (p.Fiber B) (p.Fiber (Localization.AtPrime q)) :=
      fiberLocalizationAlgebra p q
    let : IsLocalization.AtPrime (p.Fiber (Localization.AtPrime q)) (qbar p q) :=
      isLocalization_atPrime_qbar p q
    have hp := (hP (algebraMap p.ResidueField (p.Fiber B))).mp (h p)
    have hr := hp (qbar p q)
    let e : Localization.AtPrime (qbar p q) ≃ₐ[p.Fiber B]
        p.Fiber (Localization.AtPrime q) :=
      IsLocalization.algEquiv (qbar p q).primeCompl _ _
    dsimp only [PointProperty]
    exact property_of_ringEquiv P hPiso (e.restrictScalars p.ResidueField).toRingEquiv
      (fun x => (e.restrictScalars p.ResidueField).commutes x) hr
  · intro h p _
    let : IsNoetherianRing (p.Fiber B) := fiberIsNoetherian p
    apply (hP (algebraMap p.ResidueField (p.Fiber B))).mpr
    intro r _
    let q0 := (PrimeSpectrum.primesOverOrderIsoFiber A B p).symm
      (⟨r, inferInstance⟩ : PrimeSpectrum (p.Fiber B))
    let q : Ideal B := q0.1
    have : q.IsPrime := q0.2.1
    have : q.LiesOver p := q0.2.2
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let : Algebra (p.Fiber B) (p.Fiber (Localization.AtPrime q)) :=
      fiberLocalizationAlgebra p q
    let : IsLocalization.AtPrime (p.Fiber (Localization.AtPrime q)) (qbar p q) :=
      isLocalization_atPrime_qbar p q
    have eqr : qbar p q = r := by
      have he := preimageEquivFiber_fiberPoint p q
      have hi := (PrimeSpectrum.primesOverOrderIsoFiber A B p).apply_symm_apply
        (⟨r, inferInstance⟩ : PrimeSpectrum (p.Fiber B))
      exact congrArg PrimeSpectrum.asIdeal (he.symm.trans hi)
    let : IsLocalization.AtPrime (p.Fiber (Localization.AtPrime q)) r := by
      simpa only [← eqr] using (isLocalization_atPrime_qbar p q)
    let e : Localization.AtPrime r ≃ₐ[p.Fiber B]
        p.Fiber (Localization.AtPrime q) :=
      IsLocalization.algEquiv r.primeCompl _ _
    have hq : P (algebraMap p.ResidueField (p.Fiber (Localization.AtPrime q))) := by
      have hq' := h q
      dsimp only [PointProperty] at hq'
      exact fiberProperty_congr_base P (q.under A) p (q.over_def p).symm hq'
    exact property_of_ringEquiv P hPiso (e.symm.restrictScalars p.ResidueField).toRingEquiv
      (fun x => (e.symm.restrictScalars p.ResidueField).commutes x) hq

end Pointwise

section SourceLocalization

open Algebra

variable {R T S : Type*} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
  [Algebra.IsEpi R T]

private noncomputable def tensorLid : T ⊗[R] S ≃ₐ[T] S := by
  let f : T ⊗[R] S →ₐ[T] S :=
    Algebra.TensorProduct.lift (Algebra.ofId T S) (IsScalarTower.toAlgHom R S S)
      (fun _ _ => .all _ _)
  apply AlgEquiv.ofBijective f
  have hf : (f : T ⊗[R] S → S) = TensorProduct.lid' R T S := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul t s => simp [f, TensorProduct.lid'_apply_tmul, Algebra.smul_def]
    | add x y hx hy => simp [map_add, hx, hy]
  rw [hf]
  exact (TensorProduct.lid' R T S).bijective

private noncomputable def fiberBaseEquiv (K : Type*) [Field K] [Algebra T K] [Algebra R K]
    [IsScalarTower R T K] : K ⊗[T] S ≃+* K ⊗[R] S :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[T] K)
      (tensorLid (R := R) (T := T) (S := S)).symm).trans
    (Algebra.TensorProduct.cancelBaseChange R T T K S)).toRingEquiv

private lemma epiLocalization (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    (M : Submonoid R) [IsLocalization M T] : Algebra.IsEpi R T :=
  (CommRingCat.epi_iff_epi).mp (IsLocalization.epi M T)

private noncomputable def residueEquiv (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] (M : Submonoid R) [IsLocalization M T]
    (q : Ideal T) [q.IsPrime] :
    (q.under R).ResidueField ≃ₐ[R] q.ResidueField := by
  let f := Ideal.ResidueField.mapₐ (q.under R) q (Algebra.ofId R T) rfl
  apply AlgEquiv.ofBijective f
  exact (RingHom.surjectiveOnStalks_of_isLocalization M T).residueFieldMap_bijective
    (q.under R) q rfl

private noncomputable def fiberBaseEquivPrime
    (R T : Type u) (S : Type*) [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    (M : Submonoid R) [IsLocalization M T]
    (q : Ideal T) [q.IsPrime] :
    q.Fiber S ≃+* (q.under R).Fiber S := by
  letI : Algebra.IsEpi R T := epiLocalization R T M
  let e1 : q.Fiber S ≃+* q.ResidueField ⊗[R] S :=
    fiberBaseEquiv (R := R) (T := T) (S := S) q.ResidueField
  let e2 : q.ResidueField ⊗[R] S ≃ₐ[R] (q.under R).Fiber S :=
    Algebra.TensorProduct.congr (residueEquiv R T M q).symm (AlgEquiv.refl : S ≃ₐ[R] S)
  exact e1.trans e2.toRingEquiv

private lemma fiberBaseEquivPrime_field
    (R T : Type u) (S : Type*) [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    (M : Submonoid R) [IsLocalization M T]
    (q : Ideal T) [q.IsPrime] (x : q.ResidueField) :
    fiberBaseEquivPrime R T S M q (algebraMap q.ResidueField (q.Fiber S) x) =
      algebraMap (q.under R).ResidueField ((q.under R).Fiber S)
        ((residueEquiv R T M q).symm x) := by
  simp [fiberBaseEquivPrime, fiberBaseEquiv, tensorLid,
    Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.one_def]

private lemma fiberBaseProperty_iff
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P)
    (R T : Type u) (S : Type v) [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    (M : Submonoid R) [IsLocalization M T]
    (q : Ideal T) [q.IsPrime] :
    P (algebraMap q.ResidueField (q.Fiber S)) ↔
      P (algebraMap (q.under R).ResidueField ((q.under R).Fiber S)) := by
  let e := fiberBaseEquivPrime R T S M q
  let f := residueEquiv R T M q
  constructor
  · intro h
    have h' := hPiso.1 _ e h
    have h'' := hPiso.2 _ f.toRingEquiv h'
    have he : ((e.toRingHom.comp (algebraMap q.ResidueField (q.Fiber S))).comp
        f.toRingEquiv.toRingHom) =
        algebraMap (q.under R).ResidueField ((q.under R).Fiber S) := by
      apply RingHom.ext
      intro x
      simpa [e, f] using fiberBaseEquivPrime_field R T S M q (f x)
    rwa [he] at h''
  · intro h
    have h' := hPiso.1 _ e.symm h
    have h'' := hPiso.2 _ f.symm.toRingEquiv h'
    have he : ((e.symm.toRingHom.comp
        (algebraMap (q.under R).ResidueField ((q.under R).Fiber S))).comp
        f.symm.toRingEquiv.toRingHom) = algebraMap q.ResidueField (q.Fiber S) := by
      apply RingHom.ext
      intro x
      apply e.injective
      simpa [e, f] using (fiberBaseEquivPrime_field R T S M q x).symm
    rwa [he] at h''

end SourceLocalization

section TargetLocalization

variable {K : Type u} {S T : Type (max u v)} [Field K]
  [CommRing S] [CommRing T] [Algebra K S] [Algebra S T]
  [Algebra K T] [IsScalarTower K S T] [IsNoetherianRing S]

private lemma property_of_isLocalization_0bk8
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P) (hP : IsLocalForLocalization P)
    (M : Submonoid S) [IsLocalization M T]
    (h : P (algebraMap K S)) : P (algebraMap K T) := by
  let : IsNoetherianRing T := IsLocalization.isNoetherianRing M T inferInstance
  apply (hP (algebraMap K T)).mpr
  intro q _
  let p := q.under S
  let : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  let e : Localization.AtPrime p ≃ₐ[S] Localization.AtPrime q :=
    IsLocalization.algEquiv p.primeCompl _ _
  have hp := (hP (algebraMap K S)).mp h p
  exact property_of_ringEquiv P hPiso (e.restrictScalars K).toRingEquiv
    (fun x => (e.restrictScalars K).commutes x) hp

end TargetLocalization

section FiberTargetLocalization

variable {A : Type u} {B C : Type v} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [IsNoetherianRing B]

private lemma fiberProperty_of_targetLocalization
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P) (hP : IsLocalForLocalization P)
    (M : Submonoid B) [IsLocalization M C]
    (p : Ideal A) [p.IsPrime]
    (h : P (algebraMap p.ResidueField (p.Fiber B))) :
    P (algebraMap p.ResidueField (p.Fiber C)) := by
  let f : p.Fiber B →ₐ[p.ResidueField] p.Fiber C :=
    Algebra.TensorProduct.lTensor _ (IsScalarTower.toAlgHom A B C)
  let : Algebra (p.Fiber B) (p.Fiber C) := f.toRingHom.toAlgebra
  let : IsScalarTower p.ResidueField (p.Fiber B) (p.Fiber C) :=
    IsScalarTower.of_algHom f
  let N := M.map (Algebra.TensorProduct.includeRight
    (R := A) (A := p.ResidueField) (B := B))
  let : IsLocalization N (p.Fiber C) :=
    IsLocalization.tensorProduct_tensorProduct_right A p.ResidueField M C
      (by ext x; rfl)
  let : IsNoetherianRing (p.Fiber B) := fiberIsNoetherian p
  exact property_of_isLocalization_0bk8 P hPiso hP N h

end FiberTargetLocalization

section GlobalToPrime

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing B]

private lemma fibersHaveProperty_iff_localizedAtPrimes
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P)
    (hP : IsLocalForLocalization P) :
    FibersHaveProperty P A B ↔
      ∀ (q : Ideal B) [q.IsPrime],
        letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
          Localization.AtPrime.algebraOfLiesOver (q.under A) q
        FibersHaveProperty P (Localization.AtPrime (q.under A))
          (Localization.AtPrime q) := by
  constructor
  · intro h q _
    let p := q.under A
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    intro r _
    have hr : P (algebraMap (r.under A).ResidueField
        ((r.under A).Fiber (Localization.AtPrime q))) :=
      fiberProperty_of_targetLocalization P hPiso hP q.primeCompl
        (r.under A) (h (r.under A))
    exact (fiberBaseProperty_iff P hPiso A (Localization.AtPrime p)
      (Localization.AtPrime q) p.primeCompl r).mpr hr
  · intro h
    apply (fibersHaveProperty_iff_pointProperty P hPiso hP).mpr
    intro q _
    let p := q.under A
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    let r := IsLocalRing.maximalIdeal (Localization.AtPrime p)
    have : r.IsPrime := inferInstance
    have hr := h q r
    have hp := (fiberBaseProperty_iff P hPiso A (Localization.AtPrime p)
      (Localization.AtPrime q) p.primeCompl r).mp hr
    dsimp only [PointProperty]
    exact fiberProperty_congr_base P (r.under A) p
      (Localization.AtPrime.under_maximalIdeal) hp

end GlobalToPrime

section NestedAtPrime

variable {R : Type*} [CommRing R] (p m : Ideal R) [p.IsPrime] [m.IsPrime]

@[instance_reducible]
private noncomputable def atPrimeAlgebraOfLe (h : p ≤ m) :
    Algebra (Localization.AtPrime m) (Localization.AtPrime p) :=
  (IsLocalization.lift (S := Localization.AtPrime m) (M := m.primeCompl)
    (g := algebraMap R (Localization.AtPrime p)) (fun x ↦ by
      exact (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
        ⟨x.1, fun hx ↦ x.2 (h hx)⟩))).toAlgebra

private lemma atPrimeIsScalarTower (h : p ≤ m) :
    letI : Algebra (Localization.AtPrime m) (Localization.AtPrime p) :=
      atPrimeAlgebraOfLe p m h
    IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime p) := by
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime p) :=
    atPrimeAlgebraOfLe p m h
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  let hg : ∀ y : m.primeCompl,
      IsUnit (algebraMap R (Localization.AtPrime p) y) := fun y ↦
    IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨y.1, fun hy ↦ y.2 (h hy)⟩
  change (algebraMap R (Localization.AtPrime p)) x =
    (IsLocalization.lift (S := Localization.AtPrime m) (g :=
      algebraMap R (Localization.AtPrime p)) hg)
      ((algebraMap R (Localization.AtPrime m)) x)
  exact (IsLocalization.lift_eq hg x).symm

end NestedAtPrime

section MaximalToGlobal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing B]

private lemma fibersHaveProperty_of_localizedAtMaximals
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P)
    (hP : IsLocalForLocalization P)
    (hmax : ∀ (m : Ideal B) [m.IsMaximal],
      letI : Algebra (Localization.AtPrime (m.under A)) (Localization.AtPrime m) :=
        Localization.AtPrime.algebraOfLiesOver (m.under A) m
      FibersHaveProperty P (Localization.AtPrime (m.under A))
        (Localization.AtPrime m)) :
    FibersHaveProperty P A B := by
  apply (fibersHaveProperty_iff_pointProperty P hPiso hP).mpr
  intro q _
  obtain ⟨m, hm, hqm⟩ := Ideal.ne_top_iff_exists_maximal.mp
    (show q ≠ ⊤ from (show q.IsPrime from inferInstance).ne_top)
  let : m.IsMaximal := hm
  let : m.IsPrime := hm.isPrime
  let p := q.under A
  let mA := m.under A
  have hpm : p ≤ mA := Ideal.comap_mono hqm
  let r : Ideal (Localization.AtPrime mA) :=
    Ideal.map (algebraMap A (Localization.AtPrime mA)) p
  have : r.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime mA hpm
  have hrunder : r.under A = p :=
    Ideal.under_map_of_isLocalizationAtPrime mA hpm
  let : Algebra (Localization.AtPrime mA) (Localization.AtPrime m) :=
    Localization.AtPrime.algebraOfLiesOver mA m
  have hr : P (algebraMap r.ResidueField (r.Fiber (Localization.AtPrime m))) :=
    hmax m r
  have hp' := (fiberBaseProperty_iff P hPiso A (Localization.AtPrime mA)
    (Localization.AtPrime m) mA.primeCompl r).mp hr
  have hp : P (algebraMap p.ResidueField (p.Fiber (Localization.AtPrime m))) :=
    fiberProperty_congr_base P (r.under A) p hrunder hp'
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime q) :=
    atPrimeAlgebraOfLe q m hqm
  let : IsScalarTower B (Localization.AtPrime m) (Localization.AtPrime q) :=
    atPrimeIsScalarTower q m hqm
  let : IsScalarTower A (Localization.AtPrime m) (Localization.AtPrime q) := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro x
    simp only [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q),
      IsScalarTower.algebraMap_apply B (Localization.AtPrime m) (Localization.AtPrime q)]
    rfl
  let N := q.primeCompl.map (algebraMap B (Localization.AtPrime m))
  let : IsLocalization N (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Localization.AtPrime m) (Localization.AtPrime q)
      m.primeCompl q.primeCompl (by
        intro x hx
        exact fun hxq ↦ hx (hqm hxq))
  let : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl (Localization.AtPrime m) inferInstance
  dsimp only [PointProperty]
  exact fiberProperty_of_targetLocalization P hPiso hP N p hp

end MaximalToGlobal

/-- A fibre property which is local for localization may be checked on all maps of localizations
at primes lying over one another, or only on those obtained from maximal ideals of the target. -/
@[stacks 0BK8]
public theorem fibersHaveProperty_iff_localizations_at_primes_and_maximals
    (P : ∀ {k : Type u} {S : Type (max u v)} [Field k] [CommRing S], (k →+* S) → Prop)
    (hPiso : RespectsIsomorphisms P)
    (hP : IsLocalForLocalization P)
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] :
    (FibersHaveProperty P A B ↔
      ∀ (q : Ideal B) [q.IsPrime],
        letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
          Localization.AtPrime.algebraOfLiesOver (q.under A) q
        FibersHaveProperty P (Localization.AtPrime (q.under A)) (Localization.AtPrime q)) ∧
    ((∀ (q : Ideal B) [q.IsPrime],
        letI : Algebra (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
          Localization.AtPrime.algebraOfLiesOver (q.under A) q
        FibersHaveProperty P (Localization.AtPrime (q.under A)) (Localization.AtPrime q)) ↔
      ∀ (m : Ideal B) [m.IsMaximal],
        letI : Algebra (Localization.AtPrime (m.under A)) (Localization.AtPrime m) :=
          Localization.AtPrime.algebraOfLiesOver (m.under A) m
        FibersHaveProperty P (Localization.AtPrime (m.under A)) (Localization.AtPrime m)) := by
  constructor
  · exact fibersHaveProperty_iff_localizedAtPrimes P hPiso hP
  · constructor
    · intro h m _
      exact h m
    · intro h
      exact (fibersHaveProperty_iff_localizedAtPrimes P hPiso hP).mp
        (fibersHaveProperty_of_localizedAtMaximals P hPiso hP h)

end

end

end
