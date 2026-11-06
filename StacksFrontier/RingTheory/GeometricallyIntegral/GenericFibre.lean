module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.GeometricallyIntegral.IrreducibleLocus

/-!
# Fibres of a base change, and detecting that one of them is not a domain

Stacks 05FT is reduced in `StacksFrontier.RingTheory.GeometricallyIntegral.IrreducibleLocus` to one
statement about a single generic fibre: over a Noetherian domain `D` with a finite type algebra
`T`, some nonempty basic open of `Spec D` either lies in or misses
`Algebra.geometricallyIntegralFibreLocus D T`. Since the generic point `(0)` belongs to every
nonempty basic open of the spectrum of a domain, the two alternatives are decided in advance by
the generic fibre: if `T ⊗[D] K` is a domain for every field `K` into which `D` embeds, the
inclusion is the only possibility, and otherwise the disjointness is.

This file provides the tools for the second alternative, the one that spreads a *failure* out. The
failure is witnessed over one field `K`, by a pair of nonzero elements of `T ⊗[D] K` with product
zero; such a pair involves only finitely many elements of `K`, hence already lives over a finite
type `D`-subalgebra `E ⊆ K`. The problem is then to keep the two elements nonzero in the fibres
`T ⊗[D] κ(q)` at the primes `q` of `E`, and the tool for that is freeness: a nonzero element of a
free module is separated from zero by a coordinate functional, and a coordinate functional
survives every base change along which its value at the element survives. That is the content of
`Algebra.exists_ne_zero_forall_not_mem_geometricallyIntegralFibreLocus_of_free`, which inverts the
two coordinates and lands on the basic open of `Spec E` where they are both nonzero.

The passage from `E` back to `D` — that the primes of `E` in a basic open cover a basic open of
`Spec D` — is Chevalley's theorem and is carried out in
`StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut`.

## Main definitions

* `Algebra.fibreTensorEquiv`: for a `D`-algebra `E` and an `E`-algebra `F`, the ring isomorphism
  `T ⊗[D] F ≃+* F ⊗[E] (E ⊗[D] T)` exhibiting the fibre of `T` at `F` as the fibre at `F` of the
  base change of `T` to `E`.

## Main results

* `TensorProduct.one_tmul_ne_zero_of_apply_ne_zero`: a linear functional `φ : M →ₗ[R] F` into a
  commutative `R`-algebra `F` detects nonvanishing of `1 ⊗ₜ a` in `F ⊗[R] M`.
* `Module.Free.exists_linearMap_apply_ne_zero`: a nonzero element of a free module is nonzero on
  some coordinate functional.
* `Module.Free.one_tmul_ne_zero`: for `M` free over `E`, a nonzero `a : M` stays nonzero in
  `F ⊗[E] M` for every `E`-algebra `F` with `E → F` injective.
* `Algebra.not_mem_fibreLocus_comap`: a prime `q` of a `D`-algebra `E` whose fibre
  `F ⊗[E] (E ⊗[D] T)` at the residue field `F = κ(q)` fails an iso-invariant property `P`
  contracts to a prime of `D` outside the fibre locus of `P`, with the cases `P = IsDomain` and
  `P = IsReduced` recorded as
  `Algebra.not_mem_geometricallyIntegralFibreLocus_comap` and
  `Algebra.not_mem_geometricallyReducedFibreLocus_comap`.
* `Algebra.exists_ne_zero_forall_not_mem_geometricallyIntegralFibreLocus_of_free`: **the spreading
  step.** If `E ⊗[D] T` is free over the domain `E` and carries a pair of nonzero elements with
  product zero, then some nonempty basic open of `Spec E` consists of primes contracting outside
  the geometrically integral fibre locus of `T`.
* `Algebra.exists_ne_zero_forall_not_mem_geometricallyReducedFibreLocus_of_free`: the same
  spreading step for a nonzero nilpotent element, landing outside the geometrically reduced fibre
  locus.
* `Algebra.forall_not_mem_geometricallyIntegralFibreLocus_of_subsingleton`: the degenerate case,
  where `E ⊗[D] T` is the zero ring and *every* prime of `E` contracts outside the locus.
* `Algebra.not_mem_fibreLocus_iff`: membership in a fibre locus unfolded, in the form in which a
  failure is extracted from its negation.

## Implementation notes

The fibre of `T` over a prime `p` of `D` is `T ⊗[D] K` for the fields `K` over `D` with
`ker (D → K) = p`, which is the shape `Algebra.geometricallyIntegralFibreLocus` uses; the base
change of `T` to an auxiliary algebra `E` is written `E ⊗[D] T`, with the new base on the left,
which is the shape of both `Algebra.TensorProduct.cancelBaseChange` and of generic freeness
(`Module.Free.exists_ne_zero_of_isReduced`). `Algebra.fibreTensorEquiv` absorbs the resulting
single transposition, and only the ring structure of a fibre is ever used, so a `RingEquiv`
suffices and no compatibility of algebra structures has to be tracked.

Freeness enters twice and for the same reason. A coordinate functional `φ : M →ₗ[E] E` of a free
module turns the question "is `1 ⊗ₜ a` nonzero in `F ⊗[E] M`?" into the question "is `φ a`
nonzero in `F`?", which for `F = κ(q)` is the condition `φ a ∉ q` — an open condition on `q`, and
this is exactly what makes the failure spread. For `F` a field into which `E` embeds it is
automatic, which is how the relation `a * b = 0` is transported back from the chosen witness field
to `E` in `StacksFrontier.RingTheory.GeometricallyIntegral.SpreadOut`.

Nothing here is Noetherian: the Noetherian hypothesis of Stacks 0577 is used only through generic
freeness and Chevalley's theorem, both of which are applied elsewhere.

## References

* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 0577](https://stacks.math.columbia.edu/tag/0577)
* [Stacks Project, Tag 055A](https://stacks.math.columbia.edu/tag/055A)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace TensorProduct

/-- **A linear functional detects nonvanishing after base change.** Let `M` be a module over a
commutative ring `R`, let `F` be a commutative `R`-algebra and let `φ : M →ₗ[R] F`. If `φ a ≠ 0`
then `1 ⊗ₜ a ≠ 0` in `F ⊗[R] M`.

Indeed `φ` induces `F ⊗[R] M → F ⊗[R] F → F`, the second map being multiplication, and the
composite sends `1 ⊗ₜ a` to `φ a`. -/
theorem one_tmul_ne_zero_of_apply_ne_zero {R M F : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [CommRing F] [Algebra R F] (φ : M →ₗ[R] F) {a : M} (h : φ a ≠ 0) :
    (1 : F) ⊗ₜ[R] a ≠ 0 := by
  intro ha
  refine h ?_
  have := congrArg ((LinearMap.mul' R F).comp
    (TensorProduct.map (LinearMap.id (R := R) (M := F)) φ)) ha
  simpa using this

end TensorProduct

namespace Module.Free

/-- **A nonzero element of a free module has a nonzero coordinate.** If `M` is free over `E` and
`a : M` is nonzero then some coordinate functional of a basis of `M` is nonzero at `a`. -/
theorem exists_linearMap_apply_ne_zero (E : Type u) {M : Type u} [CommRing E] [AddCommGroup M]
    [Module E M] [Module.Free E M] {a : M} (ha : a ≠ 0) : ∃ φ : M →ₗ[E] E, φ a ≠ 0 := by
  classical
  set B := Module.Free.chooseBasis E M with hB
  have hrepr : B.repr a ≠ 0 := fun h => ha (by simpa using congrArg B.repr.symm h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
  exact ⟨B.coord i, by simpa using hi⟩

/-- **A free module injects into its base changes along injections.** If `M` is free over `E` and
`F` is an `E`-algebra with `E → F` injective, then a nonzero `a : M` has `1 ⊗ₜ a ≠ 0` in
`F ⊗[E] M`.

A coordinate functional nonzero at `a` composes with `E → F` to a functional nonzero at `a`, and
`TensorProduct.one_tmul_ne_zero_of_apply_ne_zero` applies. -/
theorem one_tmul_ne_zero (E F : Type u) {M : Type u} [CommRing E] [CommRing F] [Algebra E F]
    [AddCommGroup M] [Module E M] [Module.Free E M] (hinj : Function.Injective (algebraMap E F))
    {a : M} (ha : a ≠ 0) : (1 : F) ⊗ₜ[E] a ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_linearMap_apply_ne_zero E ha
  exact TensorProduct.one_tmul_ne_zero_of_apply_ne_zero ((Algebra.linearMap E F).comp φ)
    fun h => hφ (hinj (by simpa using h))

end Module.Free

namespace Algebra

/-- **The fibre of a base change.** For a `D`-algebra `E` and an `E`-algebra `F`, the fibre
`T ⊗[D] F` of a `D`-algebra `T` at `F` is the fibre at `F` of the base change `E ⊗[D] T` of `T` to
`E`. Both are `F ⊗[D] T` up to the commutativity of the tensor product and the cancellation
`F ⊗[E] (E ⊗[D] T) = F ⊗[D] T`. -/
noncomputable def fibreTensorEquiv (D T E F : Type u) [CommRing D] [CommRing T] [Algebra D T]
    [CommRing E] [Algebra D E] [CommRing F] [Algebra D F] [Algebra E F] [IsScalarTower D E F] :
    (T ⊗[D] F) ≃+* (F ⊗[E] (E ⊗[D] T)) :=
  (TensorProduct.comm D T F).toRingEquiv.trans
    (TensorProduct.cancelBaseChange D E E F T).symm.toRingEquiv

variable {D T : Type u} [CommRing D] [CommRing T] [Algebra D T]

/-- **Non-membership in a fibre locus, unfolded.** A prime `p` of `D` lies outside the fibre locus
of a property `P` exactly when some field `K` over `D` with `ker (D → K) = p` has `¬ P (T ⊗[D] K)`.
This is how a failure of a fibre property is extracted from the negation of membership. -/
theorem not_mem_fibreLocus_iff {P : ∀ (R : Type u) [CommRing R], Prop} (p : PrimeSpectrum D) :
    p ∉ fibreLocus D T P ↔
      ∃ (K : Type u) (_ : Field K) (_ : Algebra D K),
        RingHom.ker (algebraMap D K) = p.asIdeal ∧ ¬ P (T ⊗[D] K) := by
  refine ⟨fun h => ?_, fun ⟨K, _, _, hker, hnd⟩ hmem => hnd (hmem K hker)⟩
  simp only [fibreLocus, Set.mem_ofPred_eq, not_forall] at h
  obtain ⟨K, hfield, halg, hker, hnd⟩ := h
  exact ⟨K, hfield, halg, hker, hnd⟩

/-- `Algebra.not_mem_fibreLocus_iff` at the property of being a domain: a prime `p` of `D` lies
outside the geometrically integral fibre locus exactly when some field `K` over `D` with
`ker (D → K) = p` has `T ⊗[D] K` not a domain. -/
theorem not_mem_geometricallyIntegralFibreLocus_iff (p : PrimeSpectrum D) :
    p ∉ geometricallyIntegralFibreLocus D T ↔
      ∃ (K : Type u) (_ : Field K) (_ : Algebra D K),
        RingHom.ker (algebraMap D K) = p.asIdeal ∧ ¬ IsDomain (T ⊗[D] K) := by
  rw [geometricallyIntegralFibreLocus_eq_fibreLocus]
  exact not_mem_fibreLocus_iff p

/-- `Algebra.not_mem_fibreLocus_iff` at the property of being reduced: a prime `p` of `D` lies
outside the geometrically reduced fibre locus exactly when some field `K` over `D` with
`ker (D → K) = p` has `T ⊗[D] K` not reduced. -/
theorem not_mem_geometricallyReducedFibreLocus_iff (p : PrimeSpectrum D) :
    p ∉ geometricallyReducedFibreLocus D T ↔
      ∃ (K : Type u) (_ : Field K) (_ : Algebra D K),
        RingHom.ker (algebraMap D K) = p.asIdeal ∧ ¬ IsReduced (T ⊗[D] K) := by
  rw [geometricallyReducedFibreLocus_eq_fibreLocus]
  exact not_mem_fibreLocus_iff p

variable (E : Type u) [CommRing E] [Algebra D E]

/-- **A bad fibre of the base change is a bad fibre of `T`.** Let `P` be a property of rings
invariant under ring isomorphism. If the fibre of `E ⊗[D] T` at the residue field `κ(q)` of a
prime `q` of `E` does not have `P`, then the prime of `D` under `q` does not lie in the fibre
locus of `P` for `T`: the field `κ(q)` is a field over `D` with kernel that prime, and its fibre
is the same ring by `Algebra.fibreTensorEquiv`. -/
theorem not_mem_fibreLocus_comap {P : ∀ (R : Type u) [CommRing R], Prop}
    (hP : ∀ (R S : Type u) [CommRing R] [CommRing S], (R ≃+* S) → (P R ↔ P S))
    (q : PrimeSpectrum E) (hq : ¬ P (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T))) :
    PrimeSpectrum.comap (algebraMap D E) q ∉ fibreLocus D T P := by
  intro hmem
  refine hq ((hP _ _ (fibreTensorEquiv D T E q.asIdeal.ResidueField)).mp
    (hmem q.asIdeal.ResidueField ?_))
  rw [IsScalarTower.algebraMap_eq D E q.asIdeal.ResidueField, ← RingHom.comap_ker,
    Ideal.ker_algebraMap_residueField]
  rfl

/-- `Algebra.not_mem_fibreLocus_comap` at the property of being a domain: a prime `q` of `E` whose
fibre `κ(q) ⊗[E] (E ⊗[D] T)` is not a domain contracts outside the geometrically integral fibre
locus of `T`. -/
theorem not_mem_geometricallyIntegralFibreLocus_comap (q : PrimeSpectrum E)
    (hq : ¬ IsDomain (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T))) :
    PrimeSpectrum.comap (algebraMap D E) q ∉ geometricallyIntegralFibreLocus D T :=
  geometricallyIntegralFibreLocus_eq_fibreLocus D T ▸
    not_mem_fibreLocus_comap E (fun _ _ _ _ e => isDomain_congr e) q hq

/-- `Algebra.not_mem_fibreLocus_comap` at the property of being reduced: a prime `q` of `E` whose
fibre `κ(q) ⊗[E] (E ⊗[D] T)` is not reduced contracts outside the geometrically reduced fibre
locus of `T`. -/
theorem not_mem_geometricallyReducedFibreLocus_comap (q : PrimeSpectrum E)
    (hq : ¬ IsReduced (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T))) :
    PrimeSpectrum.comap (algebraMap D E) q ∉ geometricallyReducedFibreLocus D T :=
  geometricallyReducedFibreLocus_eq_fibreLocus D T ▸
    not_mem_fibreLocus_comap E (fun _ _ _ _ e => isReduced_congr e) q hq

/-- **The degenerate case of the spreading step.** If the base change `E ⊗[D] T` is the zero ring
then so is every one of its fibres, so no prime of `E` contracts into the geometrically integral
fibre locus of `T`. -/
theorem forall_not_mem_geometricallyIntegralFibreLocus_of_subsingleton
    (h : Subsingleton (E ⊗[D] T)) (q : PrimeSpectrum E) :
    PrimeSpectrum.comap (algebraMap D E) q ∉ geometricallyIntegralFibreLocus D T := by
  refine not_mem_geometricallyIntegralFibreLocus_comap E q fun hdom => ?_
  have : Subsingleton (q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T)) := by
    refine ⟨fun x y => ?_⟩
    have hz : ∀ z : q.asIdeal.ResidueField ⊗[E] (E ⊗[D] T), z = 0 := by
      intro z
      induction z with
      | tmul c m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
      | add z w hz hw => rw [hz, hw, add_zero]
    rw [hz x, hz y]
  exact (not_nontrivial_iff_subsingleton.mpr this) hdom.toNontrivial

/-- A functional `φ` with `φ a ∉ q` gives `1 ⊗ₜ a ≠ 0` in the fibre at the residue field of `q`. -/
private theorem one_tmul_ne_zero_residueField {M : Type*} [AddCommGroup M] [Module E M]
    (φ : M →ₗ[E] E) {a : M} (q : Ideal E) [q.IsPrime] (h : φ a ∉ q) :
    (1 : q.ResidueField) ⊗ₜ[E] a ≠ 0 :=
  TensorProduct.one_tmul_ne_zero_of_apply_ne_zero ((Algebra.linearMap E _).comp φ)
    (by simpa [Ideal.algebraMap_residueField_eq_zero] using h)

/-- **The spreading step.** Let `E` be a domain which is an algebra over `D`, suppose the base
change `E ⊗[D] T` is free as an `E`-module, and suppose it carries two nonzero elements `a`, `b`
with `a * b = 0`. Then there is a nonzero `h : E` such that every prime `q` of `E` with `h ∉ q`
contracts to a prime of `D` outside the geometrically integral fibre locus of `T`.

Take `h = φ a ⬝ ψ b` for coordinate functionals `φ`, `ψ` of a basis of `E ⊗[D] T` with `φ a ≠ 0`
and `ψ b ≠ 0`, which exist because `E ⊗[D] T` is free and `a`, `b` are nonzero, and which have
nonzero product because `E` is a domain. If `h ∉ q` then neither `φ a` nor `ψ b` lies in `q`, so
`1 ⊗ₜ a` and `1 ⊗ₜ b` are nonzero in the fibre `κ(q) ⊗[E] (E ⊗[D] T)` by
`TensorProduct.one_tmul_ne_zero_of_apply_ne_zero`, while their product `1 ⊗ₜ (a * b)` vanishes; so
that fibre is not a domain and `Algebra.not_mem_geometricallyIntegralFibreLocus_comap` applies. -/
theorem exists_ne_zero_forall_not_mem_geometricallyIntegralFibreLocus_of_free [IsDomain E]
    [Module.Free E (E ⊗[D] T)] {a b : E ⊗[D] T} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 0) :
    ∃ h : E, h ≠ 0 ∧ ∀ q : PrimeSpectrum E, h ∉ q.asIdeal →
      PrimeSpectrum.comap (algebraMap D E) q ∉ geometricallyIntegralFibreLocus D T := by
  obtain ⟨φ, hφ⟩ := Module.Free.exists_linearMap_apply_ne_zero E ha
  obtain ⟨ψ, hψ⟩ := Module.Free.exists_linearMap_apply_ne_zero E hb
  refine ⟨φ a * ψ b, mul_ne_zero hφ hψ, fun q hq => ?_⟩
  have hqa : φ a ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
  have hqb : ψ b ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
  refine not_mem_geometricallyIntegralFibreLocus_comap E q fun hdom => ?_
  have hA : (1 : q.asIdeal.ResidueField) ⊗ₜ[E] a ≠ 0 :=
    one_tmul_ne_zero_residueField E φ q.asIdeal hqa
  have hB : (1 : q.asIdeal.ResidueField) ⊗ₜ[E] b ≠ 0 :=
    one_tmul_ne_zero_residueField E ψ q.asIdeal hqb
  have hz : ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] a) *
      ((1 : q.asIdeal.ResidueField) ⊗ₜ[E] b) = 0 := by
    rw [TensorProduct.tmul_mul_tmul, hab, _root_.TensorProduct.tmul_zero]
  rcases mul_eq_zero.mp hz with h | h
  · exact hA h
  · exact hB h

/-- **The spreading step for geometric reducedness.** Let `E` be an algebra over `D`, suppose the
base change `E ⊗[D] T` is free as an `E`-module, and suppose it carries a nonzero nilpotent
element `a`. Then there is a nonzero `h : E` such that every prime `q` of `E` with `h ∉ q`
contracts to a prime of `D` outside the geometrically reduced fibre locus of `T`.

Unlike the integral case this needs no hypothesis on `E`: a single coordinate functional is
inverted, so no product of two of them has to be kept nonzero.

Take `h = φ a` for a coordinate functional `φ` of a basis of `E ⊗[D] T` with `φ a ≠ 0`, which
exists because `E ⊗[D] T` is free and `a` is nonzero. If `h ∉ q` then `1 ⊗ₜ a` is a nonzero
element of the fibre `κ(q) ⊗[E] (E ⊗[D] T)` by
`TensorProduct.one_tmul_ne_zero_of_apply_ne_zero`, and it is nilpotent because `a` is; so that
fibre is not reduced and `Algebra.not_mem_geometricallyReducedFibreLocus_comap` applies. -/
theorem exists_ne_zero_forall_not_mem_geometricallyReducedFibreLocus_of_free
    [Module.Free E (E ⊗[D] T)] {a : E ⊗[D] T} (ha : a ≠ 0) (hnil : IsNilpotent a) :
    ∃ h : E, h ≠ 0 ∧ ∀ q : PrimeSpectrum E, h ∉ q.asIdeal →
      PrimeSpectrum.comap (algebraMap D E) q ∉ geometricallyReducedFibreLocus D T := by
  obtain ⟨φ, hφ⟩ := Module.Free.exists_linearMap_apply_ne_zero E ha
  obtain ⟨n, hn⟩ := hnil
  refine ⟨φ a, hφ, fun q hq => ?_⟩
  refine not_mem_geometricallyReducedFibreLocus_comap E q fun hred => ?_
  refine one_tmul_ne_zero_residueField E φ q.asIdeal hq (hred.eq_zero _ ⟨n, ?_⟩)
  rw [TensorProduct.tmul_pow, one_pow, hn, _root_.TensorProduct.tmul_zero]

end Algebra

end
