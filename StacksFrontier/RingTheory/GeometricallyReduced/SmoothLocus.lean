module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.FormallySmooth.Field

/-!
# A geometrically reduced algebra over a field is smooth at its minimal primes

Stacks 056V says that a reduced scheme locally of finite type over a field is geometrically
reduced exactly when it has a dense open subscheme which is smooth over the field; the forward
implication is proved at the level of schemes in
`StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen`, with the dense open taken to be
the smooth locus. **This file proves the affine form of the half of that statement which a
ring-theoretic consumer needs**, and in the form in which density is used rather than as a
statement about the topology of `Spec`: for a geometrically reduced algebra `B` over a field `k`,
every *minimal* prime of `B` lies in `Algebra.smoothLocus k B`.

That is all density is ever used for. A subset of `Spec B` containing every minimal prime is
dense, because every prime contains a minimal one; conversely a dense *open* contains every
minimal prime. Stating the minimal-prime form keeps the file free of any topology and of any
finiteness hypothesis on `B`: no finite type, no finite presentation, no Noetherian hypothesis
enters, because the smooth locus here is Mathlib's `Algebra.smoothLocus`, defined by formal
smoothness of the localizations, and formal smoothness of a *field* extension is a purely
separability-theoretic condition.

The argument is short. At a minimal prime `q` of a reduced ring the localization `B_q` has a
single prime, so its maximal ideal is its nilradical, which is zero: `B_q` is a field. Geometric
reducedness passes from `B` to `B_q` because `k̄ ⊗[k] B_q` is a localization of the reduced ring
`k̄ ⊗[k] B` — localization commutes with base change — and a localization of a reduced ring is
reduced. A geometrically reduced field extension is separable (Stacks 030W) and a separable field
extension is formally smooth (Stacks 0321), which is membership of the smooth locus.

## Main results

* `Algebra.isReduced_tensorProduct_localization`: a base change of a localization is a
  localization of the base change, so it inherits reducedness.
* `Algebra.isGeometricallyReduced_localization`: geometric reducedness passes to localizations.
* `Algebra.isSmoothAt_of_mem_minimalPrimes`: **the affine form of the forward half of Stacks
  056V.** A geometrically reduced algebra over a field is smooth at each of its minimal primes.
* `Algebra.mem_smoothLocus_of_mem_minimalPrimes`: the same, phrased as membership of
  `Algebra.smoothLocus`.
* `Algebra.eq_zero_of_forall_exists_notMem_smoothLocus`: the use that is made of it. An element of
  a geometrically reduced algebra which is annihilated by an element outside each prime of the
  smooth locus is zero — the algebraic content of "the smooth locus is scheme-theoretically dense
  in a reduced fibre".

## Implementation notes

`Algebra.IsSmoothAt k q` is Mathlib's `Algebra.FormallySmooth k (Localization.AtPrime q)`, which
for an algebra of finite presentation agrees with the Stacks definition 00TB by
`Algebra.basicOpen_subset_smoothLocus_iff_smooth`; nothing below needs that comparison, since the
consumer of this file converts membership of the locus into smoothness of a localization with
exactly that lemma.

The localization of the base change is produced by
`IsLocalization.tensorProduct_tensorProduct_right`, which needs the comparison map
`k̄ ⊗[k] B → k̄ ⊗[k] B_q` as an algebra structure; it is supplied as the base change of
`B → B_q`, which is where the scalar tower `k → B → B_q` is used.

## References

* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
* [Stacks Project, Tag 0321](https://stacks.math.columbia.edu/tag/0321)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-- **A base change of a localization is reduced as soon as the base change is.** For a submonoid
`M` of a `k`-algebra `B` and a `k`-algebra `L`, the ring `L ⊗[k] B_M` is the localization of
`L ⊗[k] B` at the image of `M`, so it is reduced whenever `L ⊗[k] B` is. -/
public theorem isReduced_tensorProduct_localization (k B L : Type u) [CommRing k] [CommRing B]
    [Algebra k B] [CommRing L] [Algebra k L] (M : Submonoid B) (h : IsReduced (L ⊗[k] B)) :
    IsReduced (L ⊗[k] Localization M) := by
  let : Algebra (L ⊗[k] B) (L ⊗[k] Localization M) :=
    (Algebra.TensorProduct.map (AlgHom.id k L)
      (IsScalarTower.toAlgHom k B (Localization M))).toAlgebra
  have : IsScalarTower L (L ⊗[k] B) (L ⊗[k] Localization M) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  have := IsLocalization.tensorProduct_tensorProduct_right k L M (Localization M)
    (by ext x; simp [RingHom.algebraMap_toAlgebra])
  exact isReduced_localizationPreserves
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) (L ⊗[k] Localization M) h

/-- **Geometric reducedness passes to localizations.** If a `k`-algebra `B` over a field `k` is
geometrically reduced then so is every localization `B_M`: base change to the algebraic closure
turns `B_M` into a localization of the reduced ring `k̄ ⊗[k] B`. -/
public theorem isGeometricallyReduced_localization (k B : Type u) [Field k] [CommRing B]
    [Algebra k B] [Algebra.IsGeometricallyReduced k B] (M : Submonoid B) :
    Algebra.IsGeometricallyReduced k (Localization M) := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_tensorProduct_localization k B (AlgebraicClosure k) M
    ((Algebra.isGeometricallyReduced_field_iff k B).mp ‹_›)

/-- **Stacks 056V, affine case, at a minimal prime.** A geometrically reduced algebra `B` over a
field `k` is smooth at every minimal prime `q` of `B`.

`B` is reduced and `q` is minimal, so `B_q` has a unique prime ideal and its maximal ideal, being
its nilradical, vanishes: `B_q` is a field. It is geometrically reduced over `k` by
`Algebra.isGeometricallyReduced_localization`, hence separable over `k` by Stacks 030W, hence
formally smooth over `k` by Stacks 0321 — which is what smoothness at `q` means.

No `@[stacks 056V]` attribute is placed: the covering set of that tag is already complete, the
scheme-level equivalence being
`AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth`. This is the affine
specialization of one implication, read at a minimal prime rather than on a dense open. -/
public theorem isSmoothAt_of_mem_minimalPrimes (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsGeometricallyReduced k B] (q : Ideal B) [q.IsPrime] (hq : q ∈ minimalPrimes B) :
    Algebra.IsSmoothAt k q := by
  have : IsReduced B := Algebra.isReduced_of_isGeometricallyReduced k
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) :=
    Ring.KrullDimLE.of_isLocalization q hq _
  have : Algebra.IsGeometricallyReduced k (Localization.AtPrime q) :=
    isGeometricallyReduced_localization k B q.primeCompl
  let : Field (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced.toField
  exact (Algebra.FormallySmooth.iff_isSeparableExtension k (Localization.AtPrime q)).mpr
    (((Algebra.isSeparableExtension_tfae k (Localization.AtPrime q) (ringExpChar k)).out 4 1).mp
      ‹_›)

/-- **The minimal primes of a geometrically reduced algebra lie in the smooth locus.**
`Algebra.isSmoothAt_of_mem_minimalPrimes` phrased as membership of `Algebra.smoothLocus`, the
form in which `Algebra.basicOpen_subset_smoothLocus_iff_smooth` consumes it. -/
public theorem mem_smoothLocus_of_mem_minimalPrimes (k B : Type u) [Field k] [CommRing B]
    [Algebra k B] [Algebra.IsGeometricallyReduced k B] (p : PrimeSpectrum B)
    (hp : p.asIdeal ∈ minimalPrimes B) : p ∈ Algebra.smoothLocus k B :=
  isSmoothAt_of_mem_minimalPrimes k B p.asIdeal hp

/-- **The smooth locus is scheme-theoretically dense in a geometrically reduced algebra.** Let `B`
be a geometrically reduced algebra over a field `k` and let `x : B` be such that every prime of
the smooth locus of `B` contains an annihilator of `x` outside itself. Then `x = 0`.

This is the only use the constructibility argument of Stacks 0579 makes of the density of the
smooth locus. Every minimal prime of `B` lies in the smooth locus by
`Algebra.isSmoothAt_of_mem_minimalPrimes`, so the hypothesis puts `x` in every minimal prime; a
prime contains a minimal prime, so `x` lies in every prime, hence is nilpotent, hence is zero
because `B` is reduced. -/
public theorem eq_zero_of_forall_exists_notMem_smoothLocus {k B : Type u} [Field k] [CommRing B]
    [Algebra k B] [Algebra.IsGeometricallyReduced k B] {x : B}
    (hx : ∀ p : PrimeSpectrum B, p ∈ Algebra.smoothLocus k B →
      ∃ g : B, g ∉ p.asIdeal ∧ g * x = 0) :
    x = 0 := by
  have hred : IsReduced B := Algebra.isReduced_of_isGeometricallyReduced k
  refine hred.eq_zero x (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)
  obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := J) bot_le
  have hqp : q.IsPrime := hq.1.1
  obtain ⟨g, hgq, hgx⟩ := hx ⟨q, hqp⟩ (mem_smoothLocus_of_mem_minimalPrimes k B ⟨q, hqp⟩ hq)
  have hmem : g * x ∈ q := by rw [hgx]; exact q.zero_mem
  exact hqJ ((hqp.mem_or_mem hmem).resolve_left hgq)

end Algebra

end
