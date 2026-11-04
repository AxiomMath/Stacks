module

import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import StacksFrontier.FieldTheory.Separable.TFAE
import StacksFrontier.FieldTheory.SeparableAlgebraic.TensorProduct
import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct

public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separable field extension is geometrically normal

Let `k` be a field and let `K/k` be a separable field extension, in the sense of Definition
[stacks, 030O](2): every subextension of `K/k` which is finitely generated over `k` has a
separating transcendence basis. This file proves that `K` is geometrically normal over `k`
(Definition [stacks, 0380]), i.e. that `k' ⊗[k] K` is a normal ring for every field extension
`k'/k`.

The content is that `k' ⊗[k] K` is a *field* whenever `k'/k` is purely inseparable. It is reduced
because `K/k` is separable and `k'` is a reduced `k`-algebra, which is Lemma [stacks, 030U]; and
its spectrum is a single point because `Spec(K ⊗[k] k') → Spec(K)` is a homeomorphism for `k'/k`
purely inseparable (Lemma [stacks, 0BRD]) while `Spec(K)` is a point. A reduced ring with a single
prime ideal is a field, and a field is a normal ring. Nothing more is needed: by Lemma
[stacks, 037Z] it is enough for geometric normality that `k' ⊗[k] K` be a normal ring for the
finite purely inseparable extensions `k'/k`, which the source arranges by base changing once to a
perfect closure of `k`.

## Main results

* `Stacks.GeometricallyNormal.SeparableExtension.solution`: the proof of
  `Algebra.IsGeometricallyNormal.of_isSeparableExtension`, Lemma [stacks, 0C30].

## Implementation notes

Three steps of the source's proof are not tags of the Stacks Project and are proved as helpers, each
stated in the generality it has rather than the one it is used in.

* `isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable` carries the mathematics.
  It lives in `StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct`, in namespace
  `Stacks.GeometricallyReduced.Separability`, beside Lemma 030U, which it uses. It is stated for an
  arbitrary purely inseparable extension `k'/k` rather than for the perfect closure the source
  names, nothing beyond pure inseparability being used; purely inseparable is Mathlib's
  `IsPurelyInseparable`, and Lemma [stacks, 046W] enters as the instance of it for
  `perfectClosure k (AlgebraicClosure k)`. "The spectrum is a point" is
  `Subsingleton (PrimeSpectrum _)`, and it comes from Mathlib's
  `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`, which is the conclusion of Lemma
  [stacks, 0BRD] for a purely inseparable field extension and an arbitrary base change (tag 0BRA):
  the residue field extensions of 0BRD's third hypothesis are, for an extension of two fields at
  their zero ideals, the extension `k'/k` itself, so the two routes prove the same thing. Lemma
  030U states reducedness in the order `K ⊗[k] k'`, and Mathlib's homeomorphism is for the same
  order, so both halves are proved for `K ⊗[k] k'` and the result transported once to `k' ⊗[k] K`
  by `Algebra.TensorProduct.comm` along `MulEquiv.isField`.
* `isGeometricallyNormal_of_forall_finiteDimensional_isPurelyInseparable` is item (3) ⇒ item (1) of
  Lemma [stacks, 037Z], packaged so that the perfect closure needed to state that lemma does not
  appear anywhere else. It is taken to be `perfectClosure k (AlgebraicClosure k)`, the purely
  inseparable closure of `k` in an algebraic closure, which is a perfect closure of `k` for the
  exponential characteristic of `k`, in characteristic zero the trivial extension.
* `IsNormalRing.of_isIntegrallyClosed` is "a normal domain is a normal ring", the comparison of
  Definition [stacks, 0309] with Definition [stacks, 00GV]: the localizations of a domain at its
  primes are domains, and localizing at a submonoid of nonzerodivisors preserves integral closure.
  It is stated for a normal domain, not for a field, since nothing in the proof uses more; the
  field case is reached through `IsField.toField`.

## References

* [Stacks 0C30](https://stacks.math.columbia.edu/tag/0C30), Lemma 10.166.6. Separability of a field
  extension is Definition 030O, geometric normality is Definition 0380, the criterion by purely
  inseparable base change is Lemma 037Z, reducedness of the base change is Lemma 030U, and pure
  inseparability of a perfect closure with the resulting bijection on spectra is Lemma 046W with
  Lemma 0BRD.
-/

@[expose] public section

open scoped TensorProduct
open Stacks.GeometricallyReduced.Separability

universe u v

namespace Stacks.GeometricallyNormal.SeparableExtension

/-- **Geometric normality is detected by the finite purely inseparable base changes**: item (3) ⇒
item (1) of Lemma [stacks, 037Z], stated for a `k`-algebra `A`. The perfect closure of `k` that
Lemma 037Z needs in order to be stated is supplied here as `perfectClosure k (AlgebraicClosure k)`,
the purely inseparable closure of `k` in an algebraic closure, which is perfect for the exponential
characteristic of `k`. -/
private theorem isGeometricallyNormal_of_forall_finiteDimensional_isPurelyInseparable
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (h : ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'], IsNormalRing (k' ⊗[k] A)) :
    Algebra.IsGeometricallyNormal k A := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : ExpChar (AlgebraicClosure k) p :=
    expChar_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
  have : PerfectRing (AlgebraicClosure k) p := PerfectField.toPerfectRing p
  set kp := (perfectClosure k (AlgebraicClosure k) : IntermediateField k (AlgebraicClosure k))
  have : ExpChar kp p := expChar_of_injective_algebraMap (algebraMap k kp).injective p
  have : IsPerfectClosure (algebraMap k kp) p := IsPurelyInseparable.isPRadical k kp p
  exact ⟨((Algebra.isNormalRing_tensorProduct_tfae k p A kp).out 3 1).mp h⟩

/-- **A separable field extension is geometrically normal.** Proof of Lemma [stacks, 0C30]: for
every finite purely inseparable extension `k'/k` the ring `k' ⊗[k] K` is a field, hence a normal
ring, and by Lemma [stacks, 037Z] that suffices. -/
public theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] : Algebra.IsGeometricallyNormal k K := by
  refine isGeometricallyNormal_of_forall_finiteDimensional_isPurelyInseparable k K
    fun k' _ _ _ _ => ?_
  let := (isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable k K k').toField
  exact IsNormalRing.of_isIntegrallyClosed _

end Stacks.GeometricallyNormal.SeparableExtension

end

/-!
# A separable field extension is geometrically normal

Let `k` be a field and let `K/k` be a separable field extension, that is, one all of whose finitely
generated subextensions are separably generated (Definition 030O (2)). Then `K` is geometrically
normal over `k` (Definition 0380): `k' ⊗[k] K` is a normal ring — every localization at a prime is
an integrally closed domain, Definition 00GV — for every field extension `k'/k`.

The reason is that geometric normality is already detected by a single base change, that to a
perfect closure `k^{perf}` of `k` (Lemma 037Z (4)), and `k^{perf} ⊗[k] K` is a *field*. It is
reduced because `K/k` is separable and `k^{perf}` is a reduced `k`-algebra (Lemma 030U), and it has
a unique prime ideal because the extension `k^{perf}/k` is purely inseparable (Lemma 046W), so that
`K → k^{perf} ⊗[k] K` is integral, bijective on spectra and with purely inseparable residue field
extensions (Lemma 0BRD). A reduced ring with a unique prime ideal has zero nilradical equal to that
prime, hence is a local ring whose maximal ideal is zero, hence a field; and a field is a normal
ring.

The converse holds as well: a geometrically normal `K` is geometrically reduced, since a normal
ring is reduced, and a geometrically reduced field extension is separable (Proposition 0322). It is
not part of this lemma, whose content is the implication the source states, and stating the
equivalence here would make the statement depend on that proposition.

Separability is *not* an algebraicity hypothesis in disguise: a purely transcendental extension
`k(x)/k` is separable, and in characteristic zero every extension is. So the lemma covers, beyond
the separable algebraic extensions, the function fields of geometrically integral varieties over
`k`, which is how it is used: for a geometrically normal domain `A` over `k` the fraction field is
geometrically normal by Lemma 06DE, and this lemma is the converse-facing criterion recognizing
geometric normality of a field from separability alone.

## Main results

* `Algebra.IsGeometricallyNormal.of_isSeparableExtension`: a separable field extension of a field
  `k` is geometrically normal over `k`.
* `Algebra.isGeometricallyNormal_iff_of_isSeparable`: Stacks 0C31, geometric normality of a
  `k'`-algebra is the same over `k` and over a separable algebraic extension `k'` of `k`.

## Implementation notes

The source's "separable field extension" is Definition 030O (2), `Algebra.IsSeparableExtension`,
the notion for extensions that need not be algebraic, and not Mathlib's `Algebra.IsSeparable`,
which is separability of an algebraic extension and would give a strictly weaker statement (it
excludes `k(x)/k`, one of the intended cases). The separably generated extensions of Definition
030O (1) are covered through Lemma 030X, which turns a separating transcendence basis into
separability of every finitely generated subextension.

The hypothesis is instance-implicit, as `Algebra.IsSeparableExtension` is a class and as the
project's other consumers of it take it (Lemma 00TU, Proposition 07BV). The conclusion is a class
too, and the statement is a theorem rather than an `instance`, matching Mathlib's siblings
`Algebra.FormallyUnramified.of_isSeparable` and `Algebra.FormallyEtale.of_isSeparable`: an instance
would be tried on every geometric-normality goal, including the ones about algebras that are not
fields. The name is those siblings' name with the source's separability substituted for Mathlib's.

`K` lives in its own universe, free of `k`'s, while the test fields quantified over inside
`Algebra.IsGeometricallyNormal` stay in the universe of `k`, exactly as in Definition 0380.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead: `Field k`, `Field K` and `Algebra k K` are the extension itself, and
`Algebra.IsSeparableExtension k K` is used by the conclusion, which fails without it — over
`k = 𝔽_p(t)` the extension `K = k(t^{1/p})` is not separable and `k^{perf} ⊗[k] K` is not even
reduced. Nothing restricts `K/k` to be algebraic, finitely generated, or of positive
characteristic.
(2) The scalars and the base are the source's: separability is of `K` over `k`, and geometric
normality is over the same `k`, so every tensor product inside the conclusion is over `k` and the
test fields are extensions of `k`, not of `K`.
(3) The source names no canonical map here; what the statement pins is the algebra structure
`Algebra k K` through which both hypothesis and conclusion are read, so `K` is the source's
extension of `k` and not a field carrying some other `k`-algebra structure — a distinction with
content, since `𝔽_p(t) → 𝔽_p(t)`, `t ↦ t^p`, makes a field separable over itself into an
inseparable extension.
(4) The instantiation is not degenerate: `K = k` is separable and geometrically normal, `K = k(x)`
gives the transcendental case, where `k' ⊗[k] k(x)` is the normal domain `k'(x)`, and over
`k = 𝔽_p(t)` the extension `K = k(t^{1/p})` satisfies neither side, so the conclusion is neither
vacuous nor automatic for field extensions.

## References

* [Stacks 0C31](https://stacks.math.columbia.edu/tag/0C31)
* [Stacks 0C30](https://stacks.math.columbia.edu/tag/0C30), Lemma 10.166.6, in the section
  "Geometrically normal algebras"; separability of a field extension is Definition 030O (2),
  geometric normality is Definition 0380, and the ingredients of the proof are Lemmas 030U, 046W
  and 0BRD together with Definition 046X.
-/

@[expose] public section

open scoped TensorProduct
open Stacks.GeometricallyReduced.Separability

namespace Algebra

/-- A separable field extension is geometrically normal: if `K/k` is a field extension all of whose
finitely generated subextensions are separably generated (Definition 030O (2)), then `k' ⊗[k] K` is
a normal ring for every field extension `k'/k`. -/
@[stacks 0C30 "Separability is the source's Definition 030O (2),
  `Algebra.IsSeparableExtension`, which does not require `K/k` algebraic, and not Mathlib's
  `Algebra.IsSeparable`; the converse implication is Proposition 0322 and is not part of this tag.",
  ega "IV 6.7.6" "separable ⇒ geom normal"]
public theorem IsGeometricallyNormal.of_isSeparableExtension {k K : Type*} [Field k] [Field K]
    [Algebra k K] [IsSeparableExtension k K] : IsGeometricallyNormal k K :=
  Stacks.GeometricallyNormal.SeparableExtension.solution

open Stacks.GeometricallyNormal.SeparableExtension in
/-- **Stacks 0C31.** For a separable algebraic field extension `k'/k`, a `k'`-algebra `A` is
geometrically normal over `k` if and only if it is geometrically normal over `k'`. Both directions
are tested on finite purely inseparable extensions `L` (Lemma 037Z). Over `k'`, the ring
`L ⊗[k'] A` is a localization of `L ⊗[k] A` (Lemma 0C2X). Over `k`, the ring `k' ⊗[k] L` is a field
and `L ⊗[k] A = (k' ⊗[k] L) ⊗[k'] A`. -/
@[stacks 0C31 "Separable algebraic is Mathlib's `Algebra.IsSeparable k k'`, which includes
  algebraicity; the `k`-algebra structure of `A` is the restriction of its `k'`-algebra structure."]
public theorem isGeometricallyNormal_iff_of_isSeparable (k k' A : Type*) [Field k] [Field k']
    [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] : IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · refine isGeometricallyNormal_of_forall_finiteDimensional_isPurelyInseparable k' A
      fun L _ _ _ _ ↦ ?_
    let _ : Algebra k L := ((algebraMap k' L).comp (algebraMap k k')).toAlgebra
    have : IsScalarTower k k' L := .of_algebraMap_eq' rfl
    obtain ⟨M, hM⟩ :=
      Algebra.TensorProduct.exists_isLocalization_mapOfCompatibleSMul_of_isSeparable k k' L A
    let _ := (Algebra.TensorProduct.mapOfCompatibleSMul k' k k' L A).toRingHom.toAlgebra
    exact (IsGeometricallyNormal.isNormalRing_tensorProduct_of_field (A := A) L).isLocalization M _
  · refine isGeometricallyNormal_of_forall_finiteDimensional_isPurelyInseparable k A
      fun L _ _ _ _ ↦ ?_
    obtain ⟨p, _⟩ := ExpChar.exists k
    have : IsSeparableExtension k k' := ((isSeparableExtension_tfae k k' p).out 1 4).mpr
      (IsGeometricallyReduced.of_isSeparable k k')
    let _ : Field (k' ⊗[k] L) := IsField.toField <| MulEquiv.isField
      (isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable k k' L)
      (TensorProduct.comm k k' L).toRingEquiv.toMulEquiv
    let e : (k' ⊗[k] L) ⊗[k'] A ≃+* L ⊗[k] A :=
      ((TensorProduct.comm k' (k' ⊗[k] L) A).trans
        (TensorProduct.cancelBaseChange k k' k' A L)).toRingEquiv.trans
        (TensorProduct.comm k A L).toRingEquiv
    exact IsNormalRing.congr e
      (IsGeometricallyNormal.isNormalRing_tensorProduct_of_field (k := k') (A := A) (k' ⊗[k] L))

end Algebra

end
