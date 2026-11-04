module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.RingTheory.Length.FlatLocalHom

/-!
# Flat pullback and the order of vanishing along a prime divisor

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces, let `Z' ⊆ Y` be a prime divisor with
generic point `ξ'` and let `Z ⊆ X` be a prime divisor with generic point `ξ` lying over `ξ'`.
Flatness makes the induced map of henselian local rings
`φ : 𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}` a flat local homomorphism, and the *multiplicity of `Z` over `Z'`*
is the colength

  `m = length_{𝒪^h_{X,ξ}} (𝒪^h_{X,ξ} / 𝔪^h_{Y,ξ'} 𝒪^h_{X,ξ})`.

The order of vanishing then pulls back with that multiplicity: for a rational function `g` on
`Y` whose ratio at `ξ'` is `a / b` with `a` and `b` nonzerodivisors,

  `ord_Z(g ∘ f) = m · ord_{Z'}(g)`,

because `length(𝒪^h_{X,ξ} / φ(a)) = m · length(𝒪^h_{Y,ξ'} / a)` by Stacks 02M1 and the same for
`b`. This is the pointwise content of Stacks 0EQA. When `𝔪^h_{Y,ξ'} 𝒪^h_{X,ξ} = 𝔪^h_{X,ξ}` the
multiplicity is one, and the orders agree outright; that is the pointwise content of Stacks
0EQH for the multiplicative torsor `q : T ⟶ X` of Stacks 0EQG, and Stacks 0EQQ is the same
identity read on a meromorphic section rather than on a rational function.

## Main definitions

* `AlgebraicGeometry.Space.primeDivisorFlatMultiplicity`: the multiplicity `m` above, as the
  colength of the extended maximal ideal.

## Main results

* `Ring.ord_map_of_flatHom`: for a flat local homomorphism `φ : A ⟶ B` of local rings,
  `ord_B(φ x) = length_B(B / 𝔪_A B) · ord_A(x)`. This is Stacks 02M1 applied to `A / xA`.
* `Ring.ordTotalFracInt_map_mk'_of_flatHom`: the same identity on the total rings of fractions,
  for a fraction `a / b` of nonzerodivisors and its image `φ(a) / φ(b)`.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_multiplicity_mul_ord` is **Stacks 0EQA**,
  coefficientwise: the order of vanishing of a rational function along a prime divisor of `X`
  is the multiplicity times its order along the prime divisor of `Y` beneath it.
* `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ord_of_extendedMaximalIdeal_eq` is **Stacks
  0EQH**, coefficientwise: when the maximal ideal extends to the maximal ideal, the order of
  vanishing along a prime divisor of `T` of the rational function attached to a meromorphic
  section equals the order of vanishing of that section along the prime divisor of `X` beneath.
* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_multiplicity_mul` is **Stacks 0EQQ**,
  coefficientwise: the same as Stacks 0EQA, for a meromorphic section of an invertible sheaf in
  place of a rational function, with its ratio at the generic point in place of the function.

## Implementation notes

### What is carried and what is proved

The whole identity rests on one computation, and that computation is carried out here: the
length of `𝒪^h_{X,ξ} / φ(a)` is the multiplicity times the length of `𝒪^h_{Y,ξ'} / a`, by Stacks
02M1 in the form `length_baseChange_eq_length_mul_length_quotient`. Nothing about the order of
vanishing pulling back is assumed; `Ring.ord_map_of_flatHom` derives it, and the geometric
statements are that derivation read along a prime divisor.

What is carried is the comparison datum, and only it. The local homomorphism
`φ : 𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}` is an explicit parameter together with its locality and flatness,
because the map of henselian local rings induced by a morphism of decent algebraic spaces is
not available in this development; so is the identification of the ratio of the pulled-back
object at `ξ` with the image under `φ` of the ratio at `ξ'`, which is the source's own step of
writing `s / s_{ξ'} = a / b` and pulling the fraction back. That rule `a / b ↦ f^♯a / f^♯b` is
canonical: it is `AlgebraicGeometry.Space.chartPullbackMeromorphicFunctions_mk'`, the chartwise
form of Stacks 0ENC, part (1), which this repository carries. The composite `g ∘ f|_{X'}` and
the pulled-back section `f^*s` themselves are parameters for the same reason: there is no
pullback of a rational function and no pullback of a meromorphic section along a morphism of
algebraic spaces here, only the chartwise fraction rule just named. Likewise the embeddings
`R(Y) ⟶ Q(𝒪^h_{Y,ξ'})` of Stacks 0ENK are the parameters `embY` and `embX`, exactly as in
Stacks 0EPT as carried by
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`.

### Why the statements are coefficientwise

The source states all three lemmas as identities of cycles. Neither side is available here: the
flat pullback of cycles along a morphism of algebraic spaces is Stacks 0EP8, which this
repository does not have — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatCompositeRelativeDimension` — and the principal
divisor `div(g)` of Stacks 0ENP is not available either, which is why Stacks 0EPT and 0EPV are
already carried coefficientwise in
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`. The statements below are
coefficientwise in the same sense and for the same reason: at each prime divisor of the source,
with the multiplicity of the source's formula appearing as the colength that computes it. The
case of the source's proof in which the prime divisor of the source dominates the target, where
both coefficients vanish, is bookkeeping internal to the flat pullback and does not arise in a
statement indexed by a prime divisor lying over a prime divisor.

### The multiplicity, and the two readings of the identity

Two different multiplicities occur in the source's formulas, and the colength below is the one
Stacks 02M1 computes with. It is the multiplicity with which `Z` occurs in the closed subspace
`f^{-1}(Z')`, so it is the coefficient that the flat pullback of Stacks 0EP8 attaches to `Z` in
`f^* div_Y(g)`; Stacks 0EE9 reads such a multiplicity as a length of a stalk, and along a flat
morphism that length is this colength.

The coefficient `m_{X',X}` of the source's right-hand side is a different number: the
multiplicity of an irreducible component `X'` in `X`. The statements below therefore have two
readings. Taking the source space to be `X` and `φ` the map induced by `f` gives the coefficient
of the left-hand side at `Z`; taking it to be a component `X'` and `φ` the map induced by
`f|_{X'}` gives the inner order of vanishing `ord_{Z,X'}(g ∘ f|_{X'})` of the right-hand side.
When `X` is integral the two coincide — there is one component, of multiplicity one — and the
statements are the source's identity read at the coefficient of `Z`. When `X` has several
components the step from the two readings to the cycle identity is the additivity of the
multiplicities of Stacks 0EE2 and Stacks 0EE9 over the irreducible components, which this
repository does not have; `AlgebraicGeometry.Space.moduleMultiplicity` and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` carry such multiplicities, but no
additivity of theirs is proved. That step is recorded in the attribute clauses as not covered.

The colength appears below as `AlgebraicGeometry.Space.primeDivisorFlatMultiplicity`. Its
finiteness is the hypothesis `hm`, which names the natural number it equals; the identity of
lengths itself holds in `ℕ∞` and needs no finiteness, and is stated that way in
`Ring.ord_map_of_flatHom`.

### Locality of the henselian local rings

That `𝒪^h_{X,ξ}` is a local ring is carried as an instance argument, as it is in
`StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison`: it follows from the
cofilteredness of the elementary étale neighbourhoods of `ξ`, Stacks 0BGV, which this
development does not have. The nontriviality, Noetherianness and dimension hypotheses are
carried as instance arguments too, quantified over all prime divisors, exactly as they are in
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`, whose
`AlgebraicGeometry.Space.orderOfVanishingSection` consumes them in that form.

The unit hypotheses on the rational functions are the regularity of those functions, and they
are hypotheses because `AlgebraicGeometry.Space.PrimeDivisor.ord` takes a proof of unitness as
an argument; the value does not depend on which proof is supplied, by
`Ring.ordTotalFracInt_congr`. This is the shape of Stacks 0EPT as carried.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EQH](https://stacks.math.columbia.edu/tag/0EQH)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct nonZeroDivisors

universe u z

/-! ### The order of vanishing under a flat local homomorphism -/

namespace Ring

/-- Multiplying a finite element of `ℕ∞` by a natural number commutes with `ENat.toNat`. -/
private theorem toNat_natCast_mul (m : ℕ) {k : ℕ∞} (hk : k ≠ ⊤) :
    ((m : ℕ∞) * k).toNat = m * k.toNat := by
  lift k to ℕ using hk
  rw [show ((m : ℕ∞) * (k : ℕ∞)) = ((m * k : ℕ) : ℕ∞) by push_cast; ring]
  simp

/-- A flat ring homomorphism carries nonzerodivisors to nonzerodivisors: multiplication by a
nonzerodivisor of the source stays injective after the flat base change. -/
@[ega "IV 20.6.9" "partial"]
theorem map_mem_nonZeroDivisors_of_flatHom {A B : Type*} [CommRing A] [CommRing B]
    {φ : A →+* B} (hflat : φ.Flat) {x : A} (hx : x ∈ A⁰) : φ x ∈ B⁰ := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hflat
  refine mem_nonZeroDivisors_iff_right.2 fun y hy => ?_
  refine Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hx ?_
  have hy' : y * algebraMap A B x = 0 := hy
  simpa [Algebra.smul_def, mul_comm] using hy'

/-- **The order of vanishing multiplies by the colength of the extended maximal ideal.** For a
flat local homomorphism `φ : A ⟶ B` of local rings and every `x ∈ A`,

  `ord_B(φ x) = length_B(B / 𝔪_A B) · ord_A(x)`.

Both sides are lengths of cyclic modules, and `B / φ(x)B` is the base change of `A / xA` along
`φ`, so this is the length identity of Stacks 02M1 for the module `A / xA`. The identity holds
in `ℕ∞`; no finiteness is needed. -/
@[ega "IV 4.7.1" "cyclic modules A/(x)"]
theorem ord_map_of_flatHom {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] {φ : A →+* B} (hloc : IsLocalHom φ) (hflat : φ.Flat) (x : A) :
    Ring.ord B (φ x) =
      Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) * Ring.ord A x := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hflat
  have : IsLocalHom (algebraMap A B) := hloc
  have halg : algebraMap A B = φ := rfl
  have hspan : Ideal.span {φ x} = Ideal.map (algebraMap A B) (Ideal.span {x}) := by
    rw [Ideal.map_span, Set.image_singleton, halg]
  calc Ring.ord B (φ x)
      = Module.length B (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {x})) := by
        rw [Ring.ord, hspan]
    _ = Module.length B (B ⊗[A] (A ⧸ Ideal.span {x})) :=
        (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
          (Ideal.span {x})).toLinearEquiv.length_eq
    _ = Module.length A (A ⧸ Ideal.span {x}) *
          Module.length B (B ⧸ extendedMaximalIdeal A B) :=
        (length_baseChange_eq_length_mul_length_quotient A B _).symm
    _ = Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) * Ring.ord A x := by
        rw [Ring.ord, mul_comm, extendedMaximalIdeal, halg]

/-- A fraction whose numerator and denominator are both nonzerodivisors is a unit of the total
ring of fractions, the inverse fraction being its inverse. -/
theorem isUnit_mk'_of_mem {A : Type*} [CommRing A] {K : Type*} [CommRing K] [Algebra A K]
    [IsFractionRing A K] (a : A) (ha : a ∈ A⁰) (b : A⁰) : IsUnit (IsLocalization.mk' K a b) :=
  ⟨⟨IsLocalization.mk' K a b, IsLocalization.mk' K (b : A) ⟨a, ha⟩,
    IsLocalization.mk'_mul_mk'_eq_one' (S := K) a b ha,
    by rw [mul_comm]; exact IsLocalization.mk'_mul_mk'_eq_one' (S := K) a b ha⟩, rfl⟩

/-- **The order of vanishing of a fraction multiplies by the colength of the extended maximal
ideal.** If `φ : A ⟶ B` is a flat local homomorphism of Noetherian local rings of Krull
dimension at most one and the colength of `𝔪_A B` is the natural number `m`, then the order of
vanishing of `φ(a) / φ(b)` in `Q(B)` is `m` times the order of vanishing of `a / b` in `Q(A)`.

The two orders are the differences of lengths given by `Ring.ordTotalFracInt_mk'`, and each of
the four lengths transforms by `Ring.ord_map_of_flatHom`; the lengths over `A` are finite
because `a` and `b` are nonzerodivisors of a Noetherian ring of dimension at most one. -/
theorem ordTotalFracInt_map_mk'_of_flatHom {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
    {KA : Type*} [CommRing KA] [Algebra A KA] [IsFractionRing A KA]
    {KB : Type*} [CommRing KB] [Algebra B KB] [IsFractionRing B KB]
    {φ : A →+* B} (hloc : IsLocalHom φ) (hflat : φ.Flat) {m : ℕ}
    (hm : Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) = (m : ℕ∞))
    (a b : A⁰)
    (hu : IsUnit (IsLocalization.mk' KA (a : A) b))
    (hu' : IsUnit (IsLocalization.mk' KB (φ (a : A))
      (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : B⁰))) :
    Ring.ordTotalFracInt B (IsLocalization.mk' KB (φ (a : A))
        (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : B⁰)) hu' =
      (m : ℤ) * Ring.ordTotalFracInt A (IsLocalization.mk' KA (a : A) b) hu := by
  have hanz : φ (a : A) ∈ B⁰ := map_mem_nonZeroDivisors_of_flatHom hflat a.2
  have hbnz : φ (b : A) ∈ B⁰ := map_mem_nonZeroDivisors_of_flatHom hflat b.2
  rw [Ring.ordTotalFracInt_congr B hu' (isUnit_mk'_of_mem _ hanz (⟨φ (b : A), hbnz⟩ : B⁰))
      (show IsLocalization.mk' KB (φ (a : A)) (⟨φ (b : A), hbnz⟩ : B⁰)
        = IsLocalization.mk' KB ((⟨φ (a : A), hanz⟩ : B⁰) : B) (⟨φ (b : A), hbnz⟩ : B⁰) from rfl),
    Ring.ordTotalFracInt_mk' A a b hu,
    Ring.ordTotalFracInt_mk' B (⟨φ (a : A), hanz⟩ : B⁰) (⟨φ (b : A), hbnz⟩ : B⁰) _]
  have hord : ∀ c : A⁰, Ring.ord B ((⟨φ (c : A), map_mem_nonZeroDivisors_of_flatHom hflat c.2⟩ :
      B⁰) : B) = (m : ℕ∞) * Ring.ord A (c : A) := fun c => by
    rw [← hm]
    exact ord_map_of_flatHom hloc hflat _
  rw [hord a, hord b, toNat_natCast_mul m (Ring.ord_ne_top a.2),
    toNat_natCast_mul m (Ring.ord_ne_top b.2)]
  push_cast
  ring

/-- The order of vanishing of any unit equal to `φ(a) / φ(b)` is `m` times that of any unit equal
to `a / b`. -/
private theorem ordTotalFracInt_map_eq_mul_of_eq_mk' {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
    {KA : Type*} [CommRing KA] [Algebra A KA] [IsFractionRing A KA]
    {KB : Type*} [CommRing KB] [Algebra B KB] [IsFractionRing B KB]
    {φ : A →+* B} (hloc : IsLocalHom φ) (hflat : φ.Flat) {m : ℕ}
    (hm : Module.length B (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) = (m : ℕ∞))
    (a b : A⁰) {x : KA} {y : KB} (hx : IsUnit x) (hy : IsUnit y)
    (hxe : x = IsLocalization.mk' KA (a : A) b)
    (hye : y = IsLocalization.mk' KB (φ (a : A))
      (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : B⁰)) :
    Ring.ordTotalFracInt B y hy = (m : ℤ) * Ring.ordTotalFracInt A x hx := by
  have huA := isUnit_mk'_of_mem (K := KA) _ a.2 b
  have huB := isUnit_mk'_of_mem (K := KB) _ (map_mem_nonZeroDivisors_of_flatHom hflat a.2)
    (⟨φ (b : A), map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ : B⁰)
  rw [Ring.ordTotalFracInt_congr B hy huB hye, Ring.ordTotalFracInt_congr A hx huA hxe]
  exact ordTotalFracInt_map_mk'_of_flatHom hloc hflat hm a b huA huB

end Ring

namespace AlgebraicGeometry.Space

/-! ### The multiplicity of a prime divisor over a prime divisor -/

/-- The *multiplicity of a prime divisor `Z ⊆ X` over a prime divisor `Z' ⊆ Y`* along a flat
local homomorphism `φ : 𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}` of the henselian local rings at their generic
points: the length of `𝒪^h_{X,ξ} / 𝔪^h_{Y,ξ'} 𝒪^h_{X,ξ}`.

This is the coefficient `m_{X',X}` of Stacks 0EQA and Stacks 0EQQ, in the form in which Stacks
02M1 computes with it: Stacks 0EE9 reads a multiplicity as the length of a stalk, and along a
flat morphism the relevant length is this colength. -/
def primeDivisorFlatMultiplicity (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdecX : IsDecentSpace B S hS X)
    (ZX : PrimeDivisor B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hdecY : IsDecentSpace B S hS Y)
    (ZY : PrimeDivisor B S hS Y)
    [IsLocalRing ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)]
    (φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
      ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) : ℕ∞ :=
  Module.length ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)
    (↥(ZX.genericHenselianLocalRing B S hS hX hdecX) ⧸ Ideal.map φ
      (IsLocalRing.maximalIdeal ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)))

section Pullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (hX : IsAlgebraicSpace B S hS X) (hdecX : IsDecentSpace B S hS X)
variable (ZX : PrimeDivisor B S hS X)
variable (hY : IsAlgebraicSpace B S hS Y) (hdecY : IsDecentSpace B S hS Y)
variable (ZY : PrimeDivisor B S hS Y)
variable [∀ W : PrimeDivisor B S hS X,
  IsLocalRing ↥(W.genericHenselianLocalRing B S hS hX hdecX)]
variable [∀ W : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdecX)]
variable [∀ W : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdecX)]
variable [∀ W : PrimeDivisor B S hS Y,
  IsLocalRing ↥(W.genericHenselianLocalRing B S hS hY hdecY)]
variable [∀ W : PrimeDivisor B S hS Y,
  IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hY hdecY)]
variable [∀ W : PrimeDivisor B S hS Y,
  Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hY hdecY)]
variable {φ : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY) →+*
  ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)}

/-! ### Stacks 0EQA -/

/-- **Stacks 0EQA, coefficientwise.** *The order of vanishing of a rational function pulls back
with multiplicities.* Let `f : X ⟶ Y` be flat, let `Z' ⊆ Y` and `Z ⊆ X` be prime divisors with
`Z` lying over `Z'`, let `φ : 𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{X,ξ}` be the induced flat local homomorphism and
let `m` be the multiplicity of `Z` over `Z'`. For a rational function `g` on `Y` whose ratio at
`ξ'` is `a / b` with `a` and `b` nonzerodivisors, and for the composite `g ∘ f|_X`, whose ratio
at `ξ` is therefore `φ(a) / φ(b)`,

  `ord_Z(g ∘ f|_X) = m · ord_{Z'}(g)`.

The multiplicity `m` is the one with which `Z` occurs in `f^{-1}(Z')`, so for `X` integral this
is the source's identity `f^* div_Y(g) = ∑ m_{X',X} (X' ⟶ X)_* div_{X'}(g ∘ f|_{X'})` read at
the coefficient of `Z`; for `X` with several components it is each of the two readings of that
identity, as the implementation notes explain.

Nothing about the conclusion is assumed. The multiplicity enters as the colength `hm` and the
whole content — that the order of vanishing multiplies by it — is `Ring.ord_map_of_flatHom`,
which is Stacks 02M1 applied to `𝒪^h_{Y,ξ'} / a` and to `𝒪^h_{Y,ξ'} / b`. -/
@[stacks 0EQA "coefficientwise at a prime divisor Z of X with generic point ξ lying over a prime
divisor Z' of Y with generic point ξ': the order of vanishing of a rational function pulls back
with the multiplicity, ord_Z(g ∘ f) = m · ord_{Z'}(g), where m is the colength of the extended
maximal ideal — the multiplicity with which Z occurs in the closed subspace f^{-1}(Z'), hence
the coefficient the flat pullback of Stacks 0EP8 attaches to Z. PROVED, not assumed: that the
order of vanishing multiplies by the multiplicity, from Stacks 02M1
(length_baseChange_eq_length_mul_length_quotient) applied to the cyclic modules O^h/a and O^h/b,
which is how Stacks 02M1 computes with a multiplicity. For X integral this is the source's
identity f^* div_Y(g) = ∑ m_{X',X} (X' → X)_* div_{X'}(g ∘ f|_{X'}) read at the coefficient of
Z, the one component having multiplicity one; the statement is coefficientwise because neither
side exists in this repository — the flat pullback of cycles is Stacks 0EP8 and the principal
divisor div(g) is Stacks 0ENP — and for that same reason Stacks 0EPT and 0EPV are already
carried coefficientwise here. NOT COVERED: for X with several irreducible components, the step
from this identity to the cycle identity, namely the additivity over the components of the
multiplicities of Stacks 0EE2 and Stacks 0EE9; the statement applies to X and to each component
X' separately, with m read in each, but no additivity of those multiplicities is proved in this
repository. RESTRICTED: carried as explicit named hypotheses are (i) the flat local homomorphism
φ of the henselian local rings at the generic points, the map of henselian local rings induced
by a morphism of decent algebraic spaces not being available here, with its locality and
flatness as the hypotheses hloc and hflat; (ii) the embeddings R(Y) → Q(O^h_{Y,ξ'}) and
R(X) → Q(O^h_{X,ξ}) of Stacks 0ENK as embY and embX, exactly as Stacks 0EPT carries them;
(iii) the composite g ∘ f|_X as the parameter gf together with hgf, that its ratio at ξ is the
image under φ of the ratio of g at ξ' — this repository has no pullback of a rational function
along a morphism of algebraic spaces, only the chartwise fraction rule a/b ↦ f-sharp a /
f-sharp b of Stacks 0ENC, which is what hgf states; and (iv) finiteness of the multiplicity, as
hm naming the natural number m it equals. Locality, Noetherianness and the dimension bound on
the henselian local rings are instance arguments, as they are for PrimeDivisor.ord and
orderOfVanishingSection themselves"]
theorem PrimeDivisor.ord_eq_multiplicity_mul_ord
    (hloc : IsLocalHom φ) (hflat : φ.Flat) {m : ℕ}
    (hm : primeDivisorFlatMultiplicity B S hS hX hdecX ZX hY hdecY ZY φ = (m : ℕ∞))
    (embY : rationalFunctions B S hS hY →+* ZY.genericTotalFractionRing B S hS hY hdecY)
    (embX : rationalFunctions B S hS hX →+* ZX.genericTotalFractionRing B S hS hX hdecX)
    (g : rationalFunctions B S hS hY) (gf : rationalFunctions B S hS hX)
    (a b : nonZeroDivisors ↥(ZY.genericHenselianLocalRing B S hS hY hdecY))
    (hg : embY g = IsLocalization.mk' (ZY.genericTotalFractionRing B S hS hY hdecY)
      (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) b)
    (hgf : embX gf = IsLocalization.mk' (ZX.genericTotalFractionRing B S hS hX hdecX)
      (φ (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)))
      (⟨φ (b : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)),
        Ring.map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
        nonZeroDivisors ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)))
    (hgu : IsUnit (embY g)) (hgfu : IsUnit (embX gf)) :
    ZX.ord B S hS hX hdecX (embX gf) hgfu =
      (m : ℤ) * ZY.ord B S hS hY hdecY (embY g) hgu :=
  Ring.ordTotalFracInt_map_eq_mul_of_eq_mk' hloc hflat hm a b hgu hgfu hg hgf

/-! ### Stacks 0EQQ -/

/-- **Stacks 0EQQ, coefficientwise.** *The order of vanishing of a meromorphic section pulls
back with multiplicities.* Let `f : X ⟶ Y` be flat, let `ℒ` be an `𝒪_Y`-module and `𝒩` an
`𝒪_X`-module standing for `f^*ℒ`, let `Z' ⊆ Y` and `Z ⊆ X` be prime divisors with `Z` over `Z'`,
and let `m` be the multiplicity of `Z` over `Z'` along the induced flat local homomorphism `φ`.
For a nonzero meromorphic section `s` of `ℒ` whose ratio `s / s_{ξ'}` at `ξ'` is `a / b`, and for
a meromorphic section `fs` of `𝒩` standing for `f^*s`, whose ratio at `ξ` against the
pulled-back generator is therefore `φ(a) / φ(b)`,

  `ord_{Z,𝒩}(fs) = m · ord_{Z',ℒ}(s)`.

The multiplicity `m` is the one with which `Z` occurs in `f^{-1}(Z')`, so for `X` integral this
is the source's identity `f^* div_ℒ(s) = ∑ n_i div_{f^*ℒ|_{X_i}}(s_i)` read at the coefficient
of `Z`; for `X` with several components it is each of the two readings of that identity, as the
implementation notes explain. The source proves it by passing to the multiplicative torsor
`q : T ⟶ Y`, where the section becomes a rational function, and then invoking Stacks 0EQA; here
the two are the same length computation, read on the ratio parameter of Stacks 0EPR rather than
on an embedding of the function field. -/
@[stacks 0EQQ "coefficientwise at a prime divisor Z of X with generic point ξ lying over a prime
divisor Z' of Y with generic point ξ': the order of vanishing of a meromorphic section pulls back
with the multiplicity, ord_{Z,f^*L}(f^*s) = m · ord_{Z',L}(s), where m is the colength of the
extended maximal ideal — the multiplicity with which Z occurs in f^{-1}(Z'), hence the
coefficient the flat pullback of Stacks 0EP8 attaches to Z. PROVED, not assumed: that the order
of vanishing multiplies by the multiplicity, from Stacks 02M1
(length_baseChange_eq_length_mul_length_quotient) applied to the cyclic modules O^h/a and O^h/b.
For X integral this is the source's identity f^* div_L(s) = ∑ n_i div_{f^*L|_{X_i}}(s_i) in
Z_{n+r-1}(X) read at the coefficient of Z, the one component having multiplicity one; the
statement is coefficientwise because the flat pullback of cycles is Stacks 0EP8, which this
repository does not have, and for the same reason Stacks 0EPV is already carried coefficientwise
here. NOT COVERED: for X with several irreducible components, the step from this identity to the
cycle identity, namely the additivity over the components of the multiplicities n_i = m_{X_i,X}
of Stacks 0EE2 and Stacks 0EE9; the statement applies to X and to each component X_i separately,
with m read in each, but no additivity of those multiplicities is proved in this repository.
RESTRICTED: carried as explicit named hypotheses are (i) the flat local homomorphism φ of the
henselian local rings at the generic points, with hloc and hflat; (ii) the module N and the
meromorphic section fs standing for f^*L and f^*s, this repository having no pullback of a
meromorphic section along a morphism of algebraic spaces, together with hfs, that the ratio of
fs at ξ against the pulled-back generator is the image under φ of the ratio of s at ξ' — which
is the source's own step of writing s/s_{ξ'} = a/b and pulling the fraction back, the chartwise
rule a/b ↦ f-sharp a / f-sharp b of Stacks 0ENC; (iii) the ratios of Stacks 0EPR at the two
generic points as the parameters ratioY and ratioX, exactly as Stacks 0EPR and 0EPV carry them;
and (iv) finiteness of the multiplicity, as hm naming the natural number m it equals. The
source's reduction through the multiplicative torsor of Stacks 0EQG is not used: the length
computation is the same one and is carried out directly on the ratio"]
theorem orderOfVanishingSection_eq_multiplicity_mul
    (hloc : IsLocalHom φ) (hflat : φ.Flat) {m : ℕ}
    (hm : primeDivisorFlatMultiplicity B S hS hX hdecX ZX hY hdecY ZY φ = (m : ℕ∞))
    (L : Modules.{u, max u z} B S hS Y hY) (N : Modules.{u, max u z} B S hS X hX)
    (s : MeromorphicSection.{u, z} B S hS Y hY L)
    (fs : MeromorphicSection.{u, z} B S hS X hX N)
    (ratioY : LocalRatio.{u, z} B S hS hY hdecY ZY L)
    (ratioX : LocalRatio.{u, z} B S hS hX hdecX ZX N)
    (a b : nonZeroDivisors ↥(ZY.genericHenselianLocalRing B S hS hY hdecY))
    (hs : (ratioY s : ZY.genericTotalFractionRing B S hS hY hdecY) =
      IsLocalization.mk' (ZY.genericTotalFractionRing B S hS hY hdecY)
        (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) b)
    (hfs : (ratioX fs : ZX.genericTotalFractionRing B S hS hX hdecX) =
      IsLocalization.mk' (ZX.genericTotalFractionRing B S hS hX hdecX)
        (φ (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)))
        (⟨φ (b : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)),
          Ring.map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
          nonZeroDivisors ↥(ZX.genericHenselianLocalRing B S hS hX hdecX))) :
    orderOfVanishingSection.{u, z} B S hS hX hdecX ZX N fs ratioX =
      (m : ℤ) * orderOfVanishingSection.{u, z} B S hS hY hdecY ZY L s ratioY :=
  Ring.ordTotalFracInt_map_eq_mul_of_eq_mk' hloc hflat hm a b (ratioY s).isUnit
    (ratioX fs).isUnit hs hfs

/-! ### Stacks 0EQH -/

/-- **Stacks 0EQH, coefficientwise.** *The divisor of a meromorphic section pulls back to the
divisor of the associated rational function on the multiplicative torsor.* Let `q : T ⟶ Y` be
the morphism of Stacks 0EQG for an invertible `𝒪_Y`-module `ℒ`, so that `q^*ℒ ≅ 𝒪_T` and a
nonzero meromorphic section `s` of `ℒ` becomes a nonzero meromorphic function `q^*(s)` on `T`.
Let `Z' ⊆ Y` be a prime divisor and `Z = q^{-1}(Z')`, and let `φ : 𝒪^h_{Y,ξ'} ⟶ 𝒪^h_{T,ξ}` be
the induced flat local homomorphism. Because `𝔪^h_{Y,ξ'} 𝒪^h_{T,ξ} = 𝔪^h_{T,ξ}`,

  `ord_Z(q^*(s)) = ord_{Z',ℒ}(s)`,

which is `q^* div_ℒ(s) = div_T(q^*(s))` coefficientwise.

The hypothesis `hmax` is the identity of ideals that Stacks 0EQG supplies, and it is what makes
the multiplicity one: the quotient is then the residue field of `𝒪^h_{T,ξ}`, whose length is
one, so `Ring.ord_map_of_flatHom` gives equality of the two orders rather than a multiple. -/
@[stacks 0EQH "coefficientwise at a prime divisor Z = q^{-1}(Z') of T: ord_Z(q^*(s)) =
ord_{Z',L}(s), which is the source's q^* div_L(s) = div_T(q^*(s)) read at the coefficient of Z.
No component bookkeeping arises: the source assumes the base integral, so the multiplicity of a
component is one, and the multiplicity of Z over Z' is one as well by hmax.
It is stated coefficientwise because the flat pullback of cycles is Stacks 0EP8, which this
repository does not have, and because the principal divisor div(q^*(s)) of Stacks 0ENP is not
available either; for the same reason Stacks 0EPT and 0EPV are already carried coefficientwise
here. The source's other case, a prime divisor of T dominating Y, where both coefficients
vanish, is bookkeeping internal to the flat pullback and does not arise in a statement indexed
by a prime divisor lying over a prime divisor. PROVED, not assumed: that the two orders of
vanishing are equal, from Stacks 02M1 (length_baseChange_eq_length_mul_length_quotient) through
Ring.ord_map_of_flatHom, the multiplicity being one because the extended maximal ideal is the
maximal ideal and the residue field has length one. RESTRICTED: carried as explicit named
hypotheses are (i) the flat local homomorphism φ : O^h_{Y,ξ'} → O^h_{T,ξ} with hloc and hflat,
and (ii) the identity hmax that the maximal ideal of O^h_{Y,ξ'} extends to the maximal ideal of
O^h_{T,ξ} — these are the two properties of q that Lemma 0EQG supplies and that the source uses
here, the morphism q itself being available in this repository only as
multiplicativeTorsorProjection, whose surjectivity, smoothness and relative dimension are not
proved there; (iii) the rational function qs standing for q^*(s), with the embedding embT of
Stacks 0ENK, and hqs, that its ratio at ξ is the image under φ of the ratio of s at ξ' — the
trivialization alpha : q^*L ≅ O_T is not constructed in this repository, as the clause of
Stacks 0EQG on multiplicativeTorsorBaseChange records, so the identification of q^*(s) as a
function is this hypothesis, which is the source's own step of writing s/s_{ξ'} = a/b and
pulling the fraction back; and (iv) the ratio of Stacks 0EPR at the generic point of Z' as the
parameter ratioY"]
theorem PrimeDivisor.ord_eq_ord_of_extendedMaximalIdeal_eq
    (hloc : IsLocalHom φ) (hflat : φ.Flat)
    (hmax : Ideal.map φ
        (IsLocalRing.maximalIdeal ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) =
      IsLocalRing.maximalIdeal ↥(ZX.genericHenselianLocalRing B S hS hX hdecX))
    (L : Modules.{u, max u z} B S hS Y hY)
    (s : MeromorphicSection.{u, z} B S hS Y hY L)
    (ratioY : LocalRatio.{u, z} B S hS hY hdecY ZY L)
    (embT : rationalFunctions B S hS hX →+* ZX.genericTotalFractionRing B S hS hX hdecX)
    (qs : rationalFunctions B S hS hX)
    (a b : nonZeroDivisors ↥(ZY.genericHenselianLocalRing B S hS hY hdecY))
    (hs : (ratioY s : ZY.genericTotalFractionRing B S hS hY hdecY) =
      IsLocalization.mk' (ZY.genericTotalFractionRing B S hS hY hdecY)
        (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)) b)
    (hqs : embT qs = IsLocalization.mk' (ZX.genericTotalFractionRing B S hS hX hdecX)
      (φ (a : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)))
      (⟨φ (b : ↥(ZY.genericHenselianLocalRing B S hS hY hdecY)),
        Ring.map_mem_nonZeroDivisors_of_flatHom hflat b.2⟩ :
        nonZeroDivisors ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)))
    (hqsu : IsUnit (embT qs)) :
    ZX.ord B S hS hX hdecX (embT qs) hqsu =
      orderOfVanishingSection.{u, z} B S hS hY hdecY ZY L s ratioY := by
  have hone : primeDivisorFlatMultiplicity B S hS hX hdecX ZX hY hdecY ZY φ = ((1 : ℕ) : ℕ∞) := by
    rw [primeDivisorFlatMultiplicity, hmax, Nat.cast_one]
    -- the quotient is the residue field, a simple module, so its length is one
    have : IsSimpleModule ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)
        (↥(ZX.genericHenselianLocalRing B S hS hX hdecX) ⧸
          IsLocalRing.maximalIdeal ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)) :=
      isSimpleModule_iff_isCoatom.2
        (IsLocalRing.maximalIdeal.isMaximal
          ↥(ZX.genericHenselianLocalRing B S hS hX hdecX)).out
    exact Module.length_eq_one _ _
  have := Ring.ordTotalFracInt_map_eq_mul_of_eq_mk' hloc hflat hone a b (ratioY s).isUnit hqsu
    hs hqs
  rwa [Nat.cast_one, one_mul] at this

end Pullback

end AlgebraicGeometry.Space

end
