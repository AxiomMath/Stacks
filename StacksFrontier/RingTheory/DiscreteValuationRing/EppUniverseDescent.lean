module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# The universe layer of Epp's theorem

`Stacks.EliminateRamification.EppTheorem` has four independent universes `uA`, `uB`, `uK`, `uL`,
and `Stacks.EliminateRamification`'s `_of_eppTheorem` needs it at two different instantiations, one
  of them
`.{uK, max uL uK, uK, max uL uK}`. The family induction that proves it, on the other hand, is
universe-**monomorphic** by design: a member of the family bundles its four carriers in one
`Type u`, which is what keeps an induction step universe-closed.

The induction stays monomorphic and the gap is bridged here: prove `EppTheorem.{u, u, u, u}` from
the induction, then lift `A`, `B`, `K`, `L` into a common universe, apply it there, and bring the
conclusion back.

This file is the first half of that bridge — the transports that make the lifted rings satisfy
Epp's hypotheses, and the descent that brings the produced solution field back down.

## The one step that is not bookkeeping

`EppTheorem` requires the solution field in `Type uK`, the universe of `K`. A monomorphic run
returns it in `Type u` with `u ≥ uK`, and there is no way to lower a type's universe. What saves it
is that the field is *finite* over `K`, hence algebraic, and `AlgebraicClosure K` already lives in
`Type uK`: `IsAlgClosed.lift` embeds the produced field there, and the range of that embedding is a
copy of it in the right universe. That is `exists_field_descent_of_module_finite`.

It is worth saying why the obvious alternative is wrong. One might hope to present the extension as
`K[X]/(f)` by a primitive element and transport the polynomial down. **Epp's solution fields are in
general inseparable** — that is the content of
`IsDiscreteValuationRing.weakSolution_isInseparable_and_inseparable_isSolution` — so a finite
extension here need not be simple, and no primitive element need exist.

## What is transported, and how cheaply

Once `ULift.algebra'` is switched on as a local instance the algebra layer is found by instance
search, and the rest is short:

* `Algebra (ULift A) (ULift B)` — instance search, via `ULift.algebra'` composed with the global
  `ULift.algebra`. Both structure maps are `ULift.up ∘ · ∘ ULift.down`, which is why the scalar
  towers below reduce to associativity in the ring downstairs.
* `IsDomain`, `IsDiscreteValuationRing` — `MulEquiv.isDomain` and
  `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing` along `ULift.ringEquiv`.
* `Field (ULift K)` — already an instance in Mathlib.
* `IsScalarTower` — one line, as above.
* `IsFractionRing` — the only one with no transport lemma available, because in this toolchain
  `IsLocalization` is stated through `Submonoid.IsLocalizationMap` and the submonoid
  `nonZeroDivisors` has to be matched across the equivalence as well. Its three fields are proved
  directly here.

## Main results

* `Stacks.EppTheorem.isDomain_ulift`, `Stacks.EppTheorem.isDiscreteValuationRing_ulift` — the
  ring-theoretic
  classes on a lifted discrete valuation ring.
* `Stacks.EppTheorem.isScalarTower_ulift` — a scalar tower lifts.
* `Stacks.EppTheorem.isFractionRing_ulift` — a fraction field lifts.
* `Stacks.EppTheorem.isExtension_ulift` — an extension of discrete valuation rings lifts.
* `Stacks.EppTheorem.charP_of_ringEquiv`, `Stacks.EppTheorem.expChar_of_ringEquiv` — the two
  characteristic
  hypotheses, transported backwards along a ring isomorphism.
* `Stacks.EppTheorem.isSeparable_of_ringEquiv_square`,
  `Stacks.EppTheorem.mem_perfectCore_ringEquiv`,
  `Stacks.EppTheorem.eppCondition_of_ringEquiv_square` — **Epp's residue-field condition** under an
  isomorphism of the data. Stated for an arbitrary isomorphism rather than for `ULift`, which is
  both the honest generality and what makes the `ULift` case `rfl`.
* `Stacks.EppTheorem.aeval_map_ringEquiv_square`, `Stacks.EppTheorem.isIntegral_ringEquiv_square`,
  `Stacks.EppTheorem.integralClosureRingEquivOfSquare` (with its `_coe` computation rule) — the
    integral
  closure under an isomorphism that moves the **base** as well as the ambient ring, which
  `Stacks.DiscreteValuationRing.EppLevelInduction.integralClosureRingEquivOfAlgEquiv` does not
    cover.
* `Stacks.EppTheorem.exists_field_descent_of_module_finite` — **the descent.** A finite extension
  of `K : Type uK` presented in any universe has an isomorphic copy in `Type uK`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
* [The Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
-/

@[expose] public noncomputable section

namespace Stacks.EppTheorem

universe uA uB uK uL v

attribute [local instance] ULift.algebra'

/-- A lifted domain is a domain. -/
theorem isDomain_ulift (A : Type uA) [CommRing A] [IsDomain A] : IsDomain (ULift.{v} A) :=
  MulEquiv.isDomain A (ULift.ringEquiv : ULift.{v} A ≃+* A).toMulEquiv

/-- A lifted discrete valuation ring is a discrete valuation ring. -/
theorem isDiscreteValuationRing_ulift (A : Type uA) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    letI := isDomain_ulift.{uA, v} A
    IsDiscreteValuationRing (ULift.{v} A) :=
  let := isDomain_ulift.{uA, v} A
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (ULift.ringEquiv : ULift.{v} A ≃+* A).symm

/-- **A scalar tower lifts.**

Every structure map between lifted rings is `ULift.up ∘ · ∘ ULift.down` for the corresponding map
downstairs, so the tower identity `(x • y) • z = x • (y • z)` unfolds to associativity of
multiplication in the ring downstairs, after the original tower rewrites the outer coefficient. -/
theorem isScalarTower_ulift (A : Type uA) (B : Type uB) (L : Type uL)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L] :
    IsScalarTower (ULift.{v} A) (ULift.{v} B) (ULift.{v} L) := by
  constructor
  intro x y z
  apply ULift.down_injective
  simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, mul_assoc]

/-- **A fraction field lifts.**

The only one of Epp's hypotheses with no transport lemma to cite. In this toolchain
`IsLocalization` is stated through `Submonoid.IsLocalizationMap`, whose three fields are proved
here directly: `map_units` because a nonzero element of `A` stays nonzero in the field `K` and
`ULift K` is a field; `surj` by lifting a fraction from downstairs, which needs the lifted
denominator to be a non-zero-divisor and hence needs `IsDomain (ULift A)`; and `exists_of_eq` from
injectivity of `algebraMap A K`, with `c = 1`. -/
theorem isFractionRing_ulift (A : Type uA) (K : Type uK)
    [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] :
    letI := isDomain_ulift.{uA, v} A
    IsFractionRing (ULift.{v} A) (ULift.{v} K) := by
  let := isDomain_ulift.{uA, v} A
  have hmap : ∀ x : ULift.{v} A,
      algebraMap (ULift.{v} A) (ULift.{v} K) x = ULift.up (algebraMap A K x.down) := fun _ => rfl
  have hinjA : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have hy : y.val.down ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero y (ULift.down_injective (by simpa using h))
    rw [hmap]
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    exact (map_ne_zero_iff _ hinjA).mpr hy (by simpa using congrArg ULift.down h)
  · intro z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z.down
    have hs0 : (ULift.up.{v} s.val : ULift.{v} A) ∈ nonZeroDivisors (ULift.{v} A) :=
      mem_nonZeroDivisors_of_ne_zero fun h =>
        nonZeroDivisors.coe_ne_zero s (by simpa using congrArg ULift.down h)
    exact ⟨⟨ULift.up a, ⟨ULift.up s.val, hs0⟩⟩, ULift.down_injective (by simpa [hmap] using hs)⟩
  · intro x y hxy
    have hxyd : x = y := ULift.down_injective (hinjA (by simpa [hmap] using hxy))
    exact ⟨1, by rw [hxyd]⟩

/-- **An extension of discrete valuation rings lifts.**

`IsDiscreteValuationRing.IsExtension` is `FaithfulSMul` together with `IsLocalHom` on the structure
map, and both transport along `ULift.ringEquiv`: injectivity because the lifted map is
`ULift.up ∘ · ∘ ULift.down`, and the local-hom property because a unit of `ULift B` is a unit of
`B` and conversely. -/
theorem isExtension_ulift (A : Type uA) (B : Type uB)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B] :
    letI := isDomain_ulift.{uA, v} A
    letI := isDomain_ulift.{uB, v} B
    letI := isDiscreteValuationRing_ulift.{uA, v} A
    letI := isDiscreteValuationRing_ulift.{uB, v} B
    IsDiscreteValuationRing.IsExtension (ULift.{v} A) (ULift.{v} B) := by
  let := isDomain_ulift.{uA, v} A
  let := isDomain_ulift.{uB, v} B
  let := isDiscreteValuationRing_ulift.{uA, v} A
  let := isDiscreteValuationRing_ulift.{uB, v} B
  have hmap : ∀ x : ULift.{v} A,
      algebraMap (ULift.{v} A) (ULift.{v} B) x = ULift.up (algebraMap A B x.down) := fun _ => rfl
  have hinj : Function.Injective (algebraMap (ULift.{v} A) (ULift.{v} B)) := by
    intro x y hxy
    rw [hmap, hmap] at hxy
    exact ULift.down_injective
      (FaithfulSMul.algebraMap_injective A B (by simpa using congrArg ULift.down hxy))
  have hlocal : IsLocalHom (algebraMap (ULift.{v} A) (ULift.{v} B)) := by
    refine ⟨fun a ha => ?_⟩
    rw [hmap] at ha
    have hdown : IsUnit (algebraMap A B a.down) :=
      ha.map (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom
    have hup : IsUnit (ULift.up.{v} a.down : ULift.{v} A) :=
      (IsLocalHom.map_nonunit _ hdown).map (ULift.ringEquiv : ULift.{v} A ≃+* A).symm.toRingHom
    exact ULift.up_down a ▸ hup
  exact { __ := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj, __ := hlocal }

/-! ### Epp's residue-field condition under an isomorphism of the data

`Stacks.EppTheorem.EppCondition A B p` is `∀ x ∈ perfectCore (ResidueField B) p, IsSeparable
(ResidueField A) x`, so transporting it needs more than a pair of isomorphisms of residue fields:
it needs the square over them to commute, because `IsSeparable` is a statement about the *base*.

The two lemmas below are stated for an arbitrary isomorphism of the data rather than for `ULift`,
both because that is the honest generality and because the `ULift` instance is then immediate with
`rfl` for the square.
-/

/-- Evaluating a transported polynomial at a transported point transports the evaluation. -/
private theorem aeval_map_ringEquiv_square_aux {R R' E E' : Type*} [CommRing R] [CommRing R']
    [CommRing E] [CommRing E'] [Algebra R E] [Algebra R' E'] (eR : R ≃+* R') (eE : E ≃+* E')
    (hsq : ∀ y : R, eE (algebraMap R E y) = algebraMap R' E' (eR y))
    (x : E) (p : Polynomial R) :
    Polynomial.aeval (eE x) (p.map (eR : R →+* R')) = eE (Polynomial.aeval x p) := by
  have hcomp : RingHom.comp (algebraMap R' E') (eR : R →+* R')
      = RingHom.comp (eE : E →+* E') (algebraMap R E) := by
    ext y
    simpa using (hsq y).symm
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, Polynomial.aeval_def]
  exact (Polynomial.hom_eval₂ p (algebraMap R E) (eE : E →+* E') x).symm

/-- **Separability transports along compatible isomorphisms of the base and of the extension.**

Neither Mathlib nor this repository has a `minpoly` lemma across an isomorphism of the *base* ring,
so the proof does not identify the two minimal polynomials. It does not need to: separability is
inherited by divisors, so it is enough that `minpoly R' x` divides the transport of
`minpoly R (eE x)`.

The transport of `Polynomial.aeval` across the square is the only computation, and it is the
statement that `(algebraMap R E).comp eR` and `eE.comp (algebraMap R' E')` are the same ring
homomorphism, which is `hsq` in point-free form. -/
theorem isSeparable_of_ringEquiv_square
    {R R' E E' : Type*} [Field R] [Field R'] [Field E] [Field E']
    [Algebra R E] [Algebra R' E']
    (eR : R' ≃+* R) (eE : E' ≃+* E)
    (hsq : ∀ y : R', eE (algebraMap R' E' y) = algebraMap R E (eR y))
    (x : E') (hx : IsSeparable R (eE x)) : IsSeparable R' x := by
  have hqsep : (minpoly R (eE x)).Separable := hx
  have hpmap : ((minpoly R (eE x)).map (eR.symm : R →+* R')).map (eR : R' →+* R)
      = minpoly R (eE x) := by
    rw [Polynomial.map_map]
    simp
  have hax : Polynomial.aeval x ((minpoly R (eE x)).map (eR.symm : R →+* R')) = 0 := by
    apply eE.injective
    rw [← aeval_map_ringEquiv_square_aux eR eE hsq, hpmap, map_zero, minpoly.aeval]
  exact hqsep.map.of_dvd (minpoly.dvd R' x hax)

/-- **Membership in the perfect core transports along a ring isomorphism of fields.**

Immediate from `Stacks.EppTheorem.mem_perfectCore_iff`: a `p ^ n`-th root of `x` maps to a `p ^
  n`-th root
of `eE x`. -/
theorem mem_perfectCore_ringEquiv {E E' : Type*} [Field E] [Field E'] (p : ℕ)
    [ExpChar E p] [ExpChar E' p]
    (eE : E' ≃+* E) {x : E'} (hx : x ∈ perfectCore E' p) : eE x ∈ perfectCore E p := by
  rw [mem_perfectCore_iff] at hx ⊢
  intro n
  obtain ⟨y, hy⟩ := hx n
  exact ⟨eE y, by rw [← map_pow, hy]⟩

/-- The characteristic transports backwards along a ring isomorphism.

`charP_of_injective_ringHom` moves `CharP` *forwards* along an injective homomorphism, so to move
it backwards one applies it to the inverse. Needed because
  `Stacks.EliminateRamification.EppTheorem` quantifies over
primes `p` with `CharP (ResidueField A) p`, and the universe layer meets that hypothesis on the
lifted ring and has to discharge it on the original. -/
theorem charP_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ)
    [CharP S p] : CharP R p :=
  charP_of_injective_ringHom (f := (e.symm : S →+* R)) e.symm.injective p

/-- The exponential characteristic transports backwards along a ring isomorphism.

`ExpChar` is a two-case inductive — characteristic zero, or a prime equal to the characteristic —
so both cases are transported: `CharZero` directly from injectivity of the natural-number cast, and
the prime case from `charP_of_ringEquiv`. -/
theorem expChar_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (p : ℕ)
    [ExpChar S p] : ExpChar R p := by
  rcases ‹ExpChar S p› with h | ⟨hp, _⟩
  · have : CharZero R :=
      ⟨fun {a b} hab => Nat.cast_injective (R := S) (by simpa using congrArg e hab)⟩
    exact .zero
  · let : CharP R p := charP_of_ringEquiv e p
    exact .prime hp

/-- **Epp's residue-field condition transports along an isomorphism of the data.**

Given local rings `A → B` and `A' → B'` with local structure maps and ring isomorphisms `eA`, `eB`
making the square commute, Epp's condition for `A → B` gives it for `A' → B'`.

The residue-field isomorphisms are `IsLocalRing.ResidueField.mapEquiv`, and the square over them
commutes because `IsLocalRing.residue` is surjective and `algebraMap_residue` computes the induced
map on residues. Then `mem_perfectCore_ringEquiv` moves the hypothesis up and
`isSeparable_of_ringEquiv_square` moves the conclusion back down. -/
theorem eppCondition_of_ringEquiv_square
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing A'] [IsLocalRing B']
    [Algebra A B] [Algebra A' B']
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A' B')]
    (p : ℕ) [ExpChar (IsLocalRing.ResidueField B) p]
    [ExpChar (IsLocalRing.ResidueField B') p]
    (eA : A' ≃+* A) (eB : B' ≃+* B)
    (hsq : ∀ a : A', eB (algebraMap A' B' a) = algebraMap A B (eA a))
    (h : EppCondition A B p) : EppCondition A' B' p := by
  set rA := IsLocalRing.ResidueField.mapEquiv eA with hrA
  set rB := IsLocalRing.ResidueField.mapEquiv eB with hrB
  have hrsq : ∀ y : IsLocalRing.ResidueField A',
      rB (algebraMap (IsLocalRing.ResidueField A') (IsLocalRing.ResidueField B') y)
        = algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) (rA y) := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    simp only [hrA, hrB, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue B) (hsq a)
  intro x hx
  exact isSeparable_of_ringEquiv_square rA rB hrsq x (h (rB x) (mem_perfectCore_ringEquiv p rB hx))

/-! ### Integral closures under an isomorphism of the data

The assembly has to identify the two integral closures `integralClosure A K₁` and
`integralClosure A' K₁'` of the two sides, and that means moving the *base* as well as the ambient
ring. `Stacks.DiscreteValuationRing.EppLevelInduction.integralClosureRingEquivOfAlgEquiv` moves
  only the ambient, over a fixed base, so
it does not apply; these do.
-/

section IntegralClosureSquare

variable {R R' E E' : Type*} [CommRing R] [CommRing R'] [CommRing E] [CommRing E']
  [Algebra R E] [Algebra R' E']

/-- **The `aeval` square.** Evaluating the transported polynomial at the transported point is the
transport of the evaluation.

This is the one computation behind everything in this section, and it is the statement that
`(algebraMap R' E').comp eR` and `eE.comp (algebraMap R E)` are the same ring homomorphism — `hsq`
in point-free form. The same computation appears, in the opposite orientation, inside
`isSeparable_of_ringEquiv_square`. -/
theorem aeval_map_ringEquiv_square (eR : R ≃+* R') (eE : E ≃+* E')
    (hsq : ∀ y : R, eE (algebraMap R E y) = algebraMap R' E' (eR y))
    (x : E) (p : Polynomial R) :
    Polynomial.aeval (eE x) (p.map (eR : R →+* R')) = eE (Polynomial.aeval x p) :=
  aeval_map_ringEquiv_square_aux eR eE hsq x p

/-- Integrality transports along compatible isomorphisms of the base and of the ambient ring: a
monic witness maps to a monic witness. -/
theorem isIntegral_ringEquiv_square (eR : R ≃+* R') (eE : E ≃+* E')
    (hsq : ∀ y : R, eE (algebraMap R E y) = algebraMap R' E' (eR y))
    {x : E} (hx : IsIntegral R x) : IsIntegral R' (eE x) := by
  obtain ⟨p, hmonic, hp⟩ := hx
  refine ⟨p.map (eR : R →+* R'), hmonic.map _, ?_⟩
  rw [← Polynomial.aeval_def] at hp ⊢
  rw [aeval_map_ringEquiv_square eR eE hsq x p, hp, map_zero]

/-- **The integral closure transports along compatible isomorphisms of the base and of the ambient
ring.**

Both directions of integrality come from `isIntegral_ringEquiv_square`, the inverse square being
derived from the given one by applying `eE.symm`. -/
noncomputable def integralClosureRingEquivOfSquare (eR : R ≃+* R') (eE : E ≃+* E')
    (hsq : ∀ y : R, eE (algebraMap R E y) = algebraMap R' E' (eR y)) :
    integralClosure R E ≃+* integralClosure R' E' := by
  have hsq' : ∀ y : R', eE.symm (algebraMap R' E' y) = algebraMap R E (eR.symm y) := by
    intro y
    apply eE.injective
    rw [eE.apply_symm_apply, hsq (eR.symm y), eR.apply_symm_apply]
  exact
    { toFun := fun x => ⟨eE x.1, isIntegral_ringEquiv_square eR eE hsq x.2⟩
      invFun := fun y => ⟨eE.symm y.1, isIntegral_ringEquiv_square eR.symm eE.symm hsq' y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }

/-- The transported integral closure is computed by the ambient isomorphism. This is what a caller
needs in order to check that the square of
  `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square`
commutes. -/
@[simp]
theorem integralClosureRingEquivOfSquare_coe (eR : R ≃+* R') (eE : E ≃+* E')
    (hsq : ∀ y : R, eE (algebraMap R E y) = algebraMap R' E' (eR y))
    (x : integralClosure R E) :
    ((integralClosureRingEquivOfSquare eR eE hsq x : integralClosure R' E') : E') = eE (x : E) :=
  rfl

end IntegralClosureSquare

/-- **The descent: a finite extension of `K` has a copy in `K`'s own universe.**

This is the step that makes the universe layer possible at all.
  `Stacks.EliminateRamification.EppTheorem` demands the
solution field in `Type uK`; a monomorphic family induction returns it in `Type u` with `u ≥ uK`,
and a type's universe cannot be lowered. But the field is finite over `K`, hence algebraic, and
`AlgebraicClosure K` is already in `Type uK`, so `IsAlgClosed.lift` embeds the produced field into
it and `AlgHom.fieldRange` names the image — a copy of the extension in the right universe,
`K`-isomorphic to the original.

Not by a primitive element: Epp's solution fields are in general inseparable
(`IsDiscreteValuationRing.weakSolution_isInseparable_and_inseparable_isSolution`), so a finite
extension here need not be simple. -/
theorem exists_field_descent_of_module_finite (K : Type uK) [Field K] (E : Type v) [Field E]
    [Algebra K E] [Module.Finite K E] :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      Nonempty (K₁ ≃ₐ[K] E) := by
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  let φ : E →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  exact ⟨φ.fieldRange, inferInstance, inferInstance,
    Module.Finite.equiv φ.equivFieldRange.toLinearEquiv, ⟨φ.equivFieldRange.symm⟩⟩

end Stacks.EppTheorem

end
