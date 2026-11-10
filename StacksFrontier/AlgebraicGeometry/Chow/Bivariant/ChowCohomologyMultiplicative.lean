module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ChowCohomologyRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# The restriction map on Chow cohomology is a ring map

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, and let
`f : Y' ⟶ Y` be a morphism of schemes locally of finite type over the base. **Stacks 0B7F**
produces from `f` the restriction map

  `res : A^*(Y) ⟶ A^*(Y')`,  often written `f^*`,

and asserts that it is a map of `ℤ`-algebras. The map itself is
`Stacks.Chow.chowCohomologyRestriction` degreewise and
`Stacks.Chow.chowCohomologyTotalRestriction` on the graded group, both in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology`, which prove it additive and
nothing more; its two functoriality laws are
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyFunctoriality`. This file supplies
the multiplicative half: `res` carries the product of Stacks 0B7E to the product, and the unit to
the unit, so that it is a homomorphism of the rings and of the `ℤ`-algebras that
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing` builds on
`A^*(Y)` and `A^*(Y')`.

## Main results

* `Stacks.Chow.chowCohomologyRestriction_toIdentityCapRule` — the key identity, and the only
  mathematical input: the operation that `res(c)` performs on a test scheme `g : T ⟶ Y'` is the
  operation that `c` performs on the test scheme `g ≫ f : T ⟶ Y`.
* `Stacks.Chow.chowCohomologyRestriction_chowCohomologyRingMul` — `res(a · b) = res(a) · res(b)`
  for the product
  `Stacks.Chow.chowCohomologyRingMul` of Stacks 0B7E, in each pair of degrees.
* `Stacks.Chow.chowCohomologyRestriction_unit` — `res(1) = 1`.
* `Stacks.Chow.chowCohomologyTotalRestriction_mul`,
  `Stacks.Chow.chowCohomologyTotalRestriction_one` — the same two on the graded group `A^*`,
  for the ring structure `Stacks.Chow.chowCohomologyRing` that `DirectSum.ring` produces.
* `Stacks.Chow.chowCohomologyTotalRestrictionRingHom`,
  `Stacks.Chow.chowCohomologyTotalRestrictionAlgHom` — **Stacks 0B7F**, `res` as a ring map and
  as a map of `ℤ`-algebras.
* `Stacks.Chow.chowCohomologyTotalRestrictionAlgHomOfInvertible` — **Stacks 0B7F**, the same for
  the Gysin system this repository constructs, where both hypotheses on the system are
  discharged.

## Implementation notes

### Why the whole thing is one identity about test schemes

Stacks 0B7E makes `A^*(Y)` a ring with composition of bivariant classes as the multiplication,
and `Stacks.Chow.chowCohomologyRingMul` builds that product not from
`Stacks.Chow.bivariantComposite` but from `Stacks.Chow.IdentityCapRule.comp`, the *composite of
the operations the two classes perform on the test schemes*. In that picture multiplicativity of
`res` is immediate from one observation. The operation a class `c ∈ A^p(Y)` induces on test
schemes is `Stacks.Chow.BivariantClass.toIdentityCapRule`, and the cap formula
`Stacks.Chow.chowCohomologyRestriction_cap` of Stacks 0B7F says exactly that the operation of
`res(c)` at `g : T ⟶ Y'` is the operation of `c` at `g ≫ f`. Reindexing along `g ↦ g ≫ f`
commutes with composing operations because it changes neither the operations nor the order, so
`res(a · b)` and `res(a) · res(b)` induce the same rule on every test scheme, and a class for an
identity morphism is determined by that rule — `Stacks.Chow.BivariantClass.toIdentityCapRule` is
inverse to `Stacks.Chow.IdentityCapRule.transport`, whence
`Stacks.Chow.BivariantClass.eq_of_toIdentityCapRule_eq`. The unit is the same argument with the
identity rule, which is reindexing-invariant on the nose.

### No transport appears, and that is not an accident

`Stacks.Chow.chowCohomologyRestriction_toIdentityCapRule` compares a class for `𝟙 Y'` over the
base `f ≫ sY` with a class for `𝟙 Y` over `sY`, so its two sides are indexed by the structure
morphisms `g ≫ (f ≫ sY)` and `(g ≫ f) ≫ sY`. Those are the same morphism and not the same term,
and `Stacks.Chow.chowGroupCongr` exists to transport between the Chow groups they index. None of
it is needed here: associativity of composition of morphisms of schemes is `rfl`, so the two
indices are definitionally equal, and the transport that
`Stacks.Chow.chowCohomologyRestriction_cap` carries in its statement is the identity. The key
identity is therefore literally that cap formula, with no rewriting at all, exactly as the two
functoriality laws of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyFunctoriality` are.

The price is that the proofs below are written as explicit chains of `Eq.trans` rather than with
`rw` or `simp only`. Those tactics match up to reducible transparency, which does not see through
`CategoryTheory.Category.assoc`, so a rewrite whose result is indexed by `(g ≫ f) ≫ sY` cannot be
fed to a lemma stated at `g ≫ (f ≫ sY)` even though the two are the same type to the kernel. Term
application does see through it, since the elaborator checks definitional equality at default
transparency.

### Hypotheses

Two `Prop`s on the Gysin system are carried, both of them already carried by the statements being
combined and neither of them new:
`Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso`, which the construction of the restriction
map of Stacks 0F9Z needs, and `Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso`, the isomorphism
case of Stacks 02TA, which the product of Stacks 0B7E needs. For the Gysin system this
repository constructs both are theorems —
`Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderBaseChangeIso` and
`Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso` — so
`Stacks.Chow.chowCohomologyTotalRestrictionAlgHomOfInvertible` assumes nothing on the system
beyond the vanishing of Stacks 02TO that the construction of
`Stacks.Chow.gysinSystemOfInvertible` itself carries and that every statement of this
development about that system carries. That is where the tag sits, matching
`Stacks.Chow.chowCohomologyAlgebraOfInvertible` of Stacks 0B7E.

The multiplication is the one of Stacks 0B7E, `Stacks.Chow.chowCohomologyRingMul`. It is *not*
identified in this repository with `Stacks.Chow.ChowCohomologySeriesRing.gradedMul` of Stacks
0FEL, and nothing below assumes such an identification; see
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup`.

## References

* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Multiplicative

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **The key identity.** The operation that the restriction `res(c)` of a class `c ∈ A^p(Y)`
performs on a test scheme `g : T ⟶ Y'` is the operation that `c` itself performs on the test
scheme `g ≫ f : T ⟶ Y`: restricting along `f` is reindexing the rule along `g ↦ g ≫ f`.

This is the cap formula `Stacks.Chow.chowCohomologyRestriction_cap` of Stacks 0B7F verbatim. Its
two sides are indexed by `g ≫ (f ≫ sY)` and `(g ≫ f) ≫ sY`, which are definitionally the same
morphism, so the transport the cap formula carries is the identity and no rewriting is needed;
see the implementation notes of this file. -/
theorem chowCohomologyRestriction_toIdentityCapRule (p : ℤ)
    (c : chowCohomologyComponent C G sY p) {T : Scheme.{u}} (g : T ⟶ Y')
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ (f ≫ sY)) k) :
    BivariantClass.toIdentityCapRule C G (f ≫ sY) p
        (chowCohomologyRestriction C G sY f p hgys c) g k α =
      BivariantClass.toIdentityCapRule C G sY p c (g ≫ f) k α :=
  chowCohomologyRestriction_cap C G sY f p hgys c g k α

variable (hiso : G.IsNaturalUnderInverseIso)

/-- **Stacks 0B7F, multiplicativity of `res` in each pair of degrees.** The restriction map
carries the product of Stacks 0B7E to the product:

  `res(a · b) = res(a) · res(b)`  in  `A^{p+q}(Y')`  for  `a ∈ A^p(Y)`,  `b ∈ A^q(Y)`.

Both sides induce, on a test scheme `g : T ⟶ Y'`, the operation "cap with `b` at `g ≫ f`, then
cap with `a` at `g ≫ f`", by `Stacks.Chow.chowCohomologyRestriction_toIdentityCapRule` applied
three times; a class for an identity morphism is determined by that operation. -/
theorem chowCohomologyRestriction_chowCohomologyRingMul {p q : ℤ}
    (a : chowCohomologyComponent C G sY p) (b : chowCohomologyComponent C G sY q) :
    chowCohomologyRestriction C G sY f (p + q) hgys (chowCohomologyRingMul C G sY hiso a b) =
      chowCohomologyRingMul C G (f ≫ sY) hiso
        (chowCohomologyRestriction C G sY f p hgys a)
        (chowCohomologyRestriction C G sY f q hgys b) := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G (f ≫ sY) (p + q) fun {T} g _ k α ↦ ?_
  have hb := chowCohomologyRestriction_toIdentityCapRule C G sY f hgys q b g k α
  have hinner :
      BivariantClass.toIdentityCapRule C G (f ≫ sY) p
          (chowCohomologyRestriction C G sY f p hgys a) g (k - q)
          (BivariantClass.toIdentityCapRule C G (f ≫ sY) q
            (chowCohomologyRestriction C G sY f q hgys b) g k α) =
        BivariantClass.toIdentityCapRule C G sY p a (g ≫ f) (k - q)
          (BivariantClass.toIdentityCapRule C G sY q b (g ≫ f) k α) :=
    (DFunLike.congr_arg (BivariantClass.toIdentityCapRule C G (f ≫ sY) p
        (chowCohomologyRestriction C G sY f p hgys a) g (k - q)) hb).trans
      (chowCohomologyRestriction_toIdentityCapRule C G sY f hgys p a g (k - q) _)
  refine Eq.trans
    ((chowCohomologyRestriction_toIdentityCapRule C G sY f hgys (p + q)
        (chowCohomologyRingMul C G sY hiso a b) g k α).trans
      (chowCohomologyMul_toIdentityCapRule C G sY hiso a b (g ≫ f) k α)) ?_
  exact ((chowCohomologyMul_toIdentityCapRule C G (f ≫ sY) hiso
      (chowCohomologyRestriction C G sY f p hgys a)
      (chowCohomologyRestriction C G sY f q hgys b) g k α).trans
    (DFunLike.congr_arg (chowGroupDegreeEquiv C (g ≫ (f ≫ sY))
      (by ring : k - q - p = k - (p + q))).toAddMonoidHom hinner)).symm

/-- **Stacks 0B7F, the unit.** The restriction map carries the unit `1 ∈ A^0(Y)` of Stacks 0B7E
to the unit of `A^0(Y')`: both induce the identity operation on every test scheme. -/
theorem chowCohomologyRestriction_unit :
    chowCohomologyRestriction C G sY f 0 hgys (chowCohomologyUnit C G sY hiso) =
      chowCohomologyUnit C G (f ≫ sY) hiso := by
  refine BivariantClass.eq_of_toIdentityCapRule_eq C G (f ≫ sY) 0 fun {T} g _ k α ↦ ?_
  refine ((chowCohomologyRestriction_toIdentityCapRule C G sY f hgys 0
      (chowCohomologyUnit C G sY hiso) g k α).trans
    (chowCohomologyUnit_toIdentityCapRule C G sY hiso (g ≫ f) k α)).trans ?_
  exact (chowCohomologyUnit_toIdentityCapRule C G (f ≫ sY) hiso g k α).symm

/-! ### The graded restriction map as a ring map -/

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` of
`Stacks.Chow.chowCohomologyTotalRestriction` sends the unit of the ring of Stacks 0B7E to the
unit. The unit of `DirectSum.ring` is the image of the degree `0` unit under
`DirectSum.of`, so this is `Stacks.Chow.chowCohomologyRestriction_unit`. -/
theorem chowCohomologyTotalRestriction_one :
    letI := chowCohomologyRing C G sY hiso
    letI := chowCohomologyRing C G (f ≫ sY) hiso
    chowCohomologyTotalRestriction C G sY f hgys 1 = 1 := by
  let := chowCohomologyGRing C G sY hiso
  let := chowCohomologyGRing C G (f ≫ sY) hiso
  rw [DirectSum.one_def, DirectSum.one_def, chowCohomologyTotalRestriction_of]
  exact congrArg (DirectSum.of _ 0) (chowCohomologyRestriction_unit C G sY f hgys hiso)

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` of
`Stacks.Chow.chowCohomologyTotalRestriction` respects the product of the ring of Stacks 0B7E.
Both sides are additive in each argument, so `DirectSum.induction_on` reduces the claim to a pair
of homogeneous classes, where the product of `DirectSum.ring` is the product of Stacks 0B7E in
the summand of the added degrees and the claim is
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyRingMul`. -/
theorem chowCohomologyTotalRestriction_mul
    (x y : chowCohomology C G sY) :
    letI := chowCohomologyRing C G sY hiso
    letI := chowCohomologyRing C G (f ≫ sY) hiso
    chowCohomologyTotalRestriction C G sY f hgys (x * y) =
      chowCohomologyTotalRestriction C G sY f hgys x *
        chowCohomologyTotalRestriction C G sY f hgys y := by
  let := chowCohomologyGRing C G sY hiso
  let := chowCohomologyGRing C G (f ≫ sY) hiso
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | of q b =>
      rw [DirectSum.of_mul_of, chowCohomologyTotalRestriction_of,
        chowCohomologyTotalRestriction_of, chowCohomologyTotalRestriction_of,
        DirectSum.of_mul_of]
      exact congrArg (DirectSum.of _ (p + q))
        (chowCohomologyRestriction_chowCohomologyRingMul C G sY f hgys hiso a b)
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` as a
homomorphism of the rings of Stacks 0B7E: the degreewise restriction map of Stacks 0F9Z, which is
additive by construction, together with the two statements above. It is often written `f^*`. -/
def chowCohomologyTotalRestrictionRingHom :
    letI := chowCohomologyRing C G sY hiso
    letI := chowCohomologyRing C G (f ≫ sY) hiso
    chowCohomology C G sY →+* chowCohomology C G (f ≫ sY) :=
  letI := chowCohomologyRing C G sY hiso
  letI := chowCohomologyRing C G (f ≫ sY) hiso
  { toFun := chowCohomologyTotalRestriction C G sY f hgys
    map_one' := chowCohomologyTotalRestriction_one C G sY f hgys hiso
    map_mul' := chowCohomologyTotalRestriction_mul C G sY f hgys hiso
    map_zero' := map_zero _
    map_add' := map_add _ }

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along `f : Y' ⟶ Y` as a map of
the `ℤ`-algebras of Stacks 0B7E, which is the full assertion of the tag. A ring map between
`ℤ`-algebras is a `ℤ`-algebra map, there being only one ring map from `ℤ`. -/
def chowCohomologyTotalRestrictionAlgHom :
    letI := chowCohomologyRing C G sY hiso
    letI := chowCohomologyRing C G (f ≫ sY) hiso
    chowCohomology C G sY →ₐ[ℤ] chowCohomology C G (f ≫ sY) :=
  letI := chowCohomologyRing C G sY hiso
  letI := chowCohomologyRing C G (f ≫ sY) hiso
  (chowCohomologyTotalRestrictionRingHom C G sY f hgys hiso).toIntAlgHom

end Multiplicative

/-! ### The restriction map for the Gysin system of this repository -/

section OfInvertible

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : Y' ⟶ Y) [LocallyOfFiniteType f]

/-- **Stacks 0B7F.** The restriction map `res : A^*(Y) ⟶ A^*(Y')` along a morphism `f : Y' ⟶ Y`
of schemes locally of finite type over the base, as a map of the `ℤ`-algebras of Stacks 0B7E, for
the Gysin system this repository constructs.

It is `Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible`, the restriction map as a
homomorphism for addition and for the composite of Stacks 0B75, together with
`Stacks.Chow.chowCohomologyTotalRestrictionRingOfInvertible_map_one`: the ring
`Stacks.Chow.chowCohomologyRingOfInvertible` has that composite as its multiplication and the
identity class as its unit, and a ring map between `ℤ`-algebras is a `ℤ`-algebra map. Nothing is
assumed about the Gysin system. -/
def chowCohomologyTotalRestrictionAlgHomOfInvertible :
    letI := chowCohomologyRingOfInvertible C sY
    letI := chowCohomologyRingOfInvertible C (f ≫ sY)
    chowCohomology C (gysinSystemOfInvertible C) sY →ₐ[ℤ]
      chowCohomology C (gysinSystemOfInvertible C) (f ≫ sY) :=
  letI := chowCohomologyRingOfInvertible C sY
  letI := chowCohomologyRingOfInvertible C (f ≫ sY)
  RingHom.toIntAlgHom
    { toFun := chowCohomologyTotalRestrictionRingOfInvertible C sY f
      map_one' := chowCohomologyTotalRestrictionRingOfInvertible_map_one C sY f
      map_mul' := map_mul (chowCohomologyTotalRestrictionRingOfInvertible C sY f)
      map_zero' := map_zero (chowCohomologyTotalRestrictionRingOfInvertible C sY f)
      map_add' := map_add (chowCohomologyTotalRestrictionRingOfInvertible C sY f) }

end OfInvertible

end Stacks.Chow

end
