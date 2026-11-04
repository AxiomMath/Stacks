module

public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctions

/-!
# Principal Weil divisors and the Weil divisor class group of an algebraic space

Let `X` be a locally Noetherian integral algebraic space over `S` and let `f ∈ R(X)^*` be an
invertible rational function. The *principal Weil divisor* of `f` is `div(f) = ∑ ord_Z(f) [Z]`,
the sum over the prime divisors of `X` of the order of vanishing of `f` along `Z`. Principal
divisors are additive in `f`, so they form a subgroup of the group `Div(X)` of all Weil
divisors, and the *Weil divisor class group* `Cl(X)` is the quotient of `Div(X)` by that
subgroup.

The order of vanishing `ord_Z(f)` is read in the total ring of fractions of the henselian local
ring `𝒪^h_{X, ξ}` at the generic point `ξ` of `Z`, along the canonical embedding
`R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK; that embedding and the ring-theoretic properties of
`𝒪^h_{X, ξ}` that make the order of vanishing available are carried here by
`AlgebraicGeometry.Space.GenericFractionEmbedding`.

## Main definitions

* `AlgebraicGeometry.Space.GenericFractionEmbedding` packages, for every prime divisor `Z` of
  `X`, the embedding of `R(X)` into the total ring of fractions of `𝒪^h_{X, ξ}` together with
  the hypotheses under which the order of vanishing along `Z` is defined.
* `AlgebraicGeometry.Space.GenericFractionEmbedding.ord` is the coefficient family
  `Z ↦ ord_Z(f)` of an invertible rational function `f`.
* `AlgebraicGeometry.Space.GenericFractionEmbedding.IsPrincipal` says that a Weil divisor is
  principal, and `AlgebraicGeometry.Space.GenericFractionEmbedding.principalWeilDivisors` is
  the subgroup these form.
* `AlgebraicGeometry.Space.GenericFractionEmbedding.weilDivisorClassGroup` is `Cl(X)`.
* `AlgebraicGeometry.Space.GenericFractionEmbedding.principalDivisor` is the principal Weil
  divisor `div(f)` itself, given the local finiteness of Stacks 0ENN.

## Main results

* `AlgebraicGeometry.Space.GenericFractionEmbedding.ord_mul`: the order of vanishing is
  additive in the rational function. The additivity of the principal Weil divisor in `Div(X)`
  is `AlgebraicGeometry.Space.divRationalFunction_mul`.
* `AlgebraicGeometry.Space.GenericFractionEmbedding.principalWeilDivisors_eq_closure`: the
  principal Weil divisors already form a subgroup, so `Cl(X)` is the quotient of `Div(X)` by
  the principal divisors and nothing more.

## Implementation notes

`R(X)^*` is the unit group of the ring `AlgebraicGeometry.Space.rationalFunctions` of Stacks
0EMP, and `Div(X)` is `AlgebraicGeometry.Space.WeilDivisor` of Stacks 0ENJ, an `AddSubgroup` of
the integer coefficient families on prime divisors; a Weil divisor is therefore a pair of a
coefficient family and a proof that its nonzero part is locally finite.

The embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK is supplied as a hypothesis rather than
constructed, together with the nontriviality, Noetherianity and dimension hypotheses on
`𝒪^h_{X, ξ}` that the same lemma supplies; these are the fields of
`AlgebraicGeometry.Space.GenericFractionEmbedding`, and the order of vanishing is
`AlgebraicGeometry.Space.PrimeDivisor.ord` evaluated along the embedding.

Everything about the class group is then unconditional: a Weil divisor is principal when its
coefficient family is `Z ↦ ord_Z(f)` for some `f`, which asks for no construction of the Weil
divisor of `f`, and the source's observation that the principal divisors form a subgroup is
the additivity of the order of vanishing. Producing the Weil divisor `div(f)` of a given `f`
does need the local finiteness of Stacks 0ENN; that is the explicit hypothesis `hlf` of
`AlgebraicGeometry.Space.GenericFractionEmbedding.principalDivisor`. The form of Stacks 0ENQ
stated in `Div(X)` rather than on coefficient families is
`AlgebraicGeometry.Space.divRationalFunction_mul`, where that local finiteness is proved.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENN](https://stacks.math.columbia.edu/tag/0ENN)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0ENQ](https://stacks.math.columbia.edu/tag/0ENQ)
* [Stacks Project, Tag 0ENR](https://stacks.math.columbia.edu/tag/0ENR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

/-- The data of Stacks 0ENK at every prime divisor `Z` of `X` with generic point `ξ`: the
henselian local ring `𝒪^h_{X, ξ}` is a nontrivial Noetherian ring of dimension at most one, and
the field `R(X)` of rational functions embeds in its total ring of fractions. -/
structure GenericFractionEmbedding where
  /-- The henselian local ring at the generic point of a prime divisor is nontrivial. -/
  nontrivial (Z : PrimeDivisor B S hS X) :
    Nontrivial ↥(Z.genericHenselianLocalRing B S hS hX hdec)
  /-- The henselian local ring at the generic point of a prime divisor is Noetherian. -/
  isNoetherianRing (Z : PrimeDivisor B S hS X) :
    IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)
  /-- The henselian local ring at the generic point of a prime divisor has dimension at most
  one. -/
  krullDimLE (Z : PrimeDivisor B S hS X) :
    Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hX hdec)
  /-- The canonical map from the rational functions on `X` into the total ring of fractions of
  the henselian local ring at the generic point of a prime divisor. -/
  emb (Z : PrimeDivisor B S hS X) :
    rationalFunctions B S hS hX →+* Z.genericTotalFractionRing B S hS hX hdec
  /-- The canonical map of Stacks 0ENK is injective. -/
  injective_emb (Z : PrimeDivisor B S hS X) : Function.Injective (emb Z)

variable {B S hS hX hdec}

namespace GenericFractionEmbedding

variable (E : GenericFractionEmbedding B S hS hX hdec)

/-- The coefficient family `Z ↦ ord_Z(f)` of an invertible rational function `f` on `X`: the
order of vanishing along the prime divisor `Z` of the image of `f` in the total ring of
fractions of the henselian local ring at the generic point of `Z`. -/
def ord (f : (rationalFunctions B S hS hX)ˣ) (Z : PrimeDivisor B S hS X) : ℤ :=
  letI := E.nontrivial Z
  letI := E.isNoetherianRing Z
  letI := E.krullDimLE Z
  Z.ord B S hS hX hdec (E.emb Z (f : rationalFunctions B S hS hX)) (f.isUnit.map (E.emb Z))

/-- The order of vanishing along a prime divisor of a product of invertible rational functions
is the sum of the orders of vanishing. -/
theorem ord_mul_apply (f g : (rationalFunctions B S hS hX)ˣ) (Z : PrimeDivisor B S hS X) :
    E.ord (f * g) Z = E.ord f Z + E.ord g Z := by
  let _ := E.nontrivial Z
  let _ := E.isNoetherianRing Z
  let _ := E.krullDimLE Z
  have hu (u : (rationalFunctions B S hS hX)ˣ) :
      IsUnit (E.emb Z (u : rationalFunctions B S hS hX)) := u.isUnit.map (E.emb Z)
  change Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec) _ (hu (f * g)) =
    Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec) _ (hu f) +
      Ring.ordTotalFracInt ↥(Z.genericHenselianLocalRing B S hS hX hdec) _ (hu g)
  rw [Ring.ordTotalFracInt_congr _ (hu (f * g)) ((hu f).mul (hu g)) (map_mul _ _ _),
    Ring.ordTotalFracInt_mul]

/-- **Stacks 0ENQ.** The order of vanishing of a product of invertible rational functions is
the sum of the orders of vanishing, as coefficient families on the prime divisors of `X`.

This is the equation `div(fg) = div(f) + div(g)` of the source, read on the coefficient families
of which the two sides of that equation are the Weil divisors. -/
@[stacks 0ENQ "additivity of the principal Weil divisor, read on the coefficient families over
  the prime divisors; this form needs no hypothesis beyond the embedding of Stacks 0ENK"]
theorem ord_mul (f g : (rationalFunctions B S hS hX)ˣ) :
    E.ord (f * g) = E.ord f + E.ord g :=
  funext fun Z => E.ord_mul_apply f g Z

/-- The order of vanishing of the constant function `1` is zero. -/
theorem ord_one : E.ord 1 = 0 := by
  have h := E.ord_mul 1 1
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

/-- The order of vanishing of the inverse of an invertible rational function is the negative of
its order of vanishing. -/
theorem ord_inv (f : (rationalFunctions B S hS hX)ˣ) : E.ord f⁻¹ = -E.ord f := by
  have h := E.ord_mul f f⁻¹
  rw [mul_inv_cancel, E.ord_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A Weil divisor on `X` is *principal* when its coefficient at every prime divisor `Z` is the
order of vanishing along `Z` of one invertible rational function. -/
def IsPrincipal (D : ↥(WeilDivisor B S hS X)) : Prop :=
  ∃ f : (rationalFunctions B S hS hX)ˣ, (D : PrimeDivisor B S hS X → ℤ) = E.ord f

/-- The zero Weil divisor is principal, being the divisor of the constant function `1`. -/
theorem isPrincipal_zero : E.IsPrincipal 0 :=
  ⟨1, E.ord_one.symm⟩

/-- A sum of principal Weil divisors is principal, by additivity of the order of vanishing. -/
theorem IsPrincipal.add {D D' : ↥(WeilDivisor B S hS X)} (hD : E.IsPrincipal D)
    (hD' : E.IsPrincipal D') : E.IsPrincipal (D + D') := by
  obtain ⟨f, hf⟩ := hD
  obtain ⟨g, hg⟩ := hD'
  exact ⟨f * g, by rw [E.ord_mul]; exact congrArg₂ (· + ·) hf hg⟩

/-- The negative of a principal Weil divisor is principal, being the divisor of the inverse
function. -/
theorem IsPrincipal.neg {D : ↥(WeilDivisor B S hS X)} (hD : E.IsPrincipal D) :
    E.IsPrincipal (-D) := by
  obtain ⟨f, hf⟩ := hD
  exact ⟨f⁻¹, by rw [E.ord_inv]; exact congrArg Neg.neg hf⟩

/-- **Stacks 0ENR.** The subgroup of `Div(X)` of principal Weil divisors: they contain zero and
are closed under addition and negation by the additivity of the order of vanishing, which is
Stacks 0ENQ. -/
@[stacks 0ENR "the subgroup of principal Weil divisors, by which the class group is formed"]
def principalWeilDivisors : AddSubgroup ↥(WeilDivisor B S hS X) where
  carrier := {D | E.IsPrincipal D}
  zero_mem' := E.isPrincipal_zero
  add_mem' := IsPrincipal.add E
  neg_mem' := IsPrincipal.neg E

/-- A Weil divisor lies in the subgroup of principal Weil divisors exactly when it is
principal. -/
@[simp]
theorem mem_principalWeilDivisors_iff (D : ↥(WeilDivisor B S hS X)) :
    D ∈ E.principalWeilDivisors ↔ E.IsPrincipal D :=
  Iff.rfl

/-- The principal Weil divisors already form a subgroup, so the subgroup they generate adds
nothing to them. -/
theorem principalWeilDivisors_eq_closure :
    E.principalWeilDivisors = AddSubgroup.closure {D | E.IsPrincipal D} :=
  (AddSubgroup.closure_eq E.principalWeilDivisors).symm

/-- **Stacks 0ENR.** The *Weil divisor class group* `Cl(X)` of `X`: the group of Weil divisors
on `X` modulo the subgroup of principal Weil divisors. -/
@[stacks 0ENR "the Weil divisor class group as the quotient of the Weil divisors by the
  principal Weil divisors"]
abbrev weilDivisorClassGroup : Type (u + 1) :=
  ↥(WeilDivisor B S hS X) ⧸ E.principalWeilDivisors

variable (hlf : ∀ f : (rationalFunctions B S hS hX)ˣ, E.ord f ∈ WeilDivisor B S hS X)

/-- **Stacks 0ENP.** The principal Weil divisor `div(f) = ∑ ord_Z(f) [Z]` of an invertible
rational function `f` on `X`, whose coefficient at a prime divisor `Z` is the order of vanishing
of `f` along `Z`. -/
def principalDivisor (f : (rationalFunctions B S hS hX)ˣ) : ↥(WeilDivisor B S hS X) :=
  ⟨E.ord f, hlf f⟩

/-- The coefficient family of the principal Weil divisor of `f` is the order of vanishing
of `f`. -/
@[simp]
theorem principalDivisor_coe (f : (rationalFunctions B S hS hX)ˣ) :
    ((E.principalDivisor hlf f : ↥(WeilDivisor B S hS X)) : PrimeDivisor B S hS X → ℤ) =
      E.ord f :=
  rfl

/-- The principal Weil divisor of an invertible rational function is a principal Weil
divisor. -/
theorem isPrincipal_principalDivisor (f : (rationalFunctions B S hS hX)ˣ) :
    E.IsPrincipal (E.principalDivisor hlf f) :=
  ⟨f, rfl⟩

end GenericFractionEmbedding

end AlgebraicGeometry.Space

end
