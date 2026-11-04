module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
import StacksCore.Tactic.StacksAttribute

/-!
# The degree pairing and the intersection product on a regular proper model

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)`, each viewed as a closed subscheme of `X`
and proper of dimension at most one over the residue field `k`. For an invertible `𝒪_X`-module
`ℒ` and `a = (a₁, …, aₙ) ∈ ℤⁿ` the *degree pairing* of [Stacks, Tag 0C64] is

`⟨a, ℒ⟩ = ∑ᵢ aᵢ · deg(ℒ|_{Cᵢ})`,

where `deg` is the degree of an invertible module on a proper curve, [Stacks, Tag 0AYR]. The
*intersection product* of [Stacks, Tag 0C65] is then

`(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ) = ⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩`.

## Main definitions

* `Stacks.Models.componentDegree` — the degree `deg(ℒ|_D)` of the restriction of an invertible
  module to a closed subscheme that is a proper curve over `k`.
* `Stacks.Models.degreePairing` — the pairing `⟨a, ℒ⟩` of [Stacks, Tag 0C64].
* `Stacks.Models.degreePairingLinear` — the same pairing bundled as a `ℤ`-linear map in `a`.
* `Stacks.Models.intersectionProduct` — the intersection product `(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ)`, defined as
  `⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩`.

## Main results

* `Stacks.Models.isInvertible_restrict` — the restriction of an invertible module to a closed
  subscheme is invertible, in the spelling the degree of a proper curve consumes.
* `Stacks.Models.degreePairing_add`, `Stacks.Models.degreePairing_smul`,
  `Stacks.Models.degreePairing_zero`, `Stacks.Models.degreePairing_neg`,
  `Stacks.Models.degreePairing_sub` — the pairing is `ℤ`-linear in `a`.
* `Stacks.Models.intersectionProduct_eq_degreePairing` — the first displayed equality of
  [Stacks, Tag 0C65], which holds by definition.

## Implementation notes

**`ℤ` on the left, `ℕ` on the right.** The coefficient family `a` of the pairing is genuinely
`ℤ`-valued: it only ever multiplies an integer degree, so no divisor is formed from it and nothing
restricts its sign. The second argument of the intersection product is different: it has to be an
*effective* Cartier divisor `∑ⱼ bⱼCⱼ` before `𝒪_X(∑ⱼ bⱼCⱼ)` is available, and the library's sum of
effective Cartier divisors is `AlgebraicGeometry.Scheme.IdealSheafData`'s multiplicative monoid,
whose `Pow` is indexed by `ℕ` (`Stacks.Divisors.isEffectiveCartierDivisor_prod`). So `b` is taken
`ℕ`-valued. The alternative would be a `ℤ`-valued divisor group; the two candidates in the
repository are `AlgebraicGeometry.Scheme.CartierDivisor` of
`StacksFrontier/AlgebraicGeometry/Divisors/CartierDivisor.lean`, the global sections of the quotient
of the sheaf of units of the total quotient ring by the units of the structure sheaf, and
`AlgebraicGeometry.WeilDivisor` of `StacksDraft/AlgebraicGeometry/Divisors/Weil/`. Neither carries
a map from a family of `IdealSheafData` nor a map to an invertible module, so using either would
mean building that bridge first, and the degree pairing itself would not change.

**Divisor sums are written multiplicatively.** `Add` on `IdealSheafData` is `⊔`, the
scheme-theoretic intersection, not the sum of divisors; the sum is `*` and `nD` is `^`. Every
divisor expression below is in `*` and `^` for that reason.

**Spellings reconciled.** Three were needed, none of them by `rw` or `simp`:

* the structure sheaf of rings is `X.ringCatSheaf.2` in
  `AlgebraicGeometry.invertibleCurveDegree` and
  `(structureSheafRing X.toRingedSpace).property` in
  the divisor and pullback API;
* invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible` for the degree and
  `Stacks.SheafOfModules.IsInvertible` for `Stacks.Modules.isInvertible_pullback` and
  `Stacks.Divisors.isTensorInvertible_invertibleSheaf`, bridged by
  `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`;
* `Stacks.Divisors.invertibleSheaf'` is a sheaf of modules over the second spelling of the sheaf
  of rings while the degree wants an `X.Modules`.

All three pairs are definitionally equal but not syntactically so, and instance search runs at
reducible transparency, so none of them is crossed by unification during a search.
`Stacks.Models.isInvertible_restrict` therefore *declares* the type it wants and lets elaboration
unify, rather than rewriting; and the invertibility hypotheses of the definitions below are
explicit arguments rather than instance arguments, so the caller chooses the spelling once. The
degree does not depend on the choice: the body of `AlgebraicGeometry.invertibleCurveDegree` does
not mention its invertibility argument, and `AlgebraicGeometry.cohomologyOverField` does not
mention properness either, so properness is likewise an explicit argument here.

**Properness and dimension of the components are hypotheses.** `Stacks.Models.componentDegree`
takes a structure morphism `D.subscheme ⟶ Spec(k)`, a proof that it is proper and the bound
`topologicalKrullDim D.subscheme ≤ 1` as arguments. That the components of the special fibre of a
proper model are proper curves over `k` is a separate result and is not formalized here;
`AlgebraicGeometry.invertibleCurveDegree` itself takes its dimension bound explicitly for the same
reason.

**Where the rest of Tag 0C64 is.** The bilinearity of the pairing in `ℒ` and the symmetry
`⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩ = ⟨b, 𝒪_X(∑ᵢ aᵢCᵢ)⟩` are
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`, which needs the
components of the special fibre themselves and so cannot be stated at the abstract family `C`
used here. Only the `ℤ`-linearity in `a` is below; it is the half of the bilinearity that holds
by the shape of the defining sum alone. The two inputs the source's proof uses are both
unconditional in this library: additivity of the degree in the tensor product is
[Stacks, Tag 0AYX],
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`, and
the identification `deg(𝒪_X(Cⱼ)|_{Cᵢ}) = deg(Cᵢ ∩ Cⱼ)` is the twist formula of
[Stacks, Tag 0AYY], the third conjunct
`AlgebraicGeometry.isFinite_and_curveDegree_tensorSheaf_invertibleSheaf … |>.2.2` of
`StacksFrontier/AlgebraicGeometry/Variety/Curve/DivisorTwistDegree.lean`. That conjunct spells
`𝒪_X(D)` as `Stacks.Divisors.invertibleSheaf'`, whereas the zero-scheme development spells it
`Stacks.Divisors.modulesInvertibleSheaf`; the two are the same term and `exact`, `show` and
`apply` cross between them freely, but `rw` and `simp` do **not**, so a rewrite step must be
written in whichever spelling its goal already carries.

## References

* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models

/-- The restriction of an invertible `𝒪_X`-module to a closed subscheme `D ⊆ X` is an invertible
`𝒪_D`-module, stated at the spelling of the structure sheaf of rings and of invertibility that
the degree of an invertible module on a proper curve consumes. -/
theorem isInvertible_restrict {X : Scheme.{u}} (D : X.IdealSheafData) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback D.subschemeι).obj L) :=
  have := hL
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Modules.isInvertible_pullback D.subschemeι L)

/-- The degree `deg(ℒ|_D)` of an invertible `𝒪_X`-module restricted to a closed subscheme
`D ⊆ X` which is proper of dimension at most one over a field `k`, the restriction being the
module pullback along the closed immersion of `D`. -/
def componentDegree (k : Type u) [Field k] {X : Scheme.{u}} (D : X.IdealSheafData)
    (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L) : ℤ :=
  @invertibleCurveDegree k _ _ g hg hdim ((Scheme.Modules.pullback D.subschemeι).obj L)
    (isInvertible_restrict D L hL)

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k))
  (hg : ∀ i, IsProper (g i)) (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- **Stacks Project, Tag 0C64.** The degree pairing `⟨a, ℒ⟩ = ∑ᵢ aᵢ · deg(ℒ|_{Cᵢ})` of an
integer coefficient family `a` against an invertible `𝒪_X`-module, over a finite family of
components `Cᵢ` of the special fibre that are proper curves over the residue field. -/
@[stacks 0C64 "the pairing ⟨a, L⟩ = ∑ aᵢ deg(L|_{Cᵢ}); the whole tag, its bilinearity and its \
symmetry together, is \
Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm of \
StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean"]
def degreePairing (a : ι → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) : ℤ :=
  ∑ i ∈ s, a i * componentDegree S.k (C i) (g i) (hg i) (hdim i) L hL

/-- The degree pairing is additive in the coefficient family. -/
theorem degreePairing_add (a a' : ι → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    degreePairing S s C g hg hdim (a + a') L hL =
      degreePairing S s C g hg hdim a L hL + degreePairing S s C g hg hdim a' L hL := by
  simp only [degreePairing, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- The degree pairing is homogeneous in the coefficient family. -/
theorem degreePairing_smul (c : ℤ) (a : ι → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    degreePairing S s C g hg hdim (c • a) L hL = c * degreePairing S s C g hg hdim a L hL := by
  simp only [degreePairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The degree pairing vanishes on the zero coefficient family. -/
theorem degreePairing_zero (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    degreePairing S s C g hg hdim 0 L hL = 0 := by
  simp only [degreePairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The degree pairing negates with the coefficient family. -/
theorem degreePairing_neg (a : ι → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    degreePairing S s C g hg hdim (-a) L hL = -degreePairing S s C g hg hdim a L hL := by
  simp only [degreePairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- The degree pairing subtracts with the coefficient family. -/
theorem degreePairing_sub (a a' : ι → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    degreePairing S s C g hg hdim (a - a') L hL =
      degreePairing S s C g hg hdim a L hL - degreePairing S s C g hg hdim a' L hL := by
  simp only [degreePairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **Stacks Project, Tag 0C64.** The degree pairing against a fixed invertible module as a
`ℤ`-linear form on the coefficient families. -/
def degreePairingLinear (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) :
    (ι → ℤ) →ₗ[ℤ] ℤ where
  toFun a := degreePairing S s C g hg hdim a L hL
  map_add' a a' := degreePairing_add S s C g hg hdim a a' L hL
  map_smul' c a := degreePairing_smul S s C g hg hdim c a L hL

/-- The underlying function of `Stacks.Models.degreePairingLinear` is the degree pairing. -/
@[simp] theorem degreePairingLinear_apply (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) (a : ι → ℤ) :
    degreePairingLinear S s C g hg hdim L hL a = degreePairing S s C g hg hdim a L hL := rfl

/-- **Stacks Project, Tag 0C65, the definition of the intersection product.** For an integer
family `a` and a nonnegative family `b` on components `Cᵢ` that are effective Cartier divisors,
`(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ)` is the degree pairing of `a` against `𝒪_X(∑ⱼ bⱼCⱼ)`. -/
@[stacks 0C65 "the product, defined as ⟨a, O_X(∑ bⱼCⱼ)⟩; its symmetry on the components of the \
special fibre is \
Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_comm of \
StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean"]
def intersectionProduct (a : ι → ℤ) (b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) : ℤ :=
  degreePairing S s C g hg hdim a (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ b j))
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ (∏ j ∈ s, C j ^ b j)
      (Stacks.Divisors.isEffectiveCartierDivisor_prod s C b hC))

/-- **Stacks Project, Tag 0C65, first equality.** The intersection product
`(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ)` is the degree pairing `⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩`. -/
@[stacks 0C65 "the first displayed equality, which is the definition"]
theorem intersectionProduct_eq_degreePairing (a : ι → ℤ) (b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) :
    intersectionProduct S s C g hg hdim a b hC =
      degreePairing S s C g hg hdim a (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ b j))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ (∏ j ∈ s, C j ^ b j)
          (Stacks.Divisors.isEffectiveCartierDivisor_prod s C b hC)) := rfl

/-- The intersection product is additive in the first coefficient family. -/
theorem intersectionProduct_add_left (a a' : ι → ℤ) (b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) :
    intersectionProduct S s C g hg hdim (a + a') b hC =
      intersectionProduct S s C g hg hdim a b hC +
        intersectionProduct S s C g hg hdim a' b hC :=
  degreePairing_add S s C g hg hdim a a' _ _

/-- The intersection product is homogeneous in the first coefficient family. -/
theorem intersectionProduct_smul_left (c : ℤ) (a : ι → ℤ) (b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) :
    intersectionProduct S s C g hg hdim (c • a) b hC =
      c * intersectionProduct S s C g hg hdim a b hC :=
  degreePairing_smul S s C g hg hdim c a _ _

end Stacks.Models

end
