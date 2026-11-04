module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product on the quotient of a ringed site by a sheaf of ideals

Let `(C, O)` be a ringed site and `I ⊆ O` a sheaf of ideals. Replacing the structure sheaf by
`O/I` leaves the underlying site untouched, so the sheafification and local-bijectivity
hypotheses that the derived tensor product of Stacks 06YU rests on are the ones already
carried by `(C, O)`, and the derived tensor product of sheaves of `O/I`-modules exists. This
file records it, together with its instance at the powers `Iⁿ`, which is what makes Tor
amplitude of an object of `D(O/Iⁿ)` a meaningful notion.

## Main definitions

* `Stacks.Sites.quotientDerivedTensorProduct`: the derived tensor product on `D(O/I)`.
* `Stacks.Sites.adicQuotientRingedSite`: the ringed site `(C, O/Iⁿ)`.
* `Stacks.Sites.adicDerivedTensorProduct`: the derived tensor product on `D(O/Iⁿ)`.

## Main results

* `Stacks.Sites.adicQuotientRingedSite_O`: its structure sheaf is `O/Iⁿ`.
* `Stacks.Sites.adicQuotientRingedSite_zero` and `Stacks.Sites.adicQuotientRingedSite_one`: the
  zeroth and first terms of the tower are the quotients by `O` and by `I`.

## Implementation notes

Only two of the six hypothesis blocks of `Stacks.SheafOfModules.exists_derivedTensorProduct`
mention the structure sheaf: the additivity of `⊗_{O/I}` in each variable and the existence of
the total tensor complexes. Both hold for every sheaf of commutative rings on a site admitting
sheafification of `AddCommGrpCat`-valued presheaves, by
`Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`, so nothing beyond the hypotheses on
`(C, O)` is needed. The remaining blocks are conditions on the site alone, and the underlying
site of the quotient is the given one.

The universes are all equal, as they are for the existence of the derived tensor product
itself; the derived category's own hom universe stays independent.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.Sites

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (I : letI := X.hasSheafCompose_forget₂_ringCat; IdealSubsheaf X.O)

/-- The ringed site `(C, O/Iⁿ)`, the `n`-th term of the tower of quotients of a ringed site by
the powers of a sheaf of ideals. -/
def adicQuotientRingedSite (n : ℕ) : RingedSite.{u, u, u} :=
  quotientRingedSite X (letI := X.hasSheafCompose_forget₂_ringCat; idealPow I n)

/-- The underlying site of `(C, O/Iⁿ)` is the given one. -/
@[simp]
theorem adicQuotientRingedSite_J (n : ℕ) : (adicQuotientRingedSite X I n).J = X.J :=
  rfl

/-- The structure sheaf of `(C, O/Iⁿ)` is `O/Iⁿ`. -/
theorem adicQuotientRingedSite_O (n : ℕ) :
    (adicQuotientRingedSite X I n).O =
      letI := X.hasSheafCompose_forget₂_ringCat; adicQuotient I n :=
  rfl

/-- The zeroth term of the tower is the quotient by the whole structure sheaf. -/
theorem adicQuotientRingedSite_zero :
    adicQuotientRingedSite X I 0 =
      quotientRingedSite X (letI := X.hasSheafCompose_forget₂_ringCat; ⊤) := by
  let := X.hasSheafCompose_forget₂_ringCat
  rw [adicQuotientRingedSite, idealPow_zero]

/-- The first term of the tower is the quotient by `I` itself. -/
theorem adicQuotientRingedSite_one :
    adicQuotientRingedSite X I 1 = quotientRingedSite X I := by
  let := X.hasSheafCompose_forget₂_ringCat
  rw [adicQuotientRingedSite, idealPow_one]

section DerivedTensor

attribute [local instance_reducible] quotientRingedSite adicQuotientRingedSite

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived tensor product of sheaves of `O/I`-modules.** The underlying site is
unchanged by passing to the quotient, so the derived tensor product of Stacks 06YU is available
on `D(O/I)` under the hypotheses already carried by `(C, O)`. -/
def quotientDerivedTensorProduct
    [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (quotientRingedSite X I))] :
    Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} (quotientRingedSite X I) :=
  Stacks.SheafOfModules.canonicalDerivedTensorProduct (quotientRingedSite X I)

/-- **The derived tensor product of sheaves of `O/Iⁿ`-modules**, against which Tor amplitude of
an object of `D(O/Iⁿ)` is measured. -/
def adicDerivedTensorProduct (n : ℕ)
    [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (adicQuotientRingedSite X I n))] :
    Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} (adicQuotientRingedSite X I n) :=
  Stacks.SheafOfModules.canonicalDerivedTensorProduct (adicQuotientRingedSite X I n)

end DerivedTensor

end Stacks.Sites

end
