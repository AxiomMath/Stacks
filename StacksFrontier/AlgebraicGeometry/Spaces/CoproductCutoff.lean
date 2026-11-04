module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# Coproducts below a size cutoff at an arbitrary index type

`AlgebraicGeometry.Scheme.size_sigmaObj_lt` bounds the size of a coproduct of schemes for an
**at most countable** index type, and `AlgebraicGeometry.BigFppfSite.contains_sigma` records
the consequence that a big fppf site is closed under at most countable coproducts. Countability
is not the real limit: the open-cover bound of Stacks 000Q bounds the size of `∐ Y` by
`max (max ℵ₀ #ι) (⨆ i, size (Y i))`, and the only condition needed to keep that below the cutoff
`κ` is that the index type be **smaller than the cofinality of `κ`**, which is what controls the
supremum. Uncountable cofinality of the cutoff is a field of
`AlgebraicGeometry.BigFppfSite`, so the countable statements are the special case `#ι ≤ ℵ₀` of
these.

This is the coproduct counterpart of
`AlgebraicGeometry.BigFppfSite.contains_glueData_glued`, which already carries exactly this
hypothesis on the index type of a glueing datum.

## Main results

* `AlgebraicGeometry.Scheme.size_sigmaObj_lt_of_lt_cof` generalizes
  `AlgebraicGeometry.Scheme.size_sigmaObj_lt` from an at most countable index type to one below
  the cofinality of the cutoff.
* `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` generalizes
  `AlgebraicGeometry.BigFppfSite.contains_sigma` in the same way.
* `AlgebraicGeometry.Scheme.size_sigmaObj_lt_of_forall_size_le` and
  `AlgebraicGeometry.BigFppfSite.contains_sigma_of_forall_size_le` drop the hypothesis on the
  cofinality altogether when the summands' sizes have a uniform bound below the cutoff, which is
  what bounds the supremum instead. An index type of cardinality below the cutoff — the point
  set of a scheme of the site, say — then qualifies.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {κ : Cardinal.{u}}

/-- The size of a coproduct is at most the maximum of `ℵ₀`, the cardinality of the index type
and any common bound for the sizes of the summands. -/
private theorem size_sigmaObj_le_max {ι : Type u} (Y : ι → Scheme.{u}) (c : Cardinal.{u})
    (hY : ∀ i, (Y i).size ≤ c) : (∐ Y).size ≤ max (max ℵ₀ #ι) c :=
  schemeSize_coproduct_le Y _ ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) fun j => (hY j).trans (le_max_right _ _)

/-- **Stacks 000R (2)** at an arbitrary index type. The coproduct of a family of objects of
`Sch_κ` indexed by a type smaller than the cofinality of `κ` is again an object of `Sch_κ`.

The hypothesis on the index type is what bounds the supremum of the sizes; the index type's own
cardinality is then below `κ` because the cofinality of an ordinal is at most the ordinal. -/
@[stacks 000R "(2), index type below the cofinality"]
theorem Scheme.size_sigmaObj_lt_of_lt_cof (hκ : ℵ₀ < κ) {ι : Type u} (hι : #ι < κ.ord.cof)
    (Y : ι → Scheme.{u}) (hY : ∀ i, (Y i).size < κ) : (∐ Y).size < κ :=
  (size_sigmaObj_le_max Y _ fun j => le_ciSup Cardinal.bddAbove_of_small j).trans_lt
    (max_lt (max_lt hκ (hι.trans_le (Ordinal.cof_ord_le κ)))
      (iSup_lt_of_lt_cof_ord hι hY))

/-- **Stacks 000R (2) for a family of uniformly bounded size.** The coproduct of a family of
objects of `Sch_κ` indexed by a type of cardinality below `κ` is again an object of `Sch_κ` as
soon as the sizes of its members admit *one* bound below `κ`.

The cofinality hypothesis of `AlgebraicGeometry.Scheme.size_sigmaObj_lt_of_lt_cof` is there only
to bound the supremum `⨆ i, size (Y i)`, and a uniform bound does that directly. This is the
form needed by a family indexed by the points of a scheme of the site — a set of size below `κ`
whose cardinality need not be below `cof κ` — whose members are cut out of affine opens of one
fixed scheme, so that their sizes are bounded in terms of that one scheme's. -/
@[stacks 000R "(2), uniformly bounded family at an index type below the cutoff"]
theorem Scheme.size_sigmaObj_lt_of_forall_size_le (hκ : ℵ₀ < κ) {ι : Type u} (hι : #ι < κ)
    (Y : ι → Scheme.{u}) (c : Cardinal.{u}) (hc : c < κ) (hY : ∀ i, (Y i).size ≤ c) :
    (∐ Y).size < κ :=
  (size_sigmaObj_le_max Y c hY).trans_lt
    (max_lt (max_lt hκ hι) hc)

namespace BigFppfSite

/-- A big fppf site is closed under coproducts of a family of uniformly bounded size indexed by
a type of cardinality below its size cutoff.

`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof` asks instead that the index type be
below the *cofinality* of the cutoff, which a uniform bound on the summands makes unnecessary.
The cutoff of a big fppf site is only a strong prelimit of uncountable cofinality, so for an
index type as large as the point set of a scheme of the site — of cardinality below the cutoff,
with no reason to be below its cofinality — this is the form that applies. -/
theorem contains_sigma_of_forall_size_le (B : BigFppfSite.{u}) {I : Type u}
    (hI : #I < B.cutoff) (Z : I → Scheme.{u}) (c : Cardinal.{u}) (hc : c < B.cutoff)
    (hZ : ∀ i, (Z i).size ≤ c) : B.Contains (∐ Z) :=
  Scheme.size_sigmaObj_lt_of_forall_size_le B.aleph0_lt_cutoff hI Z c hc hZ

/-- A big fppf site is closed under coproducts indexed by a type below the cofinality of its
size cutoff. An at most countable index type qualifies automatically, which is
`AlgebraicGeometry.BigFppfSite.contains_sigma`. -/
theorem contains_sigma_of_lt_cof (B : BigFppfSite.{u}) {I : Type u} (hI : #I < B.cutoff.ord.cof)
    (Z : I → Scheme.{u}) (hZ : ∀ i, B.Contains (Z i)) : B.Contains (∐ Z) :=
  Scheme.size_sigmaObj_lt_of_lt_cof B.aleph0_lt_cutoff hI Z hZ

end BigFppfSite

end AlgebraicGeometry

end
