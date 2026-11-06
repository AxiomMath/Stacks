module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale

/-!
# The cutoff category of schemes is essentially small

The cutoff category `Sch_κ = AlgebraicGeometry.SchemeBelow κ` of Stacks 000J lives in
`Type (u + 1)`: its objects are schemes with structure in universe `u`, and there are a
proper class worth of those. It is nevertheless *essentially small* at universe `u` — there
is a `Type u` category equivalent to it — because the size bound `X.size < κ` bounds the
data presenting a scheme in `Sch_κ`, not just some invariant of it.

This is what lets coefficient categories for sheaves on a big site stay in universe `u`:
sheafification and the characterization of local equivalences are transported from a small
model of the site, which is how
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall` are stated.

## Main results

* `CommRingCat.essentiallySmall_cardinalMk_lt`: the commutative rings of cardinality below
  `κ` form an essentially small property of objects.
* `AlgebraicGeometry.essentiallySmall_schemeSizeBelow`: the schemes of size below `κ` form an
  essentially small property of objects.
* `AlgebraicGeometry.essentiallySmall_schemeBelow`: **Stacks 000J**, the cutoff category
  itself is essentially small. It needs no countability hypothesis on `κ`, so use it rather
  than the property form above when all that is wanted is a small model of `Sch_κ`.

## Implementation notes

The argument is in two steps, and the cardinal arithmetic is already done by
`AlgebraicGeometry.Scheme.mk_affineOpens_le_size` and
`AlgebraicGeometry.Scheme.mk_sections_le_size`, which say that `X.size` bounds both the
number of affine opens of `X` and each of their rings of sections.

For rings, a commutative ring of cardinality `< κ` is isomorphic to one carried by a
*subset* of `κ.out`, and the pairs `(T : Set κ.out, CommRing T)` form a type in universe
`u`. So the spectra of such rings form an essentially small property of schemes.

For schemes, `Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski` exhibits every scheme `X`
as the colimit of the diagram of its affine opens, indexed by the thin category
`X.AffineZariskiSite`. If `X.size < κ` then that index category has fewer than `κ` arrows
and every value of the diagram is the spectrum of a ring of cardinality `< κ`, so `X` lies
in the closure of the spectra under `κ`-small colimits —
`CategoryTheory.ObjectProperty.colimitsCardinalClosure` — which is again essentially small.

The closure is taken at the *same* cardinal `κ` that bounds the rings; this is legitimate
because `κ` is uncountable, which is what turns the bound on affine opens into a bound on
arrows of the thin index category.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- The commutative rings of cardinality strictly below `κ` form an essentially small
property of objects of `CommRingCat.{u}`: every such ring is isomorphic to one whose carrier
is a subset of `κ.out`, and those are indexed by a type in universe `u`. -/
theorem CommRingCat.essentiallySmall_cardinalMk_lt (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun R : CommRingCat.{u} ↦ Cardinal.mk R < κ) := by
  classical
  let model (p : Σ T : Set κ.out, CommRing T) : CommRingCat.{u} := @CommRingCat.of p.1 p.2
  refine ⟨ObjectProperty.ofObj model, inferInstance, fun R hR ↦ ?_⟩
  obtain ⟨f⟩ : Nonempty (R ↪ κ.out) := hR.le.trans_eq (Cardinal.mk_out κ).symm
  let e := Equiv.ofInjective f f.injective
  let _ : CommRing (Set.range f) := e.symm.commRing
  exact ⟨model ⟨Set.range f, inferInstance⟩,
    ObjectProperty.ofObj_apply model ⟨Set.range f, inferInstance⟩,
    ⟨e.symm.ringEquiv.symm.toCommRingCatIso⟩⟩

namespace AlgebraicGeometry

/-- The schemes of size strictly below an uncountable cardinal `κ` form an essentially small
property of objects of `Scheme.{u}`. -/
theorem essentiallySmall_schemeSizeBelow (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) :
    ObjectProperty.EssentiallySmall.{u} (schemeSizeBelow κ) := by
  let P : ObjectProperty CommRingCat.{u} := fun R ↦ Cardinal.mk R < κ
  have : ObjectProperty.EssentiallySmall.{u} P := CommRingCat.essentiallySmall_cardinalMk_lt κ
  let Q := P.op.map Scheme.Spec
  refine ObjectProperty.EssentiallySmall.of_le (Q := Q.colimitsCardinalClosure κ) fun X hX ↦ ?_
  have hI : HasCardinalLT (Arrow X.AffineZariskiSite) κ := by
    rw [hasCardinalLT_arrow_iff_of_isThin _ _ hκ, hasCardinalLT_iff_cardinal_mk_lt]
    exact X.mk_affineOpens_le_size.trans_lt hX
  have := Q.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ X.AffineZariskiSite hI
  exact (Q.colimitsCardinalClosure κ).prop_of_isColimit
    (Scheme.AffineZariskiSite.isColimitCocone X) fun U ↦ Q.le_colimitsCardinalClosure κ _
      ⟨Opposite.op Γ(X, U.1), X.mk_sections_le_size U |>.trans_lt hX, ⟨Iso.refl _⟩⟩

/-- **Stacks 000J.** The cutoff category `Sch_κ` of schemes of size below a cardinal `κ` is
essentially small at the universe of its schemes.

No hypothesis on `κ` is needed: the schemes of size below `κ` are among those of size below
`Order.succ (max κ ℵ₀)`, which is uncountable. -/
theorem essentiallySmall_schemeBelow (κ : Cardinal.{u}) :
    EssentiallySmall.{u} (SchemeBelow κ) :=
  have hκμ : κ ≤ Order.succ (max κ Cardinal.aleph0) := (le_max_left _ _).trans (Order.le_succ _)
  have _ : ObjectProperty.EssentiallySmall.{u} (schemeSizeBelow (Order.succ
      (max κ Cardinal.aleph0))) :=
    essentiallySmall_schemeSizeBelow _ ((le_max_right _ _).trans (Order.le_succ _))
  have _ : ObjectProperty.EssentiallySmall.{u} (schemeSizeBelow κ) :=
    ObjectProperty.EssentiallySmall.of_le fun _ hX ↦ hX.trans_le hκμ
  inferInstance

end AlgebraicGeometry
