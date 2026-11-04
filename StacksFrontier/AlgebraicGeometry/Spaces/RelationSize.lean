module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The relation scheme of a relation on an object of a big fppf site belongs to the site

Let `B` be a big fppf site, let `U` be an object of the big fppf site of a scheme `S`
contained in `B`, and let `j : R ⟶ U ×_S U` be a *relation* on `U` over `S`, that is, a monic
pre-relation. Then the scheme `R` is contained in `B`, with no hypothesis on `R` at all.

This is the representability of the kernel pair in Stacks 0265. There the relation scheme is
an object of `Sch_α` by fiat — every scheme in the source lemma is — whereas
`Stacks.Groupoids.PreRelation` takes an arbitrary `S`-scheme for its relation scheme, so the
containment has to be derived. It is: the fibre product `U ×_S U` is contained in `B` because
the size cutoff is closed under fibre products, and the source of a monomorphism into a
scheme of size below a cutoff closed under powersets again has size below that cutoff.

## Main results

* `AlgebraicGeometry.Scheme.size_prod_left_lt`: the scheme underlying a product in the slice
  over `S` of two `S`-schemes of size below a cutoff has size below that cutoff.
* `AlgebraicGeometry.BigFppfSite.contains_of_mono`: the source of a monomorphism into a
  scheme contained in a big fppf site is contained in that site.
* `Stacks.Groupoids.contains_left_of_mono`: the relation scheme of a relation on an
  `S`-scheme contained in a big fppf site is contained in that site.
* `Stacks.Groupoids.contains_left_of_isEtaleEquivalenceRelation`: the same for an étale
  equivalence relation on an object of the big fppf site of `S`, which is the form Stacks
  0265 consumes.

## Implementation notes

The monomorphism bound used is `AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit`,
the unconditional one: it asks nothing of the monomorphism and instead asks the cutoff to be
closed under powersets, which a big fppf site's cutoff is by
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`.

The two conditional bounds of Stacks 000R (8) are *not* usable here.
`AlgebraicGeometry.Scheme.size_lt_of_mono_quasiCompact` would need `j` quasi-compact, which
fails already for the orbit relation of a translation action of `ℤ` on the affine line. And
`AlgebraicGeometry.Scheme.size_lt_of_mono_locallyOfFinitePresentation` would need `j` locally
of finite presentation; the cancellation lemma of Stacks 02FV
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`) derives that from the target map
`R ⟶ U` being étale only if the projection `U ×_S U ⟶ U` is locally of finite type, hence
only if `U ⟶ S` is, and an étale equivalence relation does not provide that: its étaleness
hypothesis is on the two maps `R ⟶ U`, while `U` is assumed only affine. The trivial
relation, `R = U` with `j` the diagonal of `U ⟶ S`, has both of its maps the identity and is
therefore étale, while `j` itself is the diagonal immersion of a morphism which need not be
locally of finite presentation.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The scheme underlying a product of two `S`-schemes, taken in the slice over `S`, has size
below any cardinal below which the sizes of the two factors lie.

A product in the slice is a fibre product over `S` in schemes, and the size cutoffs are
closed under fibre products. -/
theorem Scheme.size_prod_left_lt {κ : Cardinal.{u}} {S : Scheme.{u}} (U V : Over S)
    (hU : U.left.size < κ) (hV : V.left.size < κ) : (U ⨯ V : Over S).left.size < κ := by
  have h : IsPullback (prod.fst (X := U) (Y := V)).left (prod.snd (X := U) (Y := V)).left
      U.hom V.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := U) (Y := V)) prod.snd) (prodIsProd U V)
  rw [Scheme.size_congr h.isoPullback]
  exact Scheme.size_pullback_lt _ _ hU hV

namespace BigFppfSite

/-- The source of a monomorphism into a scheme contained in a big fppf site is contained in
that site.

Nothing is assumed of the monomorphism: the cutoff of a big fppf site is a strong prelimit
cardinal, and that is what the unconditional bound of Stacks 000R (8) asks for. -/
theorem contains_of_mono (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (hY : B.Contains Y) : B.Contains X :=
  Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit f hY

/-- The scheme underlying a product in the slice over `S` of two `S`-schemes contained in a
big fppf site is contained in that site. -/
theorem contains_prod_left (B : BigFppfSite.{u}) {S : Scheme.{u}} (U V : Over S)
    (hU : B.Contains U.left) (hV : B.Contains V.left) :
    B.Contains (U ⨯ V : Over S).left :=
  Scheme.size_prod_left_lt U V hU hV

end BigFppfSite

end AlgebraicGeometry

namespace Stacks.Groupoids

variable {S : Scheme.{u}}

/-- The relation scheme of a relation on an `S`-scheme contained in a big fppf site is itself
contained in that site.

A relation, as opposed to a pre-relation, is a monomorphism `R ⟶ U ×_S U`, and both bounds it
needs are unconditional: the product is contained in the site because the cutoff is closed
under fibre products, and the source of a monomorphism into it because the cutoff is closed
under powersets. -/
theorem contains_left_of_mono (B : BigFppfSite.{u}) {R U : Over S} (j : PreRelation R U)
    [Mono j] (hU : B.Contains U.left) : B.Contains R.left :=
  B.contains_of_mono j.left (B.contains_prod_left U U hU hU)

/-- The relation scheme of an étale equivalence relation on an object of the big fppf site of
`S` is contained in the site.

This is the form the proof of Stacks 0265 consumes: its relation scheme is an arbitrary
`S`-scheme, and the representability of the kernel pair of the quotient map needs it to be an
object of the site. An étale equivalence relation is monic, and the underlying scheme of an
object of the big fppf site of `S` is contained in the site by the defining property of the
site's underlying category. -/
theorem contains_left_of_isEtaleEquivalenceRelation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : BigFppfOver B S hS) {R : Over S}
    (j : PreRelation R ((Over.post B.inclusion).obj U)) [IsEtaleEquivalenceRelation j] :
    B.Contains R.left :=
  have : Mono j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mp inferInstance).1
  contains_left_of_mono B j U.left.2

end Stacks.Groupoids

end
