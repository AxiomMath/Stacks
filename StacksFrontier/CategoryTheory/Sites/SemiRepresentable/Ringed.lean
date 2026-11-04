module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Continuity

/-!
# The ringed site of a semi-representable object

Let `X` be a ringed site and `K` a semi-representable object of its underlying site. The site
`C / K` localized at `K` carries the inverse-image structure sheaf `O_K = j⁻¹ O_X`, where
`j : C / K ⥤ C` is the componentwise localization functor, and the pair is again a ringed site.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationStructureSheaf`: the sheaf of rings `O_K` on
  `C / K`.
* `AlgebraicGeometry.RingedSite.localization`: the ringed site `(C / K, O_K)`.

## Implementation notes

The inverse image along `j` is restriction of sheaves along a continuous functor between sites,
which is Mathlib's `CategoryTheory.Functor.sheafPushforwardContinuous` — its name refers to the
direction of the functor between the sites, not to the direction of the induced morphism of
topoi. Continuity of `j` is Stacks 0D85.

The localization datum feeding the functor has both of its semi-representable objects equal to
`K` and the identity between them; only its source object enters the localization functor and
its source topology.

The source's assertion that the localization *is* a ringed site is recorded as the bundled
construction `localization`.

## References

* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public section

universe w v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentable

namespace AlgebraicGeometry.RingedSite

/-- The sheaf of rings `O_K = j⁻¹ O_X` on the site localized at a semi-representable object
`K` of the underlying site of a ringed site `X`. -/
@[implicit_reducible]
noncomputable def localizationStructureSheaf (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) :
    Sheaf (componentwiseTopology X.J K) CommRingCat.{r} := by
  let S : LocalizationSites.{w} X.C X.J := { K := K, L := K, f := 𝟙 K }
  have : S.localizationFunctor.IsContinuous S.sourceTopology X.J :=
    LocalizationSites.localizationFunctor_isContinuous S
  exact (S.localizationFunctor.sheafPushforwardContinuous
    CommRingCat.{r} S.sourceTopology X.J).obj X.O

/-- The ringed site obtained by localizing a ringed site at a semi-representable object: its
underlying site is the disjoint union of the slice sites of the components of `K` with the
componentwise topology, and its structure sheaf is `O_K`. -/
noncomputable def localization (X : RingedSite.{u, u, u})
    (K : FormalCoproduct.{w} X.C) :
    RingedSite.{max u w, max u w, u} where
  C := ComponentOver K
  J := componentwiseTopology X.J K
  O := localizationStructureSheaf X K

/-- The ringed site obtained by localizing a ringed site at a semi-representable object: its
underlying site is the disjoint union of the slice sites of the components of `K` with the
componentwise topology, and its structure sheaf is `O_K`. -/
noncomputable def localization' (X : RingedSite.{u, v, r})
    (K : FormalCoproduct.{w} X.C) :
    RingedSite.{max u v w, max u v w, r} where
  C := ComponentOver K
  J := componentwiseTopology X.J K
  O := localizationStructureSheaf X K

end AlgebraicGeometry.RingedSite

end
