module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# Inverse image along pro-étale base change, and when it has a left adjoint

A morphism of schemes `i : Z ⟶ X` induces base change `X.ProEt ⥤ Z.ProEt` on the small
pro-étale categories, a continuous functor of sites. Inverse image of sheaves of sets is the
sheafified left Kan extension along it, and it is a left adjoint: its right adjoint is
restriction along base change, the direct image. This file shows that inverse image is also a
*right* adjoint — so that it has a lower shriek — as soon as base change admits a continuous
left adjoint `W : Z.ProEt ⥤ X.ProEt`.

For a closed immersion of affine schemes, lifting ind-étale algebras across the corresponding
quotient map provides such a `W`, and the existence of a left adjoint to `i⁻¹` that follows is
part (3) of [Stacks, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL). That input is *not*
available here, so no declaration of this file carries a `stacks` attribute; see the discussion
below.

## Main definitions

* `AlgebraicGeometry.ProEtale.Sets.proetaleInverseImage` is inverse image of sheaves of sets
  along base change on the small pro-étale sites.

## Main results

* `AlgebraicGeometry.ProEtale.Sets.proetaleLowerShriekAdjunction`: if base change along `i` has
  a continuous left adjoint `W`, the sheafified left Kan extension along `W` is a left adjoint
  of inverse image along `i`.
* `AlgebraicGeometry.ProEtale.Sets.isRightAdjoint_proetaleInverseImage_of_continuous_leftAdjoint`:
  consequently inverse image along `i` is a right adjoint, i.e. the lower shriek exists.

## What this supplies for Stacks 09BL, and what it does not

Stacks 09BL (3) asserts, for a closed immersion `i : Z ⟶ X` of affine schemes, that inverse
image on pro-étale sheaves of sets has a left adjoint `i^{Sh}_!`. The source's route is: the
morphism of topoi `i` is the one attached to the fully faithful cocontinuous functor
`v : Z_{app} ⟶ X_{app}` of Stacks 09BK between the *affine ind-étale* pro-étale sites, which
is a left adjoint of base change there; Sites 00XX then computes `i⁻¹` as the sheafification of
restriction along `v`, and that functor is a right adjoint because `v` is continuous. The last
step is what this file provides, and nothing else. Of the two inputs this needs, the second is
now available and the first is not.

1. The lift `v` itself, Stacks 09BK. Its ring-theoretic content, the lift of ind-étale algebras
   along a quotient map `A ⟶ A ⧸ I` of Stacks 097P, is available as
   `AlgebraicGeometry.ProEtale.indEtaleBaseChange_hasFullyFaithfulRightAdjoint`, and so is the
   functor of sites it produces on the affine ind-étale objects: for a closed immersion of
   affine schemes, `AlgebraicGeometry.ProEtale.appProetaleLift` together with
   `AlgebraicGeometry.ProEtale.appProetaleBaseChange_hasLeftAdjoint`,
   `AlgebraicGeometry.ProEtale.appProetaleLift_fullyFaithful` and
   `AlgebraicGeometry.ProEtale.appProetaleLift_isCocontinuous`. What is absent is *continuity*
   of `v`, which is what the transport in 2 asks of it; `v` is cocontinuous, and the
   sheafification in Stacks 09BL (1) is there precisely because restriction along `v` need not
   already be a sheaf. Those statements are moreover made for the `AppSmallProetale` spelling
   of the affine ind-étale site, while
   `AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_appAdjunction` is stated
   for the `AlgebraicGeometry.ProEtale.AppProetale` spelling; the two object properties agree by
   `AlgebraicGeometry.ProEtale.indEtale_iff_ind_etale_underMk`, but no functor identifying the
   two categories is in the library.
2. The comparison of the two sites, which is no longer missing.
   `AlgebraicGeometry.Scheme.ProEt` is the category of *all* weakly étale schemes over the base,
   not the affine ind-étale site, and `W` above is asked for on all of it; a weakly étale
   `Z`-scheme is only Zariski-locally affine ind-étale, so lifting it directly would mean gluing
   lifts of an affine cover. That is not needed: the conclusion transports across the
   restriction equivalence of Stacks 098X for this very site, which is
   `AlgebraicGeometry.ProEtale.AppProetale.inclusion_isDenseSubsite` — the affine ind-étale
   objects are a dense subsite of the unrestricted small pro-étale site of an affine scheme,
   with nothing assumed, the `AlgebraicGeometry.ProEtale.HasAppCover` hypothesis being
   discharged by `AlgebraicGeometry.ProEtale.hasAppCover` from the ring-level Stacks 097Z
   `AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_extension`. Base change preserves
   affine ind-étale objects, so the two direct images commute with those restrictions, and the
   transport itself is carried out in
   `AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_hasAppCover`. The
   topology on the affine ind-étale objects there is the one induced by the inclusion, which is
   what every statement in that transport takes as a parameter.

With 1, Stacks 09BL (3) closes for the sites of `AlgebraicGeometry.Scheme.ProEt` — through the
transport of 2, not through the theorems below, which ask for a continuous left adjoint of base
change on the whole of `Z.ProEt`.

## Implementation notes

Inverse image is Mathlib's `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` for
the base-change functor `AlgebraicGeometry.Scheme.proetaleBaseChange`, not for an arbitrary
functor isomorphic to it, so the left adjoint produced here is a left adjoint of the canonical
inverse-image functor. No affineness and no condition on `i` beyond the existence of the
continuous left adjoint is assumed; a closed immersion of affine schemes is the case of interest
but plays no role in the argument. Only continuity of `W` is assumed, rather than the
continuity, cocontinuity and full faithfulness that Stacks 09BK establishes for the lift:
cocontinuity of a left adjoint of a continuous functor is automatic (Stacks 09VR) and full
faithfulness is needed only for the further parts of Stacks 09BL. The coefficient universe may
be any universe containing the site.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale.Sets

/-- Inverse image of sheaves of sets along a morphism of schemes, on the small pro-étale sites:
the sheafification of the left Kan extension along pro-étale base change. -/
abbrev proetaleInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.ProEt.topology Z) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
    (Type (max (u + 1) v)) (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z)

/-- If pro-étale base change along `i : Z ⟶ X` has a continuous left adjoint `W`, then the
sheafification of the left Kan extension along `W` is a left adjoint of inverse image along
`i`. -/
def proetaleLowerShriekAdjunction {Z X : Scheme.{u}} {i : Z ⟶ X} {W : Z.ProEt ⥤ X.ProEt}
    (adj : W ⊣ Scheme.proetaleBaseChange i)
    [W.IsContinuous (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X)] :
    Functor.sheafPullbackConstruction.sheafPullback W (Type (max (u + 1) v))
        (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X) ⊣
      proetaleInverseImage.{u, v} i :=
  Functor.sheafPullbackAdjunctionOfAdjunction (Type (max (u + 1) v))
    (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X) adj

/-- If pro-étale base change along `i : Z ⟶ X` has a continuous left adjoint, then inverse
image of sheaves of sets along `i` is a right adjoint, so it has a lower shriek. -/
theorem isRightAdjoint_proetaleInverseImage_of_continuous_leftAdjoint {Z X : Scheme.{u}}
    {i : Z ⟶ X} {W : Z.ProEt ⥤ X.ProEt} (adj : W ⊣ Scheme.proetaleBaseChange i)
    [W.IsContinuous (Scheme.ProEt.topology Z) (Scheme.ProEt.topology X)] :
    (proetaleInverseImage.{u, v} i).IsRightAdjoint :=
  (proetaleLowerShriekAdjunction.{u, v} adj).isRightAdjoint

end AlgebraicGeometry.ProEtale.Sets

end
