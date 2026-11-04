module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleLift
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineSubsiteLift
public import StacksCore.Tactic.StacksAttribute

/-!
# The small pro-étale topos of a closed immersion of affine schemes

Let `i : Z ⟶ X` be a closed immersion of affine schemes in a chosen big pro-étale site. The
affine ind-étale lift of Stacks 09BK is a cocontinuous, fully faithful left adjoint to base
change between the affine ind-étale subsites, so it is exactly the data that
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_pushforward_fullyFaithful_of_cocontinuousLift`
and its companions ask for. This file supplies it, leaving as the only hypotheses the geometric
input of Stacks 098X: that each of the two subsite inclusions is cover dense and carries the
restricted topology.

So the two clauses of Stacks 09BL about the small pro-étale topos of a closed immersion of
affine schemes — full faithfulness of the direct image and invertibility of its counit — hold
*modulo Stacks 098X alone*, Stacks 09BK no longer being an assumption. No `stacks` attribute is
attached, because 098X is not available: it rests on the bounded faithfully flat ind-étale
w-contractible extensions of Stacks 0984, and so on Stacks 0982.

## Main results

* `AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange_comp_inclusion`: base change on the
  affine ind-étale subsites is small pro-étale base change.
* `smallProetaleMorphism_pushforward_fullyFaithful_of_affineIndEtaleDense`: the direct image
  along `i` on small pro-étale sheaves of sets is fully faithful.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineIndEtaleDense`: the
  counit of the direct-image adjunction along `i` is invertible.

## Implementation notes

The comparison isomorphism between the two routes from the affine ind-étale subsite of `X` to
the small pro-étale site of `Z` is the identity: both are the pullback along `i` of the
underlying object of the slice, lifted twice along full subcategory inclusions, and lifting
commutes with precomposition.

The sheaf-value universe is `Type (u + 1)`, as in
`AlgebraicGeometry.ProEtale.smallProetaleMorphism`; the equivalences on sheaves come from
`AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction_of_isDenseSubsite`
at `v := u + 1`.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) {X Z : B.Scheme} (i : Z ⟶ X)
  [IsAffine X.obj] [IsAffine Z.obj] [IsClosedImmersion (B.inclusion.map i)]

omit [IsClosedImmersion (B.inclusion.map i)] in
/-- **Base change on affine ind-étale subsites is small pro-étale base change.** Restricting an
affine ind-étale object of `X` and then base changing it along `i` in the small pro-étale site
of `Z` gives the same object of that site as base changing it in the affine ind-étale subsite
and then restricting. -/
theorem affineIndEtaleBaseChange_comp_inclusion :
    AffineIndEtaleProetale.inclusion B X ⋙ smallProetaleBaseChange B Z X i =
      affineIndEtaleBaseChange B i ⋙ AffineIndEtaleProetale.inclusion B Z :=
  rfl

/-- The comparison isomorphism of
`AlgebraicGeometry.ProEtale.affineIndEtaleBaseChange_comp_inclusion`, in the form the subsite
comparison results take it. -/
def affineIndEtaleBaseChangeIso :
    AffineIndEtaleProetale.inclusion B X ⋙ smallProetaleBaseChange B Z X i ≅
      affineIndEtaleBaseChange B i ⋙ AffineIndEtaleProetale.inclusion B Z :=
  eqToIso (affineIndEtaleBaseChange_comp_inclusion B i)

section

variable
  [(AffineIndEtaleProetale.inclusion B Z).IsCoverDense
    (SmallProetale.topology B Z.obj Z.property)]
  [(AffineIndEtaleProetale.inclusion B X).IsCoverDense
    (SmallProetale.topology B X.obj X.property)]

/-- **Full faithfulness of the direct image, from Stacks 098X.** If the two affine ind-étale
subsite inclusions are cover dense and carry the restricted topology, then the direct image
along a closed immersion of affine schemes, on small pro-étale sheaves of sets, is fully
faithful.

This is one clause of Stacks 09BL. Its 09BK input — the cocontinuous fully faithful lift
adjoint to base change — is
`AlgebraicGeometry.ProEtale.affineIndEtaleLift_adj_baseChange` together with
`AlgebraicGeometry.ProEtale.affineIndEtaleLift_fullyFaithful` and
`AlgebraicGeometry.ProEtale.affineIndEtaleLift_isCocontinuous`. -/
theorem smallProetaleMorphism_pushforward_fullyFaithful_of_affineIndEtaleDense
    (htopZ : AffineIndEtaleProetale.topology B Z =
      (AffineIndEtaleProetale.inclusion B Z).restrictedTopology
        (SmallProetale.topology B Z.obj Z.property))
    (htopX : AffineIndEtaleProetale.topology B X =
      (AffineIndEtaleProetale.inclusion B X).restrictedTopology
        (SmallProetale.topology B X.obj X.property)) :
    Nonempty (smallProetaleMorphism B Z X i).pushforward.FullyFaithful := by
  have _ := AffineIndEtaleProetale.isDenseSubsite_of_restrictedTopology htopZ
  have _ := AffineIndEtaleProetale.isDenseSubsite_of_restrictedTopology htopX
  have _ := AffineIndEtaleProetale.isEquivalence_restriction_of_isDenseSubsite.{u, u + 1}
    (B := B) (S := Z)
  have _ := AffineIndEtaleProetale.isEquivalence_restriction_of_isDenseSubsite.{u, u + 1}
    (B := B) (S := X)
  obtain ⟨adj⟩ := affineIndEtaleLift_adj_baseChange B i
  obtain ⟨ff⟩ := affineIndEtaleLift_fullyFaithful B i
  have _ := ff.full
  have _ := ff.faithful
  exact smallProetaleMorphism_pushforward_fullyFaithful_of_cocontinuousLift B i
    (AffineIndEtaleProetale.topology B Z) (AffineIndEtaleProetale.topology B X) adj
    (affineIndEtaleBaseChangeIso B i)

/-- **Invertibility of the direct-image counit, from Stacks 098X.** Under the same hypotheses,
the counit of the direct-image adjunction along a closed immersion of affine schemes, on small
pro-étale sheaves of sets, is a natural isomorphism.

This is the input that
`AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_coversTop_of_counit` carries
from affine members of a covering family to Stacks 09AA. -/
theorem smallProetaleMorphism_counit_isIso_of_affineIndEtaleDense
    (htopZ : AffineIndEtaleProetale.topology B Z =
      (AffineIndEtaleProetale.inclusion B Z).restrictedTopology
        (SmallProetale.topology B Z.obj Z.property))
    (htopX : AffineIndEtaleProetale.topology B X =
      (AffineIndEtaleProetale.inclusion B X).restrictedTopology
        (SmallProetale.topology B X.obj X.property)) :
    IsIso (smallProetaleMorphism B Z X i).adj.counit := by
  obtain ⟨ff⟩ :=
    smallProetaleMorphism_pushforward_fullyFaithful_of_affineIndEtaleDense B i htopZ htopX
  have _ := ff.full
  have _ := ff.faithful
  exact (smallProetaleMorphism B Z X i).adj.counit_isIso_of_R_fully_faithful

end

end AlgebraicGeometry.ProEtale

end
