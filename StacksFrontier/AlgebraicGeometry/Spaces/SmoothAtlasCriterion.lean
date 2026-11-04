module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafSpaceCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The smooth-atlas criterion in the relatively representable spelling

`AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas` settles, unconditionally, that an
fppf sheaf with a surjective étale atlas by an object of the site is an algebraic space.  This
module is the companion statement for a surjective *smooth* atlas, in the same spelling: the
atlas is asked to be surjective and smooth after every represented base change, which is the
form the atlas clause of Algebraic Spaces, Definition 025Y itself takes.

The smooth case is not a corollary of the étale one.  Refining the *source* of a smooth atlas
along an étale morphism leaves a smooth morphism to the sheaf, not an étale one, so the étale
local sections of a smooth surjection do not turn a smooth atlas into an étale atlas; what is
needed is a slicing of the kernel-pair groupoid, which this library does not have.  The route
taken here is instead the source's own: `AlgebraicGeometry.Space.coreCriterion`, which is the
shared content of Stacks 07WF and Stacks 0BH4.  Consequently the clause of Stacks 04S6 that
criterion carries, `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`, is carried here too.

## Main results

* `AlgebraicGeometry.Space.etaleTopologyOver_le_topology` and
  `AlgebraicGeometry.Space.isSheaf_etaleTopologyOver_of_isSheaf`: the chosen big étale topology
  over `S` is coarser than the big fppf topology over `S`, so an fppf sheaf is an étale sheaf.
* `AlgebraicGeometry.Space.hasProperty_surjectiveMorphismProperty_of_presheaf` and
  `AlgebraicGeometry.Space.hasProperty_smoothMorphismProperty_of_presheaf`: the relatively
  representable surjectivity and smoothness of a morphism of presheaves give it the
  corresponding property of Stacks 03XZ.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_surjective_smooth_atlas`: an fppf sheaf with a
  surjective smooth atlas by an object of the site is an algebraic space, granted
  `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`.

## Implementation notes

The two property bridges are both unconditional, and neither needs the conclusion.  For
surjectivity this is `AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`; for
smoothness it is `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp`
at `AlgebraicGeometry.Smooth`, which applies because an étale morphism followed by a smooth one
is smooth.  There is no such bridge for surjectivity by that route — an étale morphism composed
with a surjection need not be surjective — which is why the two are proved differently.

`AlgebraicGeometry.Space.HasProperty` asks its property of every represented base change of the
morphism, so each bridge is applied to the base change rather than to the atlas itself; that the
relatively representable property survives a base change is
`AlgebraicGeometry.Space.presheaf_of_isPullback`.

No diagonal hypothesis appears.  `AlgebraicGeometry.Space.coreCriterion` wants the atlas
representable by algebraic spaces, and Stacks 07WF obtains that from a representable diagonal;
here the relatively representable spelling of the atlas already carries representability by
objects of the site, which is stronger.  For the same reason this statement is **not** tagged
Stacks 07WF: that tag asks only for an étale sheaf and a diagonal representable by algebraic
spaces, and neither hypothesis is the one used here.  The module is infrastructure.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 07WF](https://stacks.math.columbia.edu/tag/07WF)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An fppf sheaf is an étale sheaf -/

/-- The chosen big étale topology over `S` is coarser than the big fppf topology over `S`: both
are localisations at `S` of topologies on the common underlying category of schemes, and there
the étale one is coarser. -/
theorem etaleTopologyOver_le_topology :
    (etaleTopology B).over (B.obj hS) ≤ BigFppfOver.topology B S hS := by
  intro T Z hZ
  rw [GrothendieckTopology.mem_over_iff] at hZ ⊢
  exact Stack.etaleTopology_le_topology B _ hZ

/-- A sheaf for the big fppf topology over `S` is a sheaf for the chosen big étale topology
over `S`. -/
theorem isSheaf_etaleTopologyOver_of_isSheaf {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) F := by
  rw [isSheaf_iff_isSheaf_of_type] at hF ⊢
  exact Presieve.isSheaf_of_le _ (etaleTopologyOver_le_topology B S hS) hF

/-! ### From the relatively representable properties to the properties of Stacks 03XZ -/

/-- A morphism of presheaves on the big fppf site of `S` which is surjective after every
represented base change is surjective in the sense of Stacks 03XZ. -/
theorem hasProperty_surjectiveMorphismProperty_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf := by
  intro U ξ
  exact isSurjective_of_presheafSurjective
    (hf := presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ f).flip hsurj) _

/-- A morphism of presheaves on the big fppf site of `S` which is smooth after every represented
base change is smooth in the sense of Stacks 03XZ. -/
theorem hasProperty_smoothMorphismProperty_of_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hsmooth : (MorphismProperty.inverseImage (@Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f) :
    HasProperty B S hS (smoothMorphismProperty B S hS) f hf := by
  intro U ξ
  refine presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp B S hS
    (@Smooth.{u} : MorphismProperty Scheme.{u}) (fun i p hi hp => ?_) _
    (presheaf_of_isPullback B S hS (IsPullback.of_hasPullback ξ f).flip hsmooth)
  have : Etale i := hi
  have : Smooth p := hp
  infer_instance

/-! ### The criterion -/

/-- An fppf sheaf on the big fppf site of `S` which admits an atlas by an object of the site
that is surjective and smooth after every represented base change is an algebraic space
over `S`.

This is the smooth companion of `AlgebraicGeometry.isAlgebraicSpace_of_surjective_etale_atlas`,
Stacks 0BGQ.  Unlike that one it is not unconditional: the smooth case goes through
`AlgebraicGeometry.Space.coreCriterion`, so the clause of Stacks 04S6 that criterion carries,
`AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf`, is a hypothesis here as well. -/
theorem isAlgebraicSpace_of_surjective_smooth_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hsmooth : (MorphismProperty.inverseImage (@Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsAlgebraicSpace B S hS F :=
  coreCriterion B S hS (isSheaf_etaleTopologyOver_of_isSheaf B S hS hF)
    (isAlgebraicSpace_yoneda B S hS U) f
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hsurj.rep)
    (hasProperty_surjectiveMorphismProperty_of_presheaf B S hS f hsurj _)
    (hasProperty_smoothMorphismProperty_of_presheaf B S hS f hsmooth _) h04S6

end AlgebraicGeometry.Space

end
