module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSheafAtlasCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares

/-!
# Algebraic spaces in the étale topology

The big fppf site and the big étale site of a scheme `S` are two topologies on one and the same
category `Sch_α/S` of schemes over `S`. A presheaf on that category which is a sheaf for the
étale topology and which receives a morphism from an algebraic space over `S` that is
representable by algebraic spaces, surjective and smooth is an algebraic space over `S`.

The étale topology on `Sch_α/S` is `AlgebraicGeometry.BigEtaleOver.topology` of
`AlgebraicGeometry.associatedBigEtaleSite`, the big étale site whose cutoff, covering bound and
covering ordinal are those of the given big fppf site; its slice over `S` is the category
`AlgebraicGeometry.BigFppfOver` itself, so the two sheaf conditions are conditions on one
presheaf ([Stacks, Tag 03FF]).

## Main results

* `AlgebraicGeometry.Space.hasProperty_flat_of_hasProperty_smooth` and
  `AlgebraicGeometry.Space.hasProperty_locallyOfFinitePresentation_of_hasProperty_smooth`: a
  morphism of presheaves representable by algebraic spaces which is smooth is flat and locally
  of finite presentation.
* `AlgebraicGeometry.Space.etaleTopologyOver_le_bigEtaleOverTopology`: the localization at `S`
  of the étale topology of the fppf site is coarser than the topology of the big étale site
  associated with it, so a sheaf for the latter is a sheaf for the former.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_etaleSheaf_of_smooth_surjection`: an étale sheaf
  receiving a surjective smooth morphism, representable by algebraic spaces, from an algebraic
  space is an algebraic space.

## References

* [Stacks Project, Tag 0GE0](https://stacks.math.columbia.edu/tag/0GE0)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A smooth chart is flat and locally of finite presentation -/

/-- A morphism of presheaves on the big fppf site of `S` which is representable by algebraic
spaces and smooth is flat. -/
theorem hasProperty_flat_of_hasProperty_smooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) f hf) :
    HasProperty B S hS (flatProperty B S hS) f hf := fun U ξ =>
  isFlat_of_isSyntomic B S hS (isSyntomic_of_isSmooth B S hS _ (hsmooth U ξ))

/-- A morphism of presheaves on the big fppf site of `S` which is representable by algebraic
spaces and smooth is locally of finite presentation. -/
theorem hasProperty_locallyOfFinitePresentation_of_hasProperty_smooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) f hf) :
    HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf := fun U ξ =>
  isLocallyOfFinitePresentation_of_isSyntomic B S hS
    (isSyntomic_of_isSmooth B S hS _ (hsmooth U ξ))

/-! ### The two étale topologies on `Sch_α/S` -/

/-- The étale topology of the big fppf site `B`, localized at `S`, is coarser than the topology
of the big étale site over `S` associated with `B`. -/
theorem etaleTopologyOver_le_bigEtaleOverTopology :
    (etaleTopology B).over (B.obj hS) ≤
      BigEtaleOver.topology (associatedBigEtaleSite B) S hS := by
  have hle : etaleTopology B ≤ (associatedBigEtaleSite B).topology :=
    Precoverage.toGrothendieck_mono fun X _ ⟨E, hR, hE⟩ =>
      ⟨E, hR, (etaleBounded_eq_fppfEtaleBounded B ⟨X, E⟩).mp hE⟩
  rw [bigEtaleOver_topology_eq]
  intro T Z hZ
  rw [GrothendieckTopology.mem_over_iff] at hZ ⊢
  exact hle _ hZ

/-! ### Stacks 0GE0 -/

/-- Let `S` be a scheme contained in a big fppf site `B` and let `F` be a
presheaf on the common underlying category `Sch_α/S` of the big fppf and the big étale site of
`S`. Assume

1. `F` is a sheaf for the étale topology, and
2. there are an algebraic space `U` over `S` and a morphism `f : U ⟶ F` which is representable
   by algebraic spaces, surjective and smooth.

Then `F` is an algebraic space over `S`. -/
@[stacks 0GE0]
theorem isAlgebraicSpace_of_etaleSheaf_of_smooth_surjection
    {F U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S hS) F)
    (hU : IsAlgebraicSpace B S hS U) (f : U ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hsurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hsmooth : HasProperty B S hS (smoothMorphismProperty B S hS) f hf) :
    IsAlgebraicSpace B S hS F :=
  coreCriterion_unconditional B S hS
    (Presheaf.IsSheaf.of_le (etaleTopologyOver_le_bigEtaleOverTopology B S hS) hF) hU f hf hsurj
    hsmooth

end AlgebraicGeometry.Space

end
