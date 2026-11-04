module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionProjection

/-!
# Exactness of the restriction of modules to the small étale site of an algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, and let `π_F : (Sh(𝒳_étale), 𝒪_𝒳) ⟶ (Sh(F_étale), 𝒪_F)` be the morphism of ringed topoi of
Stacks 073M, whose direct image is restriction along the functor `u_F : F_étale ⥤ 𝒳`. Then
`π_{F,*}` is exact on sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteColimits_pushforwardModules_projectionRingedToposHom`:
  the restriction of sheaves of modules to the small étale site of `F` preserves finite
  colimits.
* `AlgebraicGeometry.Space.exactFunctor_pushforwardModules_projectionRingedToposHom`: it is
  exact.

## References

* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 075N](https://stacks.math.columbia.edu/tag/075N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (hp : p.IsFiberedInGroupoids) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)

/-- The direct image of `π_F`, restriction of sheaves of sets to the small étale site of `F`,
preserves epimorphisms. -/
theorem preservesEpimorphisms_projectionRingedToposHom_pushforward :
    (projectionRingedToposHom B S hS F p hp hF e).toToposHom.pushforward.PreservesEpimorphisms :=
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let := restrictionFunctor_isCocontinuous B S hS F p hp e
  let : EssentiallySmall.{u} 𝒳 := essentiallySmall_of_equivalenceOver B S hS F p e
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  CategoryTheory.Functor.preservesEpimorphisms_sheafPushforwardContinuous
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
    (restrictionFunctor B S hS F p e)

/-- The restriction of sheaves of modules to the small étale site of `F` preserves finite
colimits. -/
theorem preservesFiniteColimits_pushforwardModules_projectionRingedToposHom
    [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
      (forget AddCommGrpCat.{u})]
    [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
    [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
    [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesFiniteColimits (RingedToposHom.pushforwardModules
      (projectionRingedToposHom B S hS F p hp hF e)) :=
  let := preservesEpimorphisms_projectionRingedToposHom_pushforward B S hS F p hp hF e
  RingedToposHom.preservesFiniteColimits_pushforwardModules _

attribute [instance] preservesFiniteColimits_pushforwardModules_projectionRingedToposHom

/-- The restriction of sheaves of modules to the small étale site of `F` is exact. -/
theorem exactFunctor_pushforwardModules_projectionRingedToposHom
    [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.HasSheafCompose
      (forget AddCommGrpCat.{u})]
    [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [HasSheafify (FibredSite.associatedRingedTopos B S hS p hp .etale).J AddCommGrpCat.{u}]
    [(FibredSite.associatedRingedTopos B S hS p hp .etale).J.WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    [HasSheafify (smallEtaleRingedTopos B S hS ⟨F, hF⟩).J AddCommGrpCat.{u}]
    [(smallEtaleRingedTopos B S hS ⟨F, hF⟩).J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    exactFunctor _ _ (RingedToposHom.pushforwardModules
      (projectionRingedToposHom B S hS F p hp hF e)) :=
  let := preservesEpimorphisms_projectionRingedToposHom_pushforward B S hS F p hp hF e
  RingedToposHom.exactFunctor_pushforwardModules _

end AlgebraicGeometry.Space

end
