module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale

/-!
# The unit of `a_X⁻¹ ⊣ a_{X,*}` for an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `X` an algebraic space of `T`.
The morphism `a_X` from the big fppf topos of `X` to its small étale topos is the composite
`π_X ∘ ε_X` (Stacks 0DGI). The unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism at every small étale
sheaf `G` such that `π_X⁻¹G` is an fppf sheaf; this is the formal part of the full faithfulness of
`a_X⁻¹` (Stacks 0DGF, part (1)).

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_bigToSmallEtaleMorphism_unit`: the unit of
  `π_X⁻¹ ⊣ π_{X,*}` is an isomorphism.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf`: the
  unit of `ε_X⁻¹ ⊣ ε_{X,*}` is an isomorphism at a big étale sheaf whose underlying presheaf is
  an fppf sheaf.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_fppfToSmallEtaleMorphism_unit_app_of_isSheaf`: the
  unit of `a_X⁻¹ ⊣ a_{X,*}` is an isomorphism at a small étale sheaf `G` as soon as `π_X⁻¹G` is
  an fppf sheaf.

## References

* [Stacks Project, Tag 0DGF](https://stacks.math.columbia.edu/tag/0DGF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) (X : T.Spaces)

/-- **The unit of `π_X⁻¹ ⊣ π_{X,*}` is an isomorphism.** -/
theorem isIso_bigToSmallEtaleMorphism_unit : IsIso (T.bigToSmallEtaleMorphism X).adj.unit := by
  let adj₂ := (T.smallToBigEtaleMorphism (𝟙 X)).adj.ofNatIsoLeft
    (T.smallToBig_inverseImageIso_bigToSmall_pushforward X)
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit ⟨(T.bigToSmallEtaleMorphism X).adj, adj₂⟩).2
    (adj₂.isIso_counit_of_iso (T.bigToSmall_comp_smallToBig_pushforwardIso X))

end AlgebraicGeometry.BigEtaleSpaceSite

namespace AlgebraicGeometry.BigFppfSpaceSite

/-- The unit of the adjunction attached to the identity functor, for two topologies on a
category with arbitrary morphism universe, is invertible at a sheaf for the coarser topology
whose underlying presheaf is a sheaf for the finer one. -/
private theorem isIso_sheafAdjunctionContinuousId_unit_app_of_isSheaf {C : Type*} [Category C]
    (J K : GrothendieckTopology C) [(𝟭 C).IsContinuous J K] (A : Type*) [Category A]
    [((𝟭 C).sheafPushforwardContinuous A J K).IsRightAdjoint]
    (G : Sheaf J A) (hG : Presheaf.IsSheaf K G.obj) :
    IsIso (((𝟭 C).sheafAdjunctionContinuous A J K).unit.app G) := by
  let ff : ((𝟭 C).sheafPushforwardContinuous A J K).FullyFaithful :=
    { preimage := fun f => ObjectProperty.homMk f.hom }
  have := ff.full
  have := ff.faithful
  rw [Adjunction.isIso_unit_app_iff_mem_essImage]
  exact ⟨⟨G.obj, hG⟩, ⟨Iso.refl _⟩⟩

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **The unit of `ε_X⁻¹ ⊣ ε_{X,*}` at an fppf sheaf.** Let `K` be a big étale sheaf on `X`
whose underlying presheaf, read on the big fppf slice at `X`, is an fppf sheaf. Then the unit
`K ⟶ ε_{X,*}ε_X⁻¹K` is an isomorphism. -/
theorem isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf (X : T.Spaces)
    (K : Sheaf (E.bigEtaleTopology (etaleSpace T E h X)) (Type (u + 1)))
    (hK : Presheaf.IsSheaf (BigFppfSpaceOver.topology T X)
      ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).functor.op ⋙ K.obj)) :
    IsIso ((fppfToBigEtaleMorphism T E h X).adj.unit.app K) := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      exact @isIso_sheafAdjunctionContinuousId_unit_app_of_isSheaf _ _ _ _
        (fppfToBigEtale_isContinuous T' E' rfl X) _ _
        ⟨_, ⟨(fppfToBigEtaleMorphism T' E' rfl X).adj⟩⟩ K hK

/-- **The unit of `a_X⁻¹ ⊣ a_{X,*}` at a small étale sheaf `G` whose pullback `π_X⁻¹G` is an
fppf sheaf is an isomorphism.** -/
theorem isIso_fppfToSmallEtaleMorphism_unit_app_of_isSheaf (X : T.Spaces)
    (G : Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      (Type (u + 1)))
    (hG : Presheaf.IsSheaf (BigFppfSpaceOver.topology T X)
      ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).functor.op ⋙
        ((E.bigToSmallEtaleMorphism (etaleSpace T E h X)).inverseImage.obj G).obj)) :
    IsIso ((fppfToSmallEtaleMorphism T E h X).adj.unit.app G) := by
  have := E.isIso_bigToSmallEtaleMorphism_unit (etaleSpace T E h X)
  have := isIso_fppfToBigEtaleMorphism_unit_app_of_isSheaf T E h X _ hG
  change IsIso (((E.bigToSmallEtaleMorphism (etaleSpace T E h X)).adj.comp
    (fppfToBigEtaleMorphism T E h X).adj).unit.app G)
  rw [Adjunction.comp_unit_app]
  infer_instance

end AlgebraicGeometry.BigFppfSpaceSite

end
