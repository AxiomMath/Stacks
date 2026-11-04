module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.FormalScheme.PseudoDiscrete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pseudo-discretisation of a sheaf of rings is a sheaf

On a topological space with a basis of quasi-compact opens, the pseudo-discrete presheaf of
topological rings attached to a sheaf of rings is itself a sheaf.

## Main results

* `AlgebraicGeometry.continuous_pseudoDiscrete_gluing_of_isSheaf`: the ring homomorphism gluing a
  compatible family of sections over an open covering is continuous for the pseudo-discrete
  topologies.
* `AlgebraicGeometry.isSheaf_pseudoDiscrete_of_isSheaf`: the pseudo-discretisation of a sheaf of
  rings is a sheaf of topological rings.

## References

* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}}

/-- A ring homomorphism into the sections of a presheaf is continuous for the pseudo-discrete
topology as soon as it factors through a discrete ring by a continuous map. -/
theorem continuous_pseudoDiscreteTopology_of_factorsThrough {R S : Type u} [CommRing R]
    [TopologicalSpace R] [CommRing S] [TopologicalSpace S] [DiscreteTopology S]
    (F : X.Presheaf CommRingCat.{u}) (U : Opens X) (q : R →+* S) (hq : Continuous q)
    (g : R →+* F.obj (op U)) (g' : S →+* F.obj (op U)) (hg : ∀ a, g a = g' (q a)) :
    @Continuous R _ _ (pseudoDiscreteTopology F U) g := by
  refine continuous_iInf_rng.2 fun V => continuous_induced_rng.2 ?_
  have hfun : ⇑(F.map (homOfLE V.2.2).op).hom ∘ ⇑g
      = (⇑(F.map (homOfLE V.2.2).op).hom ∘ ⇑g') ∘ ⇑q :=
    funext fun a => congrArg _ (hg a)
  rw [hfun]
  let _ : TopologicalSpace (F.obj (op V.1)) := ⊥
  exact (@continuous_of_discreteTopology S _ _ (F.obj (op V.1)) ⊥ _).comp hq

variable [PrespectralSpace X]

/-- The ring homomorphism gluing a compatible family of sections of a sheaf of rings over an open
covering is continuous for the pseudo-discrete topologies. -/
theorem continuous_pseudoDiscrete_gluing_of_isSheaf (F : X.Presheaf CommRingCat.{u})
    (hF : F.IsSheaf) {ι : Type u} (cover : ι → Opens X)
    (cone : Cone ((ObjectProperty.ι (fun V : Opens X => ∃ i, V ≤ cover i)).op ⋙
      pseudoDiscrete F))
    (glue : cone.pt.α →+* F.obj (op (iSup cover)))
    (fac : ∀ V : TopCat.Presheaf.SheafCondition.OpensLeCover cover,
      (F.map (homOfLE (V.property.choose_spec.trans
        (le_iSup cover V.property.choose))).op).hom.comp glue = (cone.π.app (op V)).1) :
    Continuous[cone.pt.isTopologicalSpace, pseudoDiscreteTopology F (iSup cover)] glue := by
  let _ : TopologicalSpace cone.pt.α := cone.pt.isTopologicalSpace
  refine continuous_iInf_rng.2 fun compactOpen => continuous_induced_rng.2 ?_
  let _ : ∀ V, TopologicalSpace (F.obj V) := fun _ => ⊥
  let patches := {V : TopCat.Presheaf.SheafCondition.OpensLeCover cover //
    IsCompact (V.obj : Set X) ∧ V.obj ≤ compactOpen.1}
  have hcover : (compactOpen.1 : Set X) ⊆ ⋃ patch : patches, (patch.1.obj : Set X) := by
    intro point hpoint
    obtain ⟨index, hindex⟩ := Opens.mem_iSup.1 (compactOpen.2.2 hpoint)
    obtain ⟨small, ⟨hopen, hcompact⟩, hpointSmall, hsmall⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
        (show point ∈ (compactOpen.1 ⊓ cover index : Opens X) from ⟨hpoint, hindex⟩)
        (compactOpen.1 ⊓ cover index).isOpen
    exact Set.mem_iUnion.2 ⟨⟨⟨⟨small, hopen⟩, index, fun _ hx => (hsmall hx).2⟩,
      hcompact, fun _ hx => (hsmall hx).1⟩, hpointSmall⟩
  obtain ⟨finitePatches, hfiniteCover⟩ := compactOpen.2.1.elim_finite_subcover
    (fun patch : patches => (patch.1.obj : Set X)) (fun patch => patch.1.obj.isOpen) hcover
  let restriction := (F.map (homOfLE compactOpen.2.2).op).hom.comp glue
  change Continuous restriction
  refine continuous_iff_continuousAt.2 fun sectionValue => ?_
  refine Filter.EventuallyEq.continuousAt (y := restriction sectionValue) ?_
  have heventually : ∀ patch ∈ finitePatches,
      ∀ᶠ value in nhds sectionValue,
        (cone.π.app (op patch.1)).1 value = (cone.π.app (op patch.1)).1 sectionValue := by
    intro patch hpatch
    have hcontinuous : Continuous[cone.pt.isTopologicalSpace,
        pseudoDiscreteTopology F patch.1.obj] (cone.π.app (op patch.1)).1 :=
      (cone.π.app (op patch.1)).2
    rw [pseudoDiscreteTopology_eq_bot F patch.2.1] at hcontinuous
    exact (hcontinuous.isOpen_preimage {_}
      (@isOpen_discrete _ ⊥ (discreteTopology_bot _) _)).mem_nhds (Set.mem_singleton _)
  filter_upwards [(finitePatches.eventually_all).2 heventually] with value hvalue
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F, hF⟩ : X.Sheaf CommRingCat)
    (fun patch : ↥finitePatches => patch.1.1.obj) compactOpen.1
    (fun patch => homOfLE patch.1.2.2) ?_ (restriction value) (restriction sectionValue) ?_
  · intro point hpoint
    obtain ⟨patch, hpointPatch⟩ := Set.mem_iUnion.1 (hfiniteCover hpoint)
    obtain ⟨hmem, hpointPatch⟩ := Set.mem_iUnion.1 hpointPatch
    exact Opens.mem_iSup.2 ⟨⟨patch, hmem⟩, hpointPatch⟩
  · intro patch
    have hcomp : (F.map (homOfLE patch.1.2.2).op).hom.comp restriction =
        (cone.π.app (op patch.1.1)).1 := by
      dsimp only [restriction]
      rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← F.map_comp]
      exact fac patch.1.1
    exact (RingHom.congr_fun hcomp value).trans
      ((hvalue patch.1 patch.2).trans (RingHom.congr_fun hcomp sectionValue).symm)

/-- On a space with a basis of quasi-compact opens, the pseudo-discrete presheaf of topological
rings attached to a sheaf of rings is a sheaf of topological rings. The sections over the base of
an open covering form a *subspace* of the product of the sections over the pieces. -/
@[ega "0 3.8.1" "partial"]
theorem isSheaf_pseudoDiscrete_of_isSheaf (F : X.Presheaf CommRingCat.{u}) (hF : F.IsSheaf) :
    (pseudoDiscrete F).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover _).2 fun ι cover => ?_
  let ringLimit := (hF.isSheafOpensLeCover cover).some
  let forget := forget₂ TopCommRingCat.{u} CommRingCat.{u}
  refine ⟨IsLimit.mk (fun cone => ⟨(ringLimit.lift (forget.mapCone cone)).hom, ?_⟩)
    (fun cone V => Subtype.ext (congrArg CommRingCat.Hom.hom
      (ringLimit.fac (forget.mapCone cone) V))) ?_⟩
  · exact continuous_pseudoDiscrete_gluing_of_isSheaf F hF cover cone _
      fun V => congrArg CommRingCat.Hom.hom (ringLimit.fac (forget.mapCone cone) (op V))
  · exact fun cone morphism hfac => Subtype.ext (congrArg CommRingCat.Hom.hom
      (ringLimit.uniq (forget.mapCone cone) (forget.map morphism)
        fun V => congrArg forget.map (hfac V)))

end AlgebraicGeometry

end
