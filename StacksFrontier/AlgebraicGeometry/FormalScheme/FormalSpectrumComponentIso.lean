module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-discretisation along the identification of `Spec (A/I)` with `Spf A`

For an ideal of definition `I` of a topological ring `A` the map `Spec (A/I) → Spf A` of
Stacks 0AHY is a homeomorphism: it is the corestriction to the open primes of the closed
immersion `Spec (A/I) → Spec A`, and a prime of `A` is open exactly when it contains `I`. This
file records that, and draws the consequence for pseudo-discrete topologies.

Pseudo-discretisation does not commute with pushforward in general: the topology on the sections
over `U` is taken over the quasi-compact opens contained in `U`, and pushing forward changes the
ambient space, hence the index set of that infimum. Along a homeomorphism the two index sets
correspond, so the two topologies on the common ring of sections do agree. The resulting
comparison, `AlgebraicGeometry.spfComponentPDIsoOn`, upgrades
`AlgebraicGeometry.mono_spfComponentPDOn_c_app` — which says only that
`AlgebraicGeometry.spfComponentPDOn` is a monomorphism on sections, as much as the separation
argument of Stacks 0AI1 needs — to the statement that `spfComponentPDOn` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.spfComponentPDIsoOn`: the identification
  `(Spec (A/I) → Spf A)_* 𝒪^{pd}_{Spec (A/I)} = (𝒪_I)^{pd}` of presheaves of topological rings
  on `Spf A`.
* `AlgebraicGeometry.spfComponentPDSpaceIsoOn`: the same, as an isomorphism of presheafed spaces
  of topological rings.

## Main results

* `AlgebraicGeometry.isIso_spfOfQuotientOn`: `Spec (A/I) → Spf A` is an isomorphism of
  topological spaces.
* `AlgebraicGeometry.isCompact_preimage_spfOfQuotientOn`: it pulls quasi-compact opens back to
  quasi-compact opens.
* `AlgebraicGeometry.isIso_spfComponentPDOn`: the comparison morphism
  `Spec (A/I) → (Spf A, 𝒪_I)` of pseudo-discretised presheafed spaces is an isomorphism.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- The identification of `Spec (A/I)` with the space of open primes is an isomorphism of
topological spaces: it is a continuous bijection and an open map. -/
instance isIso_spfOfQuotientOn (I : SpfIndex A P) : IsIso (spfOfQuotientOn A I) :=
  TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨injective_spfOfQuotientOn A I, surjective_spfOfQuotientOn A I⟩
    (isOpenEmbedding_spfOfQuotientOn A I).isOpenMap

/-- The identification of `Spec (A/I)` with the space of open primes is an isomorphism of
topological spaces: it is a continuous bijection and an open map.

The ideals-of-definition case of `isIso_spfOfQuotientOn`. -/
@[ega "I 10.1.1" "more general"]
instance isIso_spfOfQuotient (I : IdealsOfDefinition A) : IsIso (spfOfQuotient A I) :=
  isIso_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The preimage under `Spec (A/I) → Spf A` of a quasi-compact open is quasi-compact, the map
being a homeomorphism. -/
theorem isCompact_preimage_spfOfQuotientOn (I : SpfIndex A P) (V : Opens (spfSpace A))
    (hV : IsCompact (V : Set (spfSpace A))) :
    IsCompact (((Opens.map (spfOfQuotientOn A I)).obj V).carrier) :=
  (isInducing_spfOfQuotientOn A I).isCompact_preimage' hV (by
    rw [(surjective_spfOfQuotientOn A I).range_eq]; exact Set.subset_univ _)

/-- The preimage under `Spec (A/I) → Spf A` of a quasi-compact open is quasi-compact, the map
being a homeomorphism.

The ideals-of-definition case of `isCompact_preimage_spfOfQuotientOn`. -/
theorem isCompact_preimage_spfOfQuotient (I : IdealsOfDefinition A) (V : Opens (spfSpace A))
    (hV : IsCompact (V : Set (spfSpace A))) :
    IsCompact (((Opens.map (spfOfQuotient A I)).obj V).carrier) :=
  isCompact_preimage_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (I := I) (V := V)
    (hV := hV)

/-- Pushing forward along `Spec (A/I) → Spf A` and then pseudo-discretising gives a *finer*
topology on the sections than pseudo-discretising first: the second topology is taken over the
quasi-compact opens of `Spf A`, and each of them pulls back to a quasi-compact open of
`Spec (A/I)`. -/
theorem continuous_pseudoDiscreteTopology_spfComponentOn (I : SpfIndex A P)
    (V : Opens (spfSpace A)) :
    Continuous[pseudoDiscreteTopology (Spec (spfQuotientOn A I)).presheaf
        ((Opens.map (spfOfQuotientOn A I)).obj V),
      pseudoDiscreteTopology (spfComponentOn A I) V] (fun s => s) := by
  refine continuous_iInf_rng.2 fun W => continuous_induced_rng.2 ?_
  have hcompact : IsCompact (((Opens.map (spfOfQuotientOn A I)).obj W.1).carrier) :=
    isCompact_preimage_spfOfQuotientOn A I W.1 W.2.1
  have hle : (Opens.map (spfOfQuotientOn A I)).obj W.1
      ≤ (Opens.map (spfOfQuotientOn A I)).obj V := fun _ hx => W.2.2 hx
  exact continuous_pseudoDiscreteTopology_restrict (Spec (spfQuotientOn A I)).presheaf
    hcompact hle

/-- Pushing forward along `Spec (A/I) → Spf A` and then pseudo-discretising gives a *finer*
topology on the sections than pseudo-discretising first: the second topology is taken over the
quasi-compact opens of `Spf A`, and each of them pulls back to a quasi-compact open of
`Spec (A/I)`.

The ideals-of-definition case of `continuous_pseudoDiscreteTopology_spfComponentOn`. -/
theorem continuous_pseudoDiscreteTopology_spfComponent (I : IdealsOfDefinition A)
    (V : Opens (spfSpace A)) :
    Continuous[pseudoDiscreteTopology (Spec (spfQuotient A I)).presheaf
        ((Opens.map (spfOfQuotient A I)).obj V),
      pseudoDiscreteTopology (spfComponent A I) V] (fun s => s) :=
  continuous_pseudoDiscreteTopology_spfComponentOn (A := A) (P := IsIdealOfDefinition) (I := I)
    (V := V)

/-- **Pseudo-discretisation commutes with pushing forward along `Spec (A/I) → Spf A`.** The two
topologies on the common ring of sections are taken over the quasi-compact opens of `Spf A` and
of `Spec (A/I)` respectively, and the identification of the two spaces is a homeomorphism, so
they agree. -/
noncomputable def spfComponentPDIsoOn (I : SpfIndex A P) :
    spfOfQuotientOn A I _* pseudoDiscrete (Spec (spfQuotientOn A I)).presheaf
      ≅ pseudoDiscrete (spfComponentOn A I) :=
  NatIso.ofComponents
    (fun V =>
      { hom := ⟨RingHom.id _, continuous_pseudoDiscreteTopology_spfComponentOn A I V.unop⟩
        inv := ⟨RingHom.id _,
          continuous_pseudoDiscrete_embedding (spfComponentHomOn A I)
            (isOpenEmbedding_spfOfQuotientOn A I) V.unop⟩
        hom_inv_id := Subtype.ext rfl
        inv_hom_id := Subtype.ext rfl })
    (fun _ => Subtype.ext rfl)

/-- **Pseudo-discretisation commutes with pushing forward along `Spec (A/I) → Spf A`.** The two
topologies on the common ring of sections are taken over the quasi-compact opens of `Spf A` and
of `Spec (A/I)` respectively, and the identification of the two spaces is a homeomorphism, so
they agree.

The ideals-of-definition case of `spfComponentPDIsoOn`. -/
@[reducible] noncomputable def spfComponentPDIso (I : IdealsOfDefinition A) :
    spfOfQuotient A I _* pseudoDiscrete (Spec (spfQuotient A I)).presheaf
      ≅ pseudoDiscrete (spfComponent A I) :=
  spfComponentPDIsoOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` as presheafed spaces of *topological*
rings: the underlying map is a homeomorphism and the two pseudo-discrete topologies on the
common ring of sections agree, by `AlgebraicGeometry.spfComponentPDIsoOn`. -/
noncomputable def spfComponentPDSpaceIsoOn (I : SpfIndex A P) :
    pseudoDiscreteSpace (Spec (spfQuotientOn A I)).toPresheafedSpace
      ≅ pseudoDiscreteSpace (spfComponentSpaceOn A I) :=
  PresheafedSpace.isoOfComponents
    (@asIso TopCat.{u} _ _ _ (spfOfQuotientOn A I) (isIso_spfOfQuotientOn A I))
    (spfComponentPDIsoOn A I)

/-- The identification of `Spec (A/I)` with `(Spf A, 𝒪_I)` as presheafed spaces of *topological*
rings: the underlying map is a homeomorphism and the two pseudo-discrete topologies on the
common ring of sections agree, by `AlgebraicGeometry.spfComponentPDIso`.

The ideals-of-definition case of `spfComponentPDSpaceIsoOn`. -/
@[reducible] noncomputable def spfComponentPDSpaceIso (I : IdealsOfDefinition A) :
    pseudoDiscreteSpace (Spec (spfQuotient A I)).toPresheafedSpace
      ≅ pseudoDiscreteSpace (spfComponentSpace A I) :=
  spfComponentPDSpaceIsoOn (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The isomorphism of `AlgebraicGeometry.spfComponentPDSpaceIsoOn` is the comparison morphism
`AlgebraicGeometry.spfComponentPDOn`. -/
theorem spfComponentPDSpaceIsoOn_hom (I : SpfIndex A P) :
    (spfComponentPDSpaceIsoOn A I).hom = spfComponentPDOn A I :=
  PresheafedSpace.hext _ _ rfl
    (heq_of_eq (NatTrans.ext (funext fun _ => Subtype.ext rfl)))

/-- The isomorphism of `AlgebraicGeometry.spfComponentPDSpaceIso` is the comparison morphism
`AlgebraicGeometry.spfComponentPD`.

The ideals-of-definition case of `spfComponentPDSpaceIsoOn_hom`. -/
theorem spfComponentPDSpaceIso_hom (I : IdealsOfDefinition A) :
    (spfComponentPDSpaceIso A I).hom = spfComponentPD A I :=
  spfComponentPDSpaceIsoOn_hom (A := A) (P := IsIdealOfDefinition) (I := I)

/-- The comparison morphism `Spec (A/I) → (Spf A, 𝒪_I)` of pseudo-discretised presheafed spaces
is an *isomorphism*, not merely a monomorphism on sections as
`AlgebraicGeometry.mono_spfComponentPDOn_c_app` records. -/
theorem isIso_spfComponentPDOn (I : SpfIndex A P) : IsIso (spfComponentPDOn A I) :=
  spfComponentPDSpaceIsoOn_hom A I ▸ (spfComponentPDSpaceIsoOn A I).isIso_hom

/-- The comparison morphism `Spec (A/I) → (Spf A, 𝒪_I)` of pseudo-discretised presheafed spaces
is an *isomorphism*, not merely a monomorphism on sections as
`AlgebraicGeometry.mono_spfComponentPD_c_app` records.

The ideals-of-definition case of `isIso_spfComponentPDOn`. -/
theorem isIso_spfComponentPD (I : IdealsOfDefinition A) : IsIso (spfComponentPD A I) :=
  isIso_spfComponentPDOn (A := A) (P := IsIdealOfDefinition) (I := I)

end

end AlgebraicGeometry

end
