module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The spaces-étale site of an algebraic space inside its big fppf site

For an algebraic space `Z` of a big fppf site `T` of algebraic spaces, the inclusion
`V ↦ V/Z` of the spaces-étale site `Z_{spaces,étale}` into the big fppf site `(Spaces/Z)_{fppf}`
is continuous and preserves the final object and fibre products. Hence it is a morphism of sites
`(Spaces/Z)_{fppf} → Z_{spaces,étale}`; this is the morphism `a_Z = π_Z ∘ ε_Z` of Stacks 0DGM on
underlying sites.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.spacesEtale_generator_sieve_covering`: the image of a
  jointly surjective étale family generates a big fppf covering sieve.
* `AlgebraicGeometry.BigFppfSpaceSite.spacesEtaleInclusion_isContinuous`: the inclusion
  `V ↦ V/Z` is continuous.
* `AlgebraicGeometry.BigFppfSpaceSite.spacesEtaleInclusion_isMorphismOfSites`: the inclusion
  `V ↦ V/Z` is a morphism of sites `(Spaces/Z)_{fppf} → Z_{spaces,étale}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (Z : T.Spaces)

/-- The image under the inclusion into algebraic spaces of a jointly point-surjective étale
family of the spaces-étale site of `Z` generates a covering sieve of the big fppf site of
algebraic spaces. -/
theorem spacesEtale_generator_sieve_covering
    (A : Space.SpacesEtale T.schemeSite S T.scheme_mem Z)
    (F : PreZeroHypercover.{u + 1} A)
    (hF : Space.SpacesEtale.IsCovering T.schemeSite S T.scheme_mem Z ⟨A, F⟩) :
    Sieve.generate
        ((F.map (Space.SpacesEtale.toSpaces T.schemeSite S T.scheme_mem Z)).presieve₀) ∈
      T.topology ((Space.SpacesEtale.toSpaces T.schemeSite S T.scheme_mem Z).obj A) := by
  let G := Space.SpacesEtale.toSpaces T.schemeSite S T.scheme_mem Z
  let E : Covering.{u + 1, u + 1, u + 2} T.Spaces :=
    ⟨G.obj A, { I₀ := ULift.{u + 2, u + 1} F.I₀
                X := fun i ↦ G.obj (F.X i.down)
                f := fun i ↦ G.map (F.f i.down) }⟩
  have hE : Space.IsEtaleCovering T.schemeSite S T.scheme_mem (fun i ↦ (E.2.X i).1)
      (fun i ↦ (E.2.f i).hom) := by
    refine ⟨(G.obj A).property, fun i ↦ (G.obj (F.X i.down)).property, fun i ↦ ?_, ?_⟩
    · exact Space.isEtale_of_isEtale_over T.schemeSite S T.scheme_mem
        (G.obj (F.X i.down)).property (G.obj A).property Z.property
        (G.map (F.f i.down)).hom ((F.X i.down).1.hom).hom A.1.hom.hom
        (F.X i.down).property A.property
        (congrArg (fun k ↦ k.hom) (Over.w (F.f i.down).hom))
    · ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨i, y, hy⟩ := hF x
      exact ⟨ULift.up i, y, by simpa [E, G] using hy⟩
  obtain ⟨⟨Y, E'fam⟩, hE', hTarget, hComb⟩ := T.covering_representative E
    (Space.isFppfCovering_of_isEtaleCovering T.schemeSite S T.scheme_mem hE)
  cases hTarget
  have hE'cover : Sieve.generate E'fam.presieve₀ ∈ T.topology (G.obj A) :=
    Precoverage.generate_mem_toGrothendieck (by rw [T.mem_precoverage_iff]; exact ⟨E'fam, rfl, hE'⟩)
  have hLift : PreZeroHypercover.CombinatoriallyEquivalent (F.map G) E.2 :=
    ⟨⟨fun i ↦ ULift.up i, fun _ ↦ rfl, fun _ ↦ rfl⟩, ⟨fun i ↦ i.down, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
  rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
    (PreZeroHypercover.combinatoriallyEquivalent_trans _ _ _ hLift hComb)]
  simpa [E, G, Space.SpacesEtale.toSpaces, Space.SpacesEtale.inclusion] using hE'cover

/-- **The inclusion `V ↦ V/Z` of the spaces-étale site of `Z` into its big fppf site is
continuous.** -/
instance spacesEtaleInclusion_isContinuous :
    (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem Z).IsContinuous
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem Z)
      (BigFppfSpaceOver.topology T Z) := by
  let J := Space.SpacesEtale.precoverage T.schemeSite S T.scheme_mem Z
  let K := (BigFppfSpaceOver.topology T Z).toPrecoverage
  let G := Space.SpacesEtale.toSpaces T.schemeSite S T.scheme_mem Z
  have hle : J ≤ K.comap (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem Z) := by
    intro A R hR
    rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff]
    rw [Space.SpacesEtale.mem_precoverage_iff] at hR
    obtain ⟨F, rfl, hF⟩ := hR
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    have hEq : Sieve.generate (Presieve.functorPushforward (Over.forget Z)
        ((F.map (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem Z)).presieve₀)) =
        Sieve.generate ((F.map G).presieve₀) := by
      rw [PreZeroHypercover.presieve₀_map, ← Sieve.arrows_generate_map_eq_functorPushforward,
        Sieve.generate_sieve, PreZeroHypercover.presieve₀_map]
      simp [G, Space.SpacesEtale.toSpaces, Space.SpacesEtale.inclusion]
    rw [← PreZeroHypercover.presieve₀_map, hEq]
    exact spacesEtale_generator_sieve_covering T Z A F hF
  have hcont := Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    (F := Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem Z) (J := J) (K := K) hle
  have hK : K.toGrothendieck ≤ BigFppfSpaceOver.topology T Z :=
    GrothendieckTopology.toGrothendieck_toPrecoverage_le _
  exact ⟨fun G ↦ hcont.op_comp_isSheaf_of_types ⟨G.1, Presheaf.IsSheaf.of_le hK G.2⟩⟩

/-- **The inclusion of the spaces-étale site of `Z` into its big fppf site is a morphism of
sites** `(Spaces/Z)_{fppf} → Z_{spaces,étale}`. -/
theorem spacesEtaleInclusion_isMorphismOfSites :
    (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem Z).IsMorphismOfSites
      (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem Z)
      (BigFppfSpaceOver.topology T Z) :=
  Functor.isMorphismOfSites_of_isTerminal _
    (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem Z) (BigFppfSpaceOver.topology T Z)
    (Space.SpacesEtale.final_isTerminal T.schemeSite S T.scheme_mem Z) Over.mkIdTerminal

end AlgebraicGeometry.BigFppfSpaceSite

end
