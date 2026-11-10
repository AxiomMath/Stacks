module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

/-!
# The precoverage of a big fppf site, and the families inside a covering sieve

The covering families of a big fppf site were specified by hand, as the *bounded* fppf covering
families of Stacks 000X. This file identifies the precoverage they present with the fppf
precoverage of all schemes comapped along the site's inclusion, which is what lets closure under
isomorphisms, base change and composition be inherited from the corresponding properties of
`AlgebraicGeometry.Scheme.fppfPrecoverage` instead of being reproved. The cardinality bound is
invisible to the comparison: by `AlgebraicGeometry.BigFppfSite.fppf_has_representative` every
fppf covering family of the site is combinatorially equivalent to a bounded one, and
combinatorially equivalent families present the same presieve.

The point of doing this is the last two results. A hypothesis of local essential surjectivity —
as in Stacks 045D — produces a *covering sieve* of an object of the big fppf site of `S`, while a
locality hypothesis on a property of morphisms, `CategoryTheory.MorphismProperty.IsLocalAtTarget`
for `AlgebraicGeometry.Space.Topology.fppf.precoverage`, consumes a covering *family*. With the
four stability properties in hand, Mathlib's
`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition` extracts from a
covering sieve a covering family contained in it, and
`AlgebraicGeometry.exists_family_of_mem_topology` records the result in the form
`AlgebraicGeometry.Space.isFppfCovering_yoneda_map` consumes: a family of morphisms of the site
which is flat, locally of finite presentation and jointly surjective, every member of which is an
arrow of the given sieve.

## Main results

* `AlgebraicGeometry.bigFppfPrecoverage_eq_comap`: the site's precoverage is the fppf precoverage
  of schemes, comapped along the inclusion.
* `AlgebraicGeometry.exists_covering_le_of_mem_topology`: a covering sieve of the big fppf site
  contains a chosen covering family.
* `AlgebraicGeometry.exists_family_of_mem_topology`: the same for the big fppf site of `S`,
  with the family's flatness, local finite presentation and joint surjectivity read off.
* The instances record that the site's precoverage has isomorphisms and is stable under base
  change and composition, and has pullbacks.

## Implementation notes

The three identifications are the fppf analogues of
`AlgebraicGeometry.bigEtalePrecoverage_eq_comap` and its companions, and the proofs are the same.
`AlgebraicGeometry.Scheme.fppfPrecoverage` is already known to Mathlib to be stable under base
change and under composition; only `CategoryTheory.Precoverage.HasIsos` has to be supplied, and
it is the observation that an isomorphism of schemes is flat, locally of finite presentation and
surjective.

`AlgebraicGeometry.exists_family_of_mem_topology` is stated with the family's target spelled `U`
and its members `Over.homMk (m i) : Over.mk (m i ≫ U.hom) ⟶ U`, which is the shape in which a
member of the family is a morphism *of the site over `S`* and at the same time the comparison
morphism of `CategoryTheory.OverShriek.isPullback_relocalizeRestrictMap`. Both the index type of
the family and the sieve live in `Type (u + 1)`, the universe of the site's underlying category.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes is a one-member fppf covering family: it is flat, locally of finite
presentation and surjective. -/
instance fppfPrecoverage_hasIsos : Scheme.fppfPrecoverage.{u}.HasIsos := ⟨by
  intro X Y f hf
  have : IsIso f := hf
  exact f.singleton_mem_fppfPrecoverage⟩

/-- **The precoverage of a big fppf site is the fppf precoverage of schemes comapped along the
site's inclusion.** The cardinality bound on the chosen families is invisible here: a presieve
which is fppf after inclusion is presented by *some* family, and that family is combinatorially
equivalent to a bounded one presenting the same presieve. -/
theorem bigFppfPrecoverage_eq_comap (B : BigFppfSite.{u}) :
    B.precoverage = Scheme.fppfPrecoverage.comap B.inclusion := by
  ext X R
  rw [Precoverage.mem_comap_iff]
  constructor
  · rintro ⟨E, rfl, hE⟩
    exact Precoverage.mem_comap_iff.1 hE.1
  · intro hR
    let E : PreZeroHypercover.{u + 1} X := ⟨R.uncurry, fun i => i.1.1, fun i => i.1.2⟩
    have hE : E.presieve₀ = R := by
      funext Y g
      refine propext ⟨?_, fun hg => Presieve.ofArrows.mk (⟨⟨Y, g⟩, hg⟩ : R.uncurry)⟩
      rintro ⟨i⟩
      exact i.2
    have hEt : IsFppfCovering ⟨X, E⟩ := by
      change E.presieve₀ ∈ (Scheme.fppfPrecoverage.comap B.inclusion).coverings X
      rwa [Precoverage.mem_comap_iff, hE]
    obtain ⟨V, hV, hXV, hcomb⟩ := B.fppf_has_representative ⟨X, E⟩ hEt
    cases hXV
    exact ⟨V.2, hE.symm.trans
      (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb), hV⟩

/-- The precoverage of a big fppf site has isomorphisms. -/
instance bigFppfPrecoverage_hasIsos (B : BigFppfSite.{u}) : B.precoverage.HasIsos := by
  rw [bigFppfPrecoverage_eq_comap B]
  infer_instance

/-- The precoverage of a big fppf site is stable under base change. -/
instance bigFppfPrecoverage_isStableUnderBaseChange (B : BigFppfSite.{u}) :
    B.precoverage.IsStableUnderBaseChange := by
  rw [bigFppfPrecoverage_eq_comap B]
  infer_instance

/-- The precoverage of a big fppf site is stable under composition. -/
instance bigFppfPrecoverage_isStableUnderComposition (B : BigFppfSite.{u}) :
    B.precoverage.IsStableUnderComposition := by
  rw [bigFppfPrecoverage_eq_comap B]
  infer_instance

/-- The members of a covering family of a big fppf site admit fibre products with any morphism to
the family's target. -/
instance bigFppfPrecoverage_hasPullbacks (B : BigFppfSite.{u}) :
    B.precoverage.HasPullbacks := by
  rw [bigFppfPrecoverage_eq_comap B]
  infer_instance

/-- **A covering sieve of a big fppf site contains a chosen covering family.** The topology is
generated by the chosen families, and those are stable under isomorphisms, base change and
composition, so the saturation adds no new sieves beyond refinements. -/
theorem exists_covering_le_of_mem_topology (B : BigFppfSite.{u}) {X : B.Schemes} {R : Sieve X}
    (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover.{u + 1} X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R.arrows := by
  rw [BigFppfSite.topology,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
  obtain ⟨R', ⟨E, rfl, hE⟩, hle⟩ := hR
  exact ⟨E, hE, hle⟩

/-- **A covering sieve of the big fppf site of `S` contains a flat, locally of finite presentation
and jointly surjective family.** This is the form in which a sieve-valued local-surjectivity
hypothesis feeds `AlgebraicGeometry.Space.isFppfCovering_yoneda_map`. -/
theorem exists_family_of_mem_topology (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left),
      (∀ i, R.arrows (Over.homMk (m i) : Over.mk (m i ≫ U.hom) ⟶ U)) ∧
      (∀ i, Flat (B.inclusion.map (m i))) ∧
      (∀ i, LocallyOfFinitePresentation (B.inclusion.map (m i))) ∧
      (∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (m i))) := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hle⟩ := exists_covering_le_of_mem_topology B hR
  have hmem : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact Precoverage.mem_comap_iff.1 hE.1
  rw [Scheme.fppfPrecoverage, Scheme.presieve₀_mem_precoverage_iff] at hmem
  refine ⟨E.I₀, E.X, E.f, fun i => ?_, fun i => (hmem.2 i).1, fun i => (hmem.2 i).2, hmem.1⟩
  have h2 : (Sieve.overEquiv U R).arrows (E.f i) := hle _ _ (Presieve.ofArrows.mk i)
  rwa [Sieve.overEquiv_iff] at h2

end AlgebraicGeometry

end
