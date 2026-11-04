module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves

/-!
# The finite affine coverings of an affine object of a chosen big site are cofinal

Let `S` be a scheme and let `B` be a chosen big `τ`-site over `S`, with `τ` one of the five
topologies `Zar`, `étale`, `smooth`, `syntomic`, `fppf`. Every covering sieve of an affine
object of the site is refined by a finite covering of that object by affine objects of the
site whose underlying morphisms are `τ`-covering morphisms and are jointly surjective.

## Main results

* `Stacks.Adequate.BigSite.affineCovCofinal` — the cofinality statement.

## Implementation notes

The topology of a chosen big site is, by its field
`Stacks.Adequate.BigSite.chosen`, one of the five localized big-site topologies, and
cofinality of the standard `τ`-coverings in those is
`AlgebraicGeometry.overStandardCoverings_cofinal`. What is added here is the eliminator for
that field — five cases, each transporting the topology along the equality of the two cutoffs
— and the reindexing of the resulting covering into `Type 0`, which is the index universe the
collection `Stacks.Adequate.BigSite.affineCov` is stated at. A standard `τ`-covering is a
finite family of affines whose members are `τ`-covering morphisms by
`AlgebraicGeometry.IsStandardCovering.ofArrows_mem_precoverage` and are jointly surjective by
definition, which are exactly the remaining clauses of membership in `affineCov`.

## References

* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
* [Stacks Project, Tag 03FI](https://stacks.math.columbia.edu/tag/03FI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Adequate

universe u

/-- Over an affine object of a localized big site, every covering sieve is refined by a finite
covering by affine objects whose underlying morphisms are `τ`-covering morphisms and are
jointly surjective, indexed by a type in `Type 0`.

This is `AlgebraicGeometry.exists_isOverStandardCovering_sieve₀_le` with its conclusion
reindexed by `CategoryTheory.PreZeroHypercover.reindex` along a bijection of the finite index
type with a `Fin`, which changes neither the generated presieve nor the generated sieve. -/
private theorem exists_finite_affine_covering_le (τ : CoveringTopology)
    (𝔅 : AlgebraicGeometry.BigSite.{u} τ) (S : Scheme.{u}) (hS : S.size < cutoff τ 𝔅)
    {U : Over (base 𝔅 S hS)} (hU : IsAffine U.left.obj) {R : Sieve U}
    (hR : R ∈ overTopology τ 𝔅 S hS U) :
    ∃ E : PreZeroHypercover.{0} U, E.sieve₀ ∈ overTopology τ 𝔅 S hS U ∧ Finite E.I₀ ∧
      (∀ i, IsAffine (E.X i).left.obj) ∧
      (∀ i, coveringMorphismProperty τ
        ((schemeBelowInclusion (cutoff τ 𝔅)).map (E.f i).left)) ∧
      (∀ x : U.left.obj, ∃ i,
        x ∈ Set.range ((schemeBelowInclusion (cutoff τ 𝔅)).map (E.f i).left)) ∧
      E.sieve₀ ≤ R := by
  classical
  obtain ⟨E, hEstd, hER⟩ := exists_isOverStandardCovering_sieve₀_le τ 𝔅 S hS hU hR
  have hmem : E.sieve₀ ∈ overTopology τ 𝔅 S hS U :=
    IsOverStandardCovering.sieve₀_mem_overTopology τ 𝔅 S hS E hEstd
  obtain ⟨hUaff, hstd⟩ := hEstd
  have : IsAffine (overScheme τ 𝔅 S hS U) := hUaff
  have hfin : Finite E.I₀ := hstd.finite_index
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff
    (P := coveringMorphismProperty τ)).mp (hstd.ofArrows_mem_precoverage τ _ _)
  let eI : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  have hsieve : (E.reindex eI).sieve₀ = E.sieve₀ :=
    congrArg Sieve.generate (E.presieve₀_reindex eI)
  refine ⟨E.reindex eI, hsieve ▸ hmem, Finite.of_equiv _ eI.symm,
    fun i => hstd.affine_source (eI i), fun i => hprop (eI i), fun x => ?_, hsieve ▸ hER⟩
  obtain ⟨i, hi⟩ := hsurj x
  obtain ⟨j, rfl⟩ := eI.surjective i
  exact ⟨j, hi⟩

/-- **The finite affine `τ`-coverings are cofinal.** Every covering sieve of an affine object
of a chosen big `τ`-site over `S` is refined by a finite covering of that object by affine
objects of the site whose underlying morphisms are `τ`-covering morphisms and are jointly
surjective.

This is [Stacks, Tag 03XA], cofinality of the standard `τ`-coverings, read on the localized
big site whose topology the chosen big site carries. -/
public theorem BigSite.affineCovCofinal {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : B.AffineCovCofinal := by
  obtain ⟨cut, base_mem, J, isSheaf, chosen⟩ := B
  rcases chosen with ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ |
    ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ <;>
    subst hτ he <;> obtain rfl := eq_of_heq hJ <;> intro U hU R hR <;>
    (first
    | obtain ⟨E, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_finite_affine_covering_le .zariski C S hC hU hR
    | obtain ⟨E, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_finite_affine_covering_le .etale C S hC hU hR
    | obtain ⟨E, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_finite_affine_covering_le .fppf C S hC hU hR
    | obtain ⟨E, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_finite_affine_covering_le .smooth C S hC hU hR
    | obtain ⟨E, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        exists_finite_affine_covering_le .syntomic C S hC hU hR) <;>
    exact ⟨⟨E, h₁⟩, ⟨hU, h₂, h₃, h₄, h₅⟩, h₆⟩

end Stacks.Adequate

end
