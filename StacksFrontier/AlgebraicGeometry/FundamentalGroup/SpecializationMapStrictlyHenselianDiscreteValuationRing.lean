module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

import StacksCore.Tactic.StacksAttribute

/-!
# Realizing a specialization map over a strictly henselian discrete valuation ring

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres over a Noetherian
scheme `S`, let `s'` and `s` be geometric points of `S` and let `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be
a specialization map. Then `sp` is isomorphic to the specialization map `sp_R` of a base change
`X_R ⟶ Spec R` for a strictly henselian discrete valuation ring `R` over `S`, the specialization
being the one from the generic point of `Spec R` to its closed point.

"Isomorphic" is not defined in the source; what its proof produces, and what is proved here, is a
commutative square whose two vertical maps are isomorphisms of topological groups:
`π₁(X_{s̄'}) ≅ π₁((X_R)_{η̄})` and `π₁(X_{s̄}) ≅ π₁((X_R)_{ō})` intertwining `sp` and `sp_R`.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_strictlyHenselianDVR` —
  **Tag 0C0N**.

## Implementation notes

The construction of the discrete valuation ring and of the two comparison isomorphisms is
`AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing`, which
takes the conclusion of Tag 0A48 for proper schemes over henselian local rings as an input
`h0A48`. That input is the theorem `AlgebraicGeometry.properHenselianFiniteEtaleEquivalence`
(Tag 0A48, proved from Grothendieck existence, Tag 088C), and it is supplied here. The ring `R`
produced has algebraically closed residue field, so it is strictly henselian.

## References

* [Stacks Project, Tag 0C0N](https://stacks.math.columbia.edu/tag/0C0N)
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0C0N.** Let `f : X ⟶ S` be a proper morphism with geometrically
connected fibres over a Noetherian scheme `S`, let `s'` and `s` be geometric points of `S` and let
`sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a specialization map. Then there are a strictly henselian
discrete valuation ring `R` (whose residue field is even algebraically closed) and a morphism
`r : Spec R ⟶ S` sending the generic point `η` of `Spec R` to the image of `s'` and its closed
point `o` to the image of `s`, such that `sp` is isomorphic to the specialization map
`sp_R : π₁((X_R)_{η̄}) → π₁((X_R)_{ō})` of the base change `X_R ⟶ Spec R`: there are isomorphisms
of topological groups `π₁(X_{s̄'}) ≅ π₁((X_R)_{η̄})` and `π₁(X_{s̄}) ≅ π₁((X_R)_{ō})` intertwining
`sp` and `sp_R`.

The proof follows the source: `exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing`
builds the discrete valuation ring dominating the strict henselization `A` of `𝒪_{S,s}` (Tags 00PH,
0ARL, 0AP1) and the two comparison isomorphisms (Tag 0A49), taking Tag 0A48 for proper schemes
over henselian local rings as an argument; that argument is the theorem
`properHenselianFiniteEtaleEquivalence`, supplied here. -/
@[stacks 0C0N "The full statement under the source's hypotheses, with no extra input: Tag 0A48 is \
supplied by `properHenselianFiniteEtaleEquivalence`. The source leaves \"isomorphic\" undefined; \
it is stated as a commutative square of isomorphisms of topological groups `eη`, `eo` with \
`eo ∘ sp = sp_R ∘ eη`. The ring `R` produced also has algebraically closed residue field."]
theorem exists_isSpecializationMap_isomorphic_over_strictlyHenselianDVR
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f] [IsNoetherian S]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : StrictlyHenselianLocalRing R) (_ : IsAlgClosed (ResidueField R))
      (r : Spec (.of R) ⟶ S) (η o : GeometricPoint (Spec (.of R)))
      (yη : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) η))
      (yo : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) o))
      (spR : EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
      η.hom default = genericPoint (Spec (.of R)) ∧
      o.hom default = closedPoint R ∧
      r (η.hom default) = s'.hom default ∧
      r (o.hom default) = s.hom default ∧
      IsSpecializationMap (pullback.snd f r) η o yη yo spR ∧
      ∃ (eη : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη)
        (eo : EtaleFundamentalGroup (fiberOverGeometricPoint f s) x ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
        ∀ γ, eo (sp γ) = spR (eη γ) := by
  obtain ⟨R, hR, hdom, hdvr, hhens, halg, r, η, o, yη, yo, spR, h⟩ :=
    exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing f s' s x' x sp hsp
      properHenselianFiniteEtaleEquivalence
  exact ⟨R, hR, hdom, hdvr, { toHenselianLocalRing := hhens, toIsSepClosed := inferInstance },
    halg, r, η, o, yη, yo, spR, h⟩

end AlgebraicGeometry

end
