module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SingularBlowupChainMatch
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpDomination

/-!
# Making an ideal principal at the singular points by blowing up singular points

Let `(A, 𝔪)` be a two-dimensional local normal Nagata domain defining a rational singularity and
`J ⊆ A` a nonzero ideal. There is a finite sequence of blowups in singular closed points
`X = Xₙ ⟶ … ⟶ X₀ = Spec(A)`, every `Xᵢ` normal, such that `J 𝒪_{X, x}` is principal at every
singular point `x` of `X`. For `J` an ideal isomorphic to the dualizing module of `A` this is the
sequence of blowups of the proof of [Stacks, Tag 0BBV].

## Main results

* `AlgebraicGeometry.stalkAlgebraOfSpec_eq_baseRingToStalk`: the two spellings of the map from `A`
  to a local ring of a scheme over `Spec(A)` agree.
* `AlgebraicGeometry.exists_singularPointBlowupChain_principal`: the sequence of blowups of the
  proof of [Stacks, Tag 0BBV].

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-- The map from `A` to a local ring of a scheme over `Spec(A)` through the global sections is the
map through the local ring of `Spec(A)`. -/
theorem stalkAlgebraOfSpec_eq_baseRingToStalk (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : stalkAlgebraOfSpec A f x = baseRingToStalk f x := by
  have h1 : f.appTop ≫ X.presheaf.germ ⊤ x trivial =
      (Spec (.of A)).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x :=
    (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm
  rw [stalkAlgebraOfSpec, baseRingToStalk, h1, ← Category.assoc]
  rfl

/-- **The sequence of blowups in the proof of [Stacks, Tag 0BBV].** Let `(A, 𝔪)` be a local normal
Nagata domain of dimension two which defines a rational singularity, and `J ⊆ A` a nonzero ideal.
Then there is a finite sequence of blowups in singular closed points
`X = Xₙ ⟶ Xₙ₋₁ ⟶ … ⟶ X₀ = Spec(A)` with every `Xᵢ` normal such that `J 𝒪_{X, x}` is principal
at every singular point `x` of `X`. -/
theorem exists_singularPointBlowupChain_principal (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A] (hN : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hA : DefinesRationalSingularity A) (J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧
        ∀ y : Y, y ∈ singularLocus Y →
          ∃ t : Y.presheaf.stalk y, Ideal.map (stalkAlgebraOfSpec A f y) J = Ideal.span {t} := by
  have := hN
  obtain ⟨Y, q, -, hq, hJY⟩ := exists_isModification_map_eq_span_singleton A J hJ
  have : IsProper q := hq.isProper
  have hNagata : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A ‹_›
  have hdimS : topologicalKrullDim (Spec (.of A)) = 2 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim
  obtain ⟨Z, g, h, hchain, hhg⟩ :=
    exists_normalizedBlowUpChain_dominating hNagata hdimS q hq.isBirational
  obtain ⟨-, -, X, f, hchainX, hmatch⟩ :=
    exists_singularPointBlowupChain_of_normalizedBlowUpChain A hdim hA _ hchain
  refine ⟨X, f, hchainX, fun x hx =>
    exists_map_eq_span_singleton_of_singularLociMatch hmatch J (fun z => ?_) x hx⟩
  obtain ⟨d, hd⟩ := hJY (h z)
  refine ⟨(h.stalkMap z).hom d, ?_⟩
  rw [← hhg, stalkAlgebraOfSpec_comp, stalkAlgebraOfSpec_eq_baseRingToStalk, ← Ideal.map_map, hd,
    Ideal.map_span, Set.image_singleton]

end AlgebraicGeometry

end
