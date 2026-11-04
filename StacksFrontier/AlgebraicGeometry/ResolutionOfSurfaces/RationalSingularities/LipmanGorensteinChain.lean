module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LipmanGorensteinChainOfStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LipmanLocalStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormalizedDualizingGeneration

/-!
# Gorenstein after finitely many normalized blowups of closed points ([Stacks, Tag 0BBV])

Let `A` be a two-dimensional Noetherian local normal Nagata domain defining a rational
singularity and having a dualizing complex. Then there is a finite sequence of normalized
blowups `Y ⟶ Spec A` at closed points over the closed point of `Spec A` such that every local
ring of `Y` is Gorenstein.

## Main results

* `AlgebraicGeometry.isDualizingRingModule_map_stalk_normalizedBlowUp`: the local step, with
  nothing assumed: a canonical ideal `J ⊆ B` extends to a canonical ideal `J·𝒪_{Y,y}` at every
  point of the normalized blowup `Y` of the closed point of `Spec B`.
* `AlgebraicGeometry.exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk`:
  [Stacks, Tag 0BBV].

## The proof

This is the source's proof. Pick an ideal `I ≅ ω_A` and a sequence of normalized blowups of
closed points dominating the blowup of `I`
(`AlgebraicGeometry.exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk_of_step`).
Along it the extension of `I` stays a dualizing module of every local ring. This is the local
step, where the dualizing module of the blowup normalized relative to `ω_A`
(`AlgebraicGeometry.BlowUpDualizing.exists_dualizingNormalization_blowUp`, built from duality on
`ℙⁿ_A` with coefficients) receives a surjection from `f^*ω_A` by clause (3) of
[Stacks, Tag 0B64] (`AlgebraicGeometry.BlowUpDualizing.epi_normalizedPullbackMap`). At the end
`I·𝒪_{Y,y}` is principal, so the local rings are Gorenstein.

No `@[stacks]` attribute is attached: Tag 0BBV is not proved here.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **The local step of [Stacks, Tag 0BBV].** Let `B` be a two-dimensional Noetherian local
normal Nagata domain defining a rational singularity and `J ⊆ B` an ideal which is a dualizing
module of `B`. At every point `y` of the normalized blowup of the closed point of `Spec B`, the
extended ideal `J·𝒪_{Y,y}` is a dualizing module of `𝒪_{Y,y}`. -/
theorem isDualizingRingModule_map_stalk_normalizedBlowUp :
    ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNormalDomain B] (hN : IsNagataRing B),
      ringKrullDim B = 2 → DefinesRationalSingularity B →
      ∀ (J : Ideal B), (letI := hN.1; Stacks.Duality.IsDualizingRingModule B J) →
      ∀ (hW : ∀ U : (Spec (.of B)).Opens, IsCompact (U : Set (Spec (.of B))) →
          (irreducibleComponents U).Finite)
        (hc : IsClosed ({IsLocalRing.closedPoint B} : Set (Spec (.of B))))
        (x : Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW (IsLocalRing.closedPoint B) hc),
        ∃ _ : IsNoetherianRing ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
            (IsLocalRing.closedPoint B) hc).presheaf.stalk x),
          Stacks.Duality.IsDualizingRingModule
            ((Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
              (IsLocalRing.closedPoint B) hc).presheaf.stalk x)
            (J.map ((Scheme.ΓSpecIso (.of B)).inv ≫
              (Stacks.Blowup.normalizedBlowUp (Spec (.of B)) hW
                (IsLocalRing.closedPoint B) hc).appTop ≫
              (Stacks.Blowup.normalizedBlowUpScheme (Spec (.of B)) hW
                (IsLocalRing.closedPoint B) hc).presheaf.germ ⊤ x trivial).hom) :=
  isDualizingRingModule_map_stalk_normalizedBlowUp_of_epi
    (fun S hnot ωA hωA ωX N => BlowUpDualizing.epi_normalizedPullbackMap S hnot ωA hωA ωX N)

/-- **Stacks Project, Tag 0BBV.** Let `A` be a two-dimensional Noetherian local normal Nagata
domain defining a rational singularity and having a dualizing complex. There is a finite sequence
of normalized blowups `Y ⟶ Spec A` in closed points over the closed point of `Spec A` such that
every local ring of `Y` is Gorenstein. -/
theorem exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y) :=
  exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk_of_step
    isDualizingRingModule_map_stalk_normalizedBlowUp

end AlgebraicGeometry
