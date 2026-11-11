module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends

/-!
# The vanishing of `H¹(𝒪)` descends along a dominating normal modification

Let `f : X ⟶ Spec(A)` and `p : Y ⟶ Spec(A)` be modifications with `X` normal, and let
`g : Y ⟶ X` satisfy `g ≫ f = p`. Then `g` is proper and birational onto the normal integral `X`,
so `𝒪_X = g_*𝒪_Y` ([Stacks, Tag 0AY8]). The Leray edge map `H¹(X, 𝒪_X) ⟶ H¹(Y, 𝒪_Y)` is then
injective, which is the injective half of the first conclusion of [Stacks, Tag 0AXF]. So
`H¹(Y, 𝒪_Y) = 0` forces `H¹(X, 𝒪_X) = 0`.

This is the hypothesis `transfer` of
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing`, the source's argument for
[Stacks, Tag 0B4Q] over three of its inputs. It is proved here, and that argument is restated
without it. The complete statement of Tag 0B4Q is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

## Main results

* `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_dominates`: the descent.
* `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_dominate`: the
  argument for [Stacks, Tag 0B4Q] over its two remaining inputs.

## References

* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.ResolutionOfSurfaces

universe u

namespace AlgebraicGeometry

/-- **The vanishing of `H¹(𝒪)` descends along a dominating modification.** Let `A` be a
domain, `f : X ⟶ Spec(A)` a modification with `X` normal and `p : Y ⟶ Spec(A)` a modification
factoring as `g ≫ f`. Then `g` is proper and birational onto the normal `X`, so `𝒪_X = g_*𝒪_Y`
and the Leray edge map is injective. Hence `H¹(Y, 𝒪_Y) = 0` forces `H¹(X, 𝒪_X) = 0`. -/
theorem firstStructureSheafCohomologyVanishes_of_dominates (A : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (p : Y ⟶ Spec (.of A)) (g : Y ⟶ X) (hX : IsNormal X) (hf : IsModification f)
    (hp : IsModification p) (hgp : g ≫ f = p) (hY : FirstStructureSheafCohomologyVanishes Y) :
    FirstStructureSheafCohomologyVanishes X := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral Y := hp.source_isIntegral
  have : IsProper f := hf.isProper
  have : IsProper (g ≫ f) := by rw [hgp]; exact hp.isProper
  have : IsProper g := IsProper.of_comp g f
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hgbir : IsBirational g :=
    isBirational_of_comp_of_isBirational g f (by rw [hgp]; exact hp.isBirational)
      hf.isBirational (by
        simpa only [genericPoints_eq_singleton] using preimage_genericPoint f hf.isBirational)
  have : IsIso g.c := isIso_c_of_isBirational_of_isNormal g hgbir
  exact isZeroFirstStructureSheafCohomology_of_isIso_c g hY

/-- **The argument of [Stacks, Tag 0B4Q] over two of its inputs.** A Nagata regular local ring
`A` of dimension two defines a rational singularity once the two inputs below are given. The
complete statement, with nothing assumed, is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`.

This is `AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing` with its hypothesis
`transfer` discharged by `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_dominates`.
Two hypotheses remain. `dominate` is [Stacks, Tag 0AHI] together with the regularity and
normality of the members of the sequence ([Stacks, Tags 0AGR and 0567]). `blowUpStep` is the
survival of the vanishing across one blowup at a closed point ([Stacks, Tag 0AGS] and the exact
sequence of [Stacks, Tag 0AXF]). -/
theorem definesRationalSingularity_of_isRegularLocalRing_of_dominate (A : Type u) [CommRing A]
    [IsDomain A] [IsRegularLocalRing A] [IsNagataRing A] (hdim : ringKrullDim A = 2)
    (dominate : ∀ (X : Scheme.{u}), IsNormal X → ∀ f : X ⟶ Spec (.of A), IsModification f →
      ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A)) (g : Y ⟶ X),
        PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} Y p ∧
          IsNormal Y ∧ IsModification p ∧ g ≫ f = p)
    (blowUpStep : ∀ (W : Scheme.{u}) (h : W ⟶ Spec (.of A)),
      PointBlowupChain (Spec (.of A)) {IsLocalRing.closedPoint A} W h →
      ∀ (w : W) (hw : IsClosed ({w} : Set W)),
        FirstStructureSheafCohomologyVanishes W →
        FirstStructureSheafCohomologyVanishes
          (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) :
    DefinesRationalSingularity A :=
  definesRationalSingularity_of_isRegularLocalRing A hdim dominate
    (fun _ _ f p g hX _ hf hp hgp hY =>
      firstStructureSheafCohomologyVanishes_of_dominates A f p g hX hf hp hgp hY)
    blowUpStep

end AlgebraicGeometry

end
