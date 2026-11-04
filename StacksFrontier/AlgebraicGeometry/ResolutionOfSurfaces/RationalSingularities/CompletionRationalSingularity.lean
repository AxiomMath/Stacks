module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleCompletionDescent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# Modifications of the spectrum of the completion of a local surface singularity

Let `(A, 𝔪, κ)` be a Noetherian local ring of dimension two whose completion `A^` along `𝔪` is a
normal domain. Every modification of `Spec(A^)` is then dominated by the base change along
`Spec(A^) ⟶ Spec(A)` of a single admissible blowup of `Spec(A)`, admissible relative to the
punctured spectrum of `A`.

## Main results

* `AlgebraicGeometry.cartierBoundaryReduction_puncturedSpectrum`: the punctured spectrum of a
  Noetherian local ring becomes the complement of an effective Cartier divisor after one
  admissible blowup, which is [Stacks, Tag 080Y] over this base.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_isPullback_dominating_adicCompletion`: a
  modification of `Spec(A^)` is dominated by the base change of an admissible blowup of
  `Spec(A)`.

## Implementation notes

Normality of `A^` is taken as `IsNormalDomain (AdicCompletion (maximalIdeal A) A)`, which for a
local ring is what "normal" means. [Stacks, Tag 081S], the flattening statement putting the strict
transform of a modification inside a blowup as an open subscheme, is not available in this
development and enters as the hypothesis `h081S`.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0B4M](https://stacks.math.columbia.edu/tag/0B4M)
* [Stacks Project, Tag 0AFK](https://stacks.math.columbia.edu/tag/0AFK)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 07NV](https://stacks.math.columbia.edu/tag/07NV)
-/


@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Tag 080Y over the spectrum of a Noetherian local ring -/

/-- **[Stacks, Tag 080Y] at the punctured spectrum of a Noetherian local ring.** On `Spec(A)`
the punctured spectrum becomes the complement of an effective Cartier divisor after a single
admissible blowup. -/
public theorem cartierBoundaryReduction_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] :
    CartierBoundaryReduction (Spec (.of A)) (Stacks.puncturedSpectrum A) := by
  have hnoeth : NoetherianSpace (Spec (CommRingCat.of A)) :=
    inferInstanceAs (NoetherianSpace (PrimeSpectrum A))
  exact cartierBoundaryReduction _ (NoetherianSpace.isCompact _)

/-! ### Descending a blowup that dominates a modification of the completion -/

/-- **The geometric half of [Stacks, Tag 0BG7], clause (1).** Let `A` be a Noetherian local ring
of dimension two whose completion `A^` is a normal domain, and let `q : Y ⟶ Spec(A^)` be a
modification. Then there are an admissible blowup `f : X ⟶ Spec(A)`, relative to the punctured
spectrum of `A`, and a cartesian square exhibiting a scheme `Y'` as the base change of `f` along
`Spec(A^) ⟶ Spec(A)`, together with a morphism `Y' ⟶ Y` over `Spec(A^)`. The hypothesis
`h081S` is [Stacks, Tag 081S] for `q`. -/
public theorem exists_isAdmissibleBlowup_isPullback_dominating_adicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)] (hdim : ringKrullDim A = 2)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A)))
    (hq : IsModification q)
    (h081S : StrictTransformOpenImmersion q
      (Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A))) :
    ∃ (X Y' : Scheme.{u}) (f : X ⟶ Spec (.of A)) (c : Y' ⟶ X)
        (b : Y' ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))) (g : Y' ⟶ Y),
      Stacks.Blowup.IsAdmissibleBlowup (Stacks.puncturedSpectrum A) f ∧
        IsPullback c b f
          (Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (maximalIdeal A) A)))) ∧
        g ≫ q = b := by
  have hdim' : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 2 :=
    (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm.trans hdim
  have hproper : IsProper q := hq.isProper
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian Y := AlgebraicGeometry.IsNoetherian.mk
  let : NoetherianSpace
      (q.fiber (closedPoint (AdicCompletion (maximalIdeal A) A))) :=
    (q.fiberHomeo _).isEmbedding.noetherianSpace
  let : Finite {Z : Set (q.fiber (closedPoint (AdicCompletion (maximalIdeal A) A))) //
      Z ∈ irreducibleComponents
        (q.fiber (closedPoint (AdicCompletion (maximalIdeal A) A)))} :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  obtain ⟨Y', b, hadm, g, hg⟩ :=
    VanishingSituation.exists_isAdmissibleBlowup_dominating
      { A := AdicCompletion (maximalIdeal A) A
        dimension_two := hdim'
        X := Y
        f := q
        modification := hq
        numberOfComponents :=
          Nat.card {Z : Set (q.fiber (closedPoint (AdicCompletion (maximalIdeal A) A))) //
            Z ∈ irreducibleComponents
              (q.fiber (closedPoint (AdicCompletion (maximalIdeal A) A)))}
        components := (Finite.equivFin _).symm }
      (cartierBoundaryReduction_puncturedSpectrum (AdicCompletion (maximalIdeal A) A)) h081S
  obtain ⟨X, f, hadmX, c, hsq⟩ :=
    Stacks.Blowup.exists_isAdmissibleBlowup_isPullback_completion A Y' b hadm
  exact ⟨X, Y', f, c, b, g, hadmX, hsq, hg⟩

end AlgebraicGeometry

end
