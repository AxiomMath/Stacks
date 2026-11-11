module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.FirstCohomologyModificationTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.StructureSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletedLocalRings
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormalityExtra

/-!
# The completion of a rational surface singularity is a rational singularity

Let `(A, 𝔪, κ)` be a Nagata local normal domain of dimension two which defines a rational
singularity and whose completion `A^` is normal. Then `A^` defines a rational singularity. This
is clause (1) of [Stacks, Tag 0BG7]. Clause (2), the normality of the completed local rings at
the closed points of the blowup of `Spec(A)` in `𝔪`, is
`AlgebraicGeometry.isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal`, which takes the
normality of the blowup of `Spec(A^)` in the maximal ideal of `A^` as a hypothesis. Clause (1)
discharges that hypothesis, so clause (2) is restated here with the source's hypotheses on `A`.
Both clauses with no further hypotheses are
`AlgebraicGeometry.definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `definesRationalSingularity_adicCompletion_maximalIdeal_of_dominate`: clause (1).
* `isNormalDomain_adicCompletion_stalk_blowUp_of_definesRationalSingularity`: clause (2), with
  the source's hypotheses on `A` in place of the normality of the blowup upstairs.

## Implementation notes

The source's proof of clause (1) takes a normal modification `g : Y ⟶ Spec(A^)` and runs three
steps. The first is the hypothesis `dominate`, phrased as its conclusion.

The first step: `g` is an isomorphism over the punctured spectrum `U^` of `A^`
([Stacks, Tag 0BFP]); a `U^`-admissible blowup of `Spec(A^)` dominating `Y` exists
([Stacks, Tag 0B4M]); it descends to a `U`-admissible blowup `X ⟶ Spec(A)` whose base change to
`A^` dominates `Y` ([Stacks, Tag 0AFK]); and `X` may be replaced by its normalization, after
which `X ⟶ Spec(A)` is a normal modification, because `A` is Nagata.

The second step is flat base change for the first cohomology of the structure sheaf along the
flat map `A ⟶ A^`, `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_isPullback`. Its
hypotheses are met because `A ⟶ A^` is flat and a modification of `Spec(A)` is proper, hence
separated and quasi-compact. This is the use the source makes of [Stacks, Tag 02KH].

The third step is the descent of the vanishing from `Z` to `Y` along the dominating modification
`q : Z ⟶ Y`, `AlgebraicGeometry.firstStructureSheafCohomologyVanishes_of_comp_eq`. The source
gets it from the first conclusion of [Stacks, Tag 0AXF], the short exact sequence
`0 → H¹(Y, 𝒪_Y) → H¹(Z, 𝒪_Z) → H⁰(Y, R¹q_*𝒪_Z) → 0`, and uses only the injectivity of its first
map, which follows from `q_*𝒪_Z = 𝒪_Y` ([Stacks, Tag 0AY8]) and the injectivity of the first
Leray edge map ([Stacks, Tag 01F2]).

That `A` is Nagata is used twice: for the normalization step inside `dominate`, and for the
Noetherian hypothesis that the flatness of `A ⟶ A^` needs. That `A` has dimension two is what
Tag 0BFP consumes inside `dominate`, so it is retained in the statement although the proof does
not use it.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0B4M](https://stacks.math.columbia.edu/tag/0B4M)
* [Stacks Project, Tag 0AFK](https://stacks.math.columbia.edu/tag/0AFK)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Tag 0BG7, clause (1) -/

/-- The completion `A^` of a Nagata local normal domain `A` of dimension two which defines a
rational singularity, and whose completion is a normal domain, again defines a rational
singularity.

The hypothesis `dominate` says that for every normal modification `g : Y ⟶ Spec(A^)` there is a
normal modification `f : X ⟶ Spec(A)` whose base change `p : Z ⟶ Spec(A^)` along
`Spec(A^) ⟶ Spec(A)` factors through `g`; it is the conclusion of [Stacks, Tag 0BFP],
[Stacks, Tag 0B4M] and [Stacks, Tag 0AFK] together with the normalization step. Given it,
`H¹(X, 𝒪_X) = 0` by the hypothesis on `A`, flat base change carries that vanishing to `Z`, and
the descent along the dominating modification brings it down to `Y`. -/
public theorem definesRationalSingularity_adicCompletion_maximalIdeal_of_dominate
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hnagata : IsNagataRing A) (_hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (dominate : ∀ (Y : Scheme.{u}), IsNormal Y →
      ∀ g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A)), IsModification g →
        ∃ (X Z : Scheme.{u}) (f : X ⟶ Spec (.of A))
          (p : Z ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))) (r : Z ⟶ X) (q : Z ⟶ Y),
          IsNormal X ∧ IsModification f ∧ IsModification p ∧
            IsPullback r p f (specMapAdicCompletion A) ∧ q ≫ g = p) :
    DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A) := by
  let : IsNoetherianRing A := hnagata.isNoetherianRing
  let : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  let : Flat (specMapAdicCompletion A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  intro Y hY g hg
  obtain ⟨X, Z, f, p, r, q, hXnormal, hf, hp, hsq, hqg⟩ := dominate Y hY g hg
  have := hXnormal
  let : IsProper f := hf.2.1
  exact firstStructureSheafCohomologyVanishes_of_comp_eq g p q hY hg hp hqg
    (firstStructureSheafCohomologyVanishes_of_isPullback hsq (hrat X f hf))

/-! ### Tag 0BG7, clause (2), with the source's hypotheses -/

/-- For a Nagata local normal domain `A` of dimension two defining a rational singularity whose
completion is a normal domain, the completion of the local ring of the blowup of `Spec(A)` in the
maximal ideal is a normal domain at every closed point, given the hypothesis `dominate` of
`AlgebraicGeometry.definesRationalSingularity_adicCompletion_maximalIdeal_of_dominate`.

The normality of the blowup of `Spec(A^)` in the maximal ideal of `A^` that
`AlgebraicGeometry.isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal` takes is
[Stacks, Tag 0B4Z] at `A^`, whose four inputs are that `A^` is a normal domain (the hypothesis on
the completion), Nagata (a complete Noetherian local ring is), of dimension two (completion at the
maximal ideal preserves Krull dimension), and defines a rational singularity, which is
clause (1). -/
public theorem isNormalDomain_adicCompletion_stalk_blowUp_of_definesRationalSingularity
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hnagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (dominate : ∀ (Y : Scheme.{u}), IsNormal Y →
      ∀ g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A)), IsModification g →
        ∃ (X Z : Scheme.{u}) (f : X ⟶ Spec (.of A))
          (p : Z ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))) (r : Z ⟶ X) (q : Z ⟶ Y),
          IsNormal X ∧ IsModification f ∧ IsModification p ∧
            IsPullback r p f (specMapAdicCompletion A) ∧ q ≫ g = p)
    (x : blowUp (maximalIdealSheaf A))
    (hx : IsClosed ({x} : Set (blowUp (maximalIdealSheaf A)))) :
    IsNormalDomain (AdicCompletion
      (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk x))
      ((blowUp (maximalIdealSheaf A)).presheaf.stalk x)) := by
  let : IsNoetherianRing A := hnagata.isNoetherianRing
  have hratc : DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A) :=
    definesRationalSingularity_adicCompletion_maximalIdeal_of_dominate A hnagata hdim hrat dominate
  have hnormal : IsNormal (blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) :=
    isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow
      (AdicCompletion (maximalIdeal A) A) fun n =>
        isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity
          (AdicCompletion (maximalIdeal A) A) IsNagataRing.of_isPrecomplete_maximalIdeal
          ((_root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm.trans hdim) hratc n
  exact isNormalDomain_adicCompletion_stalk_blowUp_maximalIdeal A hnormal x hx

end AlgebraicGeometry

end
