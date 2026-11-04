module

public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Stacks Tag 09MS: the converse, reduced to two named inputs

Stacks Tag 09MS asserts that for a surjective closed immersion `i : Z ⟶ X` of Noetherian schemes
and an invertible `𝒪_X`-module `L`, the module `i^* L` is ample on `Z` if and only if `L` is ample
on `X`. The implication `L` ample `⟹` `i^* L` ample is
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`. **This file
proves the converse from two hypotheses and nothing else**, and the two hypotheses are exactly two
steps of the source argument.

## Main definitions

* `Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion`: **Stacks Tag 01YQ for a closed
  immersion.** A locally Noetherian scheme receiving a surjective closed immersion from an affine
  scheme is affine.
* `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`: **the cohomological step.** Every global
  section of a positive tensor power of `i^* L` with affine nonvanishing locus is, up to replacing
  it by a power, the restriction of a global section of a positive tensor power of `L` — recorded
  in the only form the proof uses, namely that some `X_{t'}` pulls back to `Z_t`.

## Main results

* `Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley`:
  `Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion` is implied by Stacks Tag 01YQ as
  the source states it, for a finite surjective morphism with Noetherian target. So the first
  hypothesis is not a new assertion, it is Chevalley's criterion.
* `Stacks.AmpleClosedImmersion.isAmple_of_isAmple_modulePullback`: **the converse half of Stacks
  Tag 09MS**, from the two hypotheses.
* `Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff`: **Stacks Tag 09MS**, the biconditional,
  from the two hypotheses; its `mpr` uses neither.

## The route, and what each hypothesis replaces

The source picks `x ∈ X`, takes its unique preimage `z ∈ Z`, and uses ampleness of `i^* L` to
find `n ≥ 1` and a section `t` of `(i^* L)^{⊗ n}` with `Z_t` affine and `z ∈ Z_t`. It then lifts a
power of `t` to a global section `t'` of `L^{⊗ m}` — this is where the whole cohomological
apparatus of the source goes: the ideal `𝓘` of `Z` is nilpotent by Stacks Tag 01Y9, the filtration
by its powers reduces to `𝓘² = 0`, the twisted exact sequences give an obstruction class in
`H¹(Z, 𝓘 ⊗ (i^* L)^{⊗ n})`, the boundary map of the direct sum over all degrees is a derivation by
Cohomology, Lemma 20.25.5 (Stacks Tag 0B8S), and Cohomology of Schemes, Lemma 30.17.4 (Stacks Tag
01XR) kills the class after multiplying by a power of `t`. The *conclusion* of all of that is
precisely `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`: `X_{t'}` pulls back to `Z_t`,
because `t'` restricts to a power of `t` and a power of a section of an invertible module has the
same nonvanishing locus.

Everything after the lift is this file, and it is elementary: `i` restricted over the open
`X_{t'}` is again a surjective closed immersion, its source is `Z_t`, which is affine, and
`X_{t'}` is an open subscheme of a locally Noetherian scheme, hence locally Noetherian. Chevalley
then makes `X_{t'}` affine, and `x ∈ X_{t'}` because `i z = x` and `z ∈ Z_t = i^{-1}(X_{t'})`.
Quasi-compactness of `X` is the image of the quasi-compact `Z` under a surjection.

The restriction `i ∣_ U` is a surjective closed immersion by
`AlgebraicGeometry.IsZariskiLocalAtTarget.restrict` at the Mathlib instances
`AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget` and
`AlgebraicGeometry.surjective_isZariskiLocalAtTarget`.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleClosedImmersion

/-! ### The first input: Chevalley for a closed immersion -/

/-- **Stacks Tag 01YQ for a closed immersion.** If `j : A ⟶ B` is a surjective closed immersion,
`B` is locally Noetherian and `A` is affine, then `B` is affine.

Quasi-compactness of `B` is not assumed: it follows from quasi-compactness of the affine `A` and
surjectivity of `j`, so this is the full strength of the source's hypothesis "`B` Noetherian".
`Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley` derives this from
Stacks Tag 01YQ in the source's own shape. -/
def AffineOfSurjectiveClosedImmersion : Prop :=
  ∀ (A B : Scheme.{u}) (j : A ⟶ B), IsClosedImmersion j → Surjective j →
    IsLocallyNoetherian B → IsAffine A → IsAffine B

/-- **Quasi-compactness is inherited by the target of a surjection.** -/
theorem compactSpace_of_surjective {A B : Scheme.{u}} (j : A ⟶ B) (hj : Surjective j)
    (hA : CompactSpace A) : CompactSpace B := by
  rw [← isCompact_univ_iff, ← j.surjective.range_eq]
  exact isCompact_range j.continuous

/-- **The first input is Stacks Tag 01YQ**, no more. Chevalley's criterion as the source states it
— a Noetherian scheme receiving a finite surjective morphism from an affine scheme is affine —
implies `Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion`: a closed immersion is
finite, and the missing `CompactSpace` is supplied by
`Stacks.AmpleClosedImmersion.compactSpace_of_surjective`. -/
theorem affineOfSurjectiveClosedImmersion_of_chevalley
    (h : ∀ (A B : Scheme.{u}) (j : A ⟶ B), IsFinite j → Surjective j → IsNoetherian B →
      IsAffine A → IsAffine B) :
    AffineOfSurjectiveClosedImmersion.{u} := by
  intro A B j hji hjs hB hA
  have := hji
  have := hA
  have hc : CompactSpace B := compactSpace_of_surjective j hjs inferInstance
  exact h A B j inferInstance hjs ((isNoetherian_iff B).mpr ⟨hB, hc⟩) hA

/-! ### The second input: the cohomological lift -/

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The cohomological step of Stacks Tag 09MS, isolated as a hypothesis.** For every positive
tensor power and every global section `t` of it on `Z` whose nonvanishing locus is affine, there
is a global section `t'` of a positive tensor power of `L` on `X` whose nonvanishing locus pulls
back to that of `t`.

This is weaker than the lifting statement of the source in two ways: the degree `m` of `t'` is
unconstrained (the source produces `m = n(e+1)`), and only the nonvanishing locus of `t'` is
controlled, not `t'` itself (the source produces a `t'` restricting to `t^{e+1}`, and a power of a
section of an invertible module has the same nonvanishing locus as the section). The affineness of
`Z_t` is a premise because the source uses it: it is how the obstruction class is seen to restrict
to zero on `Z_t`, which is what Stacks Tag 01XR needs. -/
def SectionsLiftAfterPower : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ t : Γ(tensorPowModule Z (Stacks.AmpleLocallyClosed.pullbackModule i L)
      (n : ℤ), ⊤),
    IsAffineOpen (powNonvanishingOpen Z (Stacks.AmpleLocallyClosed.pullbackModule i L) n t) →
      ∃ m : ℕ, 1 ≤ m ∧ ∃ t' : Γ(tensorPowModule X L (m : ℤ), ⊤),
        i ⁻¹ᵁ powNonvanishingOpen X L m t' =
          powNonvanishingOpen Z (Stacks.AmpleLocallyClosed.pullbackModule i L) n t

/-! ### Chevalley over an open of the target -/

/-- **Affineness of an open of `X` whose inverse image is affine**, given the first input. If
`i` is a surjective closed immersion onto a locally Noetherian `X` and `i^{-1}(U)` is affine, then
`U` is affine: the restriction `i ∣_ U` is again a surjective closed immersion, with affine source
and locally Noetherian target. -/
theorem isAffineOpen_of_isAffineOpen_preimage [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X] (hchev : AffineOfSurjectiveClosedImmersion.{u}) (U : X.Opens)
    (hU : IsAffineOpen (i ⁻¹ᵁ U)) : IsAffineOpen U :=
  hchev (i ⁻¹ᵁ U) U (i ∣_ U)
    (IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance U)
    (IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance U)
    inferInstance hU

/-! ### The converse, and the biconditional -/

/-- **The converse half of Stacks Tag 09MS, from the two named inputs.** If `i` is a surjective
closed immersion onto a locally Noetherian scheme and `i^* L` is ample, then `L` is ample.

The source's hypothesis that `X` is Noetherian is weakened to locally Noetherian, because
quasi-compactness of `X` comes from quasi-compactness of `Z`, which ampleness of `i^* L`
asserts. -/
theorem isAmple_of_isAmple_modulePullback [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X] (hchev : AffineOfSurjectiveClosedImmersion.{u})
    (hlift : SectionsLiftAfterPower i L)
    (h : IsAmple Z (Stacks.AmpleLocallyClosed.pullbackModule i L)) : IsAmple X L := by
  refine (isAmple_iff_forall_affine_nonvanishingOpen X L).mpr
    ⟨compactSpace_of_surjective i inferInstance h.compactSpace, fun x => ?_⟩
  obtain ⟨z, hz⟩ := i.surjective x
  obtain ⟨n, hn, t, haff, hzt⟩ := Stacks.AmpleTheory.IsAmple.exists_affine_nonvanishingOpen Z
    (Stacks.AmpleLocallyClosed.pullbackModule i L) h z
  obtain ⟨m, hm, t', he⟩ := hlift n hn t haff
  have hpre : IsAffineOpen (i ⁻¹ᵁ powNonvanishingOpen X L m t') := by rwa [he]
  have hzmem : z ∈ i ⁻¹ᵁ powNonvanishingOpen X L m t' := by rwa [he]
  exact ⟨m, hm, t', isAffineOpen_of_isAffineOpen_preimage i hchev _ hpre, hz ▸ hzmem⟩

/-- **Stacks Tag 09MS, from the two named inputs.** For a surjective closed immersion of
Noetherian schemes, an invertible `𝒪_X`-module is ample exactly when its pullback is.

The `mpr` direction uses neither hypothesis and neither surjectivity nor Noetherianness; it is
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`. -/
theorem isAmple_modulePullback_iff [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (hchev : AffineOfSurjectiveClosedImmersion.{u}) (hlift : SectionsLiftAfterPower i L) :
    IsAmple Z (Stacks.AmpleLocallyClosed.pullbackModule i L) ↔ IsAmple X L :=
  ⟨isAmple_of_isAmple_modulePullback i L hchev hlift,
    isAmple_modulePullback_of_surjective_isClosedImmersion i L⟩

end Stacks.AmpleClosedImmersion

end
