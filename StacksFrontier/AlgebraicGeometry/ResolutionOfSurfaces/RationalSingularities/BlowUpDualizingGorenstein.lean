module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleEpiFromUnit
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizingGeneration

/-!
# `ω_A ≅ A` implies `ω_X ≅ 𝒪_X` on the blowup

In Situation [Stacks, Tag 0B4W] with `A` not regular, let `X` be the blowup of `Spec(A)` in the
maximal ideal and let `ω_X` be the dualizing module of `X` normalized relative to a dualizing
module `ω_A` of `A`. Clause (3) of [Stacks, Tag 0B64] says that the canonical map
`f^*ω_A ⟶ ω_X` of [Stacks, Tag 0BBU] is surjective. **If `A` is Gorenstein — if `ω_A ≅ A` —
that map is a surjection `𝒪_X ⟶ ω_X`, and this file proves it is then an isomorphism.**

This is the step Section 54.12 of the source takes without comment: "Since `ω_A = A` we see from
Lemma [Stacks, Tag 0B64] that `ω_X ≅ 𝒪_X`". It is a consequence of clause (3) together with
`Stacks.Duality.isIso_of_epi_structureModule_to_dualizingModule`, and it is the first of the
three steps the embedding-dimension computation of [Stacks, Tag 0BGE] needs.

The second step is taken in
`…/RationalSingularities/BlowUpExceptionalDualizingGorenstein.lean`: with `ω_X ≅ 𝒪_X`,
clause (1) of [Stacks, Tag 0B64] gives `ω_E ≅ 𝒪_E(-1)`. The third step is **not** available, and
neither `deg 𝒪_E(1) = 2` nor `dim_κ(𝔪/𝔪²) = 3` follows from what is here: the source reads the
degree off `ω_E = 𝒪_E(-1)` by Riemann–Roch on `E` over `κ`, which needs `ω_E` to be the
dualizing sheaf of `E` as a proper curve over `κ` and not merely a dualizing module on the
scheme `E`, a distinction [Stacks, Tag 0A7F] does not let one ignore. See the implementation
notes of `…/RationalDoublePoints/GradedDimensions.lean` and of
`…/RationalSingularities/BlowUpExceptionalDualizing.lean`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.nonempty_iso_structureModule_of_iso_self`: **`ω_A ≅ A`
  implies `ω_X ≅ 𝒪_X`.**

## What it carries

The global generation `G` of `ω_X|_E` of [Stacks, Tag 0B5H], exactly as clause (3) does and for
the same reason — that tag is proved only with four hypotheses of its own on the curve, see
`…/RationalSingularities/BlowUpDualizingGeneration.lean`. Nothing else: the surjectivity is
clause (3), the identification of the source of the canonical map with `𝒪_X` is the pullback of
the structure sheaf (`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` and
`AlgebraicGeometry.tildeSelf`), and that a surjection `𝒪_X ⟶ ω_X` onto a dualizing module on an
integral locally Noetherian scheme is an isomorphism is proved in
`…/Duality/DualizingModuleEpiFromUnit.lean` from [Stacks, Tag 0AVL], [Stacks, Tag 0EME] and the
simplicity of a dualizing complex over a field.

No `@[stacks]` attribute is attached: the source states this inside the discussion of
Section 54.12 rather than as a numbered clause of [Stacks, Tag 0B64], and `G` is carried.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0BBU](https://stacks.math.columbia.edu/tag/0BBU)
* [Stacks Project, Tag 0B5H](https://stacks.math.columbia.edu/tag/0B5H)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

/-- **`ω_A ≅ A` implies `ω_X ≅ 𝒪_X`.** In Situation [Stacks, Tag 0B4W] with `A` not regular, let
`ω_A` be a dualizing module for `A` isomorphic to `A` itself and let `ω_X` be the dualizing
module of the blowup `X` of `Spec(A)` in the maximal ideal normalized relative to `ω_A`. Then
`ω_X` is isomorphic to the structure sheaf of `X`.

Clause (3) of [Stacks, Tag 0B64] makes the canonical map `f^*ω_A ⟶ ω_X` surjective; with
`ω_A ≅ A` its source is `𝒪_X`, and a surjection of `𝒪_X` onto a dualizing module on an integral
locally Noetherian scheme is an isomorphism
(`Stacks.Duality.isIso_of_epi_structureModule_to_dualizingModule`). -/
theorem nonempty_iso_structureModule_of_iso_self (S : RationalSingularitySituation.{u})
    (hnot : ¬ IsRegularLocalRing S.A) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (e : ωA ≅ ModuleCat.of S.A S.A) (ωX : (blowUpScheme S.A).Modules)
    (N : letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
        isLocallyNoetherian_blowUpScheme S.A
      (rationalSingularitySituationBlowUp S).NormalizedDualizingModule ωA ωX)
    (G : SheafOfModules.GeneratingSections
      ((Scheme.Modules.pullback (exceptionalImmersion S.A)).obj ωX)) :
    Nonempty (ωX ≅ Stacks.Divisors.structureModule (blowUpScheme S.A)) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  let : IsLocallyNoetherian (blowUpScheme S.A) := isLocallyNoetherian_blowUpScheme S.A
  have : IsIntegral (blowUpScheme S.A) :=
    (rationalSingularitySituationBlowUp S).source_isIntegral
  -- `f^*ω̃_A ≅ 𝒪_X`, because `ω_A ≅ A`
  have α : Stacks.Divisors.structureModule (blowUpScheme S.A) ≅
      (Scheme.Modules.pullback (rationalSingularitySituationBlowUp S).f).obj (tilde ωA) :=
    (Scheme.Modules.pullbackUnitIso (rationalSingularitySituationBlowUp S).f).symm ≪≫
      (Scheme.Modules.pullback (rationalSingularitySituationBlowUp S).f).mapIso
        (tildeSelf.symm ≪≫ ((tilde.functor (CommRingCat.of S.A)).mapIso e).symm)
  have : IsIso α.hom := α.isIso_hom
  let φ := α.hom ≫ (rationalSingularitySituationBlowUp S).dualizingPullbackMap ωA hωA ωX
    N.isDualizing ((rationalSingularitySituationBlowUp S).dualizingTraceSequenceOfNormalized N)
  have : Epi φ := epi_comp' (IsIso.epi_of_iso α.hom)
    (epi_dualizingPullbackMap_of_normalized S hnot ωA hωA ωX N G)
  have := Stacks.Duality.isIso_of_epi_structureModule_to_dualizingModule ωX N.isDualizing φ this
  exact ⟨(asIso φ).symm⟩

end AlgebraicGeometry.BlowUpDualizing

end
