module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConormalDifferentialAssembly
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConormalTranspose
import StacksCore.Tactic.StacksAttribute

/-!
# `NL_{X/Y}` for a morphism factored through a formally smooth scheme

Let `f : X ⟶ Y` be a morphism of schemes which factors as `f = g ∘ i` with `i : X ⟶ P` an
immersion and `g : P ⟶ Y` formally smooth.  Then there is a canonical isomorphism

`NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})`

in `D(𝒪_X)`, the conormal sheaf `𝒞_{X/P}` being placed in degree `-1`.  That is
[Stacks Project, Tag 0FV4].  It is proved here.

## Main results

* `Stacks.NaiveCotangentImmersionFormallySmooth.naiveCotangentIsoConormalDifferentialComplex`:
  **[Stacks Project, Tag 0FV4].**

## Route

The source's proof assembles the isomorphism out of the distinguished triangle of
[Stacks Project, Tag 0FV3], the identifications `NL_{X/P} = 𝒞_{X/P}[1]` of
[Stacks Project, Tag 0FV2] and `NL_{P/Y} = Ω_{P/Y}` of [Stacks Project, Tag 0D0L], and the
invertibility of the canonical map of [Stacks Project, Tag 0E1Z].  That route leaves the
first morphism of the resulting triangle pinned only up to automorphisms of its source and
target, so it has to be computed, and the answer carries a sign.

The proof here is different and the isomorphism it produces is canonical with no sign to track.
It rests on the observation that `𝒪_X` has, besides its canonical polynomial presentation over
`f^{-1}𝒪_Y`, the presentation `i^{-1}𝒪_P ⟶ 𝒪_X` — locally surjective because `i` is an
immersion — and that the two-term complex of *that* presentation is the right-hand side of the
tag.  A chain map between the two naive cotangent complexes therefore exists globally, with no
choices, as soon as the two presentations are compared through a third: the polynomial
presentation on the *sections of* `i^{-1}𝒪_P`, which maps to `i^{-1}𝒪_P` by evaluation.  Four
steps:

1. `Stacks.SheafOfModules.quasiIso_towerFacComparison`: a factorisation of one presentation of a
   sheaf of rings through another induces a quasi-isomorphism of the two-term complexes of their
   conormal sequences, provided both presenting rings are formally smooth over the base at every
   stalk.  Stalkwise this is
   `NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth`, which is Mathlib's
   `Algebra.Extension.H1Cotangent.equivOfFormallySmooth` in degree `1` and the
   presentation-independence of `Ω[S⁄R]` in degree `0`.
2. `Stacks.NaiveCotangentTower.schemeTowerIso`: combined with [Stacks Project, Tag 08TL] and the
   iterated-inverse-image spelling of `NL_{X/Y}`, that identifies `NL_{X/Y}` in `D(𝒪_X)` with the
   two-term complex of the presentation `i^{-1}𝒪_P ⟶ 𝒪_X`.  Formal smoothness of `g` enters
   only through
   `Stacks.NaiveCotangentInverseImageStalkSmooth.formallySmooth_stalk_inverseImageFirstRingMap`.
3. `Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf` (the degree `-1` clause of
   [Stacks Project, Tag 0FV2]), `Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge` and
   `Stacks.NaiveCotangentTower.tensorDifferentialsCrossing` identify the two terms of that
   complex with `𝒞_{X/P}` and `i^*Ω_{P/Y}`.
4. `Stacks.NaiveCotangentConormalTranspose.conormalTranspose_comp` identifies the two
   differentials: both transposes carry a section `f` of the ideal sheaf of the closed factor of
   `i` to `1 ⊗ d f`, which is what pins the first arrow of the conormal sequence of
   [Stacks Project, Tag 01UZ] (`Stacks.ConormalSequenceRight.conormalDifferential_unique`).
   `Stacks.NaiveCotangentConormalAssembly.towerComplexIso` turns that into the isomorphism of
   complexes.

## Implementation notes

The right-hand side is `Stacks.ConormalSequenceRight.conormalDifferentialComplex i g`, whose
degree `-1` term is `𝒞_{X/P}` and degree `0` term `i^*Ω_{P/Y}`
(`Stacks.ConormalSequenceRight.conormalDifferentialComplexXIsoNegOne` and `...XIsoZero`), with
no term in any other degree (`...conormalDifferentialComplex_isZero_X`) and with the first arrow
of the conormal sequence of [Stacks Project, Tag 01UZ] as its only differential
(`...conormalDifferentialComplex_d_negOne_zero`).  So the statement below is the tag's
right-hand side with `𝒞_{X/P}` in degree `-1`, as the tag requires.

`AlgebraicGeometry.Scheme.naiveCotangentComplex f` is ascribed to `CochainComplex X.Modules ℤ`:
it is formed at the spelling `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_X)`,
which is definitionally `AlgebraicGeometry.Scheme.Modules X` but a distinct term, and with the
two spellings left as they come the two occurrences of `DerivedCategory.Q` trigger two
independent searches for `HasDerivedCategory` whose universe constraint cannot be solved.

The derived category is the one of `HasDerivedCategory.standard`, taken as a local instance, as
elsewhere in this development.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence,
  whose first arrow is the differential of the right-hand side.
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL), the comparison of a
  presentation with the canonical one.
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6), smooth implies formally
  smooth, which is the tag's parenthetical remark.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.NaiveCotangentImmersionFormallySmooth

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y) [IsImmersion i]

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks Project, Tag 0FV4].**  Let `f : X ⟶ Y` be a morphism of schemes which factors as
`f = g ∘ i` with `i : X ⟶ P` an immersion and `g : P ⟶ Y` formally smooth (for example smooth,
by [Stacks Project, Tag 02H6]).  Then there is a canonical isomorphism

`NL_{X/Y} ≅ (𝒞_{X/P} ⟶ i^*Ω_{P/Y})`

in `D(𝒪_X)`, where the conormal sheaf `𝒞_{X/P}` is placed in degree `-1`.

The right-hand side is `Stacks.ConormalSequenceRight.conormalDifferentialComplex i g`: the
two-term complex whose degree `-1` term is the conormal sheaf of [Stacks Project, Tag 01R2],
whose degree `0` term is `i^*Ω_{P/Y}`, and whose only differential is the first arrow of the
conormal sequence of [Stacks Project, Tag 01UZ].

See the `Route` section of this file; the proof does not go through the distinguished triangle of
[Stacks Project, Tag 0FV3] and so has no sign to track. -/
@[stacks 0FV4 "the canonical isomorphism NL_{X/Y} = (C_{X/P} -> i^*Omega_{P/Y}) in D(O_X), \
  with C_{X/P} in degree -1, for f = g . i with i an immersion and g formally smooth",
  sga "6 VIII 2.2" "more general"]
def naiveCotangentIsoConormalDifferentialComplex (f : X ⟶ Y) (hf : f = i ≫ g)
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f : CochainComplex X.Modules ℤ) ≅
      DerivedCategory.Q.obj (Stacks.ConormalSequenceRight.conormalDifferentialComplex i g) :=
  eqToIso (congrArg (fun m : X ⟶ Y ↦ DerivedCategory.Q.obj
      (Scheme.naiveCotangentComplex m : CochainComplex X.Modules ℤ)) hf) ≪≫
    Stacks.NaiveCotangentConormalAssembly.derivedIso i g hg
      (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g)
      (Stacks.NaiveCotangentConormalAssembly.hsq_of_transpose i g
        (Stacks.NaiveCotangentTower.tensorDifferentialsCrossing i g)
        (Stacks.NaiveCotangentConormalTranspose.conormalTranspose_comp i g))

end Derived

end Stacks.NaiveCotangentImmersionFormallySmooth

end

end
