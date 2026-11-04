module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Divisors.SupportedSections.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The strict transform as a scheme over the blowup, and its module

`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransform.lean` constructs, for a scheme `X` over
`S` and a quasi-coherent sheaf of ideals `ℐ` on `S`, the strict transform
`Stacks.Blowup.strictTransform f ℐ` as a closed subscheme of `X ×_S S'` and the strict
transform `Stacks.Blowup.strictTransformSheaf f ℐ ℱ` of a module as a module on the ambient
`X ×_S S'`. The statements about strict transforms in Stacks tags 080Y, 0815, 081R and 0EV9 all
speak instead of the triple `ℱ'/X'/S'`: the module lives on the strict transform itself and the
structure morphism goes to the blowup `S'`. This file supplies that vocabulary and the
quasi-coherence of the module, and records the two facts about admissible blowups that follow
from finite presentation of the centre.

## Main definitions

* `Stacks.Blowup.strictTransformMap` is the structure morphism `X' ⟶ S'` of the strict
  transform over the blowup.
* `Stacks.Blowup.strictTransformToSource` is the other projection `X' ⟶ X`.
* `Stacks.Blowup.strictTransformModule` is the strict transform of a module, regarded as a
  module on the strict transform itself rather than on `X ×_S S'`.

## Main results

* `Stacks.Blowup.strictTransformToSource_comp`: the square formed by the two projections of the
  strict transform over `f` and the blowup morphism commutes.
* `Stacks.Blowup.strictTransformSheaf_isQuasicoherent` and
  `Stacks.Blowup.strictTransformModule_isQuasicoherent`: the strict transform of a
  quasi-coherent module is quasi-coherent, on `X ×_S S'` and on `X'`, as soon as the complement
  of `pr_{S'}⁻¹ E` is retrocompact.
* `Stacks.Blowup.IsAdmissibleBlowup.isProper`: a `U`-admissible blowup is proper, with no
  hypothesis beyond admissibility.
* `Stacks.Blowup.isAdmissibleBlowup_blowUpToBase_top`: the blowup in the unit ideal sheaf — the
  blowup with empty centre — is `U`-admissible for every open `U`, so a `U`-admissible blowup
  always exists.

## Implementation notes

The retrocompactness hypothesis is carried as `QuasiCompact` of the inclusion of
`Stacks.Blowup.exceptionalPullbackCompl`, as in
`Stacks.Blowup.ideal_strictTransformIdeal_of_quasiCompact`, and
`Stacks.Blowup.isRetrocompact_compl_exceptionalPullbackSet` converts it to the form Stacks tag
07ZP is stated in. Stacks obtains it from the second assertion of tag 02OS — the exceptional
divisor is an effective Cartier divisor, so its complement is affine over `S'`, hence
retrocompact — of which only the locally principal half is formalized
(`Stacks.Blowup.isLocallyPrincipal_exceptionalIdeal`). So the hypothesis is explicit, and these
results are *not* tagged `@[stacks 080D]`: tag 080D's definition presupposes quasi-coherence
with no hypothesis, and claiming it with an extra hypothesis would be a weakening.

Quasi-coherence of the quotient is assembled from two closure properties, both of which have to
be fed as terms. `AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent` (tag
07ZP) is stated for `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule`, while
`Stacks.Blowup.strictTransformSheaf` is built from
`AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule`. The two agree by `rfl`, but not
reducibly, so instance search does not carry a hypothesis stated for one across to the other;
the cokernel instance is therefore `@`-applied with the submodule spelled the way tag 07ZP
spells it, and the conclusion reaches `strictTransformSheaf` because that is an `abbrev`.

Properness is `Stacks.Blowup.IsAdmissibleBlowup.isProper_of_fg` fed with the finite generation
of the centre's ideals, which is what `Stacks.Flatness.finitePresentation_subschemeι_iff` — the
affine-local half of Stacks tag 01TV — extracts from finite presentation of the centre.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- If the inclusion of the complement of `pr_{S'}⁻¹ E` is quasi-compact, that complement is
retrocompact. -/
theorem isRetrocompact_compl_exceptionalPullbackSet
    [QuasiCompact (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ))] :
    IsRetrocompact (exceptionalPullbackSet f ℐ)ᶜ :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (quasiCompact_iff_isSpectralMap.mp ‹_›)

/-- The strict transform of a quasi-coherent module is quasi-coherent on `X ×_S S'`, provided
the complement of `pr_{S'}⁻¹ E` is retrocompact. -/
theorem strictTransformSheaf_isQuasicoherent
    [QuasiCompact (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ))]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (strictTransformSheaf f ℐ ℱ).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
    (Scheme.Modules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
      ((Scheme.Modules.pullback (blowUpPullbackToSource f ℐ)).obj ℱ)).toSheafOfModules _
    (Scheme.Modules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
      ((Scheme.Modules.pullback (blowUpPullbackToSource f ℐ)).obj ℱ)).ι
    (AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent
      (exceptionalPullbackSet f ℐ) (isClosed_exceptionalPullbackSet f ℐ)
      (isRetrocompact_compl_exceptionalPullbackSet f ℐ)
      ((Scheme.Modules.pullback (blowUpPullbackToSource f ℐ)).obj ℱ))
    inferInstance

/-- The structure morphism `X' ⟶ S'` of the strict transform of `X` over the blowup of `S` in
`ℐ`: the closed immersion into `X ×_S S'` followed by the projection `pr_{S'}`. -/
def strictTransformMap : strictTransform f ℐ ⟶ blowUp ℐ :=
  strictTransformι f ℐ ≫ blowUpPullbackToBlowUp f ℐ

/-- The projection `X' ⟶ X` of the strict transform of `X`: the closed immersion into
`X ×_S S'` followed by the projection `pr_X`. -/
def strictTransformToSource : strictTransform f ℐ ⟶ X :=
  strictTransformι f ℐ ≫ blowUpPullbackToSource f ℐ

/-- The strict transform of `X` lies over both `X` and the blowup of `S`, compatibly. -/
theorem strictTransformToSource_comp :
    strictTransformToSource f ℐ ≫ f = strictTransformMap f ℐ ≫ blowUpToBase ℐ := by
  rw [strictTransformToSource, strictTransformMap, Category.assoc, Category.assoc,
    pullback.condition]

/-- The strict transform of a module, regarded as a module on the strict transform `X'` of `X`
rather than on the ambient base change `X ×_S S'`: the pullback of
`Stacks.Blowup.strictTransformSheaf` along the closed immersion `X' ⟶ X ×_S S'`. This is the
module of the triple `ℱ'/X'/S'` that Stacks tags 080Y and 0815 speak about. -/
def strictTransformModule (ℱ : X.Modules) : (strictTransform f ℐ).Modules :=
  (Scheme.Modules.pullback (strictTransformι f ℐ)).obj (strictTransformSheaf f ℐ ℱ)

/-- The strict transform of a quasi-coherent module is quasi-coherent on the strict transform
`X'`, provided the complement of `pr_{S'}⁻¹ E` is retrocompact. -/
theorem strictTransformModule_isQuasicoherent
    [QuasiCompact (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ))]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (strictTransformModule f ℐ ℱ).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_pullback (strictTransformι f ℐ) _
    (strictTransformSheaf_isQuasicoherent f ℐ ℱ)

/-- The closed subscheme cut out by the unit ideal sheaf — the empty subscheme — is of finite
presentation. -/
theorem finitePresentation_subschemeι_top :
    FinitePresentation (⊤ : S.IdealSheafData).subschemeι := by
  refine (Stacks.Flatness.finitePresentation_subschemeι_iff _).mpr fun U ↦ ?_
  have h : (⊤ : S.IdealSheafData).ideal U = ⊤ := by simp
  exact h ▸ ⟨{1}, by simp⟩

/-- The blowup in the unit ideal sheaf, whose centre is empty, is a `U`-admissible blowup for
every open `U`. In particular a `U`-admissible blowup always exists. -/
theorem isAdmissibleBlowup_blowUpToBase_top (U : S.Opens) :
    IsAdmissibleBlowup U (blowUpToBase (⊤ : S.IdealSheafData)) :=
  isAdmissibleBlowup_blowUpToBase finitePresentation_subschemeι_top (by simp)

/-- A `U`-admissible blowup is proper. -/
theorem IsAdmissibleBlowup.isProper {X X' : Scheme.{u}} {U : X.Opens} {g : X' ⟶ X}
    (h : IsAdmissibleBlowup U g) : IsProper g := by
  obtain ⟨I, hfp, -, e, he⟩ := h
  exact IsAdmissibleBlowup.isProper_of_fg e he
    ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hfp)

end Stacks.Blowup

end
