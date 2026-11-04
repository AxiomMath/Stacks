module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalAffineComplement
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic

/-!
# The exceptional complement is retrocompact, and the strict transform is quasi-coherent

`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransform.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransformModule.lean` construct the strict transform
of a scheme `X` over `S` and of a module on it along the blowup of `S` in an ideal sheaf `ℐ`, but
state the facts that make the construction well behaved — that the defining ideal of the strict
transform is exactly the ideal of sections supported on `pr_{S'}⁻¹ E`, and that the strict
transform of a quasi-coherent module is quasi-coherent — under the hypothesis
`QuasiCompact (Scheme.Opens.ι (Stacks.Blowup.exceptionalPullbackCompl f ℐ))`, i.e.
retrocompactness of the complement of `pr_{S'}⁻¹ E`. Their module docstrings record that this
hypothesis cannot be supplied there, because the route Stacks takes to it goes through the
assertion of tag 02OS that the exceptional divisor is an effective Cartier divisor, and only the
locally principal half of that assertion is available.

This file supplies the hypothesis from the locally principal half alone, which is all that is
needed: the complement of a locally principal closed subscheme is affine over the base (Stacks
tag 07ZT, `Stacks.Divisors.isAffineHom_ι_of_isLocallyPrincipal`), hence retrocompact; the
exceptional divisor is locally principal by `Stacks.Blowup.isLocallyPrincipal_exceptionalIdeal`;
and local principality is stable under inverse image by
`Stacks.Divisors.isLocallyPrincipal_comap` (Stacks tag 053P), which transports it from the
blowup `S'` to `X ×_S S'`.

With the hypothesis discharged the two results become unconditional, and are recorded here in
that form — as instances, which is what consumers of the iterated strict transform need, since
forming the strict transform of a strict transform requires the quasi-coherence of the first one
to be found by instance search.

## Main results

* `Stacks.Blowup.isAffineHom_ι_compl_support_exceptionalIdeal`: the complement of the exceptional
  divisor is affine over the blowup.
* `Stacks.Blowup.quasiCompact_ι_exceptionalPullbackCompl`: the inclusion of
  `Stacks.Blowup.exceptionalPullbackCompl` is quasi-compact, with no hypothesis. This is the
  instance that discharges the hypothesis of `StrictTransform.lean` and
  `StrictTransformModule.lean`.
* `Stacks.Blowup.ideal_strictTransformIdeal`: the defining ideal of the strict transform of `X`
  consists of exactly the sections supported on `pr_{S'}⁻¹ E`, with no hypothesis.
* `Stacks.Blowup.isQuasicoherent_strictTransformSheaf` and
  `Stacks.Blowup.isQuasicoherent_strictTransformModule`: the strict transform of a quasi-coherent
  module is quasi-coherent, on `X ×_S S'` and on `X'`, with no hypothesis.

## Implementation notes

`Stacks.Blowup.exceptionalPullbackSet` is defined as a preimage of the support of the exceptional
ideal rather than as the support of its inverse image, so the two have to be identified before
tag 07ZT applies; `Stacks.Blowup.coe_exceptionalPullbackCompl_eq_compl_support` does that with
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`.

`Stacks.Blowup.exceptionalPullbackSet` attains both extremes, so the instance above is not a
disguised statement about the whole space and the quasi-coherence results are not statements
about the plain pullback of `ℱ`. The unit ideal sheaf — the blowup with empty centre, the
degenerate reading in which the strict transform *is* the base change and nothing is divided
out — gives `pr_{S'}⁻¹ E = ∅`, which is already proved as
`Stacks.Blowup.exceptionalPullbackSet_top` in
`StacksFrontier/AlgebraicGeometry/Flatness/RaynaudGrusonFlattening0815.lean`, together with the
resulting identification of the strict transform with the base change. The other extreme, the
zero ideal sheaf, gives `pr_{S'}⁻¹ E` equal to the whole space and is
`Stacks.Blowup.exceptionalPullbackSet_bot` below.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Blowup

section ExceptionalComplement

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- The complement of the exceptional divisor of a blowup is affine over the blowup: the
exceptional divisor is a locally principal closed subscheme, so Stacks tag 07ZT applies. -/
theorem isAffineHom_ι_compl_support_exceptionalIdeal :
    IsAffineHom (Scheme.Opens.ι (exceptionalIdeal ℐ).support.compl) :=
  Stacks.Divisors.isAffineHom_ι_compl_support_of_isLocallyPrincipal _
    (isLocallyPrincipal_exceptionalIdeal ℐ)

end ExceptionalComplement

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- The complement of `pr_{S'}⁻¹ E` in `X ×_S S'` is the complement of the support of the inverse
image of the exceptional ideal along `pr_{S'}`: the support of an inverse image ideal sheaf is the
preimage of the support. -/
theorem coe_exceptionalPullbackCompl_eq_compl_support :
    (exceptionalPullbackCompl f ℐ : Set (blowUpPullback f ℐ)) =
      (((exceptionalIdeal ℐ).comap (blowUpPullbackToBlowUp f ℐ)).support :
        Set (blowUpPullback f ℐ))ᶜ := by
  rw [coe_exceptionalPullbackCompl, exceptionalPullbackSet, Scheme.IdealSheafData.support_comap]
  rfl

/-- The inclusion of the complement of `pr_{S'}⁻¹ E` is quasi-compact, with no hypothesis: the
inverse image of the exceptional ideal is locally principal, so Stacks tag 07ZT applies to its
support. This is the instance that the results of
`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransform.lean` and
`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransformModule.lean` carry as a hypothesis. -/
instance quasiCompact_ι_exceptionalPullbackCompl :
    QuasiCompact (Scheme.Opens.ι (exceptionalPullbackCompl f ℐ)) :=
  Stacks.Divisors.quasiCompact_ι_of_isLocallyPrincipal _
    (Stacks.Divisors.isLocallyPrincipal_comap _ _ (isLocallyPrincipal_exceptionalIdeal ℐ))
    (coe_exceptionalPullbackCompl_eq_compl_support f ℐ)

/-- The complement of `pr_{S'}⁻¹ E` is retrocompact, with no hypothesis. -/
theorem isRetrocompact_compl_exceptionalPullbackSet' :
    IsRetrocompact (exceptionalPullbackSet f ℐ)ᶜ :=
  isRetrocompact_compl_exceptionalPullbackSet f ℐ

/-- **Stacks Project, Tag 080D, part (2).** On an affine open, the defining ideal of the strict
transform of `X` consists of exactly the sections of `𝒪_{X ×_S S'}` supported on `pr_{S'}⁻¹ E`.
This is `Stacks.Blowup.ideal_strictTransformIdeal_of_quasiCompact` with its retrocompactness
hypothesis discharged, so it is the equality that tag 080D's definition asserts. -/
@[stacks 080D "the defining ideal of the strict transform of a scheme, with no hypothesis"]
theorem ideal_strictTransformIdeal (U : (blowUpPullback f ℐ).affineOpens) :
    (strictTransformIdeal f ℐ).ideal U =
      (SheafOfModules.supportedSectionsSubmodule (exceptionalPullbackSet f ℐ)
        (SheafOfModules.unit (blowUpPullback f ℐ).ringCatSheaf)).toSubmodule.obj
          (Opposite.op U.1) :=
  ideal_strictTransformIdeal_of_quasiCompact f ℐ U

/-- **Stacks Project, Tag 080D, part (1).** The strict transform of a quasi-coherent module is
quasi-coherent on `X ×_S S'`, with no hypothesis. Recorded as an instance because the strict
transform of a strict transform is formed by instance search on the quasi-coherence of the
first. -/
@[stacks 080D "the strict transform of a quasi-coherent module is quasi-coherent"]
instance isQuasicoherent_strictTransformSheaf (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (strictTransformSheaf f ℐ ℱ).IsQuasicoherent :=
  strictTransformSheaf_isQuasicoherent f ℐ ℱ

/-- The strict transform of a quasi-coherent module, regarded as a module on the strict transform
`X'` itself, is quasi-coherent, with no hypothesis. This is the module of the triple `ℱ'/X'/S'`
that Stacks tags 080Y and 0815 speak about, so its quasi-coherence is what makes that triple
admissible data. -/
instance isQuasicoherent_strictTransformModule (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (strictTransformModule f ℐ ℱ).IsQuasicoherent :=
  strictTransformModule_isQuasicoherent f ℐ ℱ

/-- The blowup in the zero ideal sheaf has the whole of `S` as centre, so `pr_{S'}⁻¹ E` is the
whole of `X ×_S S'`, and the strict transform of a module is the quotient by all of its sections.
This is one of the two extremes of `Stacks.Blowup.exceptionalPullbackSet`; the other,
`pr_{S'}⁻¹ E = ∅` for the unit ideal sheaf, is
`Stacks.Blowup.exceptionalPullbackSet_top`. -/
theorem exceptionalPullbackSet_bot :
    exceptionalPullbackSet f (⊥ : S.IdealSheafData) = Set.univ := by
  rw [exceptionalPullbackSet_eq_preimage_support]
  simp

end Stacks.Blowup

end
