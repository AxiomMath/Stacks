module

public import StacksFrontier.AlgebraicGeometry.Divisors.SupportedSections.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The strict transform of a quasi-coherent module is quasi-coherent

Let `f : X ⟶ S` be a morphism of schemes, let `b : S' ⟶ S` be a second morphism and let `E` be a
quasi-coherent ideal sheaf on `S'`. The strict transform
`Stacks.StrictTransform.sheaf f b E F` of a quasi-coherent module `F` on `X` is again
quasi-coherent, provided the open complement of the support of `E` has quasi-compact inclusion
into `S'`.

That proviso is automatic in the case the Stacks Project states, namely `b` the blowup of `S` in
a quasi-coherent ideal `I` and `E` its exceptional ideal: the exceptional ideal is an effective
Cartier divisor, so the complement of its support is affine over the blowup and in particular
quasi-compact.

So the strict transform can be transformed again along a second blowup, which is what the
comparison of iterated strict transforms needs.

## Main results

* `Stacks.StrictTransform.isRetrocompact_of_quasiCompact_ι`: an open with quasi-compact
  inclusion is retrocompact. The converse is
  `Stacks.StrictTransform.quasiCompact_ι_of_isRetrocompact`.
* `Stacks.StrictTransform.isClosed_exceptionalPreimage` and
  `Stacks.StrictTransform.isRetrocompact_compl_exceptionalPreimage`: the two hypotheses of
  [Stacks, Tag 07ZP] for the inverse image of the support of `E`.
* `Stacks.StrictTransform.isQuasicoherent_sheaf`: the strict transform of a quasi-coherent
  module is quasi-coherent.
* `Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`: the proviso holds for
  the exceptional ideal of a blowup, unconditionally.
* `Stacks.StrictTransform.isQuasicoherent_sheaf_blowUp`: the statement in the shape
  [Stacks, Tag 080I] uses it, for the blowup of `S` in a quasi-coherent ideal.

## Implementation notes

Quasi-coherence of the quotient comes from the two closure properties already in the
repository: the submodule of sections supported in a closed subset with retrocompact complement
is quasi-coherent, which is [Stacks, Tag 07ZP]
(`AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent`), and quasi-coherent modules on
a scheme are closed under cokernels
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`). The pullback of a
quasi-coherent module along the projection is quasi-coherent by
`Stacks.Modules.instIsQuasicoherentPullbackObj`, which is [Stacks, Tag 01BG] for schemes.

Retrocompactness of the complement is traded against quasi-compactness of the inclusion
morphism, which is the form the base-change instance
`Stacks.StrictTransform.quasiCompact_exceptionalComplement_ι` produces and the form in which the
hypothesis descends from the base: `IsRetrocompact_iff_isSpectralMap_subtypeVal` and
`AlgebraicGeometry.quasiCompact_iff_isSpectralMap` identify the two through the same spectral-map
condition. Carrying it as the instance hypothesis `QuasiCompact (exceptionalComplement f b E).ι`
rather than as retrocompactness of a set is what makes the blowup case discharge by instance
search.

For the blowup case the input is [Stacks, Tag 02OS],
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`, together with the affineness half of
[Stacks, Tag 07ZU], `Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`; an affine
morphism is quasi-compact. Both are unconditional, so the blowup statement carries no hypothesis
beyond quasi-coherence of `F`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

/-- An open whose inclusion is quasi-compact is retrocompact. The converse is
`Stacks.StrictTransform.quasiCompact_ι_of_isRetrocompact`. -/
public theorem isRetrocompact_of_quasiCompact_ι {T : Scheme.{u}} (V : T.Opens)
    [QuasiCompact V.ι] : IsRetrocompact (V : Set T) :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (AlgebraicGeometry.quasiCompact_iff_isSpectralMap.mp ‹_›)

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S) (E : S'.IdealSheafData)

/-- The inverse image of the support of `E` in the base change is closed: the support of an
ideal sheaf is closed and the projection is continuous. -/
public theorem isClosed_exceptionalPreimage : IsClosed (exceptionalPreimage f b E) :=
  E.support.2.preimage (pullback.snd f b).base.hom.2

/-- The complement of the inverse image of the support of `E` is retrocompact as soon as its
inclusion is quasi-compact, which `Stacks.StrictTransform.quasiCompact_exceptionalComplement_ι`
inherits from the base. -/
public theorem isRetrocompact_compl_exceptionalPreimage
    [QuasiCompact (exceptionalComplement f b E).ι] :
    IsRetrocompact (exceptionalPreimage f b E)ᶜ := by
  rw [exceptionalPreimage_eq_compl, compl_compl]
  exact isRetrocompact_of_quasiCompact_ι _

/-- **Stacks Project, Tag 07ZP** for the inverse image of the support of `E`: the sections of a
quasi-coherent module supported there form a quasi-coherent submodule. -/
public instance isQuasicoherent_supportedSectionsObj
    [QuasiCompact (exceptionalComplement f b E).ι] (G : (baseChange f b).Modules)
    [G.IsQuasicoherent] :
    (Scheme.Modules.supportedSectionsObj (exceptionalPreimage f b E) G).IsQuasicoherent :=
  AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent _
    (isClosed_exceptionalPreimage f b E) (isRetrocompact_compl_exceptionalPreimage f b E) G

/-- The strict transform of a quasi-coherent module is quasi-coherent. -/
public instance isQuasicoherent_sheaf [QuasiCompact (exceptionalComplement f b E).ι]
    (F : X.Modules) [F.IsQuasicoherent] : (sheaf f b E F).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (Scheme.Modules.supportedSectionsι (exceptionalPreimage f b E)
      ((Scheme.Modules.pullback (pullback.fst f b)).obj F))

section Blowup

variable {Y : Scheme.{u}} (g : X ⟶ Y) (I : Y.IdealSheafData)

/-- The complement of the support of the exceptional ideal of a blowup has quasi-compact
inclusion: by **Stacks Project, Tag 02OS** the exceptional ideal is an effective Cartier
divisor, so by the affineness half of **Stacks Project, Tag 07ZU** that inclusion is an affine
morphism, and an affine morphism is quasi-compact. -/
public instance quasiCompact_ι_compl_support_exceptionalIdeal :
    QuasiCompact (Scheme.Opens.ι (AlgebraicGeometry.exceptionalIdeal I).support.compl) := by
  have := Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor
    (AlgebraicGeometry.exceptionalIdeal I)
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  infer_instance

/-- The strict transform of a quasi-coherent module along the blowup of `Y` in a quasi-coherent
ideal `I` is quasi-coherent, with no hypothesis on `I`. This is the form
**Stacks Project, Tag 080I** needs in order to transform the strict transform again along a
second blowup. -/
public theorem isQuasicoherent_sheaf_blowUp (F : X.Modules) [F.IsQuasicoherent] :
    (sheaf g (AlgebraicGeometry.blowUpToBase I)
      (AlgebraicGeometry.exceptionalIdeal I) F).IsQuasicoherent :=
  inferInstance

end Blowup

end Stacks.StrictTransform

end
