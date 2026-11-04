module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackDatum.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-projective morphisms over a base with an ample invertible module

Over a base carrying an ample invertible module every quasi-projective morphism is
H-quasi-projective: the relatively ample module of quasi-projectivity and the ample module of the
base combine into an absolutely ample invertible module on the source, and an absolutely ample
module on a source of finite type gives a quasi-compact immersion into a projective space over the
base.

## Main results

* `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAmple`: H-quasi-projectivity
  from quasi-projectivity and a chosen ample invertible module on the base.
* `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple`: the same with
  the ample invertible module on the base only assumed to exist, stated at
  `AlgebraicGeometry.IsQuasiProjective` and `AlgebraicGeometry.IsHQuasiProjective`.
* `Stacks.HProjective.exists_isAmple_of_isAffine`: an affine scheme carries an ample invertible
  module, so the hypothesis on the base is satisfiable.

## Implementation notes

The two ingredients are `Stacks.AmplePullbackDatum.eventualAffineDatumUniform`, which makes
`L ⊗ f^* M ^⊗ a` ample for large `a`, and
`Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform`, which turns an absolutely ample
module on a source of finite type into an immersion into projective space over the base.

The two spellings of quasi-projectivity are interchanged by
`Stacks.HProjective.modulesIsQuasiProjective_iff_isQuasiProjective`, and the two spellings of
H-quasi-projectivity differ only in how the structure morphism of `ℙⁿ_S` is written, which is the
same morphism by `rfl`.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.HProjective

/-- **Over a base carrying an ample invertible module, a quasi-projective morphism is
H-quasi-projective.**

The relatively ample module `L` of quasi-projectivity and the ample module `M` of the base give an
absolutely ample invertible module `L ⊗ f^* M ^⊗ a` on the source for every large `a`, and an
absolutely ample module on a source of finite type gives a quasi-compact immersion into a
projective space over the base. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) : IsHQuasiProjective f :=
  Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple
    Stacks.AmplePullbackDatum.eventualAffineDatumUniform
    Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform f M hM hf

/-- An affine scheme admits an ample invertible module, namely its structure sheaf. This is the
hypothesis on the base of the theorem below, so that hypothesis holds of something. -/
theorem exists_isAmple_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    ∃ (M : S.Modules) (h : Stacks.Ample.IsInvertibleModule S M),
      letI := h; Stacks.Ample.IsAmple S M :=
  ⟨Stacks.Ample.unitModule S, Stacks.Ample.isInvertibleModule_unit S,
    Stacks.Ample.isAmple_unitModule_of_isAffine S⟩

/-- **A quasi-projective morphism to a scheme admitting an ample invertible module is
H-quasi-projective**: it admits a quasi-compact immersion into a projective space over the base.

Quasi-projectivity is finite type together with an invertible module ample relative to the
morphism, and H-quasi-projectivity is a quasi-compact immersion into `ℙⁿ_S` over `S`. -/
@[stacks 087S "part (2)", ega "II 5.3.3" "more general"]
theorem isHQuasiProjective_of_isQuasiProjective_of_exists_isAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : ∃ (M : S.Modules) (h : Stacks.Ample.IsInvertibleModule S M),
      letI := h; Stacks.Ample.IsAmple S M)
    (hf : AlgebraicGeometry.IsQuasiProjective f) : AlgebraicGeometry.IsHQuasiProjective f := by
  obtain ⟨M, h, hM⟩ := hS
  have := h
  exact isHQuasiProjective_of_isQuasiProjective_of_isAmple f M hM
    ((modulesIsQuasiProjective_iff_isQuasiProjective f).mp hf)

end Stacks.HProjective

end
