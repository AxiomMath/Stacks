module

public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Locally projective morphisms are proper

A morphism of schemes is *locally projective* when its base is covered by opens over each of
which it is, over that open, a closed immersion into the projective bundle `𝐏(ℰ)` of a
quasi-coherent module of finite type. Such a morphism is proper.

The base is covered by opens over which the morphism is a closed immersion into some `ℙⁿ`
([Stacks, Tag 01WB]), properness is Zariski-local at the target, `ℙⁿ` is proper over its base
and a closed immersion is proper.

## Main results

* `AlgebraicGeometry.isProper_of_isLocallyProjective`: a locally projective morphism is proper.
* `AlgebraicGeometry.IsProjective.isProper`: a projective morphism is proper.

## References

* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- **Stacks Project, Tag 01WC.** A locally projective morphism is proper.

Tag 01WB turns local projectivity into local H-projectivity, and a locally H-projective
morphism is proper. -/
@[stacks 01WC]
theorem isProper_of_isLocallyProjective (hf : IsLocallyProjective f) : IsProper f :=
  isProper_of_isLocallyProjectiveMorphism f
    (Stacks.LocallyProjectiveHProjective.isLocallyProjective_iff_isLocallyProjectiveMorphism.mp hf)

/-- **A projective morphism is proper.** A projective morphism is locally projective, by the
covering of the base with the single open `⊤`. -/
theorem IsProjective.isProper (hf : IsProjective f) : IsProper f :=
  isProper_of_isLocallyProjective hf.isLocallyProjective

end AlgebraicGeometry

end
