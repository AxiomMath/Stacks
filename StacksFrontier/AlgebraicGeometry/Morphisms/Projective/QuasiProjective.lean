module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple

/-!
# Projective morphisms are quasi-projective

A projective morphism `f : X ⟶ S` — one admitting a closed immersion `i : X ⟶ 𝐏(ℰ)` over the base
into the projective bundle of a quasi-coherent `𝒪_S`-module `ℰ` of finite type, which is the
first condition of [Stacks, Tag 01W8] — is quasi-projective: it is of finite type and
`i^* 𝒪_{𝐏(ℰ)}(1)` is an invertible `𝒪_X`-module ample relative to `f`. The same holds, by the
same argument with `𝐏(ℰ)` replaced by `ℙⁿ_S`, for an H-projective morphism, the second condition
of that definition.

## Main results

* `AlgebraicGeometry.isQuasiProjective_iff_hProjectiveIsQuasiProjective`: the two spellings of
  quasi-projectivity in this repository agree.
* `AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective`: an H-projective morphism is
  quasi-projective.

## References

* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01VY](https://stacks.math.columbia.edu/tag/01VY)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The two spellings of quasi-projectivity agree: both say that `f` is locally of finite type,
quasi-compact, and carries an invertible module ample relative to it, the relative ampleness
being taken at either of the two equivalent readings of [Stacks, Tag 01VH]. -/
theorem isQuasiProjective_iff_hProjectiveIsQuasiProjective (f : X ⟶ S) :
    IsQuasiProjective f ↔ Stacks.HProjective.IsQuasiProjective f := by
  constructor
  · rintro ⟨hft, L, hL, hample⟩
    exact ⟨hft, L, hL,
      (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mpr hample⟩
  · rintro ⟨hft, L, hL, hample⟩
    exact ⟨hft, L, hL,
      (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp hample⟩

/-- An H-projective morphism is quasi-projective. A closed immersion `i : X ⟶ ℙⁿ_S` over `S` is
in particular a quasi-compact immersion, so `f` is H-quasi-projective; and an H-quasi-projective
morphism is of finite type and carries the relatively ample invertible module `i^* 𝒪(1)` by
[Stacks, Tag 01VY]. -/
theorem IsProjectiveMorphism.isQuasiProjective {f : X ⟶ S} (hf : IsProjectiveMorphism f) :
    IsQuasiProjective f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  exact (isQuasiProjective_iff_hProjectiveIsQuasiProjective f).mpr
    (Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f
      ⟨n, i, inferInstance, inferInstance, hif⟩)

end AlgebraicGeometry

end
