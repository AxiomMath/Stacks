module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.CompositionPermanence

/-!
# Quasi-projectivity of the first factor of a composition

[Stacks, Tag 0C4N] asserts that if `g ∘ f` is quasi-projective and `f` is quasi-compact, then `f`
is quasi-projective. Quasi-projectivity is `AlgebraicGeometry.IsQuasiProjective`, the predicate of
[Stacks, Tag 01VW]: finite type together with an invertible sheaf on the source that is ample
relative to the morphism.

## Main results

* `AlgebraicGeometry.IsQuasiProjective.of_comp`: if `f ≫ g` is quasi-projective and `f` is
  quasi-compact, then `f` is quasi-projective.

## References

* [Stacks Project, Tag 0C4N](https://stacks.math.columbia.edu/tag/0C4N)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 0C4L](https://stacks.math.columbia.edu/tag/0C4L)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsQuasiProjective

/-- Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. If `f ≫ g` is quasi-projective and
`f` is quasi-compact, then `f` is quasi-projective. -/
@[stacks 0C4N]
public theorem of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hfg : IsQuasiProjective (f ≫ g)) (hf : QuasiCompact f) : IsQuasiProjective f := by
  obtain ⟨L, hL, hLA⟩ := hfg.exists_isRelativelyAmple
  have hLi : Stacks.Ample.IsInvertibleModule X L := hL
  refine ⟨⟨LocallyOfFiniteType.of_comp hfg.locallyOfFiniteType, hf⟩, L, hL, ?_⟩
  exact (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mp
    (Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp f g L
      ((Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple (f ≫ g) L).mpr hLA) hf)

end IsQuasiProjective

end AlgebraicGeometry

end
