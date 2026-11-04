module

public import StacksFrontier.AlgebraicGeometry.Descent.VectFpqcSingletonStack
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData

/-!
# Descent of vector bundles along one flat morphism of the big h site

The pseudofunctor `AlgebraicGeometry.bigHVectPseudofunctor` sends an object `U` of the big h
category `(Sch/S)_h` to `Vect(U)`, the category of finite locally free `𝒪_U`-modules.  It has
effective descent along every morphism whose underlying morphism of schemes is surjective, flat and
quasi-compact — in particular along every surjective flat proper morphism of finite presentation,
which is the ordinary input to condition (2) of Stacks 0EX9 for Stacks Tag 0EXE.

This is `AlgebraicGeometry.isStackFor_vectPseudofunctor_singleton` (Stacks Tags 023T and 05B2 for
one fpqc morphism of schemes) carried to the big h site by
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves`: the functor
to schemes preserves fibre products.

## Main results

* `AlgebraicGeometry.isStackFor_bigHVectPseudofunctor_singleton`: **effective descent of finite
  locally free modules along a surjective flat quasi-compact morphism of `(Sch/S)_h`.**
* `AlgebraicGeometry.isStackFor_bigHVectPseudofunctor_singleton_of_isProper`: the same for a
  surjective flat proper morphism of finite presentation.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pseudofunctor `U ↦ Vect(U)` on the big h category over `S`**, the restriction of
`AlgebraicGeometry.vectPseudofunctor` along the functor to schemes. -/
abbrev bigHVectPseudofunctor : Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat :=
  vectPseudofunctor.{u}.restrict (BigHOver.toScheme B S hS)

variable {B S hS}

/-- **Effective descent of finite locally free modules along a surjective flat quasi-compact
morphism of the big h site.** -/
theorem isStackFor_bigHVectPseudofunctor_singleton {X Y : BigHOver B S hS} (f : X ⟶ Y)
    [Flat ((BigHOver.toScheme B S hS).map f)] [Surjective ((BigHOver.toScheme B S hS).map f)]
    [QuasiCompact ((BigHOver.toScheme B S hS).map f)] :
    (bigHVectPseudofunctor B S hS).IsStackFor (Presieve.singleton f) := by
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff,
    Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves]
  have h := isStackFor_vectPseudofunctor_singleton ((BigHOver.toScheme B S hS).map f)
  rw [← Presieve.ofArrows_pUnit.{0}, Pseudofunctor.isStackFor_ofArrows_iff] at h
  exact h

/-- **Effective descent of finite locally free modules along a surjective flat proper morphism of
finite presentation of the big h site**, the ordinary input to condition (2) of Stacks 0EX9 for
Stacks Tag 0EXE. -/
theorem isStackFor_bigHVectPseudofunctor_singleton_of_isProper {X Y : BigHOver B S hS}
    (f : X ⟶ Y) [Flat ((BigHOver.toScheme B S hS).map f)]
    [IsProper ((BigHOver.toScheme B S hS).map f)]
    [Surjective ((BigHOver.toScheme B S hS).map f)] :
    (bigHVectPseudofunctor B S hS).IsStackFor (Presieve.singleton f) :=
  isStackFor_bigHVectPseudofunctor_singleton f

end AlgebraicGeometry

end
