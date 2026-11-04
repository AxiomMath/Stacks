module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# The relative Leray identification across an integral morphism

Let `π : T' ⟶ T` be an integral morphism of schemes and `g : T ⟶ S` any morphism. Direct image
of abelian sheaves on the small étale sites along `π` is exact, by [Stacks, Tag 04C2], and it
preserves injective objects, being the right adjoint of the exact inverse image. So `π_*` carries
an injective resolution of an abelian sheaf on the small étale site of `T'` to an injective
resolution of its direct image, and the right derived functors of the composite `g_* ∘ π_*`
collapse:

`π_* ⋙ R^q g_* ≅ R^q (π ≫ g)_*`.

This is a degeneration of the relative Leray spectral sequence of [Stacks, Tag 0734].

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral`: the identification
  `π_* ⋙ R^q g_* ≅ R^q (π ≫ g)_*` for an integral `π`.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **The relative Leray identification across an integral morphism.** For `π : T' ⟶ T` integral
and `g : T ⟶ S` arbitrary, the degree-`q` right derived functor of direct image along `π ≫ g` on
abelian sheaves of the small étale sites is direct image along `π` followed by the degree-`q`
right derived functor of direct image along `g`:

`π_* ⋙ R^q g_* ≅ R^q (π ≫ g)_*`. -/
public def smallEtaleRelativeLerayIsoOfIntegral {T' T S : Scheme.{u}} (π : T' ⟶ T) (g : T ⟶ S)
    (hπ : IsIntegralHom π) (q : ℕ) :
    smallEtalePushforwardAb π ⋙ (smallEtalePushforwardAb g).rightDerived q ≅
      (smallEtalePushforwardAb (π ≫ g)).rightDerived q :=
  let := hπ
  let : PreservesFiniteLimits (smallEtalePushforwardAb π) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)).1
  let : PreservesFiniteColimits (smallEtalePushforwardAb π) :=
    ((exactFunctor_iff _).mp (smallEtalePushforwardAb_exact_of_isIntegralHom π)).2
  (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (smallEtalePushforwardAb π) (smallEtalePushforwardAb g) q).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbCompIso π g) q

end Stacks.EtaleCohomology

end
