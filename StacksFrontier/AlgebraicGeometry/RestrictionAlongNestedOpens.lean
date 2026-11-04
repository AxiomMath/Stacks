module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.RestrictionSpellings

/-!
# Restriction along nested opens

For opens `U ≤ W` of a scheme `X` the inclusion of `U` factors as `U ⟶ W ⟶ X`, so restricting to
`W` and then to the copy of `U` inside `W` is restricting to `U`, on sheaves of modules and on
derived categories. For two opens `W` and `V` of `X`, restricting to `W` and then to `W ⊓ V`
agrees with restricting to `V` and then to `W ⊓ V`.

## Main definitions

* `Stacks.RestrictionSpellings.restrictFunctorNestedIso`: on sheaves of modules, restriction to
  `U` is restriction to `W` followed by restriction along `X.homOfLE h`.
* `Stacks.RestrictionSpellings.derivedRestrictNestedIso`: the same on derived categories.
* `Stacks.RestrictionSpellings.derivedPullbackNestedIso`: the same on derived categories, with
  restriction to an open given by the derived pullback along the inclusion of the open subspace.
* `Stacks.RestrictionSpellings.derivedRestrictInfIso` and
  `Stacks.RestrictionSpellings.derivedPullbackInfIso`: restricting an object of `D(𝒪_X)` to `W`
  and then to `W ⊓ V` agrees with restricting it to `V` and then to `W ⊓ V`.

## Main results

* `Stacks.RestrictionSpellings.isPullback_ofRestrict_inf`: the square of the inclusions of two
  opens and of their intersection is Cartesian as a square of ringed spaces.
* `Stacks.RestrictionSpellings.range_union_ofRestrict_eq_univ`: when two opens cover the scheme,
  the images of the two inclusions cover it.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso mapDerivedCategoryIsoOfNatIso)

universe u

namespace Stacks.RestrictionSpellings

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-! ### Two nested opens -/

/-- **Restriction to `U` factors through restriction to `W`.** For opens `U ≤ W` of `X`,
restriction of sheaves of modules to `U` is isomorphic to restriction to `W` followed by
restriction along `X.homOfLE h`. -/
def restrictFunctorNestedIso {U W : X.Opens} (h : U ≤ W) :
    Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).symm ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι

/-- **Restriction to `U` factors through restriction to `W` on derived categories.** For opens
`U ≤ W` of `X`, the derived functor of restriction to `U` is isomorphic to the derived functor of
restriction to `W` followed by that of restriction along `X.homOfLE h`. -/
def derivedRestrictNestedIso {U W : X.Opens} (h : U ≤ W) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory :=
  mapDerivedCategoryIsoOfNatIso _ _ (restrictFunctorNestedIso X h) ≪≫
    mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor W.ι)
      (Scheme.Modules.restrictFunctor (X.homOfLE h))

/-- **The nested factorization for the derived pullback.** For opens `U ≤ W` of `X`, restricting
an object of `D(𝒪_X)` to `W` by the derived pullback along the inclusion of the open subspace, and
then to `U` along `X.homOfLE h`, is restricting it to `U` by the derived pullback. -/
def derivedPullbackNestedIso {U W : X.Opens} (h : U ≤ W) :
    derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding) ⋙
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory ≅
      derivedPullback (X.toRingedSpace.ofRestrict U.isOpenEmbedding) :=
  Functor.isoWhiskerRight (derivedPullbackIsoRestrictFunctor X W)
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapDerivedCategory ≪≫
    (derivedRestrictNestedIso X h).symm ≪≫ (derivedPullbackIsoRestrictFunctor X U).symm

/-! ### The overlap of two opens -/

/-- **The overlap coherence of a two-open glueing.** For opens `W` and `V` of `X`, restricting an
object of `D(𝒪_X)` to `W` and then to `W ⊓ V` agrees with restricting it to `V` and then to
`W ⊓ V`: both are restriction to `W ⊓ V`. -/
def derivedRestrictInfIso (W V : X.Opens) :
    (Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor
          (X.homOfLE (inf_le_left : W ⊓ V ≤ W))).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor
          (X.homOfLE (inf_le_right : W ⊓ V ≤ V))).mapDerivedCategory :=
  (derivedRestrictNestedIso X (inf_le_left : W ⊓ V ≤ W)).symm ≪≫
    derivedRestrictNestedIso X (inf_le_right : W ⊓ V ≤ V)

/-- **The overlap coherence for the derived pullback.** For opens `W` and `V` of `X`, restricting
an object of `D(𝒪_X)` to `W` by the derived pullback along the inclusion of the open subspace and
then to `W ⊓ V` agrees with restricting it to `V` by the derived pullback and then to `W ⊓ V`. -/
def derivedPullbackInfIso (W V : X.Opens) :
    derivedPullback (X.toRingedSpace.ofRestrict W.isOpenEmbedding) ⋙
        (Scheme.Modules.restrictFunctor
          (X.homOfLE (inf_le_left : W ⊓ V ≤ W))).mapDerivedCategory ≅
      derivedPullback (X.toRingedSpace.ofRestrict V.isOpenEmbedding) ⋙
        (Scheme.Modules.restrictFunctor
          (X.homOfLE (inf_le_right : W ⊓ V ≤ V))).mapDerivedCategory :=
  derivedPullbackNestedIso X (inf_le_left : W ⊓ V ≤ W) ≪≫
    (derivedPullbackNestedIso X (inf_le_right : W ⊓ V ≤ V)).symm

/-! ### Two opens of a scheme as ringed spaces -/

/-- **The square of two opens is Cartesian as a square of ringed spaces.** For opens `U` and `V`
of `X`, the square formed by the inclusions of `U ⊓ V` into `U` and `V` and of the open subspaces
`U` and `V` into `X` is a pullback square of ringed spaces. -/
theorem isPullback_ofRestrict_inf (U V : X.Opens) :
    IsPullback (X.homOfLE (inf_le_left : U ⊓ V ≤ U)).toLRSHom.toShHom
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).toLRSHom.toShHom
      (X.toRingedSpace.ofRestrict U.isOpenEmbedding)
      (X.toRingedSpace.ofRestrict V.isOpenEmbedding) :=
  ((isPullback_opens_inf U V).map Scheme.forgetToLocallyRingedSpace).map
    LocallyRingedSpace.forgetToSheafedSpace

/-- **Two opens covering a scheme cover it as ranges of ringed-space morphisms.** If `U ⊔ V = ⊤`,
the images of the inclusions of the open subspaces `U` and `V` cover `X`. -/
theorem range_union_ofRestrict_eq_univ (U V : X.Opens) (hUV : U ⊔ V = ⊤) :
    Set.range (X.toRingedSpace.ofRestrict U.isOpenEmbedding).hom.base ∪
      Set.range (X.toRingedSpace.ofRestrict V.isOpenEmbedding).hom.base = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  obtain hxU | hxV : x ∈ U ⊔ V := by rw [hUV]; trivial
  exacts [Or.inl ⟨⟨x, hxU⟩, rfl⟩, Or.inr ⟨⟨x, hxV⟩, rfl⟩]

end Stacks.RestrictionSpellings

end
