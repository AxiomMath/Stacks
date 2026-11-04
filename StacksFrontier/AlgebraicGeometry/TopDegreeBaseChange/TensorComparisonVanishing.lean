module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonAffine

/-!
# The tensor comparison of Tag 0EX3 (b) where the compared sheaves vanish

`TensorComparisonAffine.lean` proves the canonicity condition
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap` of conclusion (b) of
[Stacks, Tag 0EX3] in positive degree along an **affine** morphism of schemes with
**quasi-coherent** modules, by observing that the sheaf on the right of the condition vanishes
there, and derives conclusion (b) in that range.

Neither the affineness nor the quasi-coherence is used by that argument: what the argument needs
is a zero object at one end of the equation, and nothing else. This file states the two criteria
that carry it — one at each end — for an arbitrary morphism of schemes, arbitrary sheaves of
modules and an arbitrary degree, and then reads them off conclusion (a) of the tag.

The gain is a hypothesis, and it is the one that matters here. The affine criterion applies only
to the situations built by
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom`, where the degree-`d`
object is itself zero as soon as `d > 0`
(`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.isZero_topDirectImage_of_pos`); the
criteria below apply to **every** `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation`,
including the projective one, whose top degree is positive and whose degree-`d` object is not
known to vanish.

## Main results

All of the following live in the namespace
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isHigherDirectImageTensorMap_of_isZero_pushforward`: **every** map satisfies the canonicity
  condition of conclusion (b) as soon as `R^n f_* F` vanishes, for an arbitrary morphism of
  schemes and arbitrary modules. The two sides of the condition are then morphisms out of a zero
  object.
* `isHigherDirectImageTensorMap_of_isZero_tensorPullback`: the same from vanishing of
  `R^n f_*(F ⊗_{𝒪_X} f^* G)`, where they are morphisms into a zero object. This is the
  generalisation of `isHigherDirectImageTensorMap_of_isAffineHom`, which is recovered from it by
  [Stacks, Tag 01XC].
* `topDirectImageTensorComparison_of_isZero`: conclusion (b) of [Stacks, Tag 0EX3] whenever both
  compared sheaves vanish, for an arbitrary morphism, arbitrary modules and an arbitrary degree.
* `isZero_tensorSheaf_rightDerivedPlus_of_lt` and `isZero_rightDerivedPlus_tensorPullback_of_lt`:
  both compared sheaves vanish above the degree of **any** top-degree base-change situation, by
  conclusion (a) of the tag.
* `topDirectImageTensorComparison_of_lt`: **conclusion (b) of [Stacks, Tag 0EX3] in every degree
  strictly above the degree `d` of an arbitrary top-degree base-change situation**, with the
  canonicity condition discharged and no hypothesis on the base-changed morphism.

## Implementation notes

*Why two criteria and not one.* The condition is an equation between two morphisms
`(R^n f_* F)|_V ⟶ (R^n f_*(F ⊗_{𝒪_X} f^* G))|_V`. A zero object at the source kills it by
`CategoryTheory.Limits.IsZero.eq_of_src` and one at the target by `IsZero.eq_of_tgt`, and the two
hypotheses are genuinely different: above the degree of a situation, conclusion (a) gives the
source criterion for a quasi-coherent `F'` with **no hypothesis on `G'` at all**, while the
target criterion additionally needs `F' ⊗_{𝒪_{X'}} (f')^* G'` to be quasi-coherent and hence
needs `G'` to be. The source criterion is therefore the weaker-hypothesis one, and it is the one
`topDirectImageTensorComparison_of_lt` uses for the condition.

*Why the isomorphism still needs both.* The canonicity condition needs only one zero object, but
the isomorphism of conclusion (b) is between the two sheaves, so exhibiting it needs both of them
to vanish. That is why `topDirectImageTensorComparison_of_lt` carries the quasi-coherence of `G'`
even though the condition does not.

*No Stacks attribute for Tag 0EX3.* Conclusion (b) of the tag is stated at the degree `d` of the
situation; every statement here either carries a vanishing hypothesis the tag does not have, or
is about a degree strictly above `d`, where the tag asserts conclusion (a) instead. By the
covering-set rule none of these is a member of the covering set of conclusion (b), so the
attribute is withheld. The tag's attributes in this directory remain conclusion (a), on
`isZero_rightDerivedPlus_pushforward_baseChange`, and conclusion (b) over an affine base and over
each affine open of an arbitrary base, in `EilenbergWattsUnitor.lean`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules)

/-! ### The two vanishing criteria for the canonicity condition -/

/-- **The canonicity condition of [Stacks, Tag 0EX3] (b) holds, for every map, as soon as
`R^n f_* F` vanishes.** Both sides of the defining equation are morphisms out of the restriction
of a zero object, and two morphisms out of a zero object are equal.

No hypothesis is placed on the morphism or on either module. -/
theorem isHigherDirectImageTensorMap_of_isZero_pushforward (n : ℕ)
    (hz : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G))))) :
    IsHigherDirectImageTensorMap f F G n c := fun V _ =>
  (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) hz).eq_of_src _ _

/-- **The canonicity condition of [Stacks, Tag 0EX3] (b) holds, for every map, as soon as
`R^n f_*(F ⊗_{𝒪_X} f^* G)` vanishes.** Both sides land in the restriction of a zero object.

This is `isHigherDirectImageTensorMap_of_isAffineHom` with its affineness and quasi-coherence
hypotheses removed: those were used only to produce this vanishing, through [Stacks, Tag 01XC]. -/
theorem isHigherDirectImageTensorMap_of_isZero_tensorPullback (n : ℕ)
    (hz : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G))))))
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G))))) :
    IsHigherDirectImageTensorMap f F G n c := fun V _ =>
  (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) hz).eq_of_tgt _ _

/-- **Conclusion (b) of [Stacks, Tag 0EX3] whenever both compared sheaves vanish.** The
isomorphism is the unique one between two zero objects and its inverse satisfies the canonicity
condition because every map does.

Stated for an arbitrary morphism of schemes, arbitrary sheaves of modules and an arbitrary
degree; the vanishing is kept in the signature so that the reach of the statement is visible. -/
def topDirectImageTensorComparison_of_isZero (n : ℕ)
    (hzl : IsZero ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
        ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G))))
    (hzr : IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G)))))) :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
              ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G)))) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
            ((Y.toRingedSpace)).IsSheaf⟩).obj
            ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) //
      IsHigherDirectImageTensorMap f F G n e.inv } :=
  haveI : IsIso ((hzl.iso hzr).hom) := Iso.isIso_hom _
  topDirectImageTensorComparisonOfIsIso f F G n ((hzl.iso hzr).hom)
    (isHigherDirectImageTensorMap_of_isZero_tensorPullback f F G n hzr _)

end

/-! ### Above the degree of a top-degree base-change situation -/

section Situation

variable (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})

noncomputable section

/-- **The left-hand sheaf of conclusion (b) vanishes above the degree of the situation.**
Conclusion (a) of the tag makes `R^n f'_* F'` vanish there, and a tensor product with a vanishing
left factor vanishes. No hypothesis is needed on `G'`. -/
theorem isZero_tensorSheaf_rightDerivedPlus_of_lt (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (G' : S.Y'.Modules) (n : ℕ) (hn : S.d < n) :
    IsZero ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.Y'.toRingedSpace)).presheaf,
        ((S.Y'.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward S.f').rightDerivedPlus (n : ℤ)).obj F'))).obj (G'))) :=
  isZero_tensorSheaf_of_isZero_left
    (isZero_rightDerivedPlus_pushforward_baseChange S (n : ℤ) (by exact_mod_cast hn) F')

/-- **The right-hand sheaf of conclusion (b) vanishes above the degree of the situation.**
`F' ⊗_{𝒪_{X'}} (f')^* G'` is quasi-coherent, so conclusion (a) applies to it directly. -/
theorem isZero_rightDerivedPlus_tensorPullback_of_lt (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (G' : S.Y'.Modules) [G'.IsQuasicoherent] (n : ℕ) (hn : S.d < n) :
    IsZero (((Scheme.Modules.pushforward S.f').rightDerivedPlus (n : ℤ)).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X'.toRingedSpace)).presheaf,
          ((S.X'.toRingedSpace)).IsSheaf⟩).obj (F')).obj (((Scheme.Modules.pullback S.f').obj
          G'))))) :=
  isZero_rightDerivedPlus_pushforward_baseChange S (n : ℤ) (by exact_mod_cast hn)
    (tensorPullbackObj S.f' F' G')

/-- **Conclusion (b) of [Stacks, Tag 0EX3] in every degree strictly above the degree `d` of an
arbitrary top-degree base-change situation**, for quasi-coherent modules and with the canonicity
condition discharged.

No hypothesis is placed on the base-changed morphism `f'`. That is the whole point of the
statement: `topDirectImageTensorComparisonPos` reaches the same conclusion only along an affine
morphism, hence only at the situations
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom` builds, while a situation
in general — the projective one of `SituationProjective.lean` among them — has no affine `f'`.

The degrees this reaches are exactly those in which conclusion (a) of the tag asserts vanishing,
so the statement is degenerate wherever it applies, and the vanishing that makes it so is the
tag's own conclusion rather than a hypothesis. Conclusion (b) at the degree `d` itself is not
proved here and is not implied by anything here. -/
def topDirectImageTensorComparison_of_lt (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (G' : S.Y'.Modules) [G'.IsQuasicoherent] (n : ℕ) (hn : S.d < n) :
    { e : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (n : ℤ)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.X'.toRingedSpace)).presheaf,
              ((S.X'.toRingedSpace)).IsSheaf⟩).obj (F')).obj
              (((Scheme.Modules.pullback S.f').obj G')))) ≅
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((S.Y'.toRingedSpace)).presheaf,
            ((S.Y'.toRingedSpace)).IsSheaf⟩).obj
            ((((Scheme.Modules.pushforward S.f').rightDerivedPlus (n : ℤ)).obj F'))).obj (G')) //
      IsHigherDirectImageTensorMap S.f' F' G' n e.inv } :=
  topDirectImageTensorComparison_of_isZero S.f' F' G' n
    (isZero_tensorSheaf_rightDerivedPlus_of_lt S F' G' n hn)
    (isZero_rightDerivedPlus_tensorPullback_of_lt S F' G' n hn)

end

end Situation

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
