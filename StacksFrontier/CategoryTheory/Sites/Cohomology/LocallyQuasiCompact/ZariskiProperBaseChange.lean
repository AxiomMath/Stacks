module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The base-change map of the Zariski comparison morphisms

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site. The commutative square
of topoi of Stacks 0DCU gives, on direct images, the isomorphism

`π_{X,*} ∘ f_* ≅ f_{Zar,*} ∘ π_{Y,*}`

of `zariskiComparisonDirectImageSquareIso`. Its mate under the two comparison adjunctions
`π_X^{-1} ⊣ π_{X,*}` and `π_Y^{-1} ⊣ π_{Y,*}` is a natural map

`π_Y^{-1} ∘ f_* ⟶ f_{Zar,*} ∘ π_X^{-1}`,

here `comparisonBaseChangeMap`. Clause (7a) of Stacks 0DCU is the assertion that this map is an
isomorphism when `f` is proper. This file constructs the map, on sheaves of sets and on abelian
sheaves, characterizes it by the mate equation, and identifies the direct image of the slice
morphism of topoi of Stacks 0DCU with restriction along `Over.pullback f`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.spaceDirectImage` and
  `sliceDirectImage`: the two direct images `f_*` and `f_{Zar,*}` of clause (7).
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonBaseChangeMap`: the
  base-change map, for an arbitrary choice of left adjoints of the two comparison direct
  images.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiComparisonBaseChangeMap` and
  `abelianZariskiComparisonBaseChangeMap`: the base-change map for the comparison adjunction on
  sheaves of sets and on abelian sheaves.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.mateEquiv_comparisonBaseChangeMap` and
  `eq_comparisonBaseChangeMap_of_mateEquiv`: the base-change map is characterized by its mate
  being the direct-image comparison.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiSlicePushforwardIso` and
  `zariskiSliceMorphismPushforwardIso`: the direct image of the slice morphism of topoi is
  restriction along `Over.pullback f`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 00XX](https://stacks.math.columbia.edu/tag/00XX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v a b t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- The direct image of the slice morphism of topoi of Stacks 0DCU is restriction along
`Over.pullback f`: the pushforward attached to cocontinuity of `Over.map f` agrees with the
pushforward attached to continuity of its right adjoint `Over.pullback f`, which is the
sheaf-level form of Stacks 00XX (1). Concretely, `(f_{Zar,*}G)(Z/Y) = G(Z ×_Y X / X)`. -/
def zariskiSlicePushforwardIso (A : Type a) [Category.{b} A]
    [∀ F : (Over X)ᵒᵖ ⥤ A, (Over.map f).op.HasPointwiseRightKanExtension F] :
    (Over.map f).sheafPushforwardCocontinuous A
        (S.zariskiTopology.over X) (S.zariskiTopology.over Y) ≅
      (Over.pullback f).sheafPushforwardContinuous A
        (S.zariskiTopology.over Y) (S.zariskiTopology.over X) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso A

/-- The direct image of the morphism of Zariski slice topoi `zariskiSliceMorphism` is
restriction along `Over.pullback f`. -/
def zariskiSliceMorphismPushforwardIso :
    (zariskiSliceMorphism.{u, w, t} S f).pushforward ≅
      (Over.pullback f).sheafPushforwardContinuous (Type (max u t))
        (S.zariskiTopology.over Y) (S.zariskiTopology.over X) :=
  have := hasPointwiseRightKanExtension_overMap.{u, w, t} S f
  zariskiSlicePushforwardIso S f (Type (max u t))

variable (A : Type a) [Category.{b} A]

/-- Direct image of sheaves along the underlying continuous map of a morphism of the site: this
is the `f_*` appearing in clauses (5) and (7) of Stacks 0DCU. -/
abbrev spaceDirectImage :
    Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Sheaf (Opens.grothendieckTopology Y.obj) A :=
  Functor.sheafPushforwardContinuous
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)) A
    (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)

/-- Direct image of sheaves along the morphism of Zariski slice topoi of clause (5) of
Stacks 0DCU, in the form `(f_{Zar,*}G)(Z/Y) = G(Z ×_Y X / X)` of `zariskiSlicePushforwardIso`:
this is the `f_{Zar,*}` appearing in clause (7). -/
abbrev sliceDirectImage :
    Sheaf (S.zariskiTopology.over X) A ⥤ Sheaf (S.zariskiTopology.over Y) A :=
  Functor.sheafPushforwardContinuous (Over.pullback f) A
    (S.zariskiTopology.over Y) (S.zariskiTopology.over X)

/-- **The base-change map of the Zariski comparison morphisms.** For any choice of left adjoints
`π_X^{-1}` and `π_Y^{-1}` of the two comparison direct images, the mate of the commutative
square `π_{X,*} ∘ f_* ≅ f_{Zar,*} ∘ π_{Y,*}` of Stacks 0DCU is a natural map

`π_Y^{-1} ∘ f_* ⟶ f_{Zar,*} ∘ π_X^{-1}`.

Clause (7a) of Stacks 0DCU is the assertion that it is an isomorphism when `f` is proper. -/
def comparisonBaseChangeMap
    {PX : Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Sheaf (S.zariskiTopology.over X) A}
    {PY : Sheaf (Opens.grothendieckTopology Y.obj) A ⥤ Sheaf (S.zariskiTopology.over Y) A}
    (adjX : PX ⊣ S.comparisonDirectImage X A) (adjY : PY ⊣ S.comparisonDirectImage Y A) :
    spaceDirectImage S f A ⋙ PY ⟶ PX ⋙ sliceDirectImage S f A :=
  (mateEquiv adjX adjY).symm (zariskiComparisonDirectImageSquareIso S f A).hom

/-- The base-change map is characterized by its mate: transposing it back across the two
comparison adjunctions returns the direct-image comparison of the square. -/
theorem mateEquiv_comparisonBaseChangeMap
    {PX : Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Sheaf (S.zariskiTopology.over X) A}
    {PY : Sheaf (Opens.grothendieckTopology Y.obj) A ⥤ Sheaf (S.zariskiTopology.over Y) A}
    (adjX : PX ⊣ S.comparisonDirectImage X A) (adjY : PY ⊣ S.comparisonDirectImage Y A) :
    mateEquiv adjX adjY (comparisonBaseChangeMap S f A adjX adjY) =
      (zariskiComparisonDirectImageSquareIso S f A).hom :=
  (mateEquiv adjX adjY).apply_symm_apply _

/-- A transformation whose mate is the direct-image comparison of the square *is* the
base-change map. -/
theorem eq_comparisonBaseChangeMap_of_mateEquiv
    {PX : Sheaf (Opens.grothendieckTopology X.obj) A ⥤ Sheaf (S.zariskiTopology.over X) A}
    {PY : Sheaf (Opens.grothendieckTopology Y.obj) A ⥤ Sheaf (S.zariskiTopology.over Y) A}
    (adjX : PX ⊣ S.comparisonDirectImage X A) (adjY : PY ⊣ S.comparisonDirectImage Y A)
    (τ : spaceDirectImage S f A ⋙ PY ⟶ PX ⋙ sliceDirectImage S f A)
    (hτ : mateEquiv adjX adjY τ = (zariskiComparisonDirectImageSquareIso S f A).hom) :
    τ = comparisonBaseChangeMap S f A adjX adjY :=
  (mateEquiv adjX adjY).injective
    (hτ.trans (mateEquiv_comparisonBaseChangeMap S f A adjX adjY).symm)

/-- The base-change map of the Zariski comparison morphisms on sheaves of sets, whose
invertibility for a proper `f` is clause (7a) of Stacks 0DCU.

The coefficients are types in an arbitrary universe containing the universe of the spaces. -/
def zariskiComparisonBaseChangeMap :
    spaceDirectImage S f (Type (max u t)) ⋙ comparisonInverseImage.{u, w, t} S Y ⟶
      comparisonInverseImage.{u, w, t} S X ⋙ sliceDirectImage S f (Type (max u t)) :=
  comparisonBaseChangeMap S f (Type (max u t)) (comparisonAdjunction.{u, w, t} S X)
    (comparisonAdjunction.{u, w, t} S Y)

/-- The base-change map of the Zariski comparison morphisms on abelian sheaves, whose derived
counterpart is clause (7b) of Stacks 0DCU. -/
def abelianZariskiComparisonBaseChangeMap :
    spaceDirectImage S f AddCommGrpCat.{max (u + 1) v} ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ⟶
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        sliceDirectImage S f AddCommGrpCat.{max (u + 1) v} :=
  comparisonBaseChangeMap S f AddCommGrpCat.{max (u + 1) v}
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
