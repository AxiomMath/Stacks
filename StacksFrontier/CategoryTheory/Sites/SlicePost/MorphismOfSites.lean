module

public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localized diagram of morphisms of sites

Let `u : C ⥤ D` be a functor between sites `(C, J)` and `(D, K)`, let `V : C` and put
`U = u.obj V`. Assume that

1. `C` and `D` have all finite limits,
2. `u` is continuous, and
3. `u` commutes with finite limits.

Then there is a commutative diagram of *morphisms of sites*

```
  D/U --j_U--> D
   ↑ f'         ↑ f
  C/V --j_V--> C
```

where `f` corresponds to `u`, the localized arrow `f'` corresponds to
`u' = Over.post u : Over V ⥤ Over U`, and the two horizontal arrows correspond to the functors
`X ↦ X ⨯ V` and `Y ↦ Y ⨯ U` of Stacks 03CE, i.e. to `Over.star`. The diagram is drawn in the
direction of the continuous functors, which run opposite to the morphisms of sites; Stacks states
it with `u : D → C`, so Stacks' `C` is this file's `D` and vice versa.

## Main results

* `CategoryTheory.starCompOverPostIso`: `Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V)`.
* `CategoryTheory.Functor.isMorphismOfSites_overPost`: `Over.post u` is a morphism of sites.
* `CategoryTheory.Functor.isMorphismOfSites_star`: `Over.star X` is a morphism of sites.
* `CategoryTheory.sheafPushforwardContinuousStarOverPostIso`: the induced square of pushforwards
  on sheaves commutes.

## Implementation notes

Composition of morphisms of sites is composition of the underlying continuous functors (Stacks
03CC), so commutativity of the diagram is the isomorphism `starCompOverPostIso` of functors
`C ⥤ Over U`, whose component at `X` is `Limits.prodComparison u V X`. Only preservation of binary
products by `u` is used there.

The final clause of Stacks 03EF, that the associated diagram of morphisms of topoi is equal to the
diagram of Stacks 03CF, is not formalized here. What remains for it is the equation
`CategoryTheory.SliceTopos.sheafFunctorToOverCompOverPostIso_of_eq`, that the identification
forced by the triangle at the terminal sheaf is the one of Stacks 04D3. The consequence
`f'_* j_U^{-1} = j_V^{-1} f_*` is `sheafPushforwardContinuous_overPost_eq`.

## References

* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

universe u u₁ u₂ v₁ v₂

section StarCompOverPost

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency false in
/-- For a functor `u : C ⥤ D` preserving binary products and `V : C`, the isomorphism
`Over.star V ⋙ Over.post u ≅ u ⋙ Over.star (u.obj V)` of functors `C ⥤ Over (u.obj V)`, whose
component at `X` is `Limits.prodComparison u V X : u.obj (V ⨯ X) ⟶ u.obj V ⨯ u.obj X`. -/
@[stacks 03EF "Commutativity of the diagram of 03EF: the two composites `C ⥤ Over (u.obj V)` of
  continuous functors around the square are isomorphic, which since morphisms of sites compose by
  composing their continuous functors (03CC) is what it means for the square of morphisms of sites
  to commute. The final clause of 03EF, that the induced diagram of topoi equals the diagram of
  03CF, is NOT covered — see the module docstring."]
noncomputable def starCompOverPostIso [HasBinaryProducts C] [HasBinaryProducts D] (u : C ⥤ D)
    [PreservesLimitsOfShape (Discrete WalkingPair) u] (V : C) :
    Over.star V ⋙ Over.post (X := V) u ≅ u ⋙ Over.star (u.obj V) :=
  NatIso.ofComponents
    (fun X => Over.isoMk (PreservesLimitPair.iso u V X) (by
      have h : ((Over.post u).obj ((Over.star V).obj X)).hom
          = u.map ((Over.star V).obj X).hom := rfl
      simp [Over.star_obj_hom, PreservesLimitPair.iso_hom, prodComparison_fst]))
    (fun {X Y} f => by
      ext
      dsimp
      simp [PreservesLimitPair.iso_hom, Over.star_map_left, prodComparison_natural])

end StarCompOverPost

section SmallSites

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

namespace Functor

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- If `C` and `D` have all finite limits and `u : C ⥤ D` is continuous and commutes with finite
limits, then for `V : C` the localized functor `Over.post u : Over V ⥤ Over (u.obj V)` defines a
morphism of sites `D/U → C/V`, where `U = u.obj V`. -/
@[stacks 03EF "The left vertical arrow of 03EF's diagram: `u' = Over.post u` is a morphism of
  sites `D/U → C/V` under 03EF's hypotheses. This is 03CF's clause (a) in the special case where
  03EF's hypotheses hold; clause (a) in the generality of 03CF is
  `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites` in
  Sites/SlicePost/MorphismOfSitesGeneral.lean, proved there through 00Y1 as Stacks does.",
  sga "4 VI 7.4.13.6" "special case"]
theorem isMorphismOfSites_overPost [HasFiniteLimits C] [HasFiniteLimits D] (u : C ⥤ D)
    [u.IsContinuous J K] [PreservesFiniteLimits u] (V : C) :
    (Over.post (X := V) u).IsMorphismOfSites (J.over V) (K.over (u.obj V)) :=
  have := isContinuous_overPost_of_flat J K u V
  isMorphismOfSites_of_representablyFlat _ _ _

/-- On a site with binary products, the localization functor `Over.star X : C ⥤ Over X`,
`Y ↦ (Y ⨯ X ⟶ X)`, defines a morphism of sites `C/X → C`. -/
@[stacks 03EF "The two horizontal arrows `j_U` and `j_V` of 03EF's diagram: the localization
  functors `X ↦ X ⨯ U` of 03CE are morphisms of sites. Stated once, for an arbitrary site and
  object; the diagram of 03EF instantiates it at `(C, J, V)` and at `(D, K, u.obj V)`."]
theorem isMorphismOfSites_star [HasBinaryProducts C] (X : C) :
    (Over.star X).IsMorphismOfSites J (J.over X) :=
  isMorphismOfSites_of_representablyFlat _ _ _

end Functor

end SmallSites

section StarCompOverPostTopos

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The isomorphism

```
  (Over.post u)_* ⋙ (Over.star V)_* ≅ (Over.star U)_* ⋙ u_* ,
```

of functors `Sheaf (K.over U) A ⥤ Sheaf J A`, for `U = u.obj V` and any category `A`, induced by
`starCompOverPostIso`: the square of pushforwards on sheaves commutes. -/
@[stacks 03EF "The induced diagram of morphisms of topoi commutes, on the pushforward side, for
  sheaves valued in any category. 03EF's final clause — that this diagram is EQUAL to 03CF's
  diagram of topoi — is NOT covered; 03CF's clause (b) is now proved in
  Sites/SliceTopos/InverseImage.lean, leaving one equation."]
noncomputable def sheafPushforwardContinuousStarOverPostIso [HasBinaryProducts C]
    [HasBinaryProducts D] (u : C ⥤ D) [PreservesLimitsOfShape (Discrete WalkingPair) u] (V : C)
    [u.IsContinuous J K]
    [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]
    (A : Type*) [Category A] :
    (Over.post (X := V) u).sheafPushforwardContinuous A (J.over V) (K.over (u.obj V)) ⋙
        (Over.star V).sheafPushforwardContinuous A J (J.over V) ≅
      (Over.star (u.obj V)).sheafPushforwardContinuous A K (K.over (u.obj V)) ⋙
        u.sheafPushforwardContinuous A J K :=
  haveI : (u ⋙ Over.star (u.obj V)).IsContinuous J (K.over (u.obj V)) :=
    Functor.isContinuous_comp _ _ _ K _
  Functor.sheafPushforwardContinuousComp' (starCompOverPostIso u V) A J (J.over V)
      (K.over (u.obj V)) ≪≫
    (Functor.sheafPushforwardContinuousComp u (Over.star (u.obj V)) A J K
      (K.over (u.obj V))).symm

end StarCompOverPostTopos

end CategoryTheory
