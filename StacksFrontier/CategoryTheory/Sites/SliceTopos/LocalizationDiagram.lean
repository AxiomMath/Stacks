module

public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagram of morphisms of sites of Stacks 03EF and the diagram of topoi of Stacks 03CF

Let `u : C ⥤ D` be a functor between the small sites `(C, J)` and `(D, K)`, let `V : C` and put
`U = u.obj V`. Assume that `C` and `D` have all finite limits, that `u` is continuous and that `u`
commutes with finite limits. (Stacks writes `u : D → C`, so Stacks' `C` is this file's `D`.)
Stacks 03EF asserts:

1. `u` defines a morphism of sites `f`;
2. `u' = Over.post u : C/V ⥤ D/U` defines a morphism of sites `f'`;
3. the functors `Over.star V : C ⥤ C/V` and `Over.star U : D ⥤ D/U`, `X ↦ X × V`, `Y ↦ Y × U`,
   define morphisms of sites `j_V`, `j_U`;
4. the square of morphisms of sites commutes, i.e. (Stacks 03CC) the two composites of continuous
   functors `C ⥤ D/U` around it agree, `Over.star V ⋙ Over.post u ≅ u ⋙ Over.star U`;
5. the associated diagram of morphisms of topoi is the diagram of Stacks 03CF;
6. in particular `f'_* j_U⁻¹ = j_V⁻¹ f_*`.

The theorem `CategoryTheory.SliceTopos.localizationDiagram` states all six. For point 5: the two
vertical arrows of the two diagrams are given by the same continuous functors `u` and `u'`, so
they are the same morphisms of topoi; the horizontal arrows of 03CF are the localization morphisms
`j_V`, `j_U` of Stacks 00XZ, with `j⁻¹` restriction along `Over.forget` and `j_*` its right
adjoint `(Over.forget _).sheafPushforwardCocontinuous`, and the horizontal arrows of 03EF are the
morphisms of topoi of the morphisms of sites `Over.star`, with inverse image `(Over.star _)`'s
`sheafPullback` and direct image `(Over.star _)`'s `sheafPushforwardContinuous`. These agree, on
both the inverse- and the direct-image side, by Stacks 03CE
(`StacksLocalizationProducts.sheafPullbackStarIso`,
`StacksLocalizationProducts.sheafPushforwardOverForgetIso`). The diagram of 03CF commutes
(clause (b), `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso`), and so,
transported along these identifications, does the inverse-image square of the 03EF diagram; that
is recorded too.

## Main results

* `CategoryTheory.SliceTopos.sheafPullbackStarCompOverPostIso`: the inverse-image square of the
  03EF diagram commutes, `(f')⁻¹ j_V⁻¹ ≅ j_U⁻¹ f⁻¹` with `j⁻¹` the inverse image of `Over.star`.
* `CategoryTheory.SliceTopos.localizationDiagram`: Stacks 03EF.
-/

@[expose] public section

namespace CategoryTheory.SliceTopos

open Limits

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) (V : C)

noncomputable section

/-- For a morphism of sites given by `u : C ⥤ D` (with `C`, `D` having binary products) and
`V : C`, the square of inverse images of the 03EF diagram commutes:
`(Over.star V)_s ⋙ (Over.post u)_s ≅ u_s ⋙ (Over.star (u.obj V))_s` on sheaves of sets. It is
clause (b) of Stacks 03CF transported along the identifications of Stacks 03CE of the inverse
image of `Over.star` with restriction along `Over.forget`. -/
def sheafPullbackStarCompOverPostIso [HasBinaryProducts C] [HasBinaryProducts D]
    [u.IsContinuous J K] [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))]
    (hu : u.IsMorphismOfSites J K) :
    (Over.star V).sheafPullback (Type u) J (J.over V) ⋙
        (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ≅
      u.sheafPullback (Type u) J K ⋙
        (Over.star (u.obj V)).sheafPullback (Type u) K (K.over (u.obj V)) :=
  Functor.isoWhiskerRight (StacksLocalizationProducts.sheafPullbackStarIso J V) _ ≪≫
    overPullbackCompSheafPullbackOverPostIso J K u V hu ≪≫
    Functor.isoWhiskerLeft _ (StacksLocalizationProducts.sheafPullbackStarIso K (u.obj V)).symm

/-- **Stacks 03EF.** Let `u : C ⥤ D` be a continuous, left exact functor between small sites
`(C, J)` and `(D, K)` with all finite limits, let `V : C` and `U = u.obj V`. Then:

1. `u` is a morphism of sites `f` (Stacks 00X6);
2. `u' = Over.post u : C/V ⥤ D/U`, `V'/V ↦ u(V')/U`, is a morphism of sites `f'`;
3. `Over.star V : C ⥤ C/V` and `Over.star U : D ⥤ D/U` (`X ↦ X × V`, `Y ↦ Y × U`, Stacks 03CE)
   are morphisms of sites `j_V`, `j_U`;
4. the square of morphisms of sites commutes: `Over.star V ⋙ u' ≅ u ⋙ Over.star U`, which by
   Stacks 03CC is commutativity of the square of morphisms of sites;
5. the associated diagram of morphisms of topoi is the diagram of Stacks 03CF: its vertical
   arrows are the morphisms of topoi of `u` and `u'` in both diagrams; its horizontal arrows,
   the morphisms of topoi of the morphisms of sites `Over.star`, are the localization morphisms
   `j_V`, `j_U` of 03CF, as their inverse images are restriction along `Over.forget` and their
   direct images are `j_{V*}`, `j_{U*}` (`(Over.forget _).sheafPushforwardCocontinuous`);
   03CF's square commutes, `(f')⁻¹ j_V⁻¹ ≅ j_U⁻¹ f⁻¹`, and so does the inverse-image square of
   the morphisms of sites, `(Over.star V)_s ⋙ u'_s ≅ u_s ⋙ (Over.star U)_s`;
6. `f'_* j_U⁻¹ = j_V⁻¹ f_*`. -/
@[stacks 03EF "The complete statement: `u`, `u' = Over.post u` and both `Over.star` are morphisms
  of sites, the square of sites commutes (03CC), its diagram of topoi is 03CF's (the `Over.star`
  morphisms of topoi are the localization morphisms `j_V`, `j_U` on both the inverse- and the
  direct-image side, by 03CE), both squares of inverse images commute, and
  `f'_* j_U⁻¹ = j_V⁻¹ f_*`."]
theorem localizationDiagram [HasFiniteLimits C] [HasFiniteLimits D] [u.IsContinuous J K]
    [PreservesFiniteLimits u] :
    u.IsMorphismOfSites J K ∧
      (Over.post (X := V) u).IsMorphismOfSites (J.over V) (K.over (u.obj V)) ∧
      (Over.star V).IsMorphismOfSites J (J.over V) ∧
      (Over.star (u.obj V)).IsMorphismOfSites K (K.over (u.obj V)) ∧
      Nonempty (Over.star V ⋙ Over.post (X := V) u ≅ u ⋙ Over.star (u.obj V)) ∧
      Nonempty ((Over.star V).sheafPullback (Type u) J (J.over V) ≅
        J.overPullback (Type u) V) ∧
      Nonempty ((Over.forget V).sheafPushforwardCocontinuous (Type u) (J.over V) J ≅
        (Over.star V).sheafPushforwardContinuous (Type u) J (J.over V)) ∧
      Nonempty ((Over.star (u.obj V)).sheafPullback (Type u) K (K.over (u.obj V)) ≅
        K.overPullback (Type u) (u.obj V)) ∧
      Nonempty ((Over.forget (u.obj V)).sheafPushforwardCocontinuous (Type u)
          (K.over (u.obj V)) K ≅
        (Over.star (u.obj V)).sheafPushforwardContinuous (Type u) K (K.over (u.obj V))) ∧
      Nonempty (J.overPullback (Type u) V ⋙
          (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ≅
        u.sheafPullback (Type u) J K ⋙ K.overPullback (Type u) (u.obj V)) ∧
      Nonempty ((Over.star V).sheafPullback (Type u) J (J.over V) ⋙
          (Over.post (X := V) u).sheafPullback (Type u) (J.over V) (K.over (u.obj V)) ≅
        u.sheafPullback (Type u) J K ⋙
          (Over.star (u.obj V)).sheafPullback (Type u) K (K.over (u.obj V))) ∧
      (Over.forget (u.obj V)).sheafPushforwardContinuous (Type u) (K.over (u.obj V)) K ⋙
          (Over.post (X := V) u).sheafPushforwardContinuous (Type u) (J.over V)
            (K.over (u.obj V)) =
        u.sheafPushforwardContinuous (Type u) J K ⋙
          (Over.forget V).sheafPushforwardContinuous (Type u) (J.over V) J := by
  have hu : u.IsMorphismOfSites J K := Functor.isMorphismOfSites_of_preservesFiniteLimits u J K
  exact ⟨hu, Functor.isMorphismOfSites_overPost J K u V,
    StacksLocalizationProducts.isMorphismOfSites_star J V,
    StacksLocalizationProducts.isMorphismOfSites_star K (u.obj V),
    ⟨starCompOverPostIso u V⟩,
    ⟨StacksLocalizationProducts.sheafPullbackStarIso J V⟩,
    ⟨StacksLocalizationProducts.sheafPushforwardOverForgetIso J V⟩,
    ⟨StacksLocalizationProducts.sheafPullbackStarIso K (u.obj V)⟩,
    ⟨StacksLocalizationProducts.sheafPushforwardOverForgetIso K (u.obj V)⟩,
    ⟨overPullbackCompSheafPullbackOverPostIso J K u V hu⟩,
    ⟨sheafPullbackStarCompOverPostIso J K u V hu⟩,
    sheafPushforwardContinuous_overPost_eq J K u V (Type u)⟩

end

end CategoryTheory.SliceTopos
