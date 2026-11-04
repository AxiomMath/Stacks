module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyComparison

/-!
# Zariski cohomology as a cohomology presheaf of the locally quasi-compact site

Let `X` be an object of the locally quasi-compact Zariski site and let
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)` be the comparison morphism of topoi induced by the open-subset
functor `ι_X : Opens X ⥤ LC_Zar/X`. For the right derived functors of `sheafToPresheaf`,
cohomology does not change under `π_X^{-1}`, at every open subset at once:

`R^p Γ_{X_Zar} ≅ π_X^{-1} ⋙ R^p Γ_{LC_Zar/X} ⋙ (- ∘ ι_X.op)`,

an isomorphism of functors into presheaves on `Opens X`, natural in the open subset and in the
abelian sheaf. Objectwise it reads `H^p(V, G) ≅ H^p(ι_X V, π_X^{-1} G)`.

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`.

* `preservesInjectiveObjects_comparisonDirectImage`: the comparison direct image preserves
  injective abelian sheaves.
* `comparisonDirectImageRightDerivedPresheafIso`: the cohomology presheaf of a direct image along
  the comparison, `π_{X,*} ⋙ R^p Γ_{X_Zar} ≅ R^p Γ_{LC_Zar/X} ⋙ (- ∘ ι_X.op)`.
* `zariskiRightDerivedPresheafComparisonIso`: the display above.
* `zariskiRightDerivedSectionsComparisonIso`: its objectwise form at an open subset `V`.
* `isZero_zariskiRightDerivedPresheaf_inverseImage_opensToSlice`: for `J` injective on `X_Zar` and
  `p > 0` the cohomology presheaf of `π_X^{-1} J` on the big site vanishes at every open subset of
  `X`.

## Implementation notes

The exactness and injective-preservation instances for `π_{X,*}` are supplied in the
`Functor.sheafPushforwardContinuous` spelling of `comparisonDirectImage`, because instance search
does not see through that definition.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- The comparison direct image `π_{X,*}` preserves injective abelian sheaves. -/
theorem preservesInjectiveObjects_comparisonDirectImage :
    (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v}).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- The cohomology presheaf of a comparison direct image is the cohomology presheaf of the big
site, restricted to the open subsets: `π_{X,*} ⋙ R^p Γ_{X_Zar} ≅ R^p Γ_{LC_Zar/X} ⋙ (- ∘ ι_X.op)`
for every `p`. -/
def comparisonDirectImageRightDerivedPresheafIso (p : ℕ) :
    S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} ⋙
        (sheafToPresheaf (Opens.grothendieckTopology X.obj)
          AddCommGrpCat.{max (u + 1) v}).rightDerived p ≅
      (sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p ⋙
        (Functor.whiskeringLeft (Opens X.obj)ᵒᵖ (Over X)ᵒᵖ
          AddCommGrpCat.{max (u + 1) v}).obj (S.opensToSlice X).1.op := by
  haveI := S.opensToSlice_isContinuous X
  haveI : PreservesFiniteColimits ((S.opensToSlice X).1.sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X)) :=
    abelianComparisonDirectImage_preservesFiniteColimits.{u, w, v} S X
  haveI : ((S.opensToSlice X).1.sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X)).PreservesInjectiveObjects :=
    preservesInjectiveObjects_comparisonDirectImage.{u, w, v} S X
  exact pushforwardRightDerivedSheafToPresheafIso AddCommGrpCat.{max (u + 1) v}
    (S.opensToSlice X).1 p

/-- Zariski cohomology on the space of `X` agrees with cohomology of the inverse image on the
localized Zariski site, as an isomorphism of functors into presheaves on `Opens X`:
`R^p Γ_{X_Zar} ≅ π_X^{-1} ⋙ R^p Γ_{LC_Zar/X} ⋙ (- ∘ ι_X.op)`. -/
def zariskiRightDerivedPresheafComparisonIso (p : ℕ) :
    (sheafToPresheaf (Opens.grothendieckTopology X.obj)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p ⋙
          (Functor.whiskeringLeft (Opens X.obj)ᵒᵖ (Over X)ᵒᵖ
            AddCommGrpCat.{max (u + 1) v}).obj (S.opensToSlice X).1.op := by
  haveI : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
        (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (comparisonDirectImageRightDerivedPresheafIso.{u, w, v} S X p)

/-- Zariski cohomology at one open subset `V` of the space of `X` agrees with cohomology of the
inverse image on the localized Zariski site: `H^p(V, G) ≅ H^p(ι_X V, π_X^{-1} G)`, naturally in
`G`. -/
def zariskiRightDerivedSectionsComparisonIso (p : ℕ) (V : Opens X.obj) :
    (sheafToPresheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⋙
        (evaluation (Opens X.obj)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj (op V)).rightDerived p ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (sheafToPresheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⋙
          (evaluation (Over X)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj
            (op ((S.opensToSlice X).1.obj V))).rightDerived p := by
  haveI := S.opensToSlice_isContinuous X
  haveI : PreservesFiniteColimits ((S.opensToSlice X).1.sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X)) :=
    abelianComparisonDirectImage_preservesFiniteColimits.{u, w, v} S X
  haveI : ((S.opensToSlice X).1.sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology X.obj)
      (S.zariskiTopology.over X)).PreservesInjectiveObjects :=
    preservesInjectiveObjects_comparisonDirectImage.{u, w, v} S X
  haveI : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  exact (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
        (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (pushforwardRightDerivedSectionsIso AddCommGrpCat.{max (u + 1) v}
            (S.opensToSlice X).1 p V)

/-- For `J` injective on `X_Zar` and `p > 0`, the `p`-th cohomology presheaf of `π_X^{-1} J` on
the big site vanishes at every object coming from an open subset `V` of `X`.

The sheaf `π_X^{-1} J` itself need not be injective: its cohomology at a non-open object of the
site need not vanish. -/
theorem isZero_zariskiRightDerivedPresheaf_inverseImage_opensToSlice
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    [Injective J] (p : ℕ) (hp : 0 < p) (V : Opens X.obj) :
    IsZero ((((sheafToPresheaf (S.zariskiTopology.over X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).obj
        (op ((S.opensToSlice X).1.obj V))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.mpr hp
  have h0 : IsZero (((sheafToPresheaf (Opens.grothendieckTopology X.obj)
      AddCommGrpCat.{max (u + 1) v} ⋙
        (evaluation (Opens X.obj)ᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj
          (op V)).rightDerived (n + 1)).obj J) :=
    Functor.isZero_rightDerived_obj_injective_succ _ n J
  exact (h0.of_iso
      ((zariskiRightDerivedSectionsComparisonIso.{u, w, v} S X (n + 1) V).app J).symm).of_iso
    ((sheafToPresheafRightDerivedEvaluationIso AddCommGrpCat.{max (u + 1) v} (n + 1)
      ((S.opensToSlice X).1.obj V)).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).symm

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
