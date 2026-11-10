module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Localization.CocontinuousBaseChange
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Morphism
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Morphisms of ringed topoi given by cocontinuous functors, and their localizations

A cocontinuous functor `v : X.C ⥤ Y.C` between the sites of two ringed sites induces a morphism
of topoi `Sh(X) ⟶ Sh(Y)` (Stacks 00XO) with direct image the right Kan extension along `v` and
inverse image the sheafified restriction along `v`; together with a structure map
`O_Y ⟶ v_* O_X` it is a morphism of ringed topoi. For an object `V` of `X.C` the functor
`v' = Over.post v : X.C/V ⥤ Y.C/v(V)` is again cocontinuous (Stacks 03EG), and restricting the
structure map to `Y.C/v(V)` and composing with the base change map
`j_{v(V)}^{-1}(v_* O_X) ⟶ v'_*(O_X|_V)` gives the structure map of the localized morphism of
ringed topoi.

## Main definitions

* `cocontinuousToposHomCocontinuousMorphism`: the morphism of topoi of Stacks 00XO.
* `cocontinuousRingedToposHomCocontinuousMorphism`: the morphism of ringed topoi with a given
  structure map.
* `localizedCocontinuousFSharpCocontinuousMorphism`: the structure map of the localized morphism.
* `localizedCocontinuousRingedToposHomCocontinuousMorphism`: the localized morphism of ringed
  topoi.

## Main results

* `forgetFSharp_localizedCocontinuousRingedToposHom_cocontinuousMorphism`: on underlying sheaves of
  sets the localized structure map is the restricted structure map followed by the base change map.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 03EG](https://stacks.math.columbia.edu/tag/03EG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible] Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor

/-- The direct image `gStar` along a cocontinuous functor preserves finite products. -/
instance CategoryTheory.preservesFiniteProducts_gStar_cocontinuousMorphism {C : Type u}
    [SmallCategory C] {D : Type u} [SmallCategory D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (w : C ⥤ D) [w.IsCocontinuous J K] :
    PreservesFiniteProducts (gStar _ _ J K w) :=
  haveI := (gAdjunction _ _ J K w).rightAdjoint_preservesLimits
  inferInstance

/-- The direct image along a cocontinuous functor preserves finite products. -/
instance CategoryTheory.preservesFiniteProducts_sheafPushforwardCocontinuous_cocontinuousMorphism
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (w : C ⥤ D) [w.IsCocontinuous J K] :
    PreservesFiniteProducts (w.sheafPushforwardCocontinuous (Type u) J K) :=
  CategoryTheory.preservesFiniteProducts_gStar_cocontinuousMorphism J K w

namespace AlgebraicGeometry.RingedSite

section Generic

variable {C D C' D' : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory C']
  [SmallCategory D'] {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {JC' : GrothendieckTopology C'} {JD' : GrothendieckTopology D'}
  (Φ : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)) [PreservesFiniteProducts Φ]
  (Φ' : Sheaf JC' (Type u) ⥤ Sheaf JD' (Type u)) [PreservesFiniteProducts Φ']
  (a : C' ⥤ C) [a.IsContinuous JC' JC] (b : D' ⥤ D) [b.IsContinuous JD' JD]
  (e : Φ ⋙ b.sheafPushforwardContinuous (Type u) JD' JD ⟶
    a.sheafPushforwardContinuous (Type u) JC' JC ⋙ Φ')
  (OC : Sheaf JC CommRingCat.{u}) (OD : Sheaf JD CommRingCat.{u})

/-- The base change of a structure map `O_D ⟶ Φ O_C` along restrictions `a`, `b` and a
transformation `e : Φ ⋙ b^s ⟶ a^s ⋙ Φ'`: the restriction of the structure map followed by `e`,
carrying the ring operations along. -/
noncomputable def baseChangeCommRingMapCocontinuousMorphism
    (fs : OD ⟶ pullbackCommRingSheaf (K := JC) JD Φ OC) :
    (b.sheafPushforwardContinuous CommRingCat.{u} JD' JD).obj OD ⟶
      pullbackCommRingSheaf (K := JC') JD' Φ'
        ((a.sheafPushforwardContinuous CommRingCat.{u} JC' JC).obj OC) :=
  (b.sheafPushforwardContinuous CommRingCat.{u} JD' JD).map fs ≫
    (restrictionCommRingIso JD' JD b (pullbackCommRingSheaf (K := JC) JD Φ OC)).inv ≫
    (pullbackCommRingSheafComp JD JD' Φ (b.sheafPushforwardContinuous (Type u) JD' JD) OC).hom ≫
    pullbackCommRingSheafMapOfNatTrans JD' e OC ≫
    (pullbackCommRingSheafComp JC' JD' (a.sheafPushforwardContinuous (Type u) JC' JC) Φ' OC).inv ≫
    pullbackCommRingSheafMap JD' Φ' (restrictionCommRingIso JC' JC a OC).hom

/-- On underlying sheaves of sets the base-changed structure map is the restricted structure map
followed by `e`. -/
theorem forget_map_baseChangeCommRingMap_cocontinuousMorphism
    (fs : OD ⟶ pullbackCommRingSheaf (K := JC) JD Φ OC) :
    (sheafCompose JD' (forget CommRingCat.{u})).map
        (baseChangeCommRingMapCocontinuousMorphism Φ Φ' a b e OC OD fs) =
      (b.sheafPushforwardContinuous (Type u) JD' JD).map
          ((sheafCompose JD (forget CommRingCat.{u})).map fs) ≫
        e.app ((sheafCompose JC (forget CommRingCat.{u})).obj OC) := by
  have h₃ : (sheafCompose JD' (forget CommRingCat.{u})).map
      (pullbackCommRingSheafComp JC' JD' (a.sheafPushforwardContinuous (Type u) JC' JC) Φ'
        OC).inv = 𝟙 _ :=
    Iso.inv_ext (f := (sheafCompose JD' (forget CommRingCat.{u})).mapIso _) (by
      rw [Functor.mapIso_hom, forget_map_pullbackCommRingSheafComp_hom]
      exact Category.comp_id _)
  have h₄ : (sheafCompose JD' (forget CommRingCat.{u})).map
      (pullbackCommRingSheafMap JD' Φ' (restrictionCommRingIso JC' JC a OC).hom) =
        𝟙 (Φ'.obj ((a.sheafPushforwardContinuous (Type u) JC' JC).obj
          ((sheafCompose JC (forget CommRingCat.{u})).obj OC))) := by
    rw [underlyingRingSheaf_map_pullbackCommRingSheafMap, restrictionCommRingIso_hom_forget]
    exact CategoryTheory.Functor.map_id _ _
  have h₀ : (sheafCompose JD' (forget CommRingCat.{u})).map
      ((b.sheafPushforwardContinuous CommRingCat.{u} JD' JD).map fs) =
      (b.sheafPushforwardContinuous (Type u) JD' JD).map
        ((sheafCompose JD (forget CommRingCat.{u})).map fs) := rfl
  simp only [baseChangeCommRingMapCocontinuousMorphism, CategoryTheory.Functor.map_comp, h₀,
    restrictionCommRingIso_inv_forget, forget_map_pullbackCommRingSheafComp_hom,
    pullbackCommRingSheafMapOfNatTrans_forget, h₃, h₄]
  refine congrArg (_ ≫ ·) ?_
  refine (Category.id_comp _).trans ((Category.id_comp _).trans ?_)
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.comp_id _)

end Generic

variable {X Y : RingedSite.{u, u, u}} (v : X.C ⥤ Y.C)

/-- **Stacks 00XO.** The morphism of topoi `Sh(X) ⟶ Sh(Y)` induced by a cocontinuous functor
`v : X.C ⥤ Y.C`: its direct image is the right Kan extension along `v` and its inverse image the
sheafified restriction along `v`. -/
noncomputable abbrev cocontinuousToposHomCocontinuousMorphism (hv : v.IsCocontinuous X.J Y.J) :
    MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)) :=
  letI := hv
  { pushforward := gStar _ _ _ _ v
    inverseImage := gInv _ _ _ _ v
    adj := gAdjunction _ _ _ _ v
    preservesFiniteLimits := main_left_exact _ _ _ _ v }

/-- The morphism of ringed topoi induced by a cocontinuous functor and a structure map
`O_Y ⟶ v_* O_X`. -/
noncomputable abbrev cocontinuousRingedToposHomCocontinuousMorphism (hv : v.IsCocontinuous X.J Y.J)
    (fsharp : Y.O ⟶
      (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O) :
    RingedToposHom (ringedTopos X) (ringedTopos Y) where
  toToposHom := cocontinuousToposHomCocontinuousMorphism v hv
  fSharp := fsharp

variable (V : X.C)

/-- The localized functor `Over.post v` is cocontinuous for the localized topologies. -/
theorem isCocontinuous_overPost_over_cocontinuousMorphism [v.IsCocontinuous X.J Y.J] :
    (Over.post (X := V) v).IsCocontinuous (X.over V).J (Y.over (v.obj V)).J :=
  inferInstanceAs ((Over.post (X := V) v).IsCocontinuous (X.J.over V) (Y.J.over (v.obj V)))

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}} (v : X.C ⥤ Y.C) [hv : v.IsCocontinuous X.J Y.J] (V : X.C)

include hv

/-- **The structure map of the localized morphism of ringed topoi.** The restriction of the
structure map `O_Y ⟶ v_* O_X` to `Y.C/v(V)`, followed by the base change map
`j_{v(V)}^{-1}(v_* O_X) ⟶ v'_*(O_X|_V)` carrying the ring operations along. -/
noncomputable def localizedCocontinuousFSharpCocontinuousMorphism
    (fsharp : Y.O ⟶
      (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O) :
    (Y.over (v.obj V)).O ⟶
      (pushforwardCommRingFunctor
        (cocontinuousToposHomCocontinuousMorphism.{u} (X := X.over V) (Y := Y.over (v.obj V))
          (Over.post (X := V) v)
          (isCocontinuous_overPost_over_cocontinuousMorphism v V))).obj (X.over V).O :=
  baseChangeCommRingMapCocontinuousMorphism (JC' := X.J.over V) (JD' := Y.J.over (v.obj V))
    (cocontinuousToposHomCocontinuousMorphism v hv).pushforward
    (cocontinuousToposHomCocontinuousMorphism.{u} (X := X.over V) (Y := Y.over (v.obj V))
      (Over.post (X := V) v) (isCocontinuous_overPost_over_cocontinuousMorphism v V)).pushforward
    (Over.forget V) (Over.forget (v.obj V))
    (Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J) (K := Y.J))
      X.O Y.O fsharp

/-- **The localized morphism of ringed topoi** `(Sh(X/V), O_X|_V) ⟶ (Sh(Y/v(V)), O_Y|_{v(V)})`
of a morphism given by a cocontinuous functor. -/
noncomputable abbrev localizedCocontinuousRingedToposHomCocontinuousMorphism
    (fsharp : Y.O ⟶
      (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O) :
    RingedToposHom (ringedTopos (X.over V)) (ringedTopos (Y.over (v.obj V))) :=
  cocontinuousRingedToposHomCocontinuousMorphism.{u} (X := X.over V) (Y := Y.over (v.obj V))
    (Over.post (X := V) v) (isCocontinuous_overPost_over_cocontinuousMorphism v V)
    (localizedCocontinuousFSharpCocontinuousMorphism v V fsharp)

/-- On underlying sheaves of sets, the structure map of the localized morphism is the restricted
structure map followed by the base change map of sheaves of sets. -/
theorem forgetFSharp_localizedCocontinuousRingedToposHom_cocontinuousMorphism
    (fsharp : Y.O ⟶
      (pushforwardCommRingFunctor (cocontinuousToposHomCocontinuousMorphism v hv)).obj X.O) :
    RingedToposHom.forgetFSharp
        (localizedCocontinuousRingedToposHomCocontinuousMorphism v V fsharp) =
      (Y.J.overPullback (Type u) (v.obj V)).map
          ((sheafCompose Y.J (forget CommRingCat.{u})).map fsharp) ≫
        (Functor.overPostSheafBaseChangeCocontinuousBaseChange v V (J := X.J)
            (K := Y.J)).app
          ((sheafCompose X.J (forget CommRingCat.{u})).obj X.O) :=
  forget_map_baseChangeCommRingMap_cocontinuousMorphism (JC' := X.J.over V)
    (JD' := Y.J.over (v.obj V)) _ _ _ _ _
    X.O Y.O fsharp

end AlgebraicGeometry.RingedSite
