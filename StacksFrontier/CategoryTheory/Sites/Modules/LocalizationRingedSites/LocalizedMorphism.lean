module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.InverseImage
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization
public import StacksFrontier.CategoryTheory.Sites.SlicePost.MorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Localizing a morphism of ringed sites, as a morphism of ringed topoi

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C` which defines a morphism of sites, let `V` be an object of `D` and put `U = u(V)`.
Stacks 03CF localizes the underlying morphism of sites to `f' : C/U ⟶ D/V`, given by
`u' = Over.post u : D/V ⥤ C/U`, and Stacks 04J0 equips `f'` with the structure map making it a
morphism of ringed topoi `(Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)`.

The structure map of `f'` is the restriction `j_V^{-1}(f♯)` of the structure map of `f`: this
typechecks on the nose because the identity `f'_* j_U^{-1} = j_V^{-1} f_*` of Stacks 03CF is a
*strict* equality of functors, for sheaves valued in any category
(`CategoryTheory.sheafPushforwardContinuous_overPost_eq`), so no comparison isomorphism has to
be inserted. That is the sense in which the map is canonical, and it is the structure map that
`AlgebraicGeometry.RingedSite.MorphismLocalization.localizedStructureMap` pins down by
uniqueness.

This file assembles the passage from a morphism of ringed sites to a morphism of ringed topoi in
the sense of Stacks 01D3 part (2), and the localized morphism of ringed sites and of ringed
topoi.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.toposHom`: the morphism of topoi underlying a morphism of
  ringed sites.
* `AlgebraicGeometry.RingedSite.Hom.ringedToposHom`: a morphism of ringed sites read as a
  morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.Hom.localizedRingedToposHom`: the localized morphism of ringed
  sites `(C/U, O_U) ⟶ (D/V, O'_V)` of Stacks 04J0, read as a morphism of ringed topoi. The
  morphism of ringed sites itself is `AlgebraicGeometry.RingedSite.Hom.localized`, which needs no
  finite-limit hypothesis on `u`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom`: on underlying sheaves of sets
  the structure map of `ringedToposHom` is the structure map of the morphism of ringed sites.
* `AlgebraicGeometry.RingedSite.Hom.overPullback_comp_localizedPushforward`: the last assertion
  of Stacks 04J0, `f'_* j_U^{-1} = j_V^{-1} f_*`, for the assembled morphism.
* `AlgebraicGeometry.RingedSite.Hom.localizedRingedSquare`: Stacks 04J0's commutative diagram of
  ringed topoi, as a 2-isomorphism of the two composites.

## Implementation notes

The site, its morphisms and the sections of its structure sheaf all lie in one universe. That is
forced upstream, not chosen here: `CategoryTheory.Functor.IsMorphismOfSites` — the condition that
`u_s` be exact, which is what makes `u` a morphism of *sites* rather than merely a continuous
functor — is stated for sheaves of sets valued in the universe of the site, and
`AlgebraicGeometry.RingedSite.Hom` already requires the objects and the morphisms of the two
sites to share a universe. Exactness of `u_s` on sheaves valued in a larger universe does not
follow from the statement at the site's own universe, so a morphism of ringed sites whose
structure sheaf has larger sections cannot be read as a morphism of ringed topoi at all.

The continuity of `u' = Over.post u`, which Stacks 03CF asserts for every continuous `u`, is
available in this repository at that generality: `u'` is a morphism of sites for an arbitrary
morphism of sites `u` by
`CategoryTheory.Functor.isMorphismOfSites_overPost_of_isMorphismOfSites`, which is Stacks 03CF's
clause (a), and its continuity alone by
`CategoryTheory.Functor.isContinuous_overPost_of_isContinuous`. Taking the latter as a local
instance makes that generality available to *every* declaration below, so none of them assumes
the hypotheses of Stacks 03EF — `[HasFiniteLimits C]`, `[HasFiniteLimits D]`,
`[PreservesFiniteLimits u]` — which Stacks 04J0 does not ask for. The witness is always the
field `f.isMorphismOfSites`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- **Stacks 00XC** for a morphism of ringed sites: the underlying morphism of topoi
`Sh(C) ⟶ Sh(D)`, whose inverse image is `u_s` and whose direct image is `u^s`. Left exactness of
the inverse image is the substantive half of `CategoryTheory.Functor.IsMorphismOfSites`. -/
noncomputable def Hom.toposHom :
    MorphismOfTopoi (Sheaf X.J (Type u)) (Sheaf Y.J (Type u)) where
  inverseImage := f.u.sheafPullback (Type u) Y.J X.J
  pushforward := f.u.sheafPushforwardContinuous (Type u) Y.J X.J
  adj := f.u.sheafAdjunctionContinuous (Type u) Y.J X.J
  preservesFiniteLimits := f.isMorphismOfSites.preservesFiniteLimits

/-- **Stacks 01D3 part (2)** for a morphism of ringed sites: a morphism of ringed sites read as
a morphism of ringed topoi. The morphism of topoi is `toposHom`, and the structure map is the
structure map `f♯ : O' ⟶ f_*O` of the morphism of ringed sites, read through the identification
of the direct image of a sheaf of commutative rings with its restriction along `u`. -/
noncomputable def Hom.ringedToposHom :
    AlgebraicGeometry.RingedToposHom (ringedTopos X) (ringedTopos Y) where
  toToposHom := f.toposHom
  fSharp := f.fsharp ≫ (restrictionCommRingIso Y.J X.J f.u X.O).inv

/-- The morphism of topoi underlying `ringedToposHom` is `toposHom`. -/
@[simp]
theorem Hom.ringedToposHom_toToposHom : f.ringedToposHom.toToposHom = f.toposHom := rfl

/-- On underlying sheaves of sets, the structure map of `ringedToposHom` is the structure map of
the morphism of ringed sites: the identification it is composed with is the identity there. -/
theorem Hom.forgetFSharp_ringedToposHom :
    AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom =
      (sheafCompose Y.J (forget CommRingCat.{u})).map f.fsharp := by
  change (sheafCompose Y.J (forget CommRingCat.{u})).map
      (f.fsharp ≫ (restrictionCommRingIso Y.J X.J f.u X.O).inv) = _
  rw [CategoryTheory.Functor.map_comp, restrictionCommRingIso_inv_forget]
  exact Category.comp_id _

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

/-- The localized morphism of ringed *topoi* `(f', (f')♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)`,
with `U = u(V)`. -/
@[stacks 04J0 "(1): the localized morphism of ringed topoi"]
noncomputable def Hom.localizedRingedToposHom (V : Y.C) :
    AlgebraicGeometry.RingedToposHom (ringedTopos (X.over (f.u.obj V)))
      (ringedTopos (Y.over V)) :=
  (f.localized V).ringedToposHom

/-- The identity `f'_* j_U^{-1} = j_V^{-1} f_*`, as a strict equality of functors
`Sh(C) ⥤ Sh(D/V)`. This is Stacks 03CF's clause (d) read on the assembled morphisms of ringed
topoi: the localizations contribute their inverse images and `f`, `f'` their direct images. -/
@[stacks 04J0 "(3): the identity `f'_* j_U^{-1} = j_V^{-1} f_*`"]
theorem Hom.overPullback_comp_localizedPushforward (V : Y.C) :
    (X.localizationRingedToposHom (f.u.obj V)).toToposHom.inverseImage ⋙
        (f.localizedRingedToposHom V).toToposHom.pushforward =
      f.ringedToposHom.toToposHom.pushforward ⋙
        (Y.localizationRingedToposHom V).toToposHom.inverseImage :=
  sheafPushforwardContinuous_overPost_eq Y.J X.J f.u V (Type u)

/-- The structure map of the localization morphism of ringed topoi, on underlying sheaves of
sets, is the unit of `j_T^{-1} ⊣ j_{T,*}` at the structure sheaf. This is
`forgetRing_localizationRingedToposHom_fSharp` read through
`AlgebraicGeometry.RingedToposHom.forgetFSharp`. -/
theorem forgetFSharp_localizationRingedToposHom (Z : RingedSite.{u, u, u}) (T : Z.C) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (Z.localizationRingedToposHom T) =
      (Z.overMorphismOfTopoi T).adj.unit.app ((ringedTopos Z).forgetRing.obj Z.O) :=
  Z.forgetRing_localizationRingedToposHom_fSharp T

/-- The structure map of the localized morphism is the restriction of the structure map of `f`,
on underlying sheaves of sets: both are `f♯` read through `j_V^{-1}`, which is precomposition
with `(Over.forget V)ᵒᵖ` on either side of the forgetful functor. -/
theorem Hom.forgetFSharp_localizedRingedToposHom (V : Y.C) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (f.localizedRingedToposHom V) =
      (Y.overMorphismOfTopoi V).inverseImage.map
        (AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom) := by
  rw [Hom.forgetFSharp_ringedToposHom f]
  exact Hom.forgetFSharp_ringedToposHom (f.localized V)

/-- The structure map of `j_V ∘ f'`, on underlying sheaves of sets: the structure map of `f`
followed by the unit of `j_V^{-1} ⊣ j_{V,*}` at `f_*O`. -/
theorem Hom.forgetFSharp_localizationComp (V : Y.C) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
          (Y.localizationRingedToposHom V) (f.localizedRingedToposHom V)) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom ≫
        (Y.overMorphismOfTopoi V).adj.unit.app
          (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O)) := by
  refine (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
    (Y.localizationRingedToposHom V) (f.localizedRingedToposHom V)).trans ?_
  refine Eq.trans (congrArg (fun z => AlgebraicGeometry.RingedToposHom.forgetFSharp
      (Y.localizationRingedToposHom V) ≫ (Y.overMorphismOfTopoi V).pushforward.map z)
    (f.forgetFSharp_localizedRingedToposHom V)) ?_
  refine Eq.trans (congrArg (fun z => z ≫ (Y.overMorphismOfTopoi V).pushforward.map
      ((Y.overMorphismOfTopoi V).inverseImage.map
        (AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom)))
    (forgetFSharp_localizationRingedToposHom Y V)) ?_
  exact (Y.overMorphismOfTopoi V).adj.unit_naturality _

/-- The structure map of `f ∘ j_{U'}`, on underlying sheaves of sets: the structure map of `f`
followed by `f_*` of the unit of `j_{U'}^{-1} ⊣ j_{U',*}` at `O`. -/
theorem Hom.forgetFSharp_compLocalization (V : Y.C) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos X) (Z := ringedTopos Y)
          f.ringedToposHom (X.localizationRingedToposHom (f.u.obj V))) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom ≫
        f.toposHom.pushforward.map
          ((X.overMorphismOfTopoi (f.u.obj V)).adj.unit.app
            ((ringedTopos X).forgetRing.obj X.O)) := by
  refine (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp
    f.ringedToposHom (X.localizationRingedToposHom (f.u.obj V))).trans ?_
  exact congrArg (fun z => AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom ≫
    f.toposHom.pushforward.map z) (forgetFSharp_localizationRingedToposHom X (f.u.obj V))

/-- The comparison of the two direct images in the square of Stacks 04J0: the two composites have
the same inverse image up to Stacks 03CF's clause (b), so their direct images are canonically
isomorphic by uniqueness of right adjoints. -/
noncomputable def Hom.localizedRingedSquareComparison (V : Y.C) :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
          (Y.localizationRingedToposHom V)
          (f.localizedRingedToposHom V)).toToposHom.pushforward ≅
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos X) (Z := ringedTopos Y)
          f.ringedToposHom
          (X.localizationRingedToposHom (f.u.obj V))).toToposHom.pushforward :=
  Adjunction.rightAdjointUniq
    ((AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
        (Y.localizationRingedToposHom V)
        (f.localizedRingedToposHom V)).toToposHom.adj.ofNatIsoLeft
      (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
        f.isMorphismOfSites))
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
      (Y := ringedTopos X) (Z := ringedTopos Y)
      f.ringedToposHom (X.localizationRingedToposHom (f.u.obj V))).toToposHom.adj

/-- **The square of Stacks 04J0 on structure sheaves.** The unit of `j_V^{-1} ⊣ j_{V,*}` at
`f_*O`, followed by the comparison of the two direct images, is `f_*` of the unit of
`j_{U'}^{-1} ⊣ j_{U',*}` at `O`. -/
theorem Hom.unit_localizedRingedSquareComparison (V : Y.C) :
    (Y.overMorphismOfTopoi V).adj.unit.app
          (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O)) ≫
        (f.localizedRingedSquareComparison V).hom.app
          ((ringedTopos (X.over (f.u.obj V))).forgetRing.obj (X.over (f.u.obj V)).O) =
      f.toposHom.pushforward.map
        ((X.overMorphismOfTopoi (f.u.obj V)).adj.unit.app
          ((ringedTopos X).forgetRing.obj X.O)) := by
  have := Functor.isContinuous_overPost_of_isContinuous Y.J X.J f.u V
  have hA : (((Y.overMorphismOfTopoi V).adj.comp (f.localized V).toposHom.adj).homEquiv
          (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O))
          ((X.J.overPullback (Type u) (f.u.obj V)).obj
            ((ringedTopos X).forgetRing.obj X.O))).symm
        ((Y.overMorphismOfTopoi V).adj.unit.app
          (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O))) =
      ((Over.post (X := V) f.u).sheafAdjunctionContinuous (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))).counit.app
        ((X.J.overPullback (Type u) (f.u.obj V)).obj
          ((ringedTopos X).forgetRing.obj X.O)) := by
    have htri : (f.localized V).toposHom.inverseImage.map
            ((Y.overMorphismOfTopoi V).inverseImage.map
              ((Y.overMorphismOfTopoi V).adj.unit.app
                (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O)))) ≫
          (f.localized V).toposHom.inverseImage.map
            ((Y.overMorphismOfTopoi V).adj.counit.app
              ((Y.overMorphismOfTopoi V).inverseImage.obj
                (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O)))) =
        𝟙 _ :=
      ((f.localized V).toposHom.inverseImage.map_comp _ _).symm.trans
        ((congrArg (f.localized V).toposHom.inverseImage.map
            ((Y.overMorphismOfTopoi V).adj.left_triangle_components _)).trans
          ((f.localized V).toposHom.inverseImage.map_id _))
    refine Eq.trans (Adjunction.homEquiv_symm_apply _ _ _ _) ?_
    refine Eq.trans (congrArg (fun z => ((Y.overMorphismOfTopoi V).inverseImage ⋙
        (f.localized V).toposHom.inverseImage).map
          ((Y.overMorphismOfTopoi V).adj.unit.app
            (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O))) ≫ z)
      (Adjunction.comp_counit_app _ _ _)) ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (f.localized V).toposHom.adj.counit.app
          ((X.J.overPullback (Type u) (f.u.obj V)).obj
            ((ringedTopos X).forgetRing.obj X.O))) htri).trans (Category.id_comp _))
  have hB : (((f.u.sheafAdjunctionContinuous (Type u) Y.J X.J).comp
          (X.overMorphismOfTopoi (f.u.obj V)).adj).homEquiv
          (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O))
          ((X.overMorphismOfTopoi (f.u.obj V)).inverseImage.obj
            ((ringedTopos X).forgetRing.obj X.O))).symm
        (f.toposHom.pushforward.map
          ((X.overMorphismOfTopoi (f.u.obj V)).adj.unit.app
            ((ringedTopos X).forgetRing.obj X.O))) =
      (X.overMorphismOfTopoi (f.u.obj V)).inverseImage.map
        ((f.u.sheafAdjunctionContinuous (Type u) Y.J X.J).counit.app
          ((ringedTopos X).forgetRing.obj X.O)) := by
    refine Eq.trans (Adjunction.homEquiv_symm_apply _ _ _ _) ?_
    rw [Adjunction.comp_counit_app]
    change (X.overMorphismOfTopoi (f.u.obj V)).inverseImage.map
          ((f.u.sheafPullback (Type u) Y.J X.J).map
            ((f.u.sheafPushforwardContinuous (Type u) Y.J X.J).map
              ((X.overMorphismOfTopoi (f.u.obj V)).adj.unit.app
                ((ringedTopos X).forgetRing.obj X.O)))) ≫ _ = _
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    rw [← CategoryTheory.Functor.map_comp, Adjunction.counit_naturality,
      CategoryTheory.Functor.map_comp, Category.assoc]
    exact (congrArg (fun z => (X.overMorphismOfTopoi (f.u.obj V)).inverseImage.map
        ((f.u.sheafAdjunctionContinuous (Type u) Y.J X.J).counit.app
          ((ringedTopos X).forgetRing.obj X.O)) ≫ z)
      ((X.overMorphismOfTopoi (f.u.obj V)).adj.left_triangle_components _)).trans
      (Category.comp_id _)
  have hmate := SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit
    Y.J X.J f.u V f.isMorphismOfSites ((ringedTopos X).forgetRing.obj X.O)
  refine ((AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
    (Y := ringedTopos X) (Z := ringedTopos Y) f.ringedToposHom
    (X.localizationRingedToposHom (f.u.obj V))).toToposHom.adj.homEquiv _ _).symm.injective ?_
  refine Eq.trans (Adjunction.homEquiv_symm_comp_rightAdjointUniq_hom_app _ _ _ _) ?_
  refine Eq.trans (congrArg (fun z =>
    (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
        f.isMorphismOfSites).inv.app
      (f.toposHom.pushforward.obj ((ringedTopos X).forgetRing.obj X.O)) ≫ z) hA) ?_
  refine Eq.trans ?_ hB.symm
  rw [← hmate]
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- With `U = u(V)`, the square
```
  (Sh(C/U), O_U)   --j_U-->  (Sh(C), O)
       | f'                     | f
  (Sh(D/V), O'_V)  --j_V-->  (Sh(D), O')
```
commutes, as a square of ringed topoi. -/
@[stacks 04J0 "(2): the commutative diagram of ringed topoi"]
noncomputable def Hom.localizedRingedSquare (V : Y.C) :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (X.over (f.u.obj V))) (B := ringedTopos Y)
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V)) (Z := ringedTopos Y)
        (Y.localizationRingedToposHom V) (f.localizedRingedToposHom V))
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos X) (Z := ringedTopos Y)
        f.ringedToposHom (X.localizationRingedToposHom (f.u.obj V))) where
  e := f.localizedRingedSquareComparison V
  commutes := by
    rw [f.forgetFSharp_localizationComp V, f.forgetFSharp_compLocalization V]
    exact (Category.assoc _ _ _).trans (congrArg (fun z =>
      AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom ≫ z)
      (f.unit_localizedRingedSquareComparison V))

end AlgebraicGeometry.RingedSite

end
