module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjectZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.HigherDirectImageSections
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImage

/-!
# Zariski cohomology over the affine objects of the small étale site

Let `a : X ⟶ Y` be a quasi-compact and quasi-separated morphism of the big étale site and `𝓕` a
quasi-coherent `𝒪_X`-module. For an affine object `V` of the small étale site of `Y`, the base
change `X ×_Y V` is an object of the small étale site of `X`, and the Zariski cohomology of the
pullback of `𝓕` to it is the module of sections of `V^* R^p a_* 𝓕`:

`Hᵖ(X ×_Y V, 𝓕) ≅ Γ(V, V^* R^p a_* 𝓕)`.

This is `Stacks.AlgebraicGeometry.HigherDirectImageSections.abelianCohomologyIso` for the
cartesian square of `X ×_Y V`, the morphism `V ⟶ Y` being étale and `V` affine. Its naturality in
`V`, against the pullback maps of [Stacks, Tag 01FA] on the left and the pullback of sections on
the right, is the hypothesis through which Descent, Lemma 071N is assembled
(`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIsoOfZariski`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.baseChangeCohomologyIso`: the isomorphism above.

## Main results

* `AlgebraicGeometry.SmallEtale.objPullbackCohomologyMap_comp_baseChangeCohomologyIso_hom`: its
  naturality in the affine object `V`.
* `AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIso`: Descent, Lemma 071N for
  the étale topology, `R^p a_{small,*}(𝓕^a) ≅ (R^p a_* 𝓕)^a`.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.HigherDirectImageSections

universe u

namespace AlgebraicGeometry

/-- **The pullback of sections along a morphism of schemes over `S` is the `g`-map on global
sections**, `AlgebraicGeometry.pullbackSectionsMap` read through
`Stacks.AlgebraicGeometry.HigherDirectImageSections.pullbackModuleMap`. -/
theorem pullbackSectionsMap_eq_sections_map {S : Scheme.{u}} (F : S.Modules) {A C : Over S}
    (g : A ⟶ C) :
    pullbackSectionsMap F g =
      (sections C.left).map (pullbackModuleMap A.hom C.hom g.left (Over.w g) F) := by
  have h₁ : ((Scheme.Modules.pullback A.hom).obj F).presheaf.map
      (eqToHom (show (⊤ : A.left.Opens) = g.left ⁻¹ᵁ ⊤ by simp)).op = 𝟙 _ :=
    (congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _)
  rw [pullbackSectionsMap, h₁]
  exact Category.comp_id _

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The cartesian square of the base change of an object `V` of the small étale site of `Y`
along `a`. -/
theorem isPullback_objHom_smallEtaleBaseChange (V : SmallEtale B Y.obj Y.property) :
    IsPullback (objHom B X.obj X.property ((smallEtaleBaseChange B a).obj V))
      (show objScheme B X.obj X.property ((smallEtaleBaseChange B a).obj V) ⟶
          (toScheme B Y.obj Y.property).obj V from
        B.inclusion.map (pullback.fst V.obj.hom a))
      (schemeHom B a) ((toOver B Y.obj Y.property).obj V).hom :=
  ((IsPullback.of_hasPullback V.obj.hom a).map B.inclusion).flip

variable [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]

/-- **Zariski cohomology over the base change of an affine object of the small étale site**:
for `V` affine in the small étale site of `Y`, `Hᵖ(X ×_Y V, 𝓕) ≅ Γ(V, V^* R^p a_* 𝓕)`, the left
side being the cohomology of the underlying abelian sheaf of the pullback of `𝓕`. -/
def baseChangeCohomologyIso (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] (p : ℕ)
    (V : SmallAffineEtale B Y.obj Y.property) :
    (((sheafSections (Opens.grothendieckTopology
        ↥(objScheme B X.obj X.property ((smallEtaleBaseChange B a).obj V.obj)))
        AddCommGrpCat.{u}).obj (op ⊤)).rightDerived p).obj
      ((SheafOfModules.toSheaf _).obj ((Scheme.Modules.pullback
        (objHom B X.obj X.property ((smallEtaleBaseChange B a).obj V.obj))).obj 𝓕)) ≅
      AddCommGrpCat.of Γ((Scheme.Modules.pullback ((toOver B Y.obj Y.property).obj V.obj).hom).obj
        (((Scheme.Modules.pushforward (schemeHom B a)).rightDerived p).obj 𝓕), ⊤) :=
  haveI : Etale ((toOver B Y.obj Y.property).obj V.obj).hom := V.obj.property
  have hF : Flat ((toOver B Y.obj Y.property).obj V.obj).hom := WeaklyEtale.flat
  have hA : AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj V.obj) := V.property
  @abelianCohomologyIso _ _ _ _ _ _ _ _ (isPullback_objHom_smallEtaleBaseChange B a V.obj) hF hA
    _ _ 𝓕 _ p

/-- **`AlgebraicGeometry.SmallEtale.baseChangeCohomologyIso` is natural in the affine object**:
for a morphism `g : V₁ ⟶ V₂` of affine objects of the small étale site of `Y`, it carries the
pullback map of [Stacks, Tag 01FA] on Zariski cohomology along `X ×_Y V₁ ⟶ X ×_Y V₂`
(`AlgebraicGeometry.SmallEtale.objPullbackCohomologyMap`) to the pullback of sections of
`V^* R^p a_* 𝓕` along `g` (`AlgebraicGeometry.pullbackSectionsMap`). -/
theorem objPullbackCohomologyMap_comp_baseChangeCohomologyIso_hom (𝓕 : X.obj.Modules)
    [𝓕.IsQuasicoherent] (p : ℕ) {V₁ V₂ : SmallAffineEtale B Y.obj Y.property} (g : V₁ ⟶ V₂) :
    objPullbackCohomologyMap ((smallEtaleBaseChange B a).map
        ((SmallAffineEtale.inclusion B Y.obj Y.property).map g)) 𝓕 p ≫
        (baseChangeCohomologyIso B a 𝓕 p V₁).hom =
      (baseChangeCohomologyIso B a 𝓕 p V₂).hom ≫
        pullbackSectionsMap (((Scheme.Modules.pushforward (schemeHom B a)).rightDerived p).obj 𝓕)
          ((toOver B Y.obj Y.property).map
            ((SmallAffineEtale.inclusion B Y.obj Y.property).map g)) := by
  let g' := (SmallAffineEtale.inclusion B Y.obj Y.property).map g
  let h' := (smallEtaleBaseChange B a).map g'
  have : Etale (objMap h') := etale_toScheme_map h'
  have hF (V : SmallAffineEtale B Y.obj Y.property) :
      Flat ((toOver B Y.obj Y.property).obj V.obj).hom :=
    haveI : Etale ((toOver B Y.obj Y.property).obj V.obj).hom := V.obj.property
    WeaklyEtale.flat
  have hφ : objMap h' ≫ B.inclusion.map (pullback.fst V₂.obj.obj.hom a) =
      B.inclusion.map (pullback.fst V₁.obj.obj.hom a) ≫ ((toOver B Y.obj Y.property).map g').left :=
    (isPullback_toScheme_smallEtaleBaseChange B a g').w
  have hN := @abelianPullback_comp_abelianCohomologyIso_hom _ _ _ _ _ _ _ _ _ _ _ _ _
    ((toOver B Y.obj Y.property).map g').left (objMap h')
    (isPullback_objHom_smallEtaleBaseChange B a V₁.obj)
    (isPullback_objHom_smallEtaleBaseChange B a V₂.obj) (hF V₁) (hF V₂) V₁.property
    V₂.property _ _ WeaklyEtale.flat
    hφ (Over.w ((toOver B Y.obj Y.property).map g')) (objMap_comp_objHom h') 𝓕 _ p
  rw [pullbackSectionsMap_eq_sections_map]
  have t (V : SmallAffineEtale B Y.obj Y.property) : (baseChangeCohomologyIso B a 𝓕 p V).hom =
      (@abelianCohomologyIso _ _ _ _ _ _ _ _ (isPullback_objHom_smallEtaleBaseChange B a V.obj)
        (hF V) V.property _ _ 𝓕 _ p).hom := rfl
  have t₃ : objModuleMap h' 𝓕 = pullbackModuleMap _ _ (objMap h') (objMap_comp_objHom h') 𝓕 := rfl
  rw [t V₁, t V₂]
  unfold objPullbackCohomologyMap
  rw [t₃]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (hN.trans ?_)) <;> rfl

/-- **Descent, Lemma 071N, for the étale topology**: for a quasi-compact and quasi-separated
morphism `a` of the big étale site and a quasi-coherent `𝒪_X`-module `𝓕`,
`R^p a_{small,*}(𝓕^a) ≅ (R^p a_* 𝓕)^a` on the small étale site of `Y`, assembled by
`AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIsoOfZariski` from
`AlgebraicGeometry.SmallEtale.baseChangeCohomologyIso` and its naturality. -/
@[stacks 071N "the étale topology"]
def higherDirectImageAssociatedSheafIso (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] (p : ℕ) :
    ((Stacks.HigherDirectImage.pushforward.{u, u} B a).rightDerived p).obj
        ((associatedSheaf B X).obj 𝓕) ≅
      (associatedSheaf B Y).obj
        (((Scheme.Modules.pushforward (schemeHom B a)).rightDerived p).obj 𝓕) :=
  higherDirectImageAssociatedSheafIsoOfZariski B a 𝓕 p _ (baseChangeCohomologyIso B a 𝓕 p)
    (objPullbackCohomologyMap_comp_baseChangeCohomologyIso_hom B a 𝓕 p)

end AlgebraicGeometry.SmallEtale
