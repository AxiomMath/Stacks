module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.Basic
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.ModuleProduct
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Family.PullbackExact
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Over

/-!
# The ringed site of a semi-representable object over an object

Let `X` be a ringed site, let `Y` be an object of its underlying site and let `K = {U i / Y}` be
a semi-representable object over `Y`, that is, a formal coproduct of objects of `C / Y`; the
Stacks Project writes `SR(C, Y)` for these. Combining the localization of a ringed site at a
semi-representable object with the localization of a site at an object gives:

1. the ringed site `(C / K, O_K)`, which is the ringed site of the underlying semi-representable
   object of `C` and needs nothing new;
2. the decomposition `Mod(O_K) = ∏ Mod(O_{U i})`, likewise;
3. the localization morphism `j : (Sh(C / K), O_K) ⟶ (Sh(C / Y), O_Y)` of ringed topoi, whose
   underlying geometric morphism is restriction along the componentwise localization functor
   `C / K ⥤ C / Y` and whose structure map is the canonical identity comparison of the two
   restrictions of `O_X`;
4. the morphism of ringed topoi attached to a morphism `K ⟶ L` of `SR(C, Y)`.

The results of Stacks 0D9U hold here too: the localization morphism is flat, its pullback of
sheaves of modules is exact, and that pullback has a left adjoint `j_!`.

## Main definitions

* `AlgebraicGeometry.RingedSite.underlyingFormalCoproduct`: the semi-representable object of `C`
  underlying one over `Y`.
* `AlgebraicGeometry.RingedSite.localizationToposMorphismOver`: the geometric morphism
  `Sh(C / K) ⟶ Sh(C / Y)`.
* `AlgebraicGeometry.RingedSite.localizationStructureIsoOver`: the identification of the inverse
  image of `O_Y` with `O_K`.
* `AlgebraicGeometry.RingedSite.localizationMorphismOver`: the localization morphism of ringed
  topoi, part (3).
* `AlgebraicGeometry.RingedSite.familyMorphismOver`: the morphism of ringed topoi attached to a
  morphism of `SR(C, Y)`, part (4).

## Main results

* `AlgebraicGeometry.RingedSite.componentwiseLocalizationFunctor_comp_forget`: the componentwise
  localization functor to `C / Y`, followed by the slice projection, is the componentwise
  localization functor to `C`.
* `AlgebraicGeometry.RingedSite.localizationToposMorphismOver_inverseImage` and
  `AlgebraicGeometry.RingedSite.forgetRing_localizationMorphismOver_fSharpInverseImage`: the
  inverse image of the localization morphism is restriction along the componentwise localization
  functor, and its structure map is the canonical identity comparison.
* `AlgebraicGeometry.RingedSite.localizationMorphismOver_isFlat`,
  `AlgebraicGeometry.RingedSite.localizationMorphismOver_pullback_exact`,
  `AlgebraicGeometry.RingedSite.localizationMorphismOver_pullback_isRightAdjoint`: the
  localization morphism is flat, its pullback of sheaves of modules is exact, and that pullback
  has a left adjoint, so that the lower shriek
  `AlgebraicGeometry.RingedToposHom.lowerShriekModules` is available for it.
* `AlgebraicGeometry.RingedSite.familyMorphismOver_inverseImage`,
  `AlgebraicGeometry.RingedSite.familyMorphismOver_isFlat`,
  `AlgebraicGeometry.RingedSite.familyMorphismOver_pullback_exact`,
  `AlgebraicGeometry.RingedSite.familyMorphismOver_pullback_isRightAdjoint`: the same four
  statements for the morphism attached to a morphism of `SR(C, Y)`.

## Implementation notes

The site `C / K` is the disjoint union of the slice sites `C / U i` of `C` — not of the slice
sites of `C / Y` — so parts (1), (2) and (4) are the constructions of Stacks 0D9U applied to the
underlying semi-representable object of `C`, and the structural maps to `Y` enter only through
part (3). Accordingly parts (1) and (2) are recorded on the declarations of Stacks 0D9U with
`add_to_stacks`, and part (4) is the morphism of Stacks 0D9U attached to the induced morphism of
underlying semi-representable objects.

The localization morphism is given as a morphism together with lemmas pinning down its inverse
image and its structure map, rather than as an element of a subtype as in
`AlgebraicGeometry.RingedSite.familyMorphism`: the existence of the lower shriek is proved by
recognising the inverse image as restriction along a continuous functor, and that recognition has
to hold definitionally rather than only up to a propositional equation. The same recognition for
`familyMorphismOver` is `familyMorphismOver_inverseImage`, which holds by `rfl` because the
subtype of Stacks 0D9U is built from an explicitly given morphism.

That the structure map is the canonical identity comparison is recorded in the same form as for
Stacks 0D9U, as an equality with an `eqToHom` between the underlying sheaves of sets. The two
restrictions of `O_X` are equal rather than merely isomorphic because the componentwise
localization functor followed by the slice projection `C / Y ⥤ C` *is* the componentwise
localization functor `C / K ⥤ C`, which is
`AlgebraicGeometry.RingedSite.componentwiseLocalizationFunctor_comp_forget`.

Flatness is stated as flatness of the inverse-image structure map,
`AlgebraicGeometry.SheafOfModules.IsFlatMapULift`, which is what the exactness criterion
consumes and what the flatness predicate for a morphism of ringed topoi unfolds to.

The sections of the structure sheaf live in the universe `max u v w` containing the site and the
index type of the family: the right adjoint of restriction and the sheafification of presheaves
of abelian groups both need the sections to accommodate the site, and the left adjoint of the
inverse image of sheaves of modules needs `C / K` to be essentially small there.

## References

* [Stacks Project, Tag 0D9V](https://stacks.math.columbia.edu/tag/0D9V)
* [Stacks Project, Tag 0D9U](https://stacks.math.columbia.edu/tag/0D9U)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SemiRepresentable
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedSite

universe w v u

attribute [local instance] componentwiseTopology_hasSheafCompose_forget₂
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

/-- The semi-representable object of `C` underlying a semi-representable object over `Y`: its
components are the domains of the structural maps of the components of `K`, and the structural
maps themselves are forgotten. -/
abbrev underlyingFormalCoproduct (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) : FormalCoproduct.{w} X.C :=
  ⟨K.I, fun i => (K.obj i).left⟩

/-- The localization datum of the underlying semi-representable object of `C`: both of its
semi-representable objects are `underlyingFormalCoproduct X K` and the morphism between them is
the identity, so that only its localization functor `C / K ⥤ C` and its topology on `C / K`
enter. These are the functor and the topology that `O_K` is defined by. -/
abbrev underlyingLocalizationSites (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) : LocalizationSites.{w} X.C X.J :=
  ⟨underlyingFormalCoproduct X K, underlyingFormalCoproduct X K, 𝟙 _⟩

/-- The componentwise localization functor `C / K ⥤ C` of the underlying semi-representable
object is continuous from the componentwise topology to `J`. This is
`CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor_isContinuous` with the
topology on `C / K` spelled as a `componentwiseTopology`. -/
theorem underlyingLocalizationFunctor_isContinuous (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    (underlyingLocalizationSites X K).localizationFunctor.IsContinuous
      (componentwiseTopology X.J (underlyingFormalCoproduct X K)) X.J := by
  simpa [LocalizationSites.sourceTopology] using
    LocalizationSites.localizationFunctor_isContinuous (underlyingLocalizationSites X K)

attribute [local instance] underlyingLocalizationFunctor_isContinuous

/-- On objects, the componentwise localization functor `C / K ⥤ C / Y` followed by the slice
projection is the componentwise localization functor `C / K ⥤ C`. -/
theorem componentwiseLocalizationFunctor_comp_forget_obj
    (X : RingedSite.{u, v, max u v w}) {Y : X.C} (K : FormalCoproduct.{w} (Over Y))
    (Z : ComponentOver (underlyingFormalCoproduct X K)) :
    (componentwiseLocalizationFunctor K ⋙ Over.forget Y).obj Z =
      (underlyingLocalizationSites X K).localizationFunctor.obj Z := by
  rcases Z with ⟨i, V⟩
  rfl

/-- On morphisms, the componentwise localization functor `C / K ⥤ C / Y` followed by the slice
projection is the componentwise localization functor `C / K ⥤ C`. -/
theorem componentwiseLocalizationFunctor_comp_forget_map
    (X : RingedSite.{u, v, max u v w}) {Y : X.C} (K : FormalCoproduct.{w} (Over Y))
    (Z W : ComponentOver (underlyingFormalCoproduct X K)) (a : Z ⟶ W) :
    (componentwiseLocalizationFunctor K ⋙ Over.forget Y).map a ≍
      (underlyingLocalizationSites X K).localizationFunctor.map a := by
  rcases Z with ⟨i, V⟩
  cases a with | mk a => rfl

/-- **The componentwise localization functor `C / K ⥤ C / Y`, followed by the slice projection
`C / Y ⥤ C`, is the componentwise localization functor `C / K ⥤ C`.** On the component indexed
by `i` both are the slice projection of `C / U i`. This is what makes the structure sheaf `O_K`
of the underlying semi-representable object also the restriction of `O_Y`. -/
theorem componentwiseLocalizationFunctor_comp_forget (X : RingedSite.{u, v, max u v w})
    {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    componentwiseLocalizationFunctor K ⋙ Over.forget Y =
      (underlyingLocalizationSites X K).localizationFunctor :=
  CategoryTheory.Functor.hext (componentwiseLocalizationFunctor_comp_forget_obj X K)
    (componentwiseLocalizationFunctor_comp_forget_map X K)

/-- **Stacks 0D9V, part (3).** The geometric morphism `Sh(C / K) ⟶ Sh(C / Y)` underlying the
localization morphism of a semi-representable object `K` over `Y`: its inverse image is
restriction along the componentwise localization functor `C / K ⥤ C / Y` and its direct image is
the right adjoint of that restriction. -/
@[stacks 0D9V "part (3): the geometric morphism underlying the localization over Y"]
noncomputable def localizationToposMorphismOver (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    MorphismOfTopoi
      (Sheaf (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (Type (max u v w)))
      (Sheaf (X.J.over Y) (Type (max u v w))) where
  inverseImage := (componentwiseLocalizationFunctor K).sheafPushforwardContinuous
    (Type (max u v w)) (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y)
  pushforward := (componentwiseLocalizationFunctor K).sheafPushforwardCocontinuous
    (Type (max u v w)) (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y)
  adj := (componentwiseLocalizationFunctor K).sheafAdjunctionCocontinuous
    (Type (max u v w)) (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y)
  preservesFiniteLimits := inferInstance

/-- The inverse image of the localization morphism over `Y` is restriction along the
componentwise localization functor `C / K ⥤ C / Y`. -/
theorem localizationToposMorphismOver_inverseImage (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    (localizationToposMorphismOver X K).inverseImage =
      (componentwiseLocalizationFunctor K).sheafPushforwardContinuous
        (Type (max u v w)) (componentwiseTopology X.J (underlyingFormalCoproduct X K))
        (X.J.over Y) :=
  rfl

/-- **Stacks 0D9V, part (3).** The structure map of the localization morphism over `Y`, in
inverse-image form: the inverse image of `O_Y` along restriction is the restriction of `O_Y`,
and that restriction is `O_K` because the composite of the componentwise localization functor
with the slice projection is the componentwise localization functor to `C`. -/
@[stacks 0D9V "part (3): the structure map of the localization over Y"]
noncomputable def localizationStructureIsoOver (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    (inverseImageCommRingFunctor (localizationToposMorphismOver X K)).obj
        (ringedTopos.{max u v, v, w} (X.over Y)).O ≅
      (localizationRingedTopos X (underlyingFormalCoproduct X K)).O := by
  dsimp [localizationRingedTopos, localizationStructureSheaf, ringedTopos, over]
  exact restrictionCommRingIso
      (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y)
      (componentwiseLocalizationFunctor K)
      (((Over.forget Y).sheafPushforwardContinuous CommRingCat.{max u v w}
        (X.J.over Y) X.J).obj X.O) ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (F := componentwiseLocalizationFunctor K) (G := Over.forget Y)
      (FG := (underlyingLocalizationSites X K).localizationFunctor)
      (eqToIso (componentwiseLocalizationFunctor_comp_forget X K))
      CommRingCat.{max u v w}
      (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y) X.J).app X.O

/-- **Stacks 0D9V, part (3).** The localization morphism
`j : (Sh(C / K), O_K) ⟶ (Sh(C / Y), O_Y)` of ringed topoi attached to a semi-representable
object `K` over `Y`: its geometric morphism is restriction along the componentwise localization
functor and its structure map is the canonical identity comparison of structure sheaves. -/
@[stacks 0D9V "part (3): the localization morphism of ringed topoi over Y"]
noncomputable def localizationMorphismOver (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    RingedToposHom (localizationRingedTopos X (underlyingFormalCoproduct X K))
      (ringedTopos.{max u v, v, w} (X.over Y)) where
  toToposHom := localizationToposMorphismOver X K
  fSharp := ((commRingImageAdjunction (localizationToposMorphismOver X K)).homEquiv _ _)
    (localizationStructureIsoOver X K).hom

/-- The inverse-image structure map of the localization morphism over `Y` is the isomorphism
`localizationStructureIsoOver`, being its transpose. -/
private theorem localizationMorphismOver_fSharpInverseImage_eq (X : RingedSite.{u, v, max u v w})
    {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    (localizationMorphismOver X K).fSharpInverseImage = (localizationStructureIsoOver X K).hom :=
  Equiv.symm_apply_apply _ _

/-- The structure map of the localization morphism over `Y` is an isomorphism: it is the
transpose of the isomorphism `localizationStructureIsoOver`. -/
instance isIso_localizationMorphismOver_fSharpInverseImage (X : RingedSite.{u, v, max u v w})
    {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    IsIso (localizationMorphismOver X K).fSharpInverseImage := by
  change IsIso
    (((commRingImageAdjunction (localizationToposMorphismOver X K)).homEquiv _ _).symm
      (((commRingImageAdjunction (localizationToposMorphismOver X K)).homEquiv _ _)
        (localizationStructureIsoOver X K).hom))
  simpa only [Equiv.symm_apply_apply] using (localizationStructureIsoOver X K).isIso_hom

/-- The inverse image of `O_Y` along the localization morphism over `Y` and `O_K` have the same
underlying sheaf of sets: both are the restriction of the underlying sheaf of sets of `O_X`
along the componentwise localization functor `C / K ⥤ C`. -/
theorem forgetRing_inverseImage_structureSheaf_over (X : RingedSite.{u, v, max u v w})
    {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    (localizationRingedTopos X (underlyingFormalCoproduct X K)).forgetRing.obj
        ((inverseImageCommRingFunctor (localizationToposMorphismOver X K)).obj
          (ringedTopos.{max u v, v, w} (X.over Y)).O) =
      (localizationRingedTopos X (underlyingFormalCoproduct X K)).forgetRing.obj
        (localizationRingedTopos X (underlyingFormalCoproduct X K)).O := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  have hobj : ∀ Z,
      ((localizationRingedTopos X (underlyingFormalCoproduct X K)).forgetRing.obj
        ((inverseImageCommRingFunctor (localizationToposMorphismOver X K)).obj
          (ringedTopos.{max u v, v, w} (X.over Y)).O)).obj.obj Z =
      ((localizationRingedTopos X (underlyingFormalCoproduct X K)).forgetRing.obj
        (localizationRingedTopos X (underlyingFormalCoproduct X K)).O).obj.obj Z := by
    rintro ⟨⟨i, V⟩⟩
    rfl
  refine CategoryTheory.Functor.hext hobj fun Z W a => ?_
  have hm := eq_of_heq (componentwiseLocalizationFunctor_comp_forget_map X K
    (Opposite.unop W) (Opposite.unop Z) (Opposite.unop a))
  have hZ := hobj Z
  have hW := hobj W
  cases Z with
  | op Z =>
    cases W with
    | op W =>
      cases Z
      cases W
      cases hZ
      cases hW
      dsimp [localizationRingedTopos, RingedTopos.forgetRing, localizationStructureSheaf,
        ringedTopos, over, inverseImageCommRingFunctor, pullbackCommRingSheafFunctor,
        pullbackCommRingSheaf]
      change (forget CommRingCat.{max u v w}).map
          (X.O.obj.map ((componentwiseLocalizationFunctor K ⋙ Over.forget Y).op.map a)) ≍
        (forget CommRingCat.{max u v w}).map
          (X.O.obj.map ((underlyingLocalizationSites X K).localizationFunctor.op.map a))
      exact heq_of_eq (congrArg
        (fun b => (forget CommRingCat.{max u v w}).map (X.O.obj.map (Opposite.op b))) hm)

/-- **Stacks 0D9V, part (3).** The structure map of the localization morphism over `Y` is the
canonical identity comparison: on underlying sheaves of sets it is the identification
`forgetRing_inverseImage_structureSheaf_over` and nothing more. -/
@[stacks 0D9V "part (3): the structure map of the localization over Y is the identity"]
theorem forgetRing_localizationMorphismOver_fSharpInverseImage
    (X : RingedSite.{u, v, max u v w}) {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    (localizationRingedTopos X (underlyingFormalCoproduct X K)).forgetRing.map
        (localizationMorphismOver X K).fSharpInverseImage =
      eqToHom (forgetRing_inverseImage_structureSheaf_over X K) := by
  rw [localizationMorphismOver_fSharpInverseImage_eq]
  apply Sheaf.hom_ext
  rw [ObjectProperty.eqToHom_hom]
  ext Z x
  cases Z with
  | op Z =>
    cases Z with
    | mk i V =>
      change ((forget CommRingCat.{max u v w}).map
          (X.O.obj.map
            ((eqToHom (componentwiseLocalizationFunctor_comp_forget X K).symm).app
              ⟨i, V⟩).op)) x = _
      rw [eqToHom_app, eqToHom_app]
      change ((forget CommRingCat.{max u v w}).map (X.O.obj.map (𝟙 _))) x = _
      exact congrArg (fun b : X.O.obj.obj (Opposite.op V.left) ⟶
          X.O.obj.obj (Opposite.op V.left) =>
        ((forget CommRingCat.{max u v w}).map b) x)
        (X.O.obj.map_id (Opposite.op V.left))

/-- **Stacks 0D9V.** The localization morphism over `Y` is flat: its inverse-image structure map
is an isomorphism, and an isomorphism of sheaves of commutative rings is flat. -/
@[stacks 0D9V "flatness of the localization morphism over Y"]
theorem localizationMorphismOver_isFlat (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      (localizationMorphismOver X K).fSharpInverseImage := by
  unfold AlgebraicGeometry.SheafOfModules.IsFlatMapULift
  exact SheafOfModules.isFlatMap_of_isIso
    ((AlgebraicGeometry.SheafOfModules.sheafULift
      (componentwiseTopology X.J (underlyingFormalCoproduct X K))).map
      (localizationMorphismOver X K).fSharpInverseImage)

/-- **Stacks 0D9V.** Pullback of sheaves of modules along the localization morphism over `Y` is
exact, the morphism being flat. -/
@[stacks 0D9V "exactness of the pullback of modules along the localization over Y"]
theorem localizationMorphismOver_pullback_exact (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    (K : FormalCoproduct.{w} (Over Y)) :
    exactFunctor _ _ ((localizationMorphismOver X K).toRingedToposModulesHom.pullbackModules) :=
  Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (localizationMorphismOver X K) (localizationMorphismOver_isFlat X K)

/-- **Stacks 0D9V.** Pullback of sheaves of modules along the localization morphism over `Y`
has a left adjoint `j_!`, namely `AlgebraicGeometry.RingedToposHom.lowerShriekModules` of that
morphism: the structure map is an isomorphism, and the inverse image of sheaves of modules is
restriction along the componentwise localization functor, which has a left adjoint because
`C / K` is essentially small. -/
@[stacks 0D9V "the left adjoint of the pullback of modules along the localization over Y"]
theorem localizationMorphismOver_pullback_isRightAdjoint (X : RingedSite.{u, v, max u v w})
    {Y : X.C} (K : FormalCoproduct.{w} (Over Y)) :
    (localizationMorphismOver X K).toModulesHom.pullbackModules.IsRightAdjoint :=
  AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules
    (localizationMorphismOver X K)
    (Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction
      (componentwiseTopology X.J (underlyingFormalCoproduct X K)) (X.J.over Y)
      (componentwiseLocalizationFunctor K) _)

/-- **Stacks 0D9V, part (4).** The morphism of ringed topoi
`(Sh(C / K), O_K) ⟶ (Sh(C / L), O_L)` attached to a morphism `K ⟶ L` of semi-representable
objects over `Y`: it is the morphism of Stacks 0D9U attached to the induced morphism of the
underlying semi-representable objects of `C`, since neither the two localization sites nor their
structure sheaves see the structural maps to `Y`. Its inverse image and its structure map are
specified by `AlgebraicGeometry.RingedSite.familyMorphism`. -/
@[stacks 0D9V "part (4): the morphism of ringed topoi attached to a morphism of SR(C, Y)"]
noncomputable def familyMorphismOver (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    {K L : FormalCoproduct.{w} (Over Y)} (f : K ⟶ L) :
    RingedToposHom (localizationRingedTopos X (underlyingFormalCoproduct X K))
      (localizationRingedTopos X (underlyingFormalCoproduct X L)) :=
  (familyMorphism.{w, v, u, u} X
    (⟨f.f, fun i => (f.φ i).left⟩ :
      underlyingFormalCoproduct X K ⟶ underlyingFormalCoproduct X L)).val

/-- The inverse image of the morphism attached to a morphism of `SR(C, Y)` is restriction along
the componentwise relocalization functor. This is the first clause of the specification carried
by `AlgebraicGeometry.RingedSite.familyMorphism`, with the whiskering by `sheafToPresheaf`
cancelled. -/
theorem familyMorphismOver_inverseImage (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    {K L : FormalCoproduct.{w} (Over Y)} (f : K ⟶ L) :
    letI S : LocalizationSites.{w} X.C X.J :=
      ⟨underlyingFormalCoproduct X K, underlyingFormalCoproduct X L,
        ⟨f.f, fun i => (f.φ i).left⟩⟩
    haveI : S.relocalizationFunctor.IsContinuous
        (componentwiseTopology X.J (underlyingFormalCoproduct X K))
        (componentwiseTopology X.J (underlyingFormalCoproduct X L)) :=
      LocalizationSites.relocalizationFunctor_isContinuous S
    (familyMorphismOver X f).toToposHom.inverseImage =
      S.relocalizationFunctor.sheafPushforwardContinuous (Type (max u v w))
        (componentwiseTopology X.J (underlyingFormalCoproduct X K))
        (componentwiseTopology X.J (underlyingFormalCoproduct X L)) :=
  rfl

/-- **Stacks 0D9V.** The morphism attached to a morphism of `SR(C, Y)` is flat. This is the
corresponding clause of Stacks 0D9U for the induced morphism of underlying semi-representable
objects of `C`. -/
@[stacks 0D9V "flatness of the morphism attached to a morphism of SR(C, Y)"]
theorem familyMorphismOver_isFlat (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    {K L : FormalCoproduct.{w} (Over Y)} (f : K ⟶ L) :
    AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      (familyMorphismOver X f).fSharpInverseImage :=
  familyMorphism_isFlat.{w, v, u, u} X
    (⟨f.f, fun i => (f.φ i).left⟩ :
      underlyingFormalCoproduct X K ⟶ underlyingFormalCoproduct X L)

/-- **Stacks 0D9V.** Pullback of sheaves of modules along the morphism attached to a morphism of
`SR(C, Y)` is exact, that morphism being flat. -/
@[stacks 0D9V "exactness of the pullback of modules along a morphism of SR(C, Y)"]
theorem familyMorphismOver_pullback_exact (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    {K L : FormalCoproduct.{w} (Over Y)} (f : K ⟶ L) :
    exactFunctor _ _ ((familyMorphismOver X f).toRingedToposModulesHom.pullbackModules) :=
  Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (familyMorphismOver X f) (familyMorphismOver_isFlat X f)

/-- **Stacks 0D9V.** Pullback of sheaves of modules along the morphism attached to a morphism of
`SR(C, Y)` has a left adjoint `f_!`, namely
`AlgebraicGeometry.RingedToposHom.lowerShriekModules` of that morphism: the structure map is an
isomorphism and the inverse image of sheaves of modules is restriction along the componentwise
relocalization functor, which has a left adjoint because `C / K` is essentially small. -/
@[stacks 0D9V "the left adjoint of the pullback of modules along a morphism of SR(C, Y)"]
theorem familyMorphismOver_pullback_isRightAdjoint (X : RingedSite.{u, v, max u v w}) {Y : X.C}
    {K L : FormalCoproduct.{w} (Over Y)} (f : K ⟶ L) :
    (familyMorphismOver X f).toModulesHom.pullbackModules.IsRightAdjoint := by
  let S : LocalizationSites.{w} X.C X.J :=
    ⟨underlyingFormalCoproduct X K, underlyingFormalCoproduct X L,
      ⟨f.f, fun i => (f.φ i).left⟩⟩
  have hcont : S.relocalizationFunctor.IsContinuous
      (componentwiseTopology X.J (underlyingFormalCoproduct X K))
      (componentwiseTopology X.J (underlyingFormalCoproduct X L)) :=
    LocalizationSites.relocalizationFunctor_isContinuous S
  have : IsIso (familyMorphismOver X f).fSharpInverseImage :=
    (familyMorphism.{w, v, u, u} X
      (⟨f.f, fun i => (f.φ i).left⟩ :
        underlyingFormalCoproduct X K ⟶ underlyingFormalCoproduct X L)).property.2.2
  exact AlgebraicGeometry.RingedToposHom.isRightAdjoint_pullbackModules
    (familyMorphismOver X f)
    (Stacks.Sheaves.ToposPullback.isRightAdjoint_pullbackModuleFunctor_restriction
      (componentwiseTopology X.J (underlyingFormalCoproduct X K))
      (componentwiseTopology X.J (underlyingFormalCoproduct X L)) S.relocalizationFunctor _)

end AlgebraicGeometry.RingedSite

end

/-! ### Parts (1) and (2) of Stacks 0D9V

The ringed site `(C / K, O_K)` and the decomposition `Mod(O_K) = ∏ Mod(O_{U i})` of a
semi-representable object over `Y` are those of its underlying semi-representable object of `C`,
which are the corresponding clauses of Stacks 0D9U: the componentwise localization site and its
structure sheaf are built from the component objects `U i` alone. -/

add_to_stacks 0D9V "part (1): the structure sheaf O_K"
  AlgebraicGeometry.RingedSite.localizationStructureSheaf

add_to_stacks 0D9V "part (1): the ringed site (C / K, O_K)"
  AlgebraicGeometry.RingedSite.localization

add_to_stacks 0D9V "part (2): the decomposition of Mod(O_K) into componentwise modules"
  AlgebraicGeometry.RingedSite.moduleSheavesProductEquivalence
