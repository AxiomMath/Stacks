module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposRingImageComposition
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedMorphismsLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.FlatMapIsoInvariance

/-!
# Flatness of a morphism of ringed sites is inherited by its localization

Let `(f, f^♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C` which is a morphism of sites, let `V` be an object of `D` and put `U = u(V)`. Stacks
04J0 localizes `f` to `f' : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)`. Flatness of a morphism of ringed
topoi is, by Stacks 04JB, flatness of the structure map in inverse-image form; this file proves
that `f'` is flat as soon as `f` is.

The structure map of `f'` in inverse-image form is `j_U^{-1}` of the structure map of `f`, read
between the comparison of Stacks 03CF clause (b) and the identification of the localized
structure sheaf with a restriction. Both of those are isomorphisms, so flatness of `f'` is
flatness of a restriction of the structure map of `f`, and restriction to a slice is an inverse
image along a morphism of topoi, which carries flatness along.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isFlatMapULift_localizedRingedToposHom_fSharpInverseImage`:
  the localized morphism of ringed topoi of Stacks 04J0 is flat as soon as the morphism it
  localizes is.
* `AlgebraicGeometry.RingedSite.Hom.isFlatMapULift_localized_ringedToposHom_fSharpInverseImage`:
  the same statement spelled with `(f.localized V).ringedToposHom` in place of
  `f.localizedRingedToposHom V`.

## Implementation notes

The localized structure map is computed at the level of sheaves of *commutative rings* from its
computation after forgetting to sheaves of sets,
`AlgebraicGeometry.RingedSite.Hom.fSharpSet_localizedRingedToposHom`, by promotion:
`CategoryTheory.sheafCompose` along `forget CommRingCat` is faithful, so an equation of morphisms of
sheaves of commutative rings may be checked on underlying sheaves of sets, and every comparison the
commutative-ring-level factorization is built from is the identity there — the comparison with
restriction (`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`), the comparison of iterated
inverse images (`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafComp`) and, for clause (b), the
transport of the ring operations along a natural isomorphism of inverse images
(`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso`), whose underlying map of sheaves
of sets is that natural isomorphism on the nose.

Several things are written out that look as though unification should supply them. The four
left-exactness facts are given as local instances because the inverse images involved are fields of
a `MorphismOfTopoi` and are not found by instance search through the definitions that package them.
The factorization is assembled in term mode rather than by `rw` or `simp`: the comparisons identify
sheaves of commutative rings whose underlying sheaves of sets are *equal* rather than merely
isomorphic, so a rewrite that replaces one of them by an identity leaves a goal that is type-correct
only at the default transparency, which `simp`'s congruence check does not use.

That same coincidence governs how the identities are spelled. Each comparison that becomes an
identity has, on underlying sheaves of sets, a source and a target that are the same sheaf but
not the same expression, so the identity replacing it is read at both ends. Spelled as the
inverse image of a sheaf of commutative rings, those two ends have the same head and different
arguments, and comparing them means unfolding the whole construction of the inverse image;
spelled as a functor applied to an object, the heads differ and each end is settled directly.
The second spelling is used throughout, and the collapse of the resulting composite is split off
into `forget_localizedSourceIso_factors` so that the two halves do not share one heartbeat
budget.

The localizing comparison is stated without an ascribed type, so that its type is the one its
body has; an ascription in any other spelling of the same sheaves is what makes the assembly
fail. For the same reason the universe list of
`AlgebraicGeometry.SheafOfModules.IsFlatMap` is written out where the unlifted predicate is
named: left to unification it is solved with fresh universe metavariables rather than with the
site's own universe.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedSite.Hom

attribute [local instance] CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The inverse image of the localized morphism of sites is left exact: it is the inverse image
of the morphism of topoi underlying the localized morphism of ringed sites. -/
private instance preservesFiniteLimitsPost :
    PreservesFiniteLimits ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
      (X.J.over (f.u.obj V))) :=
  (f.localized V).toposHom.preservesFiniteLimits

/-- Restriction to the slice over `V` followed by the inverse image of the localized morphism is
left exact. -/
private instance preservesFiniteLimitsPostComp :
    PreservesFiniteLimits (Y.J.overPullback (Type u) V ⋙
      (Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
        (X.J.over (f.u.obj V))) :=
  comp_preservesFiniteLimits _ _

/-- The inverse image of `f` is left exact: it is the inverse image of the morphism of topoi
underlying `f`. -/
private instance preservesFiniteLimitsSheafPullback :
    PreservesFiniteLimits (f.u.sheafPullback (Type u) Y.J X.J) :=
  f.toposHom.preservesFiniteLimits

/-- The inverse image of `f` followed by restriction to the slice over `U = u(V)` is left
exact. -/
private instance preservesFiniteLimitsPullbackComp :
    PreservesFiniteLimits (f.u.sheafPullback (Type u) Y.J X.J ⋙
      X.J.overPullback (Type u) (f.u.obj V)) :=
  comp_preservesFiniteLimits _ _

/-- **Stacks 03CF clause (b) on structure sheaves of commutative rings.** The inverse image
along the localized morphism of the localized structure sheaf of the target is the inverse image
of `O'` along `f`, restricted to the slice over `U = u(V)`.

The localized structure sheaf is a restriction, which the inverse image of sheaves of
commutative rings identifies with the transport of the ring operations along restriction of
sheaves of sets; the two iterated inverse images are then compared with single ones, and clause
(b) of Stacks 03CF compares those. -/
private def localizedSourceIso :=
  (pullbackCommRingSheafFunctor (X.J.over (f.u.obj V))
        ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V)))).mapIso
      (restrictionCommRingIso (Y.J.over V) Y.J (Over.forget V) Y.O).symm ≪≫
    pullbackCommRingSheafComp (Y.J.over V) (X.J.over (f.u.obj V))
        (Y.J.overPullback (Type u) V)
        ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))) Y.O ≪≫
    pullbackCommRingSheafIsoOfNatIso (X.J.over (f.u.obj V))
        (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites) Y.O ≪≫
    (pullbackCommRingSheafComp X.J (X.J.over (f.u.obj V)) f.toposHom.inverseImage
        (X.J.overPullback (Type u) (f.u.obj V)) Y.O).symm


/-- The identification of the localized structure sheaf of the target with a restriction is the
identity on underlying sheaves of sets, so its inverse image along the localized morphism is the
inverse image of an identity. -/
private theorem forget_restrictionInv :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (pullbackCommRingSheafMap (X.J.over (f.u.obj V))
          ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V)))
          (restrictionCommRingIso (Y.J.over V) Y.J (Over.forget V) Y.O).inv) =
      ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
          (X.J.over (f.u.obj V))).map
        (𝟙 (((Over.forget V).sheafPushforwardContinuous (Type u) (Y.J.over V) Y.J).obj
          ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O))) :=
  (underlyingRingSheaf_map_pullbackCommRingSheafMap (X.J.over (f.u.obj V)) _
      (restrictionCommRingIso (Y.J.over V) Y.J (Over.forget V) Y.O).inv).trans
    (congrArg ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
        (X.J.over (f.u.obj V))).map
      (restrictionCommRingIso_inv_forget (Y.J.over V) Y.J (Over.forget V) Y.O))

/-- The comparison of the inverse image along the localized morphism of a restriction to the
slice over `V` with the inverse image along the composite is the identity on underlying sheaves
of sets. -/
private theorem forget_compTarget :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (pullbackCommRingSheafComp (Y.J.over V) (X.J.over (f.u.obj V))
          (Y.J.overPullback (Type u) V)
          ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V))) Y.O).hom =
      𝟙 ((Y.J.overPullback (Type u) V ⋙
          (Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V))).obj
        ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) :=
  forget_map_pullbackCommRingSheafComp_hom (Y.J.over V) (X.J.over (f.u.obj V))
    (Y.J.overPullback (Type u) V)
    ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
      (X.J.over (f.u.obj V))) Y.O

/-- The comparison of the restriction to the slice over `U = u(V)` of an inverse image along `f`
with the inverse image along the composite is the identity on underlying sheaves of sets. -/
private theorem forget_compSource :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (pullbackCommRingSheafComp X.J (X.J.over (f.u.obj V)) f.toposHom.inverseImage
          (X.J.overPullback (Type u) (f.u.obj V)) Y.O).hom =
      𝟙 ((f.toposHom.inverseImage ⋙ X.J.overPullback (Type u) (f.u.obj V)).obj
        ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) :=
  forget_map_pullbackCommRingSheafComp_hom X.J (X.J.over (f.u.obj V))
    f.toposHom.inverseImage (X.J.overPullback (Type u) (f.u.obj V)) Y.O

/-- The inverse of that comparison is the identity on underlying sheaves of sets too: an
isomorphism whose forward map is an identity has an identity for its inverse. -/
private theorem forget_compSource_inv :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (pullbackCommRingSheafComp X.J (X.J.over (f.u.obj V)) f.toposHom.inverseImage
          (X.J.overPullback (Type u) (f.u.obj V)) Y.O).inv =
      𝟙 ((f.toposHom.inverseImage ⋙ X.J.overPullback (Type u) (f.u.obj V)).obj
        ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) := by
  exact Iso.inv_ext (f := (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).mapIso
    (pullbackCommRingSheafComp X.J (X.J.over (f.u.obj V)) f.toposHom.inverseImage
      (X.J.overPullback (Type u) (f.u.obj V)) Y.O))
    ((Category.comp_id _).trans (forget_compSource f V))

/-- The four factors of `localizedSourceIso`, read on underlying sheaves of sets: all but
Stacks 03CF's clause (b) become identities.

Each identity is written at a sheaf spelled as a functor applied to an object, never as the
inverse image of a sheaf of commutative rings, although the two are the same sheaf: the identity
has to be read at both ends of the factor it replaces, and at the latter spelling the two ends
agree only after the construction of the inverse image is unfolded. -/
private theorem forget_localizedSourceIso_factors :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (localizedSourceIso f V).hom =
      𝟙 (((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V))).obj
          (((Over.forget V).sheafPushforwardContinuous (Type u) (Y.J.over V) Y.J).obj
            ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O))) ≫
        𝟙 ((Y.J.overPullback (Type u) V ⋙
              (Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
                (X.J.over (f.u.obj V))).obj
            ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) ≫
          (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
              (pullbackCommRingSheafIsoOfNatIso (X.J.over (f.u.obj V))
                (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
                  f.isMorphismOfSites) Y.O).hom ≫
            𝟙 ((f.toposHom.inverseImage ⋙ X.J.overPullback (Type u) (f.u.obj V)).obj
              ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) := by
  have expand : (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (localizedSourceIso f V).hom =
      (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
          (pullbackCommRingSheafMap (X.J.over (f.u.obj V))
            ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
              (X.J.over (f.u.obj V)))
            (restrictionCommRingIso (Y.J.over V) Y.J (Over.forget V) Y.O).inv) ≫
        (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
            (pullbackCommRingSheafComp (Y.J.over V) (X.J.over (f.u.obj V))
              (Y.J.overPullback (Type u) V)
              ((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
                (X.J.over (f.u.obj V))) Y.O).hom ≫
          (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
              (pullbackCommRingSheafIsoOfNatIso (X.J.over (f.u.obj V))
                (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
                  f.isMorphismOfSites) Y.O).hom ≫
            (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
              (pullbackCommRingSheafComp X.J (X.J.over (f.u.obj V)) f.toposHom.inverseImage
                (X.J.overPullback (Type u) (f.u.obj V)) Y.O).inv :=
    by simp only [localizedSourceIso, Iso.trans_hom, Functor.map_comp]; rfl
  refine expand.trans ?_
  refine Eq.trans (congrArg (fun m => m ≫ _) (forget_restrictionInv f V)) ?_
  refine Eq.trans (congrArg (fun m => m ≫ _) (CategoryTheory.Functor.map_id _ _)) ?_
  refine Eq.trans (congrArg (fun m => _ ≫ m ≫ _) (forget_compTarget f V)) ?_
  exact congrArg (fun m => _ ≫ _ ≫ _ ≫ m) (forget_compSource_inv f V)

/-- On underlying sheaves of sets the comparison `localizedSourceIso` *is* Stacks 03CF's clause
(b): the three other factors it is built from are identities there. -/
private theorem forget_localizedSourceIso_hom :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        (localizedSourceIso f V).hom =
      (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).hom.app
        ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) := by
  refine (forget_localizedSourceIso_factors f V).trans ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans (Category.comp_id
    (Y := (f.toposHom.inverseImage ⋙ X.J.overPullback (Type u) (f.u.obj V)).obj
      ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O)) _) ?_
  exact pullbackCommRingSheafIsoOfNatIso_hom_forget (X.J.over (f.u.obj V))
    (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V f.isMorphismOfSites) Y.O

/-- The image under `sheafCompose _ (forget CommRingCat)` of the asserted factorization of the
localized structure map: Stacks 03CF's clause (b) followed by the restriction of the structure
map of `f` to the slice. The identification of the localized structure sheaf of the source with
a restriction is the identity on underlying sheaves of sets, so it contributes nothing. -/
private theorem forget_localizedFactorization :
    (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map
        ((localizedSourceIso f V).hom ≫
          pullbackCommRingSheafMap (X.J.over (f.u.obj V))
              (X.J.overPullback (Type u) (f.u.obj V)) f.ringedToposHom.fSharpInverseImage ≫
            (restrictionCommRingIso (X.J.over (f.u.obj V)) X.J
              (Over.forget (f.u.obj V)) X.O).hom) =
      (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).hom.app
          ((sheafCompose Y.J (forget CommRingCat.{u})).obj Y.O) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map
          ((sheafCompose X.J (forget CommRingCat.{u})).map
            f.ringedToposHom.fSharpInverseImage) := by
  refine Eq.trans (CategoryTheory.Functor.map_comp _ _ _) ?_
  refine Eq.trans (congrArg (fun m => m ≫ _) (forget_localizedSourceIso_hom f V)) ?_
  refine Eq.trans (congrArg (fun m => _ ≫ m) (CategoryTheory.Functor.map_comp _ _ _)) ?_
  refine Eq.trans (congrArg (fun m => _ ≫ _ ≫ m)
    (restrictionCommRingIso_hom_forget (X.J.over (f.u.obj V)) X.J
      (Over.forget (f.u.obj V)) X.O)) ?_
  refine Eq.trans (congrArg (fun m => _ ≫ m) (Category.comp_id _)) ?_
  exact congrArg (fun m => _ ≫ m)
    (underlyingRingSheaf_map_pullbackCommRingSheafMap (X.J.over (f.u.obj V)) _
      f.ringedToposHom.fSharpInverseImage)

/-- **The structure map of the localized morphism of Stacks 04J0, in inverse-image form.** It is
the structure map of `f` pulled back to the slice over `U = u(V)`, read between Stacks 03CF's
clause (b) and the identification of the localized structure sheaf of the source with a
restriction.

Both sides have the same image under the faithful functor `sheafCompose _ (forget CommRingCat)`:
on the left that image is `AlgebraicGeometry.RingedSite.Hom.fSharpSet_localizedRingedToposHom`,
and on the right the two comparisons other than clause (b) are identities there. -/
private theorem fSharpInverseImage_localizedRingedToposHom_eq :
    (f.localizedRingedToposHom V).fSharpInverseImage =
      (localizedSourceIso f V).hom ≫
        pullbackCommRingSheafMap (X.J.over (f.u.obj V))
            (X.J.overPullback (Type u) (f.u.obj V)) f.ringedToposHom.fSharpInverseImage ≫
          (restrictionCommRingIso (X.J.over (f.u.obj V)) X.J
            (Over.forget (f.u.obj V)) X.O).hom := by
  refine (sheafCompose (X.J.over (f.u.obj V)) (forget CommRingCat.{u})).map_injective ?_
  refine Eq.trans
    (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      (f.localizedRingedToposHom V)) ?_
  refine Eq.trans (f.fSharpSet_localizedRingedToposHom V) ?_
  refine Eq.trans ?_ (forget_localizedFactorization f V).symm
  exact congrArg (fun m => _ ≫ (X.J.overPullback (Type u) (f.u.obj V)).map m)
    (RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      f.ringedToposHom).symm

/-- **Stacks 04J0 together with Stacks 04JB: flatness is inherited by the localization of a
morphism of ringed sites.** If the morphism of ringed topoi attached to `f` is flat — that is,
if `O_C` is flat over `f^{-1}O_D` — then so is the morphism of ringed topoi attached to the
localization `f'` of `f` at an object `V` of the target.

The structure map of `f'` in inverse-image form is the restriction of that of `f` to the slice
over `U = u(V)`, read between two isomorphisms
(`fSharpInverseImage_localizedRingedToposHom_eq`). Restriction to a slice is the inverse image
of the localization morphism of topoi, which is a left adjoint and left exact, so it carries
flatness of a morphism of sheaves of commutative rings along by
`Stacks.Sheaves.ToposPullback.isFlatMap_pullbackCommRingSheafMap`; and the two isomorphisms do
not disturb flatness, by `AlgebraicGeometry.SheafOfModules.isFlatMap_comp_iso`. The universe
lift in the flatness predicate is removed and restored by
`AlgebraicGeometry.SheafOfModules.isFlatMapULift_iff_isFlatMap`. -/
theorem isFlatMapULift_localizedRingedToposHom_fSharpInverseImage
    (hf : SheafOfModules.IsFlatMapULift.{u, u, u} f.ringedToposHom.fSharpInverseImage) :
    SheafOfModules.IsFlatMapULift.{u, u, u}
      (f.localizedRingedToposHom V).fSharpInverseImage := by
  -- Abelian sheaves at the site universe are sheafifiable on these three sites, and the maps
  -- sheafification inverts are the locally bijective ones; both are needed to read the unlifted
  -- flatness predicate, which `AlgebraicGeometry.SheafOfModules.IsFlatMapULift` builds internally.
  have := (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} X.J).1
  have := SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} X.J
  have := (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} Y.J).1
  have := SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} Y.J
  have := (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (X.J.over (f.u.obj V))).1
  have := SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (X.J.over (f.u.obj V))
  have hjU : (X.J.overPullback (Type u) (f.u.obj V)).IsLeftAdjoint :=
    ⟨_, ⟨(X.overMorphismOfTopoi (f.u.obj V)).adj⟩⟩
  have h0 : SheafOfModules.IsFlatMap.{u, u, u} f.ringedToposHom.fSharpInverseImage :=
    (SheafOfModules.isFlatMapULift_iff_isFlatMap
      f.ringedToposHom.fSharpInverseImage).mp hf
  have h1 := Stacks.Sheaves.ToposPullback.isFlatMap_pullbackCommRingSheafMap
    (X.J.overPullback (Type u) (f.u.obj V)) f.ringedToposHom.fSharpInverseImage h0
  have h2 : SheafOfModules.IsFlatMap.{u, u, u}
      (f.localizedRingedToposHom V).fSharpInverseImage := by
    rw [fSharpInverseImage_localizedRingedToposHom_eq f V]
    exact SheafOfModules.isFlatMap_comp_iso (localizedSourceIso f V)
      (restrictionCommRingIso (X.J.over (f.u.obj V)) X.J (Over.forget (f.u.obj V)) X.O) h1
  exact (SheafOfModules.isFlatMapULift_iff_isFlatMap
    (f.localizedRingedToposHom V).fSharpInverseImage).mpr h2

/-- **Stacks 04J0 together with Stacks 04JB**, with the localized morphism of ringed topoi
spelled as the morphism of ringed topoi attached to the localized morphism of ringed sites.
That is the same morphism as `AlgebraicGeometry.RingedSite.Hom.localizedRingedToposHom`. -/
theorem isFlatMapULift_localized_ringedToposHom_fSharpInverseImage
    (hf : SheafOfModules.IsFlatMapULift.{u, u, u} f.ringedToposHom.fSharpInverseImage) :
    SheafOfModules.IsFlatMapULift.{u, u, u}
      (f.localized V).ringedToposHom.fSharpInverseImage :=
  f.isFlatMapULift_localizedRingedToposHom_fSharpInverseImage V hf

end AlgebraicGeometry.RingedSite.Hom

end
