module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelLegPinning
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocycleSystem

/-!
# The transition of a level, read on sections over an object: the pinning lemma

`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_app_apply` is the pinning lemma for
the **leg** of a level: restricting a section of `F_n` along a morphism of Mathlib's small étale
site of the stage `X_n` and then applying the leg of the level is the transpose of the geometric
leg over the target, restricted along the base change of that morphism. This file is its
counterpart for the **transition**
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap`, which is what the separatedness
half of the degree-zero step
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` needs and what
the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitOpensSections.lean`
record as absent.

**Why the interchange is needed.** The separatedness half of that step returns, for two sections
of `F_n` over the base change of `V₀` to `X_n` with the same image at the limit, a later level `m`
at which they agree *after restricting to the objects `W₀ k` of the covering datum and then
transitioning to `m`*. The sheaf condition at the level `m`, which is what turns that into an
equality of sections over the whole base change, can only consume the other order: *transition to
`m`, then restrict to the `W₀ k`*. Interchanging the two is the naturality of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition` in the object of the stage's
étale site, which is available because it is the `.hom` of a morphism of sheaves; what is needed
is the lemma that puts it in the form the conjunct is stated in, and that is
`levelCocycleMap_app_apply` below.

## Main results

* `Stacks.EtaleCohomology.systemDirTransition_hom_app` — **the direct-image transition of a system
  of étale sheaves, on sections over an object, is the transpose
  `Stacks.EtaleCohomology.etaleTransposeSection` of
  `Stacks.EtaleCohomology.systemTransitionMap`.** The transition counterpart of
  `Stacks.EtaleCohomology.systemDirLeg_transportLeg_hom_app`, and by the same one lemma.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition_hom_app` — the same at the
  levels of [Stacks, Tag 0EYL].
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap_comp_app` and
  `levelCocycleMap_app_apply` — **THE PINNING LEMMA FOR THE TRANSITION**, in morphism and in
  element form: restricting a section of `F_n` over an object `Z` of Mathlib's small étale site of
  the stage along a morphism `g` out of the image of an object `Y` of the level, and then applying
  the level transition over `Y`, is the direct-image transition over `Z` followed by restriction
  along the base change of `g` and the level transition identification.

## How it goes

**The bridge.** `Stacks.EtaleCohomology.systemDirTransition` is the transpose of the datum
`Stacks.EtaleCohomology.EtaleSheafSystem` carries across
`Stacks.EtaleCohomology.systemAdjunction`, whose left adjoint is the abstract left adjoint of the
direct image; `Stacks.EtaleCohomology.etaleTransposeSection` transposes across
`Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj`, whose left adjoint is the
construction as a left Kan extension followed by sheafification. The two adjunctions have the
**same right adjoint** — direct image is restriction along base change — so the two transposes
agree along `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`, exactly as for the
legs. The datum is read through the comparison by
`map_eq_inverseImageIsoPullbackAb_hom_app_comp`, which is the definition of
`Stacks.EtaleCohomology.systemTransitionMap` with the comparison cancelled.

**The interchange.** `levelCocycleMap_app` factors the level transition as the direct-image
transition followed by the transport along
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso`, and the naturality of the
former in the object absorbs the restriction along `g`. The associativity is done in an arbitrary
category and applied by `exact` (`Stacks.EtaleCohomology.comp_eq_of_eq_of_naturality`), for the
reason the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelCocyclePresentation.lean`
record: a goal mentioning an object of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the
transparency `rewrite` builds its motive at.

Nothing is assumed, and **no identity law** on the system of [Stacks, Tag 0EZL] is used or
available: the lemma is one arrow `b` of the index at a time.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex transitionScheme)

universe v u

namespace Stacks.EtaleCohomology

/-! ### The two transposes of the transition datum -/

section Bridge

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}

/-- **The transition datum of a system of étale sheaves, read through the comparison of the two
inverse images.** `Stacks.EtaleCohomology.systemTransitionMap` is the datum
`Stacks.EtaleCohomology.EtaleSheafSystem` carries with the comparison
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb` applied to it; this is
that identity read in the other direction, with the comparison cancelled. -/
theorem map_eq_inverseImageIsoPullbackAb_hom_app_comp
    (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    F.map a =
      (SmallEtaleLimitCohomology.inverseImageIsoPullbackAb (D.map a)).hom.app (F.obj j) ≫
        systemTransitionMap F a := by
  rw [systemTransitionMap, SmallEtaleLimitCohomology.systemPullbackIsoInverseImage_eq,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The direct-image transition datum of a system of étale sheaves, on sections over an object,
is the transpose of its transition map.** For an arrow `a : i ⟶ j` of the index and an object `Z`
of Mathlib's small étale site of the stage `X_j`, the component over `Z` of
`Stacks.EtaleCohomology.systemDirTransition` is
`Stacks.EtaleCohomology.etaleTransposeSection` of
`Stacks.EtaleCohomology.systemTransitionMap` at `Z`.

The transition counterpart of `Stacks.EtaleCohomology.systemDirLeg_transportLeg_hom_app`: the two
adjunctions have the same right adjoint, so this is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` at
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageIsoPullbackAb`, which is
`CategoryTheory.Adjunction.leftAdjointUniq` of the two. Nothing is assumed. -/
theorem systemDirTransition_hom_app (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) (Z : (D.obj j).Etale) :
    (systemDirTransition D AddCommGrpCat.{u + 1} F a).hom.app (op Z) =
      etaleTransposeSection.{u + 1, u} (D.map a) (systemTransitionMap F a) Z := by
  have key := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (smallEtaleAdjunctionAb (D.map a))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a)) (systemTransitionMap F a)
  have h0 : systemDirTransition D AddCommGrpCat.{u + 1} F a =
      (smallEtaleAdjunctionAb (D.map a)).homEquiv (F.obj j) (F.obj i)
        ((SmallEtaleLimitCohomology.inverseImageIsoPullbackAb (D.map a)).hom.app (F.obj j) ≫
          systemTransitionMap F a) := by
    rw [systemDirTransition, ← map_eq_inverseImageIsoPullbackAb_hom_app_comp]
    rfl
  rw [h0]
  exact congrArg
    (fun z : F.obj j ⟶ (smallEtalePushforwardAb (D.map a)).obj (F.obj i) => z.hom.app (op Z)) key

end Bridge

namespace AffineLimitCohomology

/-! ### The pinning lemma for the transition -/

section Level

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})

/-- **The direct-image transition datum between two levels, on sections over an object of
Mathlib's small étale site of the stage, is the transpose of the transition map of the system.**
`Stacks.EtaleCohomology.systemDirTransition_hom_app` at the arrow of `Iᵒᵖ` that
`(affineEtaleSiteColimit …).indexEquiv` assigns to an arrow of the index of the levels, the two
being the same datum.

The instance binder is not a hypothesis on the geometry: it is the levelwise sheafification of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem`'s own telescope, carried here
because `Stacks.EtaleCohomology.systemTransitionMap` is stated in the vocabulary of the
*constructed* inverse image. Instance search finds it for a variable index but exhausts its
heartbeat budget on the term `D.obj (levelIndex … m)`, whose index is
`Stacks.EtaleCohomology.affineEtaleSiteColimit`'s and so `@[no_expose]`; the binder is what makes
the search a match instead of a reduction. -/
theorem levelDirTransition_hom_app
    [∀ i : Iᵒᵖ, HasSheafify (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{max u v + 1}]
    {n m : (sys D c B hD hX hc).I} (b : m ⟶ n)
    (Z : (D.obj (levelIndex D c B hD hX hc n)).Etale) :
    (levelDirTransition D c B hD hX hc F b).hom.app (op Z) =
      etaleTransposeSection.{max u v + 1, max u v} (transitionScheme D c B hD hX hc b)
        (systemTransitionMap F
          ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b)) Z :=
  Stacks.EtaleCohomology.systemDirTransition_hom_app.{v, max u v} F
    ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b) Z

/-- **THE PINNING LEMMA FOR THE TRANSITION.** Let `(X_i)` be an inverse system of schemes over a
nonempty directed index with affine transition morphisms, all objects of a big étale site `B`, let
`X` be the vertex of a limit cone and let `F` be a system of abelian sheaves on Mathlib's small
étale sites of the `X_i` in the sense of [Stacks, Tag 0EZL]. Let `b : m ⟶ n` be an arrow of the
index of the levels of [Stacks, Tag 0EYL], let `Y` be an object of the level `n`, let `Z` be an
object of Mathlib's small étale site of the stage `X_n` and let `g` be a morphism from the image
of `Y` to `Z` there. Then restricting a section of `F_n` over `Z` along `g` and applying the
transition `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap` of the level cocycle
data over `Y` is the same as applying the direct-image transition
`Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition` over `Z` and then restricting
along the base change of `g` and the level transition identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso`.

This is the counterpart for the transition of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_comp_app`, and the two ingredients
are the same two: the factorisation `levelCocycleMap_app` of the transition and the naturality of
the factor `levelDirTransition` — the `.hom` of a morphism of sheaves — in the object of the
site. Nothing is assumed, and no identity law on the system is used or available. -/
theorem levelCocycleMap_comp_app {n m : (sys D c B hD hX hc).I} (b : m ⟶ n)
    (Y : (sys D c B hD hX hc).C n)
    {Z : (D.obj (levelIndex D c B hD hX hc n)).Etale}
    (g : (levelEtaleSite D c B hD hX hc n).obj Y ⟶ Z) :
    (F.obj (levelIndex D c B hD hX hc n)).obj.map g.op ≫
        (levelCocycleMap D c B hD hX hc F b).app (op Y) =
      (levelDirTransition D c B hD hX hc F b).hom.app (op Z) ≫
        (F.obj (levelIndex D c B hD hX hc m)).obj.map
            ((Stacks.EtaleCohomology.smallEtaleBaseChange
              (transitionScheme D c B hD hX hc b)).map g).op ≫
          (F.obj (levelIndex D c B hD hX hc m)).obj.map
            ((levelTransitionIso D c B hD hX hc b).hom.app Y).op :=
  Stacks.EtaleCohomology.comp_eq_of_eq_of_naturality
    (levelCocycleMap_app D c B hD hX hc F b Y)
    ((levelDirTransition D c B hD hX hc F b).hom.naturality g.op)

/-- `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap_comp_app` read on a section,
which is the form the second conjunct of
`Stacks.EtaleCohomology.AffineLimitCohomology.DatumIsColimit` is stated in. -/
theorem levelCocycleMap_app_apply {n m : (sys D c B hD hX hc).I} (b : m ⟶ n)
    (Y : (sys D c B hD hX hc).C n)
    {Z : (D.obj (levelIndex D c B hD hX hc n)).Etale}
    (g : (levelEtaleSite D c B hD hX hc n).obj Y ⟶ Z)
    (t : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj (op Z))) :
    (levelCocycleMap D c B hD hX hc F b).app (op Y)
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map g.op t) =
      (F.obj (levelIndex D c B hD hX hc m)).obj.map
          ((levelTransitionIso D c B hD hX hc b).hom.app Y).op
        ((F.obj (levelIndex D c B hD hX hc m)).obj.map
            ((Stacks.EtaleCohomology.smallEtaleBaseChange
              (transitionScheme D c B hD hX hc b)).map g).op
          ((levelDirTransition D c B hD hX hc F b).hom.app (op Z) t)) :=
  Eq.trans
    (ConcreteCategory.comp_apply
      ((F.obj (levelIndex D c B hD hX hc n)).obj.map g.op)
      ((levelCocycleMap D c B hD hX hc F b).app (op Y)) t).symm
    (Eq.trans
      (ConcreteCategory.congr_hom (levelCocycleMap_comp_app D c B hD hX hc F b Y g) t)
      (Eq.trans (ConcreteCategory.comp_apply _ _ t)
        (ConcreteCategory.comp_apply _ _ _)))

end Level

end AffineLimitCohomology

end Stacks.EtaleCohomology

end
