module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelCrossingAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitAdjointForm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence

/-!
# The transition coherence of the level-side crossing of Stacks 09YQ

`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange` states
[Stacks, Tag 0EYN], second half, for an abelian sheaf `F` on Mathlib's small étale site of a limit
`X = lim X_i` of schemes with affine transition morphisms, with the restrictions taken along
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing` — a level of the system of
sites of [Stacks, Tag 0EYL], read on the small étale site of `X_i` and then base changed along the
projection `p_i : X ⟶ X_i`. Its transition datum is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition`, defined by
conjugating the system's own on-the-nose cocone identity by the level identification
`levelCrossingIso`.

The statement the development wants instead,
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent`, is indexed by `Iᵒᵖ` and its
compatibility clause is stated with `Stacks.EtaleCohomology.coneDirectImageCompAb`, the comparison
of the direct image along a projection with the direct image along its factorisation through a
transition morphism of the system of schemes. **This file identifies the two transition data**, and
deduces `IsDirectImageDescent` from `restrictionIsColimitAb_levelBaseChange`.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso` — **the transition functor of
  the system of [Stacks, Tag 0EYL] is base change along the transition morphism of schemes**, on
  Mathlib's small étale sites. This is the field
  `Stacks.EtaleCohomology.AffineEtaleSiteColimit.transition_isPullback` read as a comparison with
  the chosen fibre product.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app` —
  **the transition coherence**: the transition datum of
  `restrictionIsColimitAb_levelBaseChange` is the comparison above, followed by the base-change
  comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` that underlies
  `Stacks.EtaleCohomology.coneDirectImageCompAb`.
* `Stacks.EtaleCohomology.AffineLimitCohomology.isDirectImageDescent_of_levelBaseChange` —
  **[Stacks, Tag 0EYN], second half, with the inverse images removed**, i.e.
  `Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent` for every abelian sheaf on
  Mathlib's small étale site of the limit.

## Implementation notes

**Where the coherence lives.** `coneDirectImageCompAb` is restriction of sheaves along
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'`, so the coherence is a statement about the
*chosen* fibre products of Mathlib's base change and the objects a level of [Stacks, Tag 0EYL]
stores. Both sides of `levelBaseChangeCrossing_transition_hom_app` are morphisms into a base
change along `p_j`, hence determined by one projection
(`Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext`); on that projection the left-hand side is
the stored compatibility `Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimitFst_transition` and
the right-hand side is `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst` composed with
the transition projection. No new descent argument occurs.

That last lemma is why
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence`
is imported: it is the only module carrying the first projection of the *inverse* of the
base-change comparison for a composite, and restating it here would duplicate it. This module is a
leaf, so the import costs nothing library-wide.

**The reindexing by `Iᵒᵖ`.** `restrictionIsColimitAb_levelBaseChange` is indexed by the levels of
the system, `IsDirectImageDescent` by `Iᵒᵖ`, and `(affineEtaleSiteColimit …).indexEquiv` relates
the two only up to an equivalence. The passage does *not* need base change along an isomorphism of
schemes: the conclusion for an arbitrary `i : Iᵒᵖ` follows from the conclusion at one level by
`hgen` inside `isDirectImageDescent_of_levelBaseChange`, which is the compatibility of `σ` against
the naturality of `coneDirectImageCompAb` — the same identity for both families, so the index may
be moved along any arrow of `Iᵒᵖ`, in particular along the counit of `indexEquiv`.

**Why the computations are split into lemmas stated inside `AlgebraicGeometry.Scheme`.** As in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitLevelCrossing.lean`, a
goal mentioning an object of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the
transparency `rewrite` builds its motive at, so `Category.assoc` cannot be rewritten with there.
Every such computation below is stated as a lemma *entirely inside* `AlgebraicGeometry.Scheme`
(`levelTransition_naturality_fst`, `levelTransition_naturality_snd`,
`transitionCoherence_lhs_fst`, `transitionCoherence_rhs_fst`) and the morphisms that would carry
the morphism property are taken as variables, constrained only by the projection identity they
satisfy. The one place where a transport along an *equality of functors* has to be reduced —
the `CategoryTheory.eqToIso` inside `levelBaseChangeCrossing_transition` — is handled in term
mode, `etale_eqToIso_hom_app_left` being the single `subst` that does it. No compiler option is
relaxed.

**The definitional identities the proofs rest on.** The lemmas stated inside
`AlgebraicGeometry.Scheme` are applied by `exact` and `have`, so three identities are discharged
by `rfl` at the point of use rather than named: the components of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` and of `levelTransitionIso` are,
on underlying schemes, the `CategoryTheory.IsPullback.isoPullback` of the corresponding stored
square (`CategoryTheory.NatIso.ofComponents` and `CategoryTheory.MorphismProperty.Over.isoMk`
being projections of structure literals), and the structure morphism of a level object read on
Mathlib's site is `Stacks.EtaleCohomology.AffineLimitCohomology.levelStruct`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v' u' w v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open _root_.Stacks.AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale transitionScheme)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- The crossing from a level of the system of [Stacks, Tag 0EYL] into **Mathlib's** small étale
site of its own stage `X_n`: the level crossing of [Stacks, Tag 021B] followed by the embedding
forgetting the size cutoff. It is the factor of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing` before the base change. -/
abbrev levelEtaleSite (n : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C n ⥤ (D.obj (levelIndex D c B hD hX hc n)).Etale :=
  levelToSmallEtale D c B hD hX hc n ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc n)) (hD _)

/-- The projection of the cone at the later stage factors through the transition morphism between
two levels. This is `CategoryTheory.Limits.Cone.w` at the arrow of `Iᵒᵖ` that
`(affineEtaleSiteColimit …).indexEquiv` assigns to an arrow of the index of the system. -/
theorem conePi_transition {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    c.π.app (levelIndex D c B hD hX hc j) =
      c.π.app (levelIndex D c B hD hX hc i) ≫ transitionScheme D c B hD hX hc a :=
  (c.w ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a)).symm

/-! ### The level transition is base change along the transition morphism -/

/-- The component of the transition identification at an object of a level: the object a level
stores over the earlier stage is the chosen fibre product of the later level object along the
transition morphism, because
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.transition_isPullback` exhibits it as *a* fibre
product. -/
def levelTransitionComponent {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    ((sys D c B hD hX hc).u a ⋙ levelEtaleSite D c B hD hX hc i).obj Y ≅
      (levelEtaleSite D c B hD hX hc j ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (transitionScheme D c B hD hX hc a)).obj Y :=
  MorphismProperty.Over.isoMk
    (((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback)
    (IsPullback.isoPullback_hom_snd _)

/-- The component, read on underlying schemes. -/
theorem levelTransitionComponent_hom_left {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    (levelTransitionComponent D c B hD hX hc a Y).hom.left =
      ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback.hom :=
  rfl

/-- The left-hand side of the transition identification, read on underlying schemes. -/
theorem levelTransition_lhs_map_left {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    {Y Y' : (sys D c B hD hX hc).C j} (k : Y ⟶ Y') :
    (((sys D c B hD hX hc).u a ⋙ levelEtaleSite D c B hD hX hc i).map k).left =
      (levelToScheme D c B hD hX hc i).map (((sys D c B hD hX hc).u a).map k) :=
  rfl

/-- **The first projection of the naturality square of the transition identification**, entirely
inside `AlgebraicGeometry.Scheme`: it is the naturality of the stored projection `transitionFst`.
The base change of the morphism is taken as a variable `m`, constrained only by its first
projection. -/
theorem levelTransition_naturality_fst {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    {Y Y' : (sys D c B hD hX hc).C j} (k : Y ⟶ Y')
    (m : pullback (levelStruct D c B hD hX hc j Y) (transitionScheme D c B hD hX hc a) ⟶
      pullback (levelStruct D c B hD hX hc j Y') (transitionScheme D c B hD hX hc a))
    (hm : m ≫ pullback.fst (levelStruct D c B hD hX hc j Y')
          (transitionScheme D c B hD hX hc a) =
        pullback.fst (levelStruct D c B hD hX hc j Y)
            (transitionScheme D c B hD hX hc a) ≫
          (levelToScheme D c B hD hX hc j).map k) :
    ((levelToScheme D c B hD hX hc i).map (((sys D c B hD hX hc).u a).map k) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y').isoPullback.hom) ≫
      pullback.fst (levelStruct D c B hD hX hc j Y')
        (transitionScheme D c B hD hX hc a) =
    (((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback.hom ≫ m) ≫
      pullback.fst (levelStruct D c B hD hX hc j Y')
        (transitionScheme D c B hD hX hc a) := by
  rw [Category.assoc, IsPullback.isoPullback_hom_fst, Category.assoc, hm, ← Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).naturality k

/-- **The second projection of the naturality square of the transition identification**, entirely
inside `AlgebraicGeometry.Scheme`: both sides are the structure morphism of the level object over
its own stage. -/
theorem levelTransition_naturality_snd {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    {Y Y' : (sys D c B hD hX hc).C j} (k : Y ⟶ Y')
    (m : pullback (levelStruct D c B hD hX hc j Y) (transitionScheme D c B hD hX hc a) ⟶
      pullback (levelStruct D c B hD hX hc j Y') (transitionScheme D c B hD hX hc a))
    (hm : m ≫ pullback.snd (levelStruct D c B hD hX hc j Y')
          (transitionScheme D c B hD hX hc a) =
        pullback.snd (levelStruct D c B hD hX hc j Y)
          (transitionScheme D c B hD hX hc a)) :
    ((levelToScheme D c B hD hX hc i).map (((sys D c B hD hX hc).u a).map k) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y').isoPullback.hom) ≫
      pullback.snd (levelStruct D c B hD hX hc j Y')
        (transitionScheme D c B hD hX hc a) =
    (((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback.hom ≫ m) ≫
      pullback.snd (levelStruct D c B hD hX hc j Y')
        (transitionScheme D c B hD hX hc a) := by
  rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc, hm,
    IsPullback.isoPullback_hom_snd]
  exact levelStruct_w D c B hD hX hc i (((sys D c B hD hX hc).u a).map k)

/-- **The transition functor of the system of [Stacks, Tag 0EYL] is base change along the
transition morphism of schemes**, on Mathlib's small étale sites: for an arrow `a : i ⟶ j` of the
index, the level-`i` object obtained from a level-`j` object `Y` by the transition functor is the
chosen fibre product of `Y` along `X_i ⟶ X_j`.

Nothing is assumed: the comparison is `CategoryTheory.IsPullback.isoPullback` for the
fibre-product square `Stacks.EtaleCohomology.AffineEtaleSiteColimit.transition_isPullback` that
[Stacks, Tag 0EYL] supplies as data, and its naturality is the naturality of the stored projection
`transitionFst` together with the structure triangle of the level. This is the level-transition
counterpart of `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`, which does the
same for the projections to the limit. -/
def levelTransitionIso {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    (sys D c B hD hX hc).u a ⋙ levelEtaleSite D c B hD hX hc i ≅
      levelEtaleSite D c B hD hX hc j ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (transitionScheme D c B hD hX hc a) := by
  refine NatIso.ofComponents (levelTransitionComponent D c B hD hX hc a) ?_
  intro Y Y' k
  refine MorphismProperty.Over.Hom.ext ?_
  rw [comp_left_etale, comp_left_etale, levelTransitionComponent_hom_left,
    levelTransitionComponent_hom_left, levelTransition_lhs_map_left]
  refine pullback.hom_ext ?_ ?_
  · exact levelTransition_naturality_fst D c B hD hX hc a k _
      (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst _ _)
  · exact levelTransition_naturality_snd D c B hD hX hc a k _
      (Stacks.EtaleCohomology.smallEtaleBaseChange_w _ _)

/-! ### The transition coherence -/

/-- Transport along an equality of functors into Mathlib's small étale site, read on underlying
schemes. Stated at a universe *variable*, for the reason recorded on
`Stacks.EtaleCohomology.AffineLimitCohomology.comp_left_etale`. -/
theorem etale_eqToIso_hom_app_left {Z : AlgebraicGeometry.Scheme.{w}} {A : Type u'}
    [Category.{v'} A] {F G : A ⥤ Z.Etale} (h : F = G) (Y : A) :
    ((eqToIso h).hom.app Y).left =
      eqToHom (congrArg (fun T : Z.Etale => T.left) (Functor.congr_obj h Y)) := by
  subst h
  rfl

/-- **The cocone identity of the system, read on the stored projections.** The transport along
the on-the-nose identity `levelCrossing_transition`, composed with the stored projection to `X` at
the level `j`, is the projection at the level `i` followed by the transition projection. This is
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimitFst_transition` with the two transports
cancelled against each other. -/
theorem transitionCoherence_eqToHom {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    ((eqToIso (levelCrossing_transition D c B hD hX hc a)).hom.app Y).left ≫
        ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst j).app Y =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i).app
          (((sys D c B hD hX hc).u a).obj Y) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y := by
  have h1 : ((eqToIso (levelCrossing_transition D c B hD hX hc a)).hom.app Y).left =
      eqToHom (congrArg (fun T : (c.pt).Etale => T.left)
        (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y)) :=
    etale_eqToIso_hom_app_left _ Y
  have h2 : (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
        (eqToHom (Functor.congr_obj
          ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) Y).symm) =
      eqToHom (congrArg (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).obj
        (Functor.congr_obj
          ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) Y).symm) :=
    eqToHom_map _ _
  have h : ((eqToIso (levelCrossing_transition D c B hD hX hc a)).hom.app Y).left ≫
      (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
        (eqToHom (Functor.congr_obj
          ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) Y).symm) = 𝟙 _ :=
    ((congrArg (fun z => z ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX).map
            (eqToHom (Functor.congr_obj
              ((affineEtaleSiteColimit D c B hD hX hc).toLimit_transition a) Y).symm)) h1).trans
        (congrArg (fun z => eqToHom (congrArg (fun T : (c.pt).Etale => T.left)
            (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y)) ≫ z) h2)).trans
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
  rw [(affineEtaleSiteColimit D c B hD hX hc).toLimitFst_transition a Y]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i).app
        (((sys D c B hD hX hc).u a).obj Y) ≫
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y) h)).trans
    (Category.id_comp _)

/-- **The first projection of the left-hand side of the coherence.** Stated entirely inside
`AlgebraicGeometry.Scheme`, with the transport along the cocone identity taken as a variable `eL`
constrained only by the compatibility `heL` of the stored projections that
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimitFst_transition` provides. -/
theorem transitionCoherence_lhs_fst {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j)
    (eL : (limitToScheme D c B hD hX hc i).obj (((sys D c B hD hX hc).u a).obj Y) ⟶
      (limitToScheme D c B hD hX hc j).obj Y)
    (heL : eL ≫ ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst j).app Y =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i).app
          (((sys D c B hD hX hc).u a).obj Y) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y) :
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i
            (((sys D c B hD hX hc).u a).obj Y)).isoPullback.inv ≫ eL ≫
        ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback j Y).isoPullback.hom) ≫
      pullback.fst (levelStruct D c B hD hX hc j Y)
        (c.π.app (levelIndex D c B hD hX hc j)) =
    pullback.fst (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
        (c.π.app (levelIndex D c B hD hX hc i)) ≫
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y := by
  rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst, heL, ← Category.assoc,
    IsPullback.isoPullback_inv_fst]

/-- **The first projection of the right-hand side of the coherence.** Stated entirely inside
`AlgebraicGeometry.Scheme`, with the two comparison morphisms taken as variables `m₁`, `m₂`
constrained only by their first projections: base change acts on a morphism by `m₁`'s identity
(`Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst`) and the composite base-change
comparison by `m₂`'s (`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst`). -/
theorem transitionCoherence_rhs_fst {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j)
    (m₁ : pullback (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
          (c.π.app (levelIndex D c B hD hX hc i)) ⟶
      pullback (pullback.snd (levelStruct D c B hD hX hc j Y)
          (transitionScheme D c B hD hX hc a))
        (c.π.app (levelIndex D c B hD hX hc i)))
    (hm₁ : m₁ ≫ pullback.fst (pullback.snd (levelStruct D c B hD hX hc j Y)
            (transitionScheme D c B hD hX hc a))
          (c.π.app (levelIndex D c B hD hX hc i)) =
        pullback.fst (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
            (c.π.app (levelIndex D c B hD hX hc i)) ≫
          ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback.hom)
    (m₂ : pullback (pullback.snd (levelStruct D c B hD hX hc j Y)
          (transitionScheme D c B hD hX hc a))
        (c.π.app (levelIndex D c B hD hX hc i)) ⟶
      pullback (levelStruct D c B hD hX hc j Y)
        (c.π.app (levelIndex D c B hD hX hc j)))
    (hm₂ : m₂ ≫ pullback.fst (levelStruct D c B hD hX hc j Y)
          (c.π.app (levelIndex D c B hD hX hc j)) =
        pullback.fst (pullback.snd (levelStruct D c B hD hX hc j Y)
              (transitionScheme D c B hD hX hc a))
            (c.π.app (levelIndex D c B hD hX hc i)) ≫
          pullback.fst (levelStruct D c B hD hX hc j Y)
            (transitionScheme D c B hD hX hc a)) :
    (m₁ ≫ m₂) ≫ pullback.fst (levelStruct D c B hD hX hc j Y)
        (c.π.app (levelIndex D c B hD hX hc j)) =
      pullback.fst (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
          (c.π.app (levelIndex D c B hD hX hc i)) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y := by
  rw [Category.assoc, hm₂, ← Category.assoc, hm₁, Category.assoc,
    IsPullback.isoPullback_hom_fst]

/-- **THE TRANSITION COHERENCE.** For an arrow `a : i ⟶ j` of the index of the system of
[Stacks, Tag 0EYL], the transition datum
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition` of
`restrictionIsColimitAb_levelBaseChange` is the identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso` of the level transition with
base change along the transition morphism, based along the projection `p_i`, followed by the
comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` of base change along `p_j` with base
change along `p_i` after base change along `X_i ⟶ X_j` — which is precisely the comparison
restriction along which is `Stacks.EtaleCohomology.coneDirectImageCompAb` (see
`Stacks.EtaleCohomology.AffineLimitCohomology.coneDirectImageCompAb_inv_app_hom_app`).

So the asymmetry recorded on `levelBaseChangeCrossing_transition` — the system's cocone identity
holds on the nose while base change composes only up to associativity of fibre products — is
exactly the discrepancy that `coneDirectImageCompAb` names, and nothing else. Both sides are
morphisms into a base change along `p_j`, so
`Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext` reduces the statement to one projection;
there the left-hand side is the stored compatibility
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimitFst_transition` of the projections to `X`
with the transition projections, and the right-hand side is the two projections of the iterated
base change. Nothing is assumed. -/
theorem levelBaseChangeCrossing_transition_hom_app {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    (levelBaseChangeCrossing_transition D c B hD hX hc a).hom.app Y =
      (Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc i))).map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y) ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (c.π.app (levelIndex D c B hD hX hc i))
            (transitionScheme D c B hD hX hc a)
            (c.π.app (levelIndex D c B hD hX hc j))
            (conePi_transition D c B hD hX hc a)).inv.app
          ((levelEtaleSite D c B hD hX hc j).obj Y) := by
  have hL : ((levelBaseChangeCrossing_transition D c B hD hX hc a).hom.app Y).left ≫
      pullback.fst (levelStruct D c B hD hX hc j Y)
        (c.π.app (levelIndex D c B hD hX hc j)) =
      pullback.fst (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
          (c.π.app (levelIndex D c B hD hX hc i)) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y :=
    transitionCoherence_lhs_fst D c B hD hX hc a Y
      ((eqToIso (levelCrossing_transition D c B hD hX hc a)).hom.app Y).left
      (transitionCoherence_eqToHom D c B hD hX hc a Y)
  have hR : (((Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc i))).map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y) ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (c.π.app (levelIndex D c B hD hX hc i))
            (transitionScheme D c B hD hX hc a)
            (c.π.app (levelIndex D c B hD hX hc j))
            (conePi_transition D c B hD hX hc a)).inv.app
          ((levelEtaleSite D c B hD hX hc j).obj Y)).left) ≫
      pullback.fst (levelStruct D c B hD hX hc j Y)
        (c.π.app (levelIndex D c B hD hX hc j)) =
      pullback.fst (levelStruct D c B hD hX hc i (((sys D c B hD hX hc).u a).obj Y))
          (c.π.app (levelIndex D c B hD hX hc i)) ≫
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y :=
    transitionCoherence_rhs_fst D c B hD hX hc a Y
      (((Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i))).map
        ((levelTransitionIso D c B hD hX hc a).hom.app Y)).left)
      (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst
        (c.π.app (levelIndex D c B hD hX hc i))
        ((levelTransitionIso D c B hD hX hc a).hom.app Y))
      (((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (c.π.app (levelIndex D c B hD hX hc i))
            (transitionScheme D c B hD hX hc a)
            (c.π.app (levelIndex D c B hD hX hc j))
            (conePi_transition D c B hD hX hc a)).inv.app
          ((levelEtaleSite D c B hD hX hc j).obj Y)).left)
      (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst
        (c.π.app (levelIndex D c B hD hX hc i))
        (transitionScheme D c B hD hX hc a)
        (c.π.app (levelIndex D c B hD hX hc j))
        (conePi_transition D c B hD hX hc a)
        ((levelEtaleSite D c B hD hX hc j).obj Y))
  exact Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext
    (c.π.app (levelIndex D c B hD hX hc j)) (hL.trans hR.symm)


/-! ### The identification with `coneDirectImageCompAb` -/

omit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)] in
/-- The sections of the inverse of the comparison of direct images along a factorisation of a
projection of the cone: restriction along the base-change comparison. -/
theorem coneDirectImageCompAb_inv_app_hom_app {i j : Iᵒᵖ} (a : i ⟶ j)
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (U : (D.obj j).Etale) :
    ((Stacks.EtaleCohomology.coneDirectImageCompAb c a).inv.app F).hom.app (op U) =
      F.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
        (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app U).op :=
  Category.comp_id _

omit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)] in
/-- The sections of the comparison of direct images along a factorisation of a projection of the
cone. -/
theorem coneDirectImageCompAb_hom_app_hom_app {i j : Iᵒᵖ} (a : i ⟶ j)
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (U : (D.obj j).Etale) :
    ((Stacks.EtaleCohomology.coneDirectImageCompAb c a).hom.app F).hom.app (op U) =
      F.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
        (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).hom.app U).op :=
  Category.id_comp _

omit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)] in
/-- The sections of the direct image of a map of sheaves along a transition morphism of the
system: the sections of the map over the base change of the object. -/
theorem systemPushforward_map_hom_app {i j : Iᵒᵖ} (a : i ⟶ j)
    {M N : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology (D.obj i))
      AddCommGrpCat.{max u v + 1}} (ψ : M ⟶ N) (U : (D.obj j).Etale) :
    ((Stacks.EtaleCohomology.systemPushforward D AddCommGrpCat.{max u v + 1} a).map ψ).hom.app
        (op U) =
      ψ.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange (D.map a)).obj U)) :=
  rfl

/-- **The inverse of the transition datum, against the level transition.** -/
theorem levelBaseChangeCrossing_transition_inv_app_comp {i j : (sys D c B hD hX hc).I}
    (a : i ⟶ j) (Y : (sys D c B hD hX hc).C j) :
    (levelBaseChangeCrossing_transition D c B hD hX hc a).inv.app Y ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc i))).map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y) =
      (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
          (c.π.app (levelIndex D c B hD hX hc i))
          (transitionScheme D c B hD hX hc a)
          (c.π.app (levelIndex D c B hD hX hc j))
          (conePi_transition D c B hD hX hc a)).hom.app
        ((levelEtaleSite D c B hD hX hc j).obj Y) :=
  (Iso.inv_comp_eq
      (Iso.app (levelBaseChangeCrossing_transition D c B hD hX hc a) Y)).mpr
    ((Iso.eq_comp_inv (Iso.app (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
        (c.π.app (levelIndex D c B hD hX hc i))
        (transitionScheme D c B hD hX hc a)
        (c.π.app (levelIndex D c B hD hX hc j))
        (conePi_transition D c B hD hX hc a))
      ((levelEtaleSite D c B hD hX hc j).obj Y))).mp
      (levelBaseChangeCrossing_transition_hom_app D c B hD hX hc a Y)).symm


omit [Nonempty I] [IsDirected I (· ≤ ·)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)] in
/-- **The compatibility of a family of maps of direct images, read on sections.** -/
theorem isDirectImageCompatible_app {i j : Iᵒᵖ} (a : i ⟶ j)
    (F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (σ : ∀ k : Iᵒᵖ, (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).obj F ⟶
      (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).obj G)
    (hσ : Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageCompatible c F G σ)
    (U : (D.obj j).Etale) :
    (σ j).hom.app (op U) =
      F.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
          (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).inv.app U).op ≫
        (σ i).hom.app
            (op ((Stacks.EtaleCohomology.smallEtaleBaseChange (D.map a)).obj U)) ≫
          G.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
            (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).hom.app U).op := by
  rw [hσ a]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [coneDirectImageCompAb_inv_app_hom_app, systemPushforward_map_hom_app,
    coneDirectImageCompAb_hom_app_hom_app]
  rfl


/-! ### The descent of direct images -/

/-- **Transferring a compatibility across a naturality square.** The shape of the argument that
turns the compatibility of a family of maps of direct images, read at a chosen fibre product, into
its compatibility read at the object a level stores: the two differ by the comparison of the two,
whose naturality square is `hn`. -/
theorem comp_comp_eq_of_naturality {𝒜 : Type u'} [Category.{v'} 𝒜]
    {A₁ A₂ A₃ B₁ B₂ B₃ : 𝒜} {L : A₁ ⟶ B₁} {m : A₁ ⟶ A₂} {m' : A₁ ⟶ A₃} {a : A₂ ⟶ A₃}
    {s : A₂ ⟶ B₂} {s' : A₃ ⟶ B₃} {g : B₂ ⟶ B₃} {k : B₂ ⟶ B₁} {k' : B₃ ⟶ B₁}
    (hL : L = m ≫ s ≫ k) (hm : m' = m ≫ a) (hn : a ≫ s' = s ≫ g) (hk : g ≫ k' = k) :
    L = m' ≫ s' ≫ k' := by
  rw [hL, hm, ← hk]
  simp only [Category.assoc]
  rw [← Category.assoc a s' k', hn]
  simp only [Category.assoc]

/-- **The family of maps on the levels is compatible with the transition datum.** This is where
the primary coherence is consumed: the compatibility of `σ` over `Iᵒᵖ` is stated with the chosen
fibre products of Mathlib's base change, and the compatibility
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'` asks for is
stated with the transition datum `levelBaseChangeCrossing_transition`; the two are matched by
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app` and the
naturality of `σ` along the level transition comparison
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso`. -/
theorem levelFamily_compat
    (F G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (σ : ∀ i : Iᵒᵖ, (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app i)).obj F ⟶
      (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app i)).obj G)
    (hσ : Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageCompatible c F G σ)
    {p q : (sys D c B hD hX hc).I} (b : q ⟶ p) (V : (sys D c B hD hX hc).C p) :
    (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc p).op
        (σ (levelIndex D c B hD hX hc p)).hom).app (op V) =
      F.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).hom.app V).op ≫
        (Functor.whiskerLeft (levelEtaleSite D c B hD hX hc q).op
            (σ (levelIndex D c B hD hX hc q)).hom).app
          (op (((sys D c B hD hX hc).u b).obj V)) ≫
          G.obj.map ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op := by
  have hm := (congrArg (fun z => F.obj.map (Quiver.Hom.op z))
    (levelBaseChangeCrossing_transition_hom_app D c B hD hX hc b V)).trans
      (F.obj.map_comp _ _)
  have hk := (G.obj.map_comp
      ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc q))).map
        ((levelTransitionIso D c B hD hX hc b).hom.app V)).op
      ((levelBaseChangeCrossing_transition D c B hD hX hc b).inv.app V).op).symm.trans
    (congrArg (fun z => G.obj.map (Quiver.Hom.op z))
      (levelBaseChangeCrossing_transition_inv_app_comp D c B hD hX hc b V))
  exact comp_comp_eq_of_naturality
    (isDirectImageCompatible_app D c
      ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b) F G σ hσ
      ((levelEtaleSite D c B hD hX hc p).obj V))
    hm
    ((σ (levelIndex D c B hD hX hc q)).hom.naturality
      ((levelTransitionIso D c B hD hX hc b).hom.app V).op)
    hk

include B hD hX hc in
/-- **[Stacks, Tag 0EYN], second half, with the inverse images removed: an abelian sheaf on
Mathlib's small étale site of a limit of schemes is the colimit of the inverse images of its
direct images, in adjoint form.** -/
theorem isDirectImageDescent_of_levelBaseChange
    (F : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1}) :
    Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent c F := by
  intro G σ hσ
  obtain ⟨χ, hχ, huniq⟩ := restrictionIsColimitAb_levelBaseChange D c B hD hX hc F G
    (fun n => Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op
      (σ (levelIndex D c B hD hX hc n)).hom)
    (levelFamily_compat D c B hD hX hc F G σ hσ)
  have hlev : ∀ n : (sys D c B hD hX hc).I,
      (Stacks.EtaleCohomology.smallEtalePushforwardAb
          (c.π.app (levelIndex D c B hD hX hc n))).map χ =
        σ (levelIndex D c B hD hX hc n) :=
    fun n => hom_ext_of_levelRestrictionAb D c B hD hX hc n _ _ fun V => (hχ n V).symm
  have hgen : ∀ {k l : Iᵒᵖ} (a : k ⟶ l),
      (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).map χ = σ k →
        (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app l)).map χ = σ l := by
    intro k l a hk
    rw [hσ a, ← hk]
    exact (NatIso.naturality_1 (Stacks.EtaleCohomology.coneDirectImageCompAb c a) χ).symm
  refine ⟨χ, fun i => ?_, fun ψ hψ => ?_⟩
  · exact hgen ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
      (hlev ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i))
  · refine huniq ψ fun n V => ?_
    rw [← hψ (levelIndex D c B hD hX hc n)]
    rfl

end Stacks.EtaleCohomology.AffineLimitCohomology

end
