module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitSetSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PostcompInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePostcomposition
-- the levels of the canonical system of Stacks 0EYL are indexed by `Iᵒᵖ` itself; the body of
-- `affineEtaleSiteColimit` is needed to see it
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite

/-!
# The system of restrictions of a sheaf of sets along an étale inverse system

Let `I` be a directed set with a least element `⊥`, let `(X_i)` be an inverse system of schemes
over `I` whose transition morphisms are affine and étale, and let `X = lim X_i`. For a sheaf of
sets `F` on the small étale site of `X_⊥`, the inverse image of `F` along the étale morphism
`f_i : X_i ⟶ X_⊥` is its restriction along composition with `f_i`
(`Stacks.EtaleCohomology.smallEtaleRestrictionAdj`): the sections of `f_i⁻¹F` over an étale
`V ⟶ X_i` are the sections of `F` over `V ⟶ X_i ⟶ X_⊥`, with no sheafification.

This file feeds that choice of inverse images on the levels, and the library's inverse image of
sheaves of sets along `X ⟶ X_⊥` on the limit, to the sets form of Stacks 09YN on the sites of
Stacks 0EYL (`Stacks.EtaleCohomology.LimitSiteBridge.sections_colimit_levelOf`), and computes
the abstract transition maps of the resulting system: they are restriction of sections of `F`
along the transition projections.

## Main definitions

* `levelProj`: the projection `V ×_{X_j} X_i ⟶ V` of a transition base change, as a morphism of
  the small étale site of `X_⊥`.
* `levelψPost`: restriction of sections of `F` along `levelProj`.
* `limitιPost`: the unit of the inverse image along `X ⟶ X_⊥`, followed by restriction along
  `limitLift`.

## Main results

* `levelεOf_postcomp_app`: the universal arrows of the levels are restriction of sections.
* `levelψOf_postcomp`: the transition maps are restriction along `levelProj`.
* `limitιOf_postcomp`: the structure maps of the colimit on the site of the limit are the units
  of the inverse image along `X ⟶ X_⊥`, followed by restriction along `limitLift`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.EtaleCohomology

/-- The projection `V ×_Y Y' ⟶ V` of a base change along `g : Y' ⟶ Y`, as a morphism of the small
étale site of `Z` between the two composites with étale morphisms `f : Y ⟶ Z` and
`fg = g ≫ f`. -/
def postcompBaseChangeProj {Z Y Y' : Scheme.{u}} (f : Y ⟶ Z) [Etale f] (g : Y' ⟶ Y)
    (fg : Y' ⟶ Z) [Etale fg] (h : fg = g ≫ f) (V : Y.Etale) :
    (smallEtalePostcomp fg).obj ((smallEtaleBaseChange g).obj V) ⟶
      (smallEtalePostcomp f).obj V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom g) (by
    change pullback.fst V.hom g ≫ V.hom ≫ f = pullback.snd V.hom g ≫ fg
    rw [h, reassoc_of% (pullback.condition (f := V.hom) (g := g))]) trivial

/-- Composition in Mathlib's small étale site is composition of underlying morphisms. -/
theorem etale_comp_left {X : Scheme.{u}} {A A' A'' : X.Etale} (a : A ⟶ A') (b : A' ⟶ A'') :
    (a ≫ b).left = a.left ≫ b.left :=
  rfl

/-- A transport along an equality of objects of a small étale site, on underlying schemes. -/
theorem etale_eqToHom_left {X : Scheme.{u}} {A A' : X.Etale} (h : A = A') :
    (eqToHom h).left = eqToHom (congrArg (fun V : X.Etale => V.left) h) := by
  subst h
  rfl

/-- The underlying morphism of `postcompBaseChangeProj` is the first projection of the pullback. -/
@[simp]
theorem postcompBaseChangeProj_left {Z Y Y' : Scheme.{u}} (f : Y ⟶ Z) [Etale f] (g : Y' ⟶ Y)
    (fg : Y' ⟶ Z) [Etale fg] (h : fg = g ≫ f) (V : Y.Etale) :
    (postcompBaseChangeProj f g fg h V).left = pullback.fst V.hom g :=
  rfl

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.LimitSiteBridge

open Stacks.EtaleCohomology.AffineLimitCohomology Stacks.WeakSites.PullbackSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  {hc : IsLimit c}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)]

variable (D c B hD hX hc) in
/-- The inverse images to the levels: restriction along composition with `f_i : X_i ⟶ X_⊥`. -/
abbrev postcompL (i : (sys D c B hD hX hc).I) :
    Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology (Type (max u v + 1)) ⥤
      Sheaf (lvl D c B hD hX hc i).smallEtaleTopology (Type (max u v + 1)) :=
  (smallEtalePostcomp (toBottom D c B hD hX hc i)).sheafPushforwardContinuous _ _ _

variable (D c B hD hX hc) in
/-- The adjunctions of the inverse images to the levels. -/
abbrev postcompAdj (i : (sys D c B hD hX hc).I) :=
  smallEtaleRestrictionAdj (toBottom D c B hD hX hc i) (Type (max u v + 1))

variable (F : Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology
  (Type (max u v + 1)))

/-- **The universal arrows of the levels are restriction of sections**: the restriction of the
unit of `Σ^* ⊣ f_*`, read through `levelPushforwardIso`, is restriction along the counit of
`Σ ⊣ base change` followed by the transition base change comparison. -/
theorem levelεOf_postcomp_app (i : (sys D c B hD hX hc).I)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F i).app (op W) =
      F.obj.map ((smallEtalePostcompAdj (toBottom D c B hD hX hc i)).counit.app
          ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj W)).op ≫
        F.obj.map ((smallEtalePostcomp (toBottom D c B hD hX hc i)).map
          ((transitionBaseChangeIso D c B hD hX hc
            ((bottom_isTerminal D c B hD hX hc).from i)).hom.app W)).op := by
  simp [levelεOf, levelPushforwardIso, smallEtaleRestrictionAdj,
    Functor.sheafPushforwardContinuousComp']
  rfl

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The morphism `f_j : X_j ⟶ X_⊥` factors as the transition morphism `X_j ⟶ X_i` followed by
`f_i`. -/
theorem toBottom_comp {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    toBottom D c B hD hX hc j = lvlMap D c B hD hX hc a ≫ toBottom D c B hD hX hc i := by
  rw [← lvlMap_comp]
  exact congrArg (lvlMap D c B hD hX hc) ((bottom_isTerminal D c B hD hX hc).hom_ext _ _)

/-- **The transition projection** `u_a(Y) ⟶ Y` of the system of Stacks 0EYL, embedded in the small
étale site of `X_⊥` through the composites with `f_j` and `f_i`. -/
def levelProj {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) (Y : (sys D c B hD hX hc).C i) :
    (smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
        ((levelToEtale D c B hD hX hc j).obj (((sys D c B hD hX hc).u a).obj Y)) ⟶
      (smallEtalePostcomp (toBottom D c B hD hX hc i)).obj
        ((levelToEtale D c B hD hX hc i).obj Y) :=
  (smallEtalePostcomp (toBottom D c B hD hX hc j)).map
      ((transitionBaseChangeIso D c B hD hX hc a).hom.app Y) ≫
    postcompBaseChangeProj (toBottom D c B hD hX hc i) (lvlMap D c B hD hX hc a)
      (toBottom D c B hD hX hc j) (toBottom_comp a) ((levelToEtale D c B hD hX hc i).obj Y)

/-- The underlying morphism of `levelProj a Y` is the transition projection
`transitionFst a` at `Y`. -/
theorem levelProj_left {i j : (sys D c B hD hX hc).I} (a : j ⟶ i)
    (Y : (sys D c B hD hX hc).C i) :
    (levelProj a Y).left = ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).app Y :=
  ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Y).isoPullback_hom_fst

/-- The projections `levelProj a` are natural in the object of the level `i`. -/
theorem levelProj_naturality {i j : (sys D c B hD hX hc).I} (a : j ⟶ i)
    {Y Y' : (sys D c B hD hX hc).C i} (g : Y ⟶ Y') :
    (smallEtalePostcomp (toBottom D c B hD hX hc j)).map
        ((levelToEtale D c B hD hX hc j).map (((sys D c B hD hX hc).u a).map g)) ≫
      levelProj a Y' =
    levelProj a Y ≫ (smallEtalePostcomp (toBottom D c B hD hX hc i)).map
        ((levelToEtale D c B hD hX hc i).map g) := by
  apply MorphismProperty.Over.Hom.ext
  rw [etale_comp_left, etale_comp_left, levelProj_left, levelProj_left]
  exact ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a).naturality g

/-- The concrete transition maps: restriction of sections along `levelProj`. -/
def levelψPost {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    (levelSheafOf (postcompL D c B hD hX hc) F i).obj ⟶
      ((sys D c B hD hX hc).u a).op ⋙ (levelSheafOf (postcompL D c B hD hX hc) F j).obj where
  app Y := F.obj.map (levelProj a Y.unop).op
  naturality {Y Y'} g := by
    have h := congrArg (fun m => F.obj.map m.op) (levelProj_naturality a g.unop)
    simp only [op_comp, Functor.map_comp] at h
    exact h.symm

/-- The transition projection to the bottom level, landing in the object itself rather than in its
composite with `f_⊥`: base change comparison followed by the counit of `Σ ⊣ base change`. -/
def levelProjBot (j : (sys D c B hD hX hc).I) (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
        ((levelToEtale D c B hD hX hc j).obj
          (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from j)).obj W)) ⟶
      (levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj W :=
  (smallEtalePostcomp (toBottom D c B hD hX hc j)).map
      ((transitionBaseChangeIso D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from j)).hom.app
        W) ≫
    (smallEtalePostcompAdj (toBottom D c B hD hX hc j)).counit.app
      ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj W)

/-- The underlying morphism of `levelProjBot j W` is the transition projection to the bottom
level at `W`. -/
theorem levelProjBot_left (j : (sys D c B hD hX hc).I)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (levelProjBot j W).left = ((affineEtaleSiteColimit D c B hD hX hc).transitionFst
      ((bottom_isTerminal D c B hD hX hc).from j)).app W :=
  ((affineEtaleSiteColimit D c B hD hX hc).transition_isPullback _ W).isoPullback_hom_fst

/-- The universal arrow of the level `j` at `W` is restriction of sections of `F` along
`levelProjBot j W`. -/
theorem levelεOf_postcomp_app' (j : (sys D c B hD hX hc).I)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F j).app (op W) =
      F.obj.map (levelProjBot j W).op := by
  rw [levelεOf_postcomp_app, levelProjBot, op_comp, Functor.map_comp]

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] [OrderBot I] in
/-- The transition projections along equal morphisms `b = b'` agree up to transport along the
induced equality of objects. -/
theorem transitionFst_congr {i j : (sys D c B hD hX hc).I} {b b' : i ⟶ j} (h : b = b')
    (Y : (sys D c B hD hX hc).C j) :
    ((affineEtaleSiteColimit D c B hD hX hc).transitionFst b).app Y =
      eqToHom (by rw [h]) ≫ ((affineEtaleSiteColimit D c B hD hX hc).transitionFst b').app Y := by
  subst h
  simp

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- Transporting an object of the bottom level to the level `i` and then along `a : j ⟶ i` gives
its transport to the level `j`. -/
theorem u_from_obj {i j : (sys D c B hD hX hc).I} (a : j ⟶ i)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    ((sys D c B hD hX hc).u a).obj
        (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj W) =
      ((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from j)).obj W := by
  rw [(bottom_isTerminal D c B hD hX hc).hom_ext ((bottom_isTerminal D c B hD hX hc).from j)
    (a ≫ (bottom_isTerminal D c B hD hX hc).from i), (sys D c B hD hX hc).comp]
  rfl

/-- The projection `levelProj a` followed by the projection from the level `i` to the bottom level
is, up to transport along `u_from_obj`, the projection from the level `j` to the bottom level. -/
theorem levelProj_comp_levelProjBot {i j : (sys D c B hD hX hc).I} (a : j ⟶ i)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    levelProj a (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj W) ≫
        levelProjBot i W =
      eqToHom (congrArg (fun Y => (smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
        ((levelToEtale D c B hD hX hc j).obj Y)) (u_from_obj a W)) ≫ levelProjBot j W := by
  apply MorphismProperty.Over.Hom.ext
  rw [etale_comp_left, etale_comp_left, etale_eqToHom_left, levelProj_left, levelProjBot_left,
    levelProjBot_left,
    transitionFst_congr ((bottom_isTerminal D c B hD hX hc).hom_ext
      ((bottom_isTerminal D c B hD hX hc).from j) (a ≫ (bottom_isTerminal D c B hD hX hc).from i)),
    (affineEtaleSiteColimit D c B hD hX hc).transitionFst_comp]
  simp only [Functor.comp_map, eqToHom_map, eqToHom_trans_assoc]
  exact (Category.id_comp _).symm

/-- **The transition maps of the system of restrictions are restriction of sections** along the
transition projections. -/
theorem levelψOf_postcomp {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    levelψOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F a = levelψPost F a := by
  have key := (isUniversalArrow_levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
    F i).hom_ext (M := push (sys D c B hD hX hc) a (levelSheafOf (postcompL D c B hD hX hc) F j))
    (f := ObjectProperty.homMk
      (levelψOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F a))
    (g := ObjectProperty.homMk (levelψPost F a)) ?_
  · exact congrArg (fun φ => φ.hom) key
  · show levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F i ≫
        Functor.whiskerLeft _
          (levelψOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F a) =
      levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F i ≫
        Functor.whiskerLeft _ (levelψPost F a)
    unfold levelψOf
    rw [ψ_spec]
    refine NatTrans.ext (funext fun W => ?_)
    obtain ⟨W⟩ := W
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    rw [levelεOf_postcomp_app', levelεOf_postcomp_app']
    show F.obj.map (levelProjBot j W).op ≫ eqToHom _ =
      F.obj.map (levelProjBot i W).op ≫ F.obj.map (levelProj a _).op
    rw [← Functor.map_comp, ← op_comp, levelProj_comp_levelProjBot, op_comp, Functor.map_comp,
      eqToHom_op, eqToHom_map]

variable (D c B hD hX hc) in
/-- The inverse image to the limit: the library's inverse image of sheaves of sets along
`X ⟶ X_⊥`. -/
abbrev limitL :
    Sheaf (lvl D c B hD hX hc (bottom D c B hD hX hc)).smallEtaleTopology (Type (max u v + 1)) ⥤
      Sheaf c.pt.smallEtaleTopology (Type (max u v + 1)) :=
  smallEtaleInverseImage.{max u v, 0} (lvlπ D c B hD hX hc (bottom D c B hD hX hc))

variable (D c B hD hX hc) in
/-- The adjunction of the inverse image to the limit. -/
abbrev limitAdj :=
  smallEtaleInverseImageAdjunction.{max u v, 0} (lvlπ D c B hD hX hc (bottom D c B hD hX hc))

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] [OrderBot I] in
/-- The projection `X ⟶ X_i` factors as the projection `X ⟶ X_j` followed by the transition
morphism `X_j ⟶ X_i`. -/
theorem lvlπ_comp {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    lvlπ D c B hD hX hc i = lvlπ D c B hD hX hc j ≫ lvlMap D c B hD hX hc a :=
  (c.w _).symm

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The universal arrow of the limit is the unit of the inverse image along `X ⟶ X_⊥`, read
through the base change comparison of the functor to the limit. -/
theorem limitεOf_app (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (limitεOf (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F).app (op W) =
      ((limitAdj D c B hD hX hc).unit.app F).hom.app
          (op ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj W)) ≫
        ((limitL D c B hD hX hc).obj F).obj.map
          ((toLimitBaseChangeIso D c B hD hX hc (bottom D c B hD hX hc)).hom.app W).op := by
  simp [limitεOf, limitPushforwardIso, Functor.sheafPushforwardContinuousComp']
  rfl

/-- The morphism from the image of an object `Y'` of the level `j` in the site of the limit to the
base change along `X ⟶ X_⊥` of its composite with `f_j`. -/
def limitLift (j : (sys D c B hD hX hc).I) (Y' : (sys D c B hD hX hc).C j) :
    (limitToEtale D c B hX).obj ((toLimitSmall D c B hD hX hc j).obj Y') ⟶
      (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj
        ((smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
          ((levelToEtale D c B hD hX hc j).obj Y')) :=
  (toLimitBaseChangeIso D c B hD hX hc j).hom.app Y' ≫
    baseChangePostcompMap (toBottom D c B hD hX hc j) (lvlπ D c B hD hX hc j)
      (lvlπ D c B hD hX hc (bottom D c B hD hX hc))
      (lvlπ_comp ((bottom_isTerminal D c B hD hX hc).from j)) _

/-- The underlying morphism of `limitLift j Y'`, followed by the first pullback projection, is the
projection `toLimitFst j` at `Y'`. -/
theorem limitLift_left_fst (j : (sys D c B hD hX hc).I) (Y' : (sys D c B hD hX hc).C j) :
    (limitLift j Y').left ≫ pullback.fst _ (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst j).app Y' := by
  have h1 := baseChangePostcompMap_left_fst (toBottom D c B hD hX hc j) (lvlπ D c B hD hX hc j)
    (lvlπ D c B hD hX hc (bottom D c B hD hX hc))
    (lvlπ_comp ((bottom_isTerminal D c B hD hX hc).from j)) ((levelToEtale D c B hD hX hc j).obj Y')
  have h2 := ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback j Y').isoPullback_hom_fst
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans h2)

/-- The first pullback projection of `limitLift j Y'` followed by the base change of a morphism `m`
is the projection `toLimitFst j` at `Y'` followed by `m`. -/
private theorem limitLift_comp_map_left_fst (j : (sys D c B hD hX hc).I)
    (Y' : (sys D c B hD hX hc).C j)
    {T : (lvl D c B hD hX hc (bottom D c B hD hX hc)).Etale}
    (m : (smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
      ((levelToEtale D c B hD hX hc j).obj Y') ⟶ T) :
    (limitLift j Y' ≫ (smallEtaleBaseChange (lvlπ D c B hD hX hc
      (bottom D c B hD hX hc))).map m).left ≫
        pullback.fst T.hom (lvlπ D c B hD hX hc (bottom D c B hD hX hc)) =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst j).app Y' ≫ m.left := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (smallEtaleBaseChange_map_left_fst _ m)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m.left) (limitLift_left_fst j Y'))))

/-- The morphisms `limitLift j` are natural in the object of the level `j`. -/
theorem limitLift_naturality (j : (sys D c B hD hX hc).I) {Y Y' : (sys D c B hD hX hc).C j}
    (g : Y ⟶ Y') :
    (limitToEtale D c B hX).map ((toLimitSmall D c B hD hX hc j).map g) ≫ limitLift j Y' =
      limitLift j Y ≫ (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map
        ((smallEtalePostcomp (toBottom D c B hD hX hc j)).map
          ((levelToEtale D c B hD hX hc j).map g)) := by
  apply smallEtaleBaseChange_hom_ext
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (limitLift_left_fst j Y')).trans
    ((((affineEtaleSiteColimit D c B hD hX hc).toLimitFst j).naturality g).trans
      (limitLift_comp_map_left_fst j Y
        ((smallEtalePostcomp (toBottom D c B hD hX hc j)).map
          ((levelToEtale D c B hD hX hc j).map g))).symm))

/-- The concrete structure maps of the colimit on the site of the limit: the unit of the inverse
image along `X ⟶ X_⊥`, followed by restriction along `limitLift`. -/
def limitιPost (j : (sys D c B hD hX hc).I) :
    (levelSheafOf (postcompL D c B hD hX hc) F j).obj ⟶
      (toLimitSmall D c B hD hX hc j).op ⋙ (limitSheafOf (limitL D c B hD hX hc) F).obj where
  app Y := ((limitAdj D c B hD hX hc).unit.app F).hom.app
      (op ((smallEtalePostcomp (toBottom D c B hD hX hc j)).obj
        ((levelToEtale D c B hD hX hc j).obj Y.unop))) ≫
    ((limitL D c B hD hX hc).obj F).obj.map (limitLift j Y.unop).op
  naturality {Y Y'} g := by
    have h1 := ((limitAdj D c B hD hX hc).unit.app F).hom.naturality
      ((smallEtalePostcomp (toBottom D c B hD hX hc j)).map
        ((levelToEtale D c B hD hX hc j).map g.unop)).op
    have h2 := congrArg (fun m => ((limitL D c B hD hX hc).obj F).obj.map m.op)
      (limitLift_naturality j g.unop)
    simp only [op_comp, Functor.map_comp] at h2
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2.symm).trans
        (Category.assoc _ _ _).symm)))

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- The base change comparison of the functor from the bottom level to the limit, at `W`. -/
def limitBaseChangeBot (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (limitToEtale D c B hX).obj ((toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).obj W) ⟶
      (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).obj
        ((levelToEtale D c B hD hX hc (bottom D c B hD hX hc)).obj W) :=
  (toLimitBaseChangeIso D c B hD hX hc (bottom D c B hD hX hc)).hom.app W

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), Etale (D.map a)] in
/-- An object of the bottom level, transported to the level `i`, has the same image in the site of
the limit as the object itself. -/
theorem toLimitSmall_transition_obj (i : (sys D c B hD hX hc).I)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    (toLimitSmall D c B hD hX hc i).obj
        (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj W) =
      (toLimitSmall D c B hD hX hc (bottom D c B hD hX hc)).obj W :=
  Functor.congr_obj
    (toLimitSmall_transition D c B hD hX hc ((bottom_isTerminal D c B hD hX hc).from i)) W

/-- The morphism `limitLift i`, followed by the base change of `levelProjBot i W` along
`X ⟶ X_⊥`, is, up to transport along `toLimitSmall_transition_obj`, the base change comparison
`limitBaseChangeBot W`. -/
theorem limitLift_comp_levelProjBot (i : (sys D c B hD hX hc).I)
    (W : (sys D c B hD hX hc).C (bottom D c B hD hX hc)) :
    limitLift i (((sys D c B hD hX hc).u ((bottom_isTerminal D c B hD hX hc).from i)).obj W) ≫
        (smallEtaleBaseChange (lvlπ D c B hD hX hc (bottom D c B hD hX hc))).map
          (levelProjBot i W) =
      (limitToEtale D c B hX).map (eqToHom (toLimitSmall_transition_obj i W)) ≫
        limitBaseChangeBot W := by
  apply smallEtaleBaseChange_hom_ext
  have h3 : (limitBaseChangeBot W).left ≫ pullback.fst _ _ = _ :=
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback
      (bottom D c B hD hX hc) W).isoPullback_hom_fst
  have h4 := (affineEtaleSiteColimit D c B hD hX hc).toLimitFst_transition
    ((bottom_isTerminal D c B hD hX hc).from i) W
  refine (limitLift_comp_map_left_fst i _ _).trans ?_
  rw [levelProjBot_left]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h3.symm)
  rw [h4, eqToHom_map, etale_eqToHom_left]
  simp only [eqToHom_map]
  exact (Category.id_comp _).symm

/-- **The structure maps of the colimit on the site of the limit are the units of the inverse
image along `X ⟶ X_⊥`, followed by restriction.** -/
theorem limitιOf_postcomp (j : (sys D c B hD hX hc).I) :
    limitιOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) (limitL D c B hD hX hc)
      (limitAdj D c B hD hX hc) F j = limitιPost F j := by
  have : ∀ i, (toLimitSmall D c B hD hX hc i).IsContinuous ((sys D c B hD hX hc).J i)
      (limitSitePrecoverage D c B hX).toGrothendieck :=
    fun i => toLimitSmall_isContinuous D c B hD hX hc i
  have key := (isUniversalArrow_levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
    F j).hom_ext (M := pushC (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (limitSitePrecoverage D c B hX).toGrothendieck j (limitSheafOf (limitL D c B hD hX hc) F))
    (f := ObjectProperty.homMk (limitιOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
      (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F j))
    (g := ObjectProperty.homMk (limitιPost F j)) ?_
  · exact congrArg (fun φ => φ.hom) key
  · show levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F j ≫
        Functor.whiskerLeft _ (limitιOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc)
          (limitL D c B hD hX hc) (limitAdj D c B hD hX hc) F j) =
      levelεOf (postcompL D c B hD hX hc) (postcompAdj D c B hD hX hc) F j ≫
        Functor.whiskerLeft _ (limitιPost F j)
    unfold limitιOf
    rw [ι_spec]
    refine NatTrans.ext (funext fun W => ?_)
    obtain ⟨W⟩ := W
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    rw [levelεOf_postcomp_app', limitεOf_app]
    have hn := ((limitAdj D c B hD hX hc).unit.app F).hom.naturality (levelProjBot j W).op
    have hl := congrArg (fun m => ((limitL D c B hD hX hc).obj F).obj.map (Quiver.Hom.op m))
      (limitLift_comp_levelProjBot j W)
    simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map] at hl
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
      (Category.assoc _ _ _))).symm
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hl.symm)

end Stacks.EtaleCohomology.LimitSiteBridge
