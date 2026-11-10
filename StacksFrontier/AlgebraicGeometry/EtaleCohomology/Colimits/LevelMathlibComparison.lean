module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.TransitionBaseChangeCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LevelEtaleSquareCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity

/-!
# The levels of Stacks 0EYL read in Mathlib's small étale sites

The levels of the site system of Stacks 0EYL are small models of the small affine étale sites of
the stages `X_i`. Composing the reading of a level in the size-bounded small étale site of `X_i`
(`Stacks.EtaleCohomology.TransitionBaseChange.levelEtale`) with the embedding of that site into
Mathlib's `AlgebraicGeometry.Scheme.Etale` gives a functor `levelMathlib i` from the level to
Mathlib's small étale site of `X_i`, and the transition functors of the system become base change
there (`levelMathlibIso`), with the identity and composition laws (`levelMathlibIso_id_hom_app`,
`levelMathlibIso_comp_hom_app`). The transition morphism of schemes is carried as a named
morphism `g` with an equation `B.inclusion.map (stageMap E a) = g`, so that a consumer can use
`D.map a` itself.

## Main definitions

* `Stacks.EtaleCohomology.TransitionBaseChange.levelMathlib` — the level read in Mathlib's small
  étale site.
* `Stacks.EtaleCohomology.TransitionBaseChange.levelMathlibIso` — the transition functor is base
  change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry

section Generic

universe w

/-- The component of `Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf` is the first projection. -/
theorem smallEtaleBaseChangeIdOf_hom_app_left' {X : Scheme.{w}} (g : X ⟶ X) (hg : g = 𝟙 X)
    (U : X.Etale) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf g hg).hom.app U).left =
      Limits.pullback.fst U.hom g := by
  subst hg
  rfl

/-- The comparison of the two presentations of the small étale site at an identity. -/
theorem toEtaleSiteBaseChangeIso_hom_app_comp_idOf (B' : AlgebraicGeometry.BigEtaleSite.{w})
    {S : B'.Scheme} (f : S ⟶ S) (hf : f = 𝟙 S) (h : B'.inclusion.map f = 𝟙 _)
    (X : AlgebraicGeometry.SmallEtale B' S.obj S.property) :
    (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B' f).hom.app X ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf (B'.inclusion.map f) h).hom.app
          ((AlgebraicGeometry.SmallEtale.toEtaleSite B' S.obj S.property).obj X) =
      (AlgebraicGeometry.SmallEtale.toEtaleSite B' S.obj S.property).map
        ((smallEtaleBaseChange_factoredIdIso B' f hf).hom.app X) := by
  apply MorphismProperty.Over.Hom.ext
  change (PreservesPullback.iso B'.inclusion X.obj.hom f).hom ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf (B'.inclusion.map f) h).hom.app
        ((AlgebraicGeometry.SmallEtale.toEtaleSite B' S.obj S.property).obj X)).left =
    B'.inclusion.map ((smallEtaleBaseChange_factoredIdIso B' f hf).hom.app X).hom.left
  rw [smallEtaleBaseChangeIdOf_hom_app_left', smallEtaleBaseChange_factoredIdIso_hom_app_left]
  exact PreservesPullback.iso_hom_fst B'.inclusion X.obj.hom f

/-- Composition in Mathlib's small étale site, on underlying morphisms of schemes. -/
theorem etale_comp_left {S : Scheme.{w}} {A C D : S.Etale} (a : A ⟶ C) (b : C ⟶ D) :
    (a ≫ b).left = a.left ≫ b.left := rfl

/-- The first projection of the inverse of the comparison for a composite base change. -/
theorem smallEtaleBaseChangeComp'_inv_app_left_fst' {W X Y : Scheme.{w}} (f : W ⟶ X) (g : X ⟶ Y)
    (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) :
    ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' f g fg hfg).inv.app U).left ≫
        Limits.pullback.fst U.hom fg =
      Limits.pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj U).hom f ≫
        Limits.pullback.fst U.hom g := by
  rw [← Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst f g fg hfg U, ← Category.assoc,
    ← etale_comp_left, Iso.inv_hom_id_app]
  exact Category.id_comp _

/-- A rearrangement in an arbitrary category. -/
theorem rearrange₄ {𝒞 : Type*} [Category 𝒞] {P Q R S T U W Z : 𝒞} (x : P ⟶ Q) (y : Q ⟶ R)
    (z : R ⟶ S) (w : S ⟶ T) (f : T ⟶ U) (f₁ : S ⟶ W) (f₂ : W ⟶ U) (f₁' : R ⟶ Z) (t : Z ⟶ W)
    (tr : Z ⟶ U) (lf : Q ⟶ Z) (h₁ : w ≫ f = f₁ ≫ f₂) (h₂ : z ≫ f₁ = f₁' ≫ t)
    (h₃ : t ≫ f₂ = tr) (h₄ : y ≫ f₁' = lf) :
    (x ≫ y ≫ z ≫ w) ≫ f = x ≫ lf ≫ tr := by
  simp only [Category.assoc, h₁, reassoc_of% h₂, h₃, reassoc_of% h₄]

/-- The underlying morphism of the image of an `eqToHom` in a small étale site. -/
theorem etale_map_eqToHom_left {𝒞 : Type*} [Category 𝒞] {S : Scheme.{w}} (F : 𝒞 ⥤ S.Etale)
    {X Y : 𝒞} (h : X = Y) :
    (F.map (eqToHom h)).left = eqToHom (by rw [h]) := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

end Generic

variable {I : Type v} [Preorder I]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)

/-- **The level `i` of the site system of Stacks 0EYL read in Mathlib's small étale site of the
stage `X_i`.** -/
abbrev levelMathlib (i : E.system.I) : E.system.C i ⥤ (D.obj (stage E i)).Etale :=
  levelEtale E i ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E i)) (hD (stage E i))

/-- The comparison of `levelMathlib` with base change along the transition morphism of schemes,
with that morphism written as `B.inclusion.map (stageMap E a)`. -/
def levelMathlibIsoAux {i j : E.system.I} (a : i ⟶ j) :
    E.system.u a ⋙ levelMathlib E i ≅
      levelMathlib E j ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map (stageMap E a)) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (transitionIso E a) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (levelEtale E j)
      (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E a))

/-- The component of `levelMathlibIsoAux` at `Y` is the image of the component of `transitionIso`
followed by the component of `AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`. -/
theorem levelMathlibIsoAux_hom_app {i j : E.system.I} (a : i ⟶ j) (Y : E.system.C j) :
    (levelMathlibIsoAux E a).hom.app Y =
      (AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E i)) (hD (stage E i))).map
          ((transitionIso E a).hom.app Y) ≫
        (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E a)).hom.app
          ((levelEtale E j).obj Y) := by
  simp [levelMathlibIsoAux]

/-- **The transition functor of the site system of Stacks 0EYL is base change in Mathlib's small
étale sites**, for a morphism `g` named by `B.inclusion.map (stageMap E a) = g`. -/
def levelMathlibIso {i j : E.system.I} (a : i ⟶ j) (g : D.obj (stage E i) ⟶ D.obj (stage E j))
    (hg : B.inclusion.map (stageMap E a) = g) :
    E.system.u a ⋙ levelMathlib E i ≅
      levelMathlib E j ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange g := by
  subst hg
  exact levelMathlibIsoAux E a

/-- For `g = B.inclusion.map (stageMap E a)`, `levelMathlibIso` is `levelMathlibIsoAux`. -/
theorem levelMathlibIso_rfl {i j : E.system.I} (a : i ⟶ j) :
    levelMathlibIso E a _ rfl = levelMathlibIsoAux E a := rfl

/-- **The first projection of `levelMathlibIso`** is the projection of the transition square of
the system. -/
theorem levelMathlibIso_hom_app_left_fst {i j : E.system.I} (a : i ⟶ j)
    (g : D.obj (stage E i) ⟶ D.obj (stage E j)) (hg : B.inclusion.map (stageMap E a) = g)
    (Y : E.system.C j) :
    ((levelMathlibIso E a g hg).hom.app Y).left ≫
        Limits.pullback.fst ((levelMathlib E j).obj Y).hom g = (E.transitionFst a).app Y := by
  subst hg
  rw [levelMathlibIso_rfl, levelMathlibIsoAux_hom_app, etale_comp_left]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (PreservesPullback.iso_hom_fst B.inclusion
    ((levelEtale E j).obj Y).obj.hom (stageMap E a))).trans (componentIso_hom_fst E a Y))

/-- **The composition law of `levelMathlibIso`.** -/
theorem levelMathlibIso_comp_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    (g : D.obj (stage E i) ⟶ D.obj (stage E j)) (hg : B.inclusion.map (stageMap E a) = g)
    (g' : D.obj (stage E j) ⟶ D.obj (stage E k)) (hg' : B.inclusion.map (stageMap E b) = g')
    (gg' : D.obj (stage E i) ⟶ D.obj (stage E k))
    (hgg' : B.inclusion.map (stageMap E (a ≫ b)) = gg') (h : gg' = g ≫ g')
    (Y : E.system.C k) :
    (levelMathlibIso E (a ≫ b) gg' hgg').hom.app Y =
      (levelMathlib E i).map (eqToHom (Functor.congr_obj (E.system.comp a b) Y)) ≫
        (levelMathlibIso E a g hg).hom.app ((E.system.u b).obj Y) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange g).map
            ((levelMathlibIso E b g' hg').hom.app Y) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' g g' gg' h).inv.app
              ((levelMathlib E k).obj Y) := by
  subst hg hg' hgg'
  rw [levelMathlibIso_rfl, levelMathlibIso_rfl, levelMathlibIso_rfl, levelMathlibIsoAux_hom_app,
    levelMathlibIsoAux_hom_app, levelMathlibIsoAux_hom_app, transitionIso_comp_hom_app,
    AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso_hom_app_comp' B (stageMap E a)
      (stageMap E b) (stageMap E (a ≫ b)) (stageMap_comp E a b)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E i))
    (hD (stage E i))) ((stageCompIso E a b).hom.app _), stageCompIso, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hn : ∀ {W : (D.obj (stage E i)).Etale} (h : _ ⟶ W),
      (AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E i)) (hD (stage E i))).map
        ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
          ((transitionIso E b).hom.app Y)) ≫
      (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E a)).hom.app
        ((AlgebraicGeometry.smallEtaleBaseChange B (stageMap E b)).obj ((levelEtale E k).obj Y)) ≫
        h =
      (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E a)).hom.app
          ((levelEtale E j).obj ((E.system.u b).obj Y)) ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map (stageMap E a))).map
          ((AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E j)) (hD (stage E j))).map
            ((transitionIso E b).hom.app Y)) ≫ h := fun h =>
    (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ h)
      ((AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E a)).hom.naturality
        ((transitionIso E b).hom.app Y))).trans (Category.assoc _ _ _)
  rw [hn]
  rfl

/-- **The identity law of `levelMathlibIso`.** -/
theorem levelMathlibIso_id_hom_app (i : E.system.I) (g : D.obj (stage E i) ⟶ D.obj (stage E i))
    (hg : B.inclusion.map (stageMap E (𝟙 i)) = g) (hg1 : g = 𝟙 _) (Y : E.system.C i) :
    (levelMathlibIso E (𝟙 i) g hg).hom.app Y ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf g hg1).hom.app ((levelMathlib E i).obj Y) =
      (levelMathlib E i).map (eqToHom (Functor.congr_obj (E.system.id_map i) Y)) := by
  subst hg
  have h1 : (AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso B (stageMap E (𝟙 i))).hom.app
        ((levelEtale E i).obj Y) ≫
      (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf (B.inclusion.map (stageMap E (𝟙 i)))
        hg1).hom.app ((levelMathlib E i).obj Y) =
      (AlgebraicGeometry.SmallEtale.toEtaleSite B (D.obj (stage E i)) (hD (stage E i))).map
        ((stageIdIso E i).hom.app ((levelEtale E i).obj Y)) :=
    toEtaleSiteBaseChangeIso_hom_app_comp_idOf B (stageMap E (𝟙 i)) (stageMap_id E i) hg1 _
  rw [levelMathlibIso_rfl, levelMathlibIsoAux_hom_app, Category.assoc, h1, ← Functor.map_comp,
    transitionIso_id_hom_app]
  rfl

/-! ### The functors to the limit -/

/-- **The small affine étale site of the limit, read in Mathlib's small étale site.** -/
abbrev limitMathlib :
    AlgebraicGeometry.SmallAffineEtale B c.pt hX ⥤ c.pt.Etale :=
  AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX

/-- The projection of the cone to the stage of `i`, typed with source `c.pt`. -/
def coneProj (i : E.system.I) : c.pt ⟶ D.obj (stage E i) := c.π.app (stage E i)

/-- The component at `Y` of the comparison of the functor to the limit with base change along the
projection of the cone: the comparison of the two fibre-product squares. -/
def limitComponentIso (i : E.system.I) (Y : E.system.C i) :
    (limitMathlib (c := c) (hX := hX)).obj ((E.toLimit i).obj Y) ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange (coneProj E i)).obj
        ((levelMathlib E i).obj Y) :=
  MorphismProperty.Over.isoMk ((E.toLimit_isPullback i Y).isoPullback)
    (IsPullback.isoPullback_hom_snd _)

/-- The left component of `limitComponentIso` followed by the first pullback projection is the
component of `toLimitFst`. -/
theorem limitComponentIso_hom_left_fst (i : E.system.I) (Y : E.system.C i) :
    (limitComponentIso E i Y).hom.left ≫
        Limits.pullback.fst ((levelMathlib E i).obj Y).hom (coneProj E i) =
      (E.toLimitFst i).app Y :=
  IsPullback.isoPullback_hom_fst _

/-- **The functor from a level to the limit is base change along the projection of the cone**, in
Mathlib's small étale sites. -/
def limitMathlibIso (i : E.system.I) :
    E.toLimit i ⋙ limitMathlib (c := c) (hX := hX) ≅
      levelMathlib E i ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange (coneProj E i) :=
  NatIso.ofComponents (limitComponentIso E i) (fun {Y Y'} φ => by
    refine Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext (coneProj E i) ?_
    have key : ((E.toLimit i ⋙ limitMathlib (c := c) (hX := hX)).map φ).left ≫
          (limitComponentIso E i Y').hom.left ≫
            Limits.pullback.fst ((levelMathlib E i).obj Y').hom (coneProj E i) =
        (limitComponentIso E i Y).hom.left ≫
          ((Stacks.EtaleCohomology.smallEtaleBaseChange (coneProj E i)).map
            ((levelMathlib E i).map φ)).left ≫
            Limits.pullback.fst ((levelMathlib E i).obj Y').hom (coneProj E i) := by
      rw [limitComponentIso_hom_left_fst, Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst]
      exact ((E.toLimitFst i).naturality φ).trans
        ((congrArg (· ≫ ((levelMathlib E i).map φ).left)
          (limitComponentIso_hom_left_fst E i Y).symm).trans (Category.assoc _ _ _))
    exact (Category.assoc _ _ _).trans (key.trans (Category.assoc _ _ _).symm))

/-- The component of `limitMathlibIso` at `Y` is `limitComponentIso`. -/
theorem limitMathlibIso_hom_app (i : E.system.I) (Y : E.system.C i) :
    (limitMathlibIso E i).hom.app Y = (limitComponentIso E i Y).hom := rfl

/-- **The functors to the limit are compatible with the transitions, in Mathlib's small étale
sites**: the comparison at `j` is the comparison at `i` pasted with `levelMathlibIso`. -/
theorem limitMathlibIso_hom_app_transition {i j : E.system.I} (a : i ⟶ j)
    (g : D.obj (stage E i) ⟶ D.obj (stage E j)) (hg : B.inclusion.map (stageMap E a) = g)
    (h : coneProj E j = coneProj E i ≫ g) (V : E.system.C j) :
    (limitMathlibIso E j).hom.app V =
      (limitMathlib (c := c) (hX := hX)).map
          (eqToHom (Functor.congr_obj (E.toLimit_transition a) V).symm) ≫
        (limitMathlibIso E i).hom.app ((E.system.u a).obj V) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange (coneProj E i)).map
            ((levelMathlibIso E a g hg).hom.app V) ≫
            (Stacks.EtaleCohomology.smallEtaleBaseChangeComp' (coneProj E i) g (coneProj E j)
              h).inv.app ((levelMathlib E j).obj V) := by
  refine Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext (coneProj E j) ?_
  rw [limitMathlibIso_hom_app, limitComponentIso_hom_left_fst, E.toLimitFst_transition a V]
  refine Eq.symm ((rearrange₄ _ _ _ _ _ _ _ _ _ _ _
    (smallEtaleBaseChangeComp'_inv_app_left_fst' (coneProj E i) g (coneProj E j) h _)
    (Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_fst (coneProj E i)
      ((levelMathlibIso E a g hg).hom.app V))
    (levelMathlibIso_hom_app_left_fst E a g hg V)
    (limitComponentIso_hom_left_fst E i ((E.system.u a).obj V))).trans ?_)
  rw [etale_map_eqToHom_left]
  simp only [eqToHom_map]
  rfl

end Stacks.EtaleCohomology.TransitionBaseChange

end
