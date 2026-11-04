module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystems

/-!
# The direct images of a sheaf along the projections of a limit of schemes

Let `I` be a preordered set and let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes, so that
`i' ≥ i` gives a transition morphism `f_{i'i} : X_{i'} ⟶ X_i`, and let `c` be a cone over `D`
with projections `f_i : X ⟶ X_i`. For a sheaf `𝓕` on the small étale site of `X`, the direct
images `f_{i,*}𝓕` carry canonical maps `φ_{i'i} : f_{i'i}^{-1} f_{i,*}𝓕 ⟶ f_{i',*}𝓕` making
`(f_{i,*}𝓕, φ_{i'i})` a system of sheaves on `(X_i, f_{i'i})` in the sense of Stacks 0EZL. The
map `φ_{i'i}` is adjoint to the canonical identification `f_{i,*}𝓕 ≅ f_{i'i,*} f_{i',*}𝓕` of
direct images coming from the factorisation `f_i = f_{i'} ≫ f_{i'i}` of the projection.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` — base change along a composite, with the
  composite named rather than written out.
* `Stacks.EtaleCohomology.smallEtalePresheafPushforward` — direct image of presheaves of sets
  for small étale sites.
* `Stacks.EtaleCohomology.smallEtalePushforward` — direct image of sheaves for small étale sites.
* `Stacks.EtaleCohomology.smallEtalePushforwardComp'` — the direct image along a composite is the
  composite of the direct images.
* `Stacks.EtaleCohomology.coneDirectImageMap` — the canonical map `φ_{i'i}`.
* `Stacks.EtaleCohomology.directImageSystem` — the system of sheaves `(f_{i,*}𝓕, φ_{i'i})`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_hom_ext` — a morphism into a small étale base
  change is determined by its first projection.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst` — the comparison for a composite
  base change carries the iterated first projections to the first projection of the composite.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_assoc` — the associativity pentagon of small
  étale base change.
* `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc` — the associativity pentagon of the
  induced comparison of direct images.

## References

* [Stacks Project, Tag 03PW](https://stacks.math.columbia.edu/tag/03PW)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe w' w v u

namespace Stacks.EtaleCohomology

/-- Pullbacks along any morphism of schemes exist. -/
public lemma smallEtaleHasPullbacksAlong {W X : Scheme.{u}} (f : W ⟶ X) :
    MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- Étale morphisms are stable under base change along any morphism of schemes. -/
public lemma smallEtaleIsStableUnderBaseChangeAlong {W X : Scheme.{u}} (f : W ⟶ X) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) f :=
  ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩

/-- Base change along a composite, with the composite named. -/
public def smallEtaleBaseChangeComp' {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (fg : W ⟶ Y)
    (hfg : fg = f ≫ g) :
    smallEtaleBaseChange fg ≅ smallEtaleBaseChange g ⋙ smallEtaleBaseChange f :=
  eqToIso (congrArg (fun m : W ⟶ Y => smallEtaleBaseChange m) hfg) ≪≫
    smallEtaleBaseChangeComp f g

/-- The second component of a morphism into a base change is forced. -/
public lemma smallEtaleBaseChange_w {W X : Scheme.{u}} (f : W ⟶ X) {A : W.Etale} {V : X.Etale}
    (p : A ⟶ (smallEtaleBaseChange f).obj V) :
    p.left ≫ pullback.snd V.hom f = A.hom :=
  MorphismProperty.Over.w p

/-- A morphism into a base change is determined by its first component. -/
public lemma smallEtaleBaseChange_hom_ext {W X : Scheme.{u}} (f : W ⟶ X) {A : W.Etale}
    {V : X.Etale} {p q : A ⟶ (smallEtaleBaseChange f).obj V}
    (hpq : p.left ≫ pullback.fst V.hom f = q.left ≫ pullback.fst V.hom f) : p = q :=
  MorphismProperty.Over.Hom.ext
    (pullback.hom_ext hpq ((smallEtaleBaseChange_w f p).trans (smallEtaleBaseChange_w f q).symm))

/-- Base change commutes with the first projection. -/
public lemma smallEtaleBaseChange_map_left_fst {W X : Scheme.{u}} (f : W ⟶ X) {U V : X.Etale}
    (p : U ⟶ V) :
    ((smallEtaleBaseChange f).map p).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ p.left := by
  let := smallEtaleHasPullbacksAlong f
  let := smallEtaleIsStableUnderBaseChangeAlong f
  exact MorphismProperty.Over.pullback_map_left
    (P := (@Etale : MorphismProperty Scheme.{u})) (Q := ⊤) f p ▸ pullback.lift_fst _ _ _

/-- The first projections of the comparison for a composite base change. -/
public lemma smallEtaleBaseChangeComp'_fst_fst {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) :
    ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U).left ≫
        pullback.fst ((smallEtaleBaseChange g).obj U).hom f ≫ pullback.fst U.hom g =
      pullback.fst U.hom fg := by
  subst hfg
  let := smallEtaleHasPullbacksAlong f
  let := smallEtaleHasPullbacksAlong g
  let := smallEtaleIsStableUnderBaseChangeAlong f
  let := smallEtaleIsStableUnderBaseChangeAlong g
  exact MorphismProperty.Over.pullbackComp_left_fst_fst
    (P := (@Etale : MorphismProperty Scheme.{u})) (Q := ⊤) f g U

/-- The `snd`-component of a morphism into an iterated base change is forced. -/
public lemma smallEtaleBaseChange_fst_snd {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    {A : W.Etale} {V : Y.Etale}
    (p : A ⟶ (smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj V)) :
    p.left ≫ pullback.fst ((smallEtaleBaseChange g).obj V).hom f ≫ pullback.snd V.hom g =
      A.hom ≫ f :=
  (congrArg (fun z => p.left ≫ z)
      (pullback.condition (f := ((smallEtaleBaseChange g).obj V).hom) (g := f))).trans
    (congrArg (fun z => z ≫ f) (smallEtaleBaseChange_w f p))

private lemma smallEtaleBaseChange_fst_fst_snd {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) {A : W.Etale} {U : Z.Etale}
    (p : A ⟶ (smallEtaleBaseChange f).obj
      ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U))) :
    p.left ≫ pullback.fst ((smallEtaleBaseChange g).obj
          ((smallEtaleBaseChange h).obj U)).hom f ≫
        pullback.fst ((smallEtaleBaseChange h).obj U).hom g ≫ pullback.snd U.hom h =
      (A.hom ≫ f) ≫ g :=
  (congrArg
      (fun z => p.left ≫ pullback.fst ((smallEtaleBaseChange g).obj
        ((smallEtaleBaseChange h).obj U)).hom f ≫ z)
      (pullback.condition (f := ((smallEtaleBaseChange h).obj U).hom) (g := g))).trans
    (congrArg (fun z => z ≫ g) (smallEtaleBaseChange_fst_snd f g p))

/-- The composite projection of a threefold iterated base change onto the original object. -/
private abbrev smallEtaleBaseChangeTripleFst {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (U : Z.Etale) :
    Limits.pullback ((smallEtaleBaseChange g).obj
        ((smallEtaleBaseChange h).obj U)).hom f ⟶ U.left :=
  pullback.fst ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U)).hom f ≫
    pullback.fst ((smallEtaleBaseChange h).obj U).hom g ≫ pullback.fst U.hom h

private lemma smallEtaleBaseChange_triple_hom_ext {W X Y Z : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) {A : W.Etale} {U : Z.Etale}
    {p q : A ⟶ (smallEtaleBaseChange f).obj
      ((smallEtaleBaseChange g).obj ((smallEtaleBaseChange h).obj U))}
    (hpq : p.left ≫ smallEtaleBaseChangeTripleFst f g h U =
      q.left ≫ smallEtaleBaseChangeTripleFst f g h U) : p = q :=
  smallEtaleBaseChange_hom_ext f (pullback.hom_ext
    (pullback.hom_ext hpq
      ((smallEtaleBaseChange_fst_fst_snd f g h p).trans
        (smallEtaleBaseChange_fst_fst_snd f g h q).symm))
    ((smallEtaleBaseChange_fst_snd f g p).trans (smallEtaleBaseChange_fst_snd f g q).symm))

/-- Associativity of the base-change comparison for small étale sites: for `f : W ⟶ X`,
`g : X ⟶ Y`, `h : Y ⟶ Z` the two ways of comparing base change along a threefold composite with
the composite of the three base changes agree. -/
public theorem smallEtaleBaseChangeComp'_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : W ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    (smallEtaleBaseChangeComp' f gh fgh h₂).hom ≫
        Functor.whiskerRight (smallEtaleBaseChangeComp' g h gh hgh).hom
          (smallEtaleBaseChange f) =
      (smallEtaleBaseChangeComp' fg h fgh h₁).hom ≫
        Functor.whiskerLeft (smallEtaleBaseChange h)
            (smallEtaleBaseChangeComp' f g fg hfg).hom ≫
          (Functor.associator _ _ _).inv := by
  refine NatTrans.ext (funext fun U => smallEtaleBaseChange_triple_hom_ext f g h ?_)
  have hL : ((smallEtaleBaseChangeComp' f gh fgh h₂).hom.app U).left ≫
      ((smallEtaleBaseChange f).map
          ((smallEtaleBaseChangeComp' g h gh hgh).hom.app U)).left ≫
        smallEtaleBaseChangeTripleFst f g h U = pullback.fst U.hom fgh :=
    Eq.trans
      (congrArg (fun z => ((smallEtaleBaseChangeComp' f gh fgh h₂).hom.app U).left ≫ z)
        (Eq.trans
          (congrArg
            (fun z => z ≫ pullback.fst ((smallEtaleBaseChange h).obj U).hom g ≫
              pullback.fst U.hom h)
            (smallEtaleBaseChange_map_left_fst f
              ((smallEtaleBaseChangeComp' g h gh hgh).hom.app U)))
          (congrArg
            (fun z => pullback.fst ((smallEtaleBaseChange gh).obj U).hom f ≫ z)
            (smallEtaleBaseChangeComp'_fst_fst g h gh hgh U))))
      (smallEtaleBaseChangeComp'_fst_fst f gh fgh h₂ U)
  have hR : ((smallEtaleBaseChangeComp' fg h fgh h₁).hom.app U).left ≫
      ((smallEtaleBaseChangeComp' f g fg hfg).hom.app
          ((smallEtaleBaseChange h).obj U)).left ≫
        smallEtaleBaseChangeTripleFst f g h U = pullback.fst U.hom fgh :=
    Eq.trans
      (congrArg (fun z => ((smallEtaleBaseChangeComp' fg h fgh h₁).hom.app U).left ≫ z)
        (congrArg (fun z => z ≫ pullback.fst U.hom h)
          (smallEtaleBaseChangeComp'_fst_fst f g fg hfg
            ((smallEtaleBaseChange h).obj U))))
      (smallEtaleBaseChangeComp'_fst_fst fg h fgh h₁ U)
  exact hL.trans hR.symm

/-- The direct image `f_*𝓕` of a presheaf of sets `𝓕` on the small étale site of `X` along
`f : X ⟶ Y`: the presheaf on the small étale site of `Y` sending `V/Y` to `𝓕(V ×_Y X / X)`. -/
@[stacks 03PW]
public def smallEtalePresheafPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((X.Etale)ᵒᵖ ⥤ Type w) ⥤ ((Y.Etale)ᵒᵖ ⥤ Type w) :=
  (Functor.whiskeringLeft _ _ _).obj (smallEtaleBaseChange f).op

/-- The value of the direct image presheaf: `(f_*𝓕)(V/Y) = 𝓕((V ×_Y X)/X)`. -/
public lemma smallEtalePresheafPushforward_obj_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : (X.Etale)ᵒᵖ ⥤ Type w) (V : Y.Etale) :
    ((smallEtalePresheafPushforward f).obj F).obj (Opposite.op V) =
      F.obj (Opposite.op ((smallEtaleBaseChange f).obj V)) :=
  rfl

/-- The étale `X`-scheme at which the direct image is evaluated is the fibre product
`V ×_Y X`, over `X` by the second projection. -/
public lemma smallEtaleBaseChange_obj_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    ((smallEtaleBaseChange f).obj V).hom = pullback.snd V.hom f :=
  rfl

/-- Direct image along a morphism of schemes, for sheaves on the small étale sites. -/
public abbrev smallEtalePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type w)
    [Category.{w'} A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous A (smallEtaleTopology Y)
    (smallEtaleTopology X)

/-- The direct image along a composite is the composite of the direct images, with the composite
named. -/
public def smallEtalePushforwardComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (A : Type w) [Category.{w'} A] :
    smallEtalePushforward f A ⋙ smallEtalePushforward g A ≅ smallEtalePushforward fg A :=
  Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp' f g fg hfg).symm A _ _ _

private lemma push_map_hom_app {X Y : Scheme.{u}} (h : X ⟶ Y) (A : Type w) [Category.{w'} A]
    {F G : Sheaf (smallEtaleTopology X) A} (x : F ⟶ G) (U : (Y.Etale)ᵒᵖ) :
    ((smallEtalePushforward h A).map x).hom.app U =
      x.hom.app (Opposite.op ((smallEtaleBaseChange h).obj U.unop)) := rfl

private lemma push_comp'_hom_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : Type w) [Category.{w'} A]
    (F : Sheaf (smallEtaleTopology X) A) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforwardComp' f g fg hfg A).hom.app F).hom.app U =
      F.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) :=
  Category.id_comp _

/-- Associativity of the direct-image comparison for small étale sites. -/
public theorem smallEtalePushforwardComp'_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (A : Type w) [Category.{w'} A] :
    Functor.isoWhiskerRight (smallEtalePushforwardComp' f g fg hfg A)
          (smallEtalePushforward h A) ≪≫
        smallEtalePushforwardComp' fg h fgh h₁ A =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallEtalePushforward f A)
            (smallEtalePushforwardComp' g h gh hgh A) ≪≫
          smallEtalePushforwardComp' f gh fgh h₂ A := by
  have hp := smallEtaleBaseChangeComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂
  refine Iso.ext (NatTrans.ext (funext fun F =>
    Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
  have hpU := congrArg (fun z => NatTrans.app z U.unop) hp
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, ObjectProperty.FullSubcategory.comp_hom, push_map_hom_app,
    push_comp'_hom_app_hom_app, Category.id_comp]
  exact ((F.obj.map_comp
        (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app
          ((smallEtaleBaseChange h).obj U.unop)))
        (Opposite.op ((smallEtaleBaseChangeComp' fg h fgh h₁).hom.app U.unop))).symm.trans
      (congrArg F.obj.map (congrArg Quiver.Hom.op hpU.symm))).trans
    (F.obj.map_comp
      (Opposite.op ((smallEtaleBaseChange f).map
        ((smallEtaleBaseChangeComp' g h gh hgh).hom.app U.unop)))
      (Opposite.op ((smallEtaleBaseChangeComp' f gh fgh h₂).hom.app U.unop)))

/-- The cocycle identity of the inverses of the direct-image comparisons, evaluated at a
sheaf. -/
public lemma smallEtalePushforwardComp'_inv_app_cocycle {T X Y Z : Scheme.{u}} (f : T ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (A : Type w) [Category.{w'} A]
    (F : Sheaf (smallEtaleTopology T) A) :
    (smallEtalePushforwardComp' fg h fgh h₁ A).inv.app F ≫
        (smallEtalePushforward h A).map
          ((smallEtalePushforwardComp' f g fg hfg A).inv.app F) =
      (smallEtalePushforwardComp' f gh fgh h₂ A).inv.app F ≫
        (smallEtalePushforwardComp' g h gh hgh A).inv.app
          ((smallEtalePushforward f A).obj F) :=
  (congrArg (fun z => NatTrans.app (Iso.inv z) F)
      (smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂ A)).trans
    (Category.comp_id _)

/-- Transposing a natural transformation of left adjoints across the adjunctions. -/
public lemma conjugateEquiv_homEquiv_symm {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {X : C} {Y : D} (χ : X ⟶ R₁.obj Y) :
    α.app X ≫ (adj₁.homEquiv X Y).symm χ =
      (adj₂.homEquiv X Y).symm (χ ≫ (conjugateEquiv adj₁ adj₂ α).app Y) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, conjugateEquiv_counit, NatTrans.naturality_assoc]

/-- The cocycle identity satisfied by the maps adjoint to a compatible family of comparison
isomorphisms of right adjoints. -/
public lemma leftAdjointCompIso_inv_homEquiv_symm {C₀ C₁ C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁)
    {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀}
    (adj : L ⊣ R) (e : R₂ ⋙ R₁ ≅ R) {X : C₀} {Y₁ : C₁} {Y₂ : C₂} (φ : X ⟶ R₁.obj Y₁)
    (ψ : Y₁ ⟶ R₂.obj Y₂) :
    (Adjunction.leftAdjointCompIso adj₁ adj₂ adj e).inv.app X ≫
        L₂.map ((adj₁.homEquiv X Y₁).symm φ) ≫ (adj₂.homEquiv Y₁ Y₂).symm ψ =
      (adj.homEquiv X Y₂).symm (φ ≫ R₁.map ψ ≫ e.hom.app Y₂) := by
  have h₁ : L₂.map ((adj₁.homEquiv X Y₁).symm φ) ≫ (adj₂.homEquiv Y₁ Y₂).symm ψ =
      ((adj₁.comp adj₂).homEquiv X Y₂).symm (φ ≫ R₁.map ψ) := by
    simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
    rw [Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm]
  rw [h₁, conjugateEquiv_homEquiv_symm (adj₁.comp adj₂) adj,
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv, Category.assoc]

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint] (c : Cone D)
  (F : Sheaf (smallEtaleTopology c.pt) A)

/-- The direct image `f_{i,*}𝓕` of a sheaf on the limit along the projection `f_i : X ⟶ X_i`. -/
public abbrev coneDirectImage (i : Iᵒᵖ) : Sheaf (smallEtaleTopology (D.obj i)) A :=
  (smallEtalePushforward (c.π.app i) A).obj F

/-- The canonical identification `f_{i,*}𝓕 ≅ f_{i'i,*} f_{i',*}𝓕`, coming from
`f_i = f_{i'} ≫ f_{i'i}`. -/
public def coneDirectImageComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    smallEtalePushforward (c.π.app i) A ⋙ systemPushforward D A a ≅
      smallEtalePushforward (c.π.app j) A :=
  smallEtalePushforwardComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm A

/-- The canonical map `φ_{i'i} : f_{i'i}^{-1} f_{i,*}𝓕 ⟶ f_{i',*}𝓕`, adjoint to
`Stacks.EtaleCohomology.coneDirectImageComp`. -/
public def coneDirectImageMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback D A a).obj (coneDirectImage D A c F j) ⟶ coneDirectImage D A c F i :=
  ((systemAdjunction D A a).homEquiv _ _).symm
    ((coneDirectImageComp D A c a).inv.app F)

/-- Let `(X_i, f_{i'i})` be an inverse system of schemes, let `f_i : X ⟶ X_i` be the projections
of a cone over it, and let `𝓕` be a sheaf on the small étale site of `X`. The direct images
`f_{i,*}𝓕`, with the canonical maps `φ_{i'i} : f_{i'i}^{-1} f_{i,*}𝓕 ⟶ f_{i',*}𝓕` adjoint to the
identification `f_{i,*}𝓕 ≅ f_{i'i,*} f_{i',*}𝓕` given by `f_i = f_{i'} ≫ f_{i'i}`, form a system
of sheaves on `(X_i, f_{i'i})` in the sense of Stacks 0EZL. -/
@[stacks 0EYN "the system of sheaves"]
public def directImageSystem : EtaleSheafSystem D A where
  obj i := coneDirectImage D A c F i
  map a := coneDirectImageMap D A c F a
  map_comp {i j k} a b := by
    refine (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A b) (systemAdjunction D A a)
      (systemAdjunction D A (a ≫ b)) (systemPushforwardComp D A a b) _ _).trans ?_
    refine congrArg ((systemAdjunction D A (a ≫ b)).homEquiv _ _).symm ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z => z ≫ (systemPushforwardComp D A a b).hom.app
      (coneDirectImage D A c F i)) (smallEtalePushforwardComp'_inv_app_cocycle (c.π.app i)
        (D.map a) (D.map b) (c.π.app j) (c.w a).symm (D.map (a ≫ b)) (D.map_comp a b)
        (c.π.app k) (c.w b).symm (c.w (a ≫ b)).symm A F)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun z => (coneDirectImageComp D A c (a ≫ b)).inv.app F ≫ z)
      ((smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b) A).inv_hom_id_app _)).trans (Category.comp_id _)

end Stacks.EtaleCohomology

end
