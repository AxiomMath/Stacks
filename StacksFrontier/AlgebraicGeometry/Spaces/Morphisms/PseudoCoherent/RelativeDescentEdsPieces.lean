module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueingDescentBaseChange

/-!
# Situation 0DKU over the pieces of an elementary distinguished square of `X₀`

In Situation 0DKU let `(U₀ ⊆ X₀, V₀ ⟶ X₀)` be an elementary distinguished square of the space
`X₀` over the chosen stage.  Each of its three pieces `U₀`, `V₀` and `P₀ = U₀ ×_{X₀} V₀` is
étale over `X₀`, and, once it is of finite presentation over `X₀`, it is the space over the
chosen stage of a new Situation 0DKU with the same inverse system: its base changes to the
stages and to the limit are the pieces of the base changes of the square along `Xᵢ ⟶ X₀` and
`X ⟶ X₀` (Stacks 08GN, part (2)).  These are the three situations of the square step of the
source's proof of Stacks 0DKW.

The data of a Situation 0DKU above its inverse system is packaged separately, as
`AlgebraicGeometry.Space.RelativeDescentSituation.SourceData`, so that the situations over the
pieces, and the situations met in the two inductions of the proof, are all situations with
*literally* the same inverse system, limit and chosen stage as the given one.  A situation is
recovered from its own source data by `withSource`, definitionally.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.SourceData`: the data of Situation 0DKU
  above a fixed inverse system, limit and chosen stage.
* `AlgebraicGeometry.Space.RelativeDescentSituation.withSource`: the situation with the inverse
  system of `D` and the given source data.
* `AlgebraicGeometry.Space.RelativeDescentSituation.edsOpenSource`, `edsEtaleSource`,
  `edsInterSource`: the source data over the three pieces of an elementary distinguished
  square of `X₀`.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isSchemeLimit_withSource`: the limit stays a
  limit of schemes, the inverse system being unchanged.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 08GN](https://stacks.math.columbia.edu/tag/08GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_RelativeDescentEdsPieces {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RelativeDescentEdsPieces
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section EdsPreimageMaps

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {W W' : AlgebraicSpaces B S hS} (p : W ⟶ W₀) (p' : W' ⟶ W₀) (q : W' ⟶ W)
  (hq : q ≫ p = p')

/-- The map of the open subspaces induced by `q` lies over `q`. -/
@[reassoc]
theorem edsPreimageOpenMap_hom_comp_ι :
    (edsPreimageOpenMap hsq p p' q hq).hom ≫ (U₀.preimage p.hom).ι =
      (U₀.preimage p'.hom).ι ≫ q.hom :=
  (congrArg (fun φ => φ.hom) (edsPreimageOpenMap_comp hsq p p' q hq)).symm

/-- The map of the étale algebraic spaces induced by `q` lies over `q`. -/
@[reassoc]
theorem edsPreimageEtaleMap_hom_comp_snd :
    (edsPreimageEtaleMap hsq p p' q hq).hom ≫ pullback.snd f₀ p.hom =
      pullback.snd f₀ p'.hom ≫ q.hom :=
  pullback.lift_snd _ _ _

/-- The map of the étale algebraic spaces induced by `q` lies over `V₀`. -/
theorem edsPreimageEtaleMap_hom_comp_fst :
    (edsPreimageEtaleMap hsq p p' q hq).hom ≫ pullback.fst f₀ p.hom = pullback.fst f₀ p'.hom :=
  pullback.lift_fst _ _ _

/-- The map of the open subspaces induced by `q` lies over `U₀`. -/
theorem edsPreimageOpenMap_hom_comp_fromPreimage :
    (edsPreimageOpenMap hsq p p' q hq).hom ≫ U₀.fromPreimage p.hom = U₀.fromPreimage p'.hom := by
  refine (cancel_mono U₀.ι).1 ?_
  have h₁ : U₀.fromPreimage p.hom ≫ U₀.ι = (U₀.preimage p.hom).ι ≫ p.hom :=
    (Subfunctor.isPullback_preimage p.hom U₀).w
  have h₂ : U₀.fromPreimage p'.hom ≫ U₀.ι = (U₀.preimage p'.hom).ι ≫ p'.hom :=
    (Subfunctor.isPullback_preimage p'.hom U₀).w
  have h₃ := edsPreimageOpenMap_hom_comp_ι hsq p p' q hq
  have h₄ : q.hom ≫ p.hom = p'.hom := congrArg (fun φ => φ.hom) hq
  exact ((Category.assoc _ _ _).trans (congrArg _ h₁)).trans
    (((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p.hom) h₃).trans (Category.assoc _ _ _))).trans
      ((congrArg _ h₄).trans h₂.symm))

/-- The map of the intersections induced by `q` lies over `q`. -/
theorem edsPreimageInterMap_comp_edsInterHom :
    edsPreimageInterMap hsq p p' q hq ≫ edsInterHom B S hS (edsPreimage hsq p) =
      edsInterHom B S hS (edsPreimage hsq p') ≫ q := by
  rw [edsInterHom, edsInterHom, ← Category.assoc, ← edsFst_comp_edsPreimageOpenMap,
    Category.assoc, ← edsPreimageOpenMap_comp, Category.assoc]

/-- The comparison of the open subspace of the base change of the square along `p` with the
open subspace `U₀`, as a morphism of algebraic spaces. -/
def edsPreimageOpenToBase : edsOpen B S hS (edsPreimage hsq p) ⟶ edsOpen B S hS hsq :=
  ObjectProperty.homMk (U₀.fromPreimage p.hom)

/-- The comparison of the étale space of the base change of the square along `p` with the étale
space `V₀`, as a morphism of algebraic spaces. -/
def edsPreimageEtaleToBase : edsEtale B S hS (edsPreimage hsq p) ⟶ edsEtale B S hS hsq :=
  ObjectProperty.homMk (pullback.fst f₀ p.hom)

/-- The comparison of the intersection of the base change of the square along `p` with the
intersection `U₀ ×_{W₀} V₀` of the square, as a morphism of algebraic spaces. -/
def edsPreimageInterToBase : edsInter B S hS (edsPreimage hsq p) ⟶ edsInter B S hS hsq :=
  ObjectProperty.homMk (RelativeDescentSituation.pullbackPreimageιLift U₀ f₀ p.hom)

/-- The map of the intersections induced by `q` lies over the intersection `U₀ ×_{W₀} V₀`. -/
theorem edsPreimageInterMap_hom_comp_pullbackPreimageιLift :
    (edsPreimageInterMap hsq p p' q hq).hom ≫
        RelativeDescentSituation.pullbackPreimageιLift U₀ f₀ p.hom =
      RelativeDescentSituation.pullbackPreimageιLift U₀ f₀ p'.hom := by
  have h₁ : ∀ {Z : AlgebraicSpaces B S hS} (r : Z ⟶ W₀),
      edsPreimageInterToBase hsq r ≫ edsFst B S hS hsq =
        edsFst B S hS (edsPreimage hsq r) ≫ edsPreimageOpenToBase hsq r := fun r =>
    ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)
  have h₂ : ∀ {Z : AlgebraicSpaces B S hS} (r : Z ⟶ W₀),
      edsPreimageInterToBase hsq r ≫ edsSnd B S hS hsq =
        edsSnd B S hS (edsPreimage hsq r) ≫ edsPreimageEtaleToBase hsq r := fun r =>
    ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _)
  have hU : edsPreimageOpenMap hsq p p' q hq ≫ edsPreimageOpenToBase hsq p =
      edsPreimageOpenToBase hsq p' :=
    ObjectProperty.hom_ext _ (edsPreimageOpenMap_hom_comp_fromPreimage hsq p p' q hq)
  have hV : edsPreimageEtaleMap hsq p p' q hq ≫ edsPreimageEtaleToBase hsq p =
      edsPreimageEtaleToBase hsq p' :=
    ObjectProperty.hom_ext _ (edsPreimageEtaleMap_hom_comp_fst hsq p p' q hq)
  have key : edsPreimageInterMap hsq p p' q hq ≫ edsPreimageInterToBase hsq p =
      edsPreimageInterToBase hsq p' := by
    refine (isPullback_edsInter B S hS hsq).hom_ext ?_ ?_
    · rw [Category.assoc, h₁ p, ← Category.assoc, ← edsFst_comp_edsPreimageOpenMap, Category.assoc,
        hU, h₁ p']
    · rw [Category.assoc, h₂ p, ← Category.assoc, ← edsSnd_comp_edsPreimageEtaleMap, Category.assoc,
        hV, h₂ p']
  exact congrArg (fun φ => φ.hom) key

end EdsPreimageMaps

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]

/-! ### Source data above a fixed inverse system -/

variable (B S hS) in
/-- **The data of Situation 0DKU above a fixed inverse system.**  For an inverse system `Y` of
presheaves on the site, a cone `c` on it and a chosen stage `i₀`: a flat algebraic space of
finite presentation over `Y i₀`, its base changes to the later stages and to the vertex of `c`,
and the transition maps and projections between them, with the fields of
`AlgebraicGeometry.Space.RelativeDescentSituation` that do not concern the inverse system. -/
structure SourceData (Y : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (c : Cone Y) (i₀ : I) where
  /-- The space over the chosen stage. -/
  X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its structure morphism. -/
  p₀ : X₀ ⟶ Y.obj (op i₀)
  /-- The source is an algebraic space. -/
  initial_isAlgebraicSpace : IsAlgebraicSpace B S hS X₀
  /-- The structure morphism is flat. -/
  initial_isFlat : IsFlat B S hS p₀
  /-- The structure morphism is of finite presentation. -/
  initial_isFinitePresentation : IsFinitePresentation B S hS p₀
  /-- The base change at each later stage. -/
  Xᵢ : ∀ i : I, i₀ ≤ i → ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Each base change is an algebraic space. -/
  stageX_isAlgebraicSpace : ∀ (i : I) (hi : i₀ ≤ i), IsAlgebraicSpace B S hS (Xᵢ i hi)
  /-- Its projection to the initial space. -/
  toX₀ : ∀ (i : I) (hi : i₀ ≤ i), Xᵢ i hi ⟶ X₀
  /-- Its projection to the current base. -/
  toYᵢ : ∀ (i : I) (hi : i₀ ≤ i), Xᵢ i hi ⟶ Y.obj (op i)
  /-- Each stage is the prescribed base change. -/
  stage_isPullback : ∀ (i : I) (hi : i₀ ≤ i),
    IsPullback (toYᵢ i hi) (toX₀ i hi) (Y.map (homOfLE hi).op) p₀
  /-- Transition maps between the base changes. -/
  fᵢⱼ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (_hij : i ≤ j), Xᵢ j hj ⟶ Xᵢ i hi
  /-- A transition map lies over the corresponding base transition. -/
  fᵢⱼ_toYᵢ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j),
    fᵢⱼ i j hi hj hij ≫ toYᵢ i hi = toYᵢ j hj ≫ Y.map (homOfLE hij).op
  /-- A transition map preserves the projection to the initial space. -/
  fᵢⱼ_toX₀ : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j),
    fᵢⱼ i j hi hj hij ≫ toX₀ i hi = toX₀ j hj
  /-- The base change at the limit. -/
  X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The limit base change is an algebraic space. -/
  X_isAlgebraicSpace : IsAlgebraicSpace B S hS X
  /-- Its projection to the initial space. -/
  toInitial : X ⟶ X₀
  /-- Its projection to the limit base. -/
  toLimit : X ⟶ c.pt
  /-- The limit-stage square is cartesian. -/
  limit_isPullback : IsPullback toLimit toInitial (c.π.app (op i₀)) p₀
  /-- Projection of the limit-stage base change to each later base change. -/
  fᵢ : ∀ (i : I) (hi : i₀ ≤ i), X ⟶ Xᵢ i hi
  /-- The projection is over the corresponding projection of the base limit. -/
  fᵢ_toYᵢ : ∀ (i : I) (hi : i₀ ≤ i), fᵢ i hi ≫ toYᵢ i hi = toLimit ≫ c.π.app (op i)
  /-- The projection preserves the map to the initial space. -/
  fᵢ_toX₀ : ∀ (i : I) (hi : i₀ ≤ i), fᵢ i hi ≫ toX₀ i hi = toInitial

variable (D : RelativeDescentSituation B S hS hZ I)

/-- The source data of a situation. -/
def sourceData : SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := D.X₀
  p₀ := D.p₀
  initial_isAlgebraicSpace := D.initial_isAlgebraicSpace
  initial_isFlat := D.initial_isFlat
  initial_isFinitePresentation := D.initial_isFinitePresentation
  Xᵢ := D.Xᵢ
  stageX_isAlgebraicSpace := D.stageX_isAlgebraicSpace
  toX₀ := D.toX₀
  toYᵢ := D.toYᵢ
  stage_isPullback := D.stage_isPullback
  fᵢⱼ := D.fᵢⱼ
  fᵢⱼ_toYᵢ := D.fᵢⱼ_toYᵢ
  fᵢⱼ_toX₀ := D.fᵢⱼ_toX₀
  X := D.X
  X_isAlgebraicSpace := D.X_isAlgebraicSpace
  toInitial := D.toInitial
  toLimit := D.toLimit
  limit_isPullback := D.limit_isPullback
  fᵢ := D.fᵢ
  fᵢ_toYᵢ := D.fᵢ_toYᵢ
  fᵢ_toX₀ := D.fᵢ_toX₀

/-- **The situation with the inverse system of `D` and the source data `F`.** -/
abbrev withSource (F : SourceData B S hS D.Y D.limitCone D.i₀) :
    RelativeDescentSituation B S hS hZ I where
  Y := D.Y
  limitCone := D.limitCone
  isLimit := D.isLimit
  stage_isAlgebraicSpace := D.stage_isAlgebraicSpace
  limit_isAlgebraicSpace := D.limit_isAlgebraicSpace
  stage_isQuasiCompact := D.stage_isQuasiCompact
  stage_isQuasiSeparated := D.stage_isQuasiSeparated
  transition_isAffine := D.transition_isAffine
  i₀ := D.i₀
  X₀ := F.X₀
  p₀ := F.p₀
  initial_isAlgebraicSpace := F.initial_isAlgebraicSpace
  initial_isFlat := F.initial_isFlat
  initial_isFinitePresentation := F.initial_isFinitePresentation
  Xᵢ := F.Xᵢ
  stageX_isAlgebraicSpace := F.stageX_isAlgebraicSpace
  toX₀ := F.toX₀
  toYᵢ := F.toYᵢ
  stage_isPullback := F.stage_isPullback
  fᵢⱼ := F.fᵢⱼ
  fᵢⱼ_toYᵢ := F.fᵢⱼ_toYᵢ
  fᵢⱼ_toX₀ := F.fᵢⱼ_toX₀
  X := F.X
  X_isAlgebraicSpace := F.X_isAlgebraicSpace
  toInitial := F.toInitial
  toLimit := F.toLimit
  limit_isPullback := F.limit_isPullback
  fᵢ := F.fᵢ
  fᵢ_toYᵢ := F.fᵢ_toYᵢ
  fᵢ_toX₀ := F.fᵢ_toX₀

/-- A situation is the situation with its own inverse system and its own source data. -/
theorem withSource_sourceData : D.withSource D.sourceData = D :=
  rfl

/-- The limit of a situation with the inverse system of `D` is a limit of schemes when that of
`D` is: the predicate only concerns the inverse system, its limit and the chosen stage. -/
theorem isSchemeLimit_withSource (F : SourceData B S hS D.Y D.limitCone D.i₀)
    (hD : D.IsSchemeLimit) : (D.withSource F).IsSchemeLimit :=
  ⟨hD.1, fun Z z R => hD.2 Z z
    ⟨R.W, R.c, R.p, R.q, R.isPullback, R.map_p, R.map_q, R.pc, R.qc, R.isPullback_pt, R.π_p,
      R.π_q⟩⟩

/-! ### The pieces of an elementary distinguished square of `X₀` -/

section Pieces

variable {Uo : Subfunctor D.X₀} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {fV : V₀ ⟶ D.X₀}
  (hsq : IsElementaryDistinguishedSquare B S hS D.initialSource.2 Uo fV)

/-- The open immersion `U₀ ⟶ X₀` of the square is flat. -/
theorem isFlat_edsOpen (hsq : IsElementaryDistinguishedSquare B S hS D.initialSource.2 Uo fV) :
    IsFlat B S hS Uo.ι :=
  isFlat_of_isEtale B S hS (isEtale_edsOpenHom B S hS (W := D.initialSource) hsq)

/-- The étale morphism `V₀ ⟶ X₀` of the square is flat. -/
theorem isFlat_edsEtale (hsq : IsElementaryDistinguishedSquare B S hS D.initialSource.2 Uo fV) :
    IsFlat B S hS fV :=
  isFlat_of_isEtale B S hS hsq.isEtale

/-- The morphism `P₀ = U₀ ×_{X₀} V₀ ⟶ X₀` of the square is flat. -/
theorem isFlat_edsInter (hsq : IsElementaryDistinguishedSquare B S hS D.initialSource.2 Uo fV) :
    IsFlat B S hS (pullback.fst Uo.ι fV ≫ Uo.ι) :=
  isFlat_of_isEtale B S hS (isEtale_edsInterHom B S hS (W := D.initialSource) hsq)

/-- **The source data over the open piece `U₀` of the square**, for `U₀ ⟶ X₀` of finite
presentation: the base changes are the open subspaces `Uᵢ = Xᵢ ×_{X₀} U₀` and
`U = X ×_{X₀} U₀`, and the transitions and projections are those induced by the transitions and
projections of `D` (`AlgebraicGeometry.Space.edsPreimageOpenMap`). -/
abbrev edsOpenSource (hfp : IsFinitePresentation B S hS Uo.ι) :
    SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := Uo.toFunctor
  p₀ := Uo.ι ≫ D.p₀
  initial_isAlgebraicSpace := hsq.isOpenSubspace.1
  initial_isFlat := isFlat_comp B S hS hsq.isOpenSubspace.1 D.initial_isAlgebraicSpace
    (D.stage_isAlgebraicSpace D.i₀) _ _ (D.isFlat_edsOpen hsq) D.initial_isFlat
  initial_isFinitePresentation := isFinitePresentation_comp B S hS hsq.isOpenSubspace.1
    D.initial_isAlgebraicSpace (D.stage_isAlgebraicSpace D.i₀) _ _ hfp
    D.initial_isFinitePresentation
  Xᵢ i hi := (edsOpen B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩))).1
  stageX_isAlgebraicSpace i hi :=
    (edsOpen B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩))).2
  toX₀ i hi := Uo.fromPreimage (D.toX₀ i hi)
  toYᵢ i hi := (Uo.preimage (D.toX₀ i hi)).ι ≫ D.toYᵢ i hi
  stage_isPullback i hi :=
    (Subfunctor.isPullback_preimage (D.toX₀ i hi) Uo).flip.paste_horiz (D.stage_isPullback i hi)
  fᵢⱼ i j hi hj hij := (edsPreimageOpenMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    (D.stageToInitial ⟨j, hj⟩) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    (D.sourceTransition_comp_stageToInitial _)).hom
  fᵢⱼ_toYᵢ i j hi hj hij :=
    ((edsPreimageOpenMap_hom_comp_ι_assoc (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
      (D.stageToInitial ⟨j, hj⟩) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
      (D.sourceTransition_comp_stageToInitial _) (D.toYᵢ i hi)).trans
      (congrArg ((Uo.preimage (D.toX₀ j hj)).ι ≫ ·) (D.fᵢⱼ_toYᵢ i j hi hj hij))).trans
      (Category.assoc _ _ _).symm
  fᵢⱼ_toX₀ _ _ _ _ _ := edsPreimageOpenMap_hom_comp_fromPreimage _ _ _ _ _
  X := (edsOpen B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).1
  X_isAlgebraicSpace :=
    (edsOpen B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).2
  toInitial := Uo.fromPreimage D.toInitial
  toLimit := (Uo.preimage D.toInitial).ι ≫ D.toLimit
  limit_isPullback :=
    (Subfunctor.isPullback_preimage D.toInitial Uo).flip.paste_horiz D.limit_isPullback
  fᵢ i hi := (edsPreimageOpenMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    D.limitToInitial (D.sourceProjection ⟨i, hi⟩) (D.sourceProjection_comp_stageToInitial _)).hom
  fᵢ_toYᵢ i hi :=
    ((edsPreimageOpenMap_hom_comp_ι_assoc (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
      D.limitToInitial (D.sourceProjection ⟨i, hi⟩) (D.sourceProjection_comp_stageToInitial _)
      (D.toYᵢ i hi)).trans
      (congrArg ((Uo.preimage D.toInitial).ι ≫ ·) (D.fᵢ_toYᵢ i hi))).trans
      (Category.assoc _ _ _).symm
  fᵢ_toX₀ _ _ := edsPreimageOpenMap_hom_comp_fromPreimage _ _ _ _ _

/-- **The source data over the étale piece `V₀` of the square**, for `V₀ ⟶ X₀` of finite
presentation: the base changes are `Vᵢ = V₀ ×_{X₀} Xᵢ` and `V = V₀ ×_{X₀} X`, with the
transitions and projections of `AlgebraicGeometry.Space.edsPreimageEtaleMap`. -/
abbrev edsEtaleSource (hfp : IsFinitePresentation B S hS fV) :
    SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := V₀
  p₀ := fV ≫ D.p₀
  initial_isAlgebraicSpace := hsq.isAlgebraicSpace
  initial_isFlat := isFlat_comp B S hS hsq.isAlgebraicSpace D.initial_isAlgebraicSpace
    (D.stage_isAlgebraicSpace D.i₀) _ _ (D.isFlat_edsEtale hsq) D.initial_isFlat
  initial_isFinitePresentation := isFinitePresentation_comp B S hS hsq.isAlgebraicSpace
    D.initial_isAlgebraicSpace (D.stage_isAlgebraicSpace D.i₀) _ _ hfp
    D.initial_isFinitePresentation
  Xᵢ i hi :=
    (edsEtale B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩))).1
  stageX_isAlgebraicSpace i hi :=
    (edsEtale B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩))).2
  toX₀ i hi := pullback.fst fV (D.toX₀ i hi)
  toYᵢ i hi := pullback.snd fV (D.toX₀ i hi) ≫ D.toYᵢ i hi
  stage_isPullback i hi :=
    (IsPullback.of_hasPullback fV (D.toX₀ i hi)).flip.paste_horiz (D.stage_isPullback i hi)
  fᵢⱼ i j hi hj hij := (edsPreimageEtaleMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    (D.stageToInitial ⟨j, hj⟩) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    (D.sourceTransition_comp_stageToInitial _)).hom
  fᵢⱼ_toYᵢ i j hi hj hij :=
    ((edsPreimageEtaleMap_hom_comp_snd_assoc (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
      (D.stageToInitial ⟨j, hj⟩) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
      (D.sourceTransition_comp_stageToInitial _) (D.toYᵢ i hi)).trans
      (congrArg (pullback.snd fV (D.toX₀ j hj) ≫ ·) (D.fᵢⱼ_toYᵢ i j hi hj hij))).trans
      (Category.assoc _ _ _).symm
  fᵢⱼ_toX₀ _ _ _ _ _ := edsPreimageEtaleMap_hom_comp_fst _ _ _ _ _
  X := (edsEtale B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).1
  X_isAlgebraicSpace :=
    (edsEtale B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).2
  toInitial := pullback.fst fV D.toInitial
  toLimit := pullback.snd fV D.toInitial ≫ D.toLimit
  limit_isPullback :=
    (IsPullback.of_hasPullback fV D.toInitial).flip.paste_horiz D.limit_isPullback
  fᵢ i hi := (edsPreimageEtaleMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    D.limitToInitial (D.sourceProjection ⟨i, hi⟩) (D.sourceProjection_comp_stageToInitial _)).hom
  fᵢ_toYᵢ i hi :=
    ((edsPreimageEtaleMap_hom_comp_snd_assoc (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
      D.limitToInitial (D.sourceProjection ⟨i, hi⟩) (D.sourceProjection_comp_stageToInitial _)
      (D.toYᵢ i hi)).trans
      (congrArg (pullback.snd fV D.toInitial ≫ ·) (D.fᵢ_toYᵢ i hi))).trans
      (Category.assoc _ _ _).symm
  fᵢ_toX₀ _ _ := edsPreimageEtaleMap_hom_comp_fst _ _ _ _ _

/-- **The source data over the intersection `P₀ = U₀ ×_{X₀} V₀` of the square**, for
`P₀ ⟶ X₀` of finite presentation: the base changes are the intersections of the base changes of
the square, with the transitions and projections of
`AlgebraicGeometry.Space.edsPreimageInterMap`. -/
abbrev edsInterSource (hfp : IsFinitePresentation B S hS (pullback.fst Uo.ι fV ≫ Uo.ι)) :
    SourceData B S hS D.Y D.limitCone D.i₀ where
  X₀ := pullback Uo.ι fV
  p₀ := (pullback.fst Uo.ι fV ≫ Uo.ι) ≫ D.p₀
  initial_isAlgebraicSpace := (edsInter B S hS (W := D.initialSource) hsq).2
  initial_isFlat := isFlat_comp B S hS (edsInter B S hS (W := D.initialSource) hsq).2
    D.initial_isAlgebraicSpace (D.stage_isAlgebraicSpace D.i₀) _ _ (D.isFlat_edsInter hsq)
    D.initial_isFlat
  initial_isFinitePresentation := isFinitePresentation_comp B S hS
    (edsInter B S hS (W := D.initialSource) hsq).2 D.initial_isAlgebraicSpace
    (D.stage_isAlgebraicSpace D.i₀) _ _ hfp D.initial_isFinitePresentation
  Xᵢ i hi := (edsInter B S hS (edsPreimage (W₀ := D.initialSource) hsq
    (D.stageToInitial ⟨i, hi⟩))).1
  stageX_isAlgebraicSpace i hi :=
    (edsInter B S hS (edsPreimage (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩))).2
  toX₀ i hi := pullbackPreimageιLift Uo fV (D.toX₀ i hi)
  toYᵢ i hi := (pullback.fst (Uo.preimage (D.toX₀ i hi)).ι (pullback.snd fV (D.toX₀ i hi)) ≫
    (Uo.preimage (D.toX₀ i hi)).ι) ≫ D.toYᵢ i hi
  stage_isPullback i hi :=
    (isPullback_pullbackPreimageιLift Uo fV (D.toX₀ i hi)).flip.paste_horiz
      (D.stage_isPullback i hi)
  fᵢⱼ i j hi hj hij := (edsPreimageInterMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    (D.stageToInitial ⟨j, hj⟩) (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    (D.sourceTransition_comp_stageToInitial _)).hom
  fᵢⱼ_toYᵢ i j hi hj hij :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toYᵢ i hi)
      (congrArg (fun φ => φ.hom) (edsPreimageInterMap_comp_edsInterHom (W₀ := D.initialSource) hsq
        (D.stageToInitial ⟨i, hi⟩) (D.stageToInitial ⟨j, hj⟩)
        (D.sourceTransition (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
        (D.sourceTransition_comp_stageToInitial _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg _ (D.fᵢⱼ_toYᵢ i j hi hj hij)).trans (Category.assoc _ _ _).symm)))
  fᵢⱼ_toX₀ _ _ _ _ _ := edsPreimageInterMap_hom_comp_pullbackPreimageιLift _ _ _ _ _
  X := (edsInter B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).1
  X_isAlgebraicSpace :=
    (edsInter B S hS (edsPreimage (W₀ := D.initialSource) hsq D.limitToInitial)).2
  toInitial := pullbackPreimageιLift Uo fV D.toInitial
  toLimit := (pullback.fst (Uo.preimage D.toInitial).ι (pullback.snd fV D.toInitial) ≫
    (Uo.preimage D.toInitial).ι) ≫ D.toLimit
  limit_isPullback :=
    (isPullback_pullbackPreimageιLift Uo fV D.toInitial).flip.paste_horiz D.limit_isPullback
  fᵢ i hi := (edsPreimageInterMap (W₀ := D.initialSource) hsq (D.stageToInitial ⟨i, hi⟩)
    D.limitToInitial (D.sourceProjection ⟨i, hi⟩) (D.sourceProjection_comp_stageToInitial _)).hom
  fᵢ_toYᵢ i hi :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toYᵢ i hi)
      (congrArg (fun φ => φ.hom) (edsPreimageInterMap_comp_edsInterHom (W₀ := D.initialSource) hsq
        (D.stageToInitial ⟨i, hi⟩) D.limitToInitial (D.sourceProjection ⟨i, hi⟩)
        (D.sourceProjection_comp_stageToInitial _)))).trans ((Category.assoc _ _ _).trans
      ((congrArg _ (D.fᵢ_toYᵢ i hi)).trans (Category.assoc _ _ _).symm)))
  fᵢ_toX₀ _ _ := edsPreimageInterMap_hom_comp_pullbackPreimageιLift _ _ _ _ _

end Pieces

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
