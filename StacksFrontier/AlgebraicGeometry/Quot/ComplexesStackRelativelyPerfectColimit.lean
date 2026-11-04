module

public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.CategoryTheory.Limits.PullbackOfLimitCones

/-!
# Stacks 0DKW for the base changes of Situation 0DLE along a cofiltered system of test schemes

In Situation 0DLE let `F : I ⥤ SchemesOver Y` be a cofiltered system of affine test schemes with
limit `T` (a cone `d` over `F` whose vertex is affine and whose underlying schemes form a
limit).  This file reads Stacks 0DKW, stated in Situation 0DKU as
`AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`, for the base
changes `X_{F i}` and `X_T`, in the shape
`AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit` that the proof of
Stacks 0DLJ consumes.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.descentSituation`: for a final functor
  `G : α ⥤ Iᵒᵖ` from a directed preorder and a stage `a₀ : α`, the Situation 0DKU whose stages
  are the test schemes `F (G a)` read as algebraic spaces, whose limit is `T`, and whose flat
  finitely presented space over the stage `a₀` is `X_{F (G a₀)}`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isSchemeLimit_descentSituation`: the limit of
  `descentSituation` is a limit of schemes
  (`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`), so that Stacks 0DKW, stated
  under that predicate, applies to it.
* `AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectColimit_of_relativeDescentSituation`
  is the reading of Stacks 0DKW for the base changes of Situation 0DLE.

## Implementation notes

Situation 0DKU is indexed by a directed preorder, the system `F` by a cofiltered category.
Stacks 0032 (`CategoryTheory.IsFiltered.exists_directed`) gives a final functor `G : α ⥤ Iᵒᵖ`
from a directed partial order, and `G.leftOp` is initial, so `T` is also the limit of the
restricted system.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **Regrouping a conjugation.**  For comparisons `e_{kr} : L_r ≅ L_p ⋙ L_k`,
`e_k : L_k ≅ L_g ⋙ L_f`, `e_r : L_r ≅ L_q ⋙ L_f` and `e_q : L_q ≅ L_p ⋙ L_g` satisfying the
associativity coherence, conjugating a morphism `L_g L_p M ⟶ L_g L_p N` first by `e_k` and then
by `e_{kr}` is conjugating it first by `e_q` and then by `e_r`. -/
theorem CategoryTheory.Functor.conj_conjHom_eq {C₀ C₁ C₂ C₃ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] [Category* C₃] {Lp : C₃ ⥤ C₂} {Lg : C₂ ⥤ C₁} {Lf : C₁ ⥤ C₀}
    {Lk : C₂ ⥤ C₀} {Lq : C₃ ⥤ C₁} {Lr : C₃ ⥤ C₀} (ekr : Lr ≅ Lp ⋙ Lk) (ek : Lk ≅ Lg ⋙ Lf)
    (er : Lr ≅ Lq ⋙ Lf) (eq : Lq ≅ Lp ⋙ Lg)
    (H : ekr ≪≫ Functor.isoWhiskerLeft Lp ek =
      er ≪≫ Functor.isoWhiskerRight eq Lf ≪≫ Functor.associator Lp Lg Lf)
    {M N : C₃} (ψ : Lg.obj (Lp.obj M) ⟶ Lg.obj (Lp.obj N)) :
    ekr.hom.app M ≫ Functor.conjHom ek ψ ≫ ekr.inv.app N =
      Functor.conjHom er (eq.hom.app M ≫ ψ ≫ eq.inv.app N) := by
  have hM := congrArg (fun e => e.hom.app M) H
  have hN := congrArg (fun e => e.inv.app N) H
  dsimp at hM hN
  simp only [Category.comp_id, Category.id_comp] at hM hN
  simp only [Functor.conjHom, Functor.map_comp, Category.assoc]
  rw [hN, reassoc_of% hM]

/-- A morphism is recovered from its conjugate by the components of a natural isomorphism. -/
theorem CategoryTheory.Iso.eq_of_conj_app_eq {C D : Type*} [Category* C] [Category* D]
    {P Q : C ⥤ D} (e : P ≅ Q) {M N : C} {φ : P.obj M ⟶ P.obj N} {χ : Q.obj M ⟶ Q.obj N}
    {ρ : P.obj M ⟶ P.obj N} (h₁ : e.inv.app M ≫ φ ≫ e.hom.app N = χ)
    (h₂ : e.hom.app M ≫ χ ≫ e.inv.app N = ρ) : φ = ρ := by
  subst h₁ h₂
  simp

/-- A square is a pullback as soon as its image under the Yoneda embedding is one. -/
theorem CategoryTheory.IsPullback.of_yoneda_map {C : Type*} [Category* C]
    {W X Y Z : C} {a : W ⟶ X} {b : W ⟶ Y} {c : X ⟶ Z} {e : Y ⟶ Z}
    (H : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map e)) :
    IsPullback a b c e :=
  IsPullback.of_map yoneda (yoneda.map_injective
    ((yoneda.map_comp _ _).trans (H.w.trans (yoneda.map_comp _ _).symm))) H

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : ComplexesSituation B S hS) {I : Type u} [Category.{u} I] [IsCofiltered I]
  (F : I ⥤ SchemesOver D.Y) (d : Cone F) {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)]
  (G : α ⥤ Iᵒᵖ)

/-! ### The limit in the site -/

attribute [local instance] IsCofiltered.isConnected in
/-- The vertex of `d` is the limit of `F` in the site, as soon as its underlying scheme is the
limit of the underlying schemes: the forgetful functor to schemes reflects connected limits. -/
def isLimitSite
    (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d)) :
    IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).mapCone d) :=
  isLimitOfReflects (BigFppfOver.toScheme B S hS) hd

variable {F d} in
/-- The vertex of `d` is the limit of the system restricted along an initial functor, read as
algebraic spaces. -/
def isLimitRestrictedYoneda [G.Final]
    (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d)) :
    IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda).mapCone
      (d.whisker G.leftOp)) :=
  isLimitOfPreserves yoneda
    ((Functor.Initial.isLimitWhiskerEquiv G.leftOp _).symm (D.isLimitSite F d hd))

/-! ### The situation -/

/-- The test scheme of the system at a stage `a` of `α`. -/
abbrev stage (a : α) : SchemesOver D.Y := F.obj (G.obj a).unop

/-- The morphism of test schemes from a later stage `b ≥ a` to `a`. -/
abbrev stageHom {a b : α} (h : a ≤ b) : stage D F G b ⟶ stage D F G a :=
  F.map (G.map (homOfLE h)).unop

omit [IsCofiltered I] [IsDirected α (· ≤ ·)] in
/-- The morphisms `stageHom` compose: for `a ≤ b ≤ c`, the composite of the morphisms from `c` to
`b` and from `b` to `a` is the morphism from `c` to `a`. -/
theorem stageHom_comp {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    stageHom D F G hbc ≫ stageHom D F G hab = stageHom D F G (hab.trans hbc) := by
  rw [stageHom, stageHom, stageHom, ← F.map_comp, ← unop_comp, ← G.map_comp]
  rfl

/-- The projection from the vertex of `d` to a stage `a`. -/
abbrev stageProj (a : α) : d.pt ⟶ stage D F G a := d.π.app (G.obj a).unop

omit [IsCofiltered I] [IsDirected α (· ≤ ·)] in
/-- The projections are compatible with the transition morphisms: for `a ≤ b`, the projection to
`b` followed by the morphism from `b` to `a` is the projection to `a`. -/
theorem stageProj_comp {a b : α} (h : a ≤ b) :
    stageProj D F d G b ≫ stageHom D F G h = stageProj D F d G a :=
  d.w _

/-- The square of a morphism of test schemes, in the category of presheaves. -/
theorem isPullback_relativeMap_hom {T T' : SchemesOver D.Y} (g : T ⟶ T') :
    IsPullback (D.projection T).hom (D.relativeMap g).hom (yoneda.map g.left)
      (D.projection T').hom :=
  (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)).flip

section Coherence

variable {T₀ T₁ T₂ T₃ : SchemesOver D.Y}

/-- A morphism between the pullbacks to `T₀` of two objects of `T₃`, read through the pullback
to an intermediate `T₂`, is conjugated by the comparisons of a composite `T₀ ⟶ T₁ ⟶ T₂ ⟶ T₃`
in either grouping. -/
theorem conj_tri_eq {f : T₀ ⟶ T₁} {g : T₁ ⟶ T₂} {p : T₂ ⟶ T₃} {k : T₀ ⟶ T₂} {q : T₁ ⟶ T₃}
    {r : T₀ ⟶ T₃} (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r)
    {M N : derivedModules B S hS (D.space T₃)}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p)).obj M) ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap g)).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap p)).obj N)) :
    (D.tri hkr).hom.app M ≫ Functor.conjHom (D.tri hk) ψ ≫ (D.tri hkr).inv.app N =
      Functor.conjHom (D.tri hr) ((D.tri hq).hom.app M ≫ ψ ≫ (D.tri hq).inv.app N) :=
  Functor.conj_conjHom_eq _ _ _ _ (D.tri_assoc_iso hk hq hr hkr) ψ

end Coherence

variable [G.Final]

/-- **The Situation 0DKU of a cofiltered system of affine test schemes.**  The stages are the
test schemes `F (G a)`, read as algebraic spaces, the limit is the vertex of `d`, and the flat
finitely presented space over the stage `a₀` is the base change `X_{F (G a₀)}`, with its base
changes `X_{F (G a)}` and `X_{d.pt}`. -/
def descentSituation
    (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d))
    (hF : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj i).left)) (a₀ : α) :
    RelativeDescentSituation B S hS B.contains_terminal α where
  Y := G.leftOp ⋙ F ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda
  limitCone := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda).mapCone
    (d.whisker G.leftOp)
  isLimit := D.isLimitRestrictedYoneda G hd
  stage_isAlgebraicSpace a := ((schemeSpaceFunctor B S hS).obj (stage D F G a).left).2
  limit_isAlgebraicSpace := ((schemeSpaceFunctor B S hS).obj d.pt.left).2
  stage_isQuasiCompact a :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hF (G.obj a).unop)
  stage_isQuasiSeparated a :=
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj
          (F.obj (G.leftOp.obj (op a))))) :=
      hF (G.obj a).unop
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal _ inferInstance
  transition_isAffine a b h :=
    haveI := hF (G.obj a).unop
    haveI := hF (G.obj b).unop
    isAffineHom_yoneda_map B S hS (stageHom D F G h).left
  i₀ := a₀
  X₀ := (D.space (stage D F G a₀)).1
  p₀ := (D.projection (stage D F G a₀)).hom
  initial_isAlgebraicSpace := (D.space (stage D F G a₀)).2
  initial_isFlat := D.projection_isFlat _
  initial_isFinitePresentation := D.isFinitePresentation_projection _
  Xᵢ a _ := (D.space (stage D F G a)).1
  stageX_isAlgebraicSpace a _ := (D.space (stage D F G a)).2
  toX₀ a h := (D.relativeMap (stageHom D F G h)).hom
  toYᵢ a _ := (D.projection (stage D F G a)).hom
  stage_isPullback a h := D.isPullback_relativeMap_hom (stageHom D F G h)
  fᵢⱼ a b _ _ h := (D.relativeMap (stageHom D F G h)).hom
  fᵢⱼ_toYᵢ a b _ _ h :=
    congrArg InducedCategory.Hom.hom (baseChangeMap_comp_inclusion D.f (stageHom D F G h))
  fᵢⱼ_toX₀ a b ha hb h := by
    rw [← InducedCategory.comp_hom, ← baseChangeMap_comp, stageHom_comp]
  X := (D.space d.pt).1
  X_isAlgebraicSpace := (D.space d.pt).2
  toInitial := (D.relativeMap (stageProj D F d G a₀)).hom
  toLimit := (D.projection d.pt).hom
  limit_isPullback := D.isPullback_relativeMap_hom (stageProj D F d G a₀)
  fᵢ a _ := (D.relativeMap (stageProj D F d G a)).hom
  fᵢ_toYᵢ a _ :=
    congrArg InducedCategory.Hom.hom (baseChangeMap_comp_inclusion D.f (stageProj D F d G a))
  fᵢ_toX₀ a h := by
    rw [← InducedCategory.comp_hom, ← baseChangeMap_comp, stageProj_comp]

/-! ### The limit of the situation is a limit of schemes -/

attribute [local instance] CategoryTheory.Limits.comp_preservesLimitsOfShape in
/-- The functor to schemes preserves fibre products. -/
local instance preservesPullbacks_bigFppfOverToScheme :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

variable {F d G} in
attribute [local instance] IsCofiltered.isConnected in
/-- **The limit of `descentSituation` is a limit of schemes on affine charts.**  The projection
`T ⟶ T_{a₀}` is a morphism of affine schemes, and a representation of the base changes along an
affine chart `Z ⟶ T_{a₀}` is, on underlying schemes, the base change of the limit cone of the
`T_a`, `a ≥ a₀`, along `Z ⟶ T_{a₀}`, which is a limit cone because a fibre product of limit cones
is a limit cone. -/
theorem isSchemeLimit_descentSituation
    (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d))
    (hF : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj i).left)) (a₀ : α) :
    (D.descentSituation F d G hd hF a₀).IsSchemeLimit := by
  set D' := D.descentSituation F d G hd hF a₀
  let proj := CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y
  let toS := BigFppfOver.toScheme B S hS
  have : ∀ i, IsAffine ((F ⋙ proj ⋙ toS).obj i) := hF
  have hpt : IsAffine (toS.obj (proj.obj d.pt)) :=
    EventualLimit.isAffine_of_isLimit (F ⋙ proj ⋙ toS) _ hd
  refine ⟨?_, fun Z z R => ⟨?_⟩⟩
  · have : IsAffine (toS.obj (proj.obj (F.obj (G.obj a₀).unop))) := hF _
    exact isAffineHom_yoneda_map B S hS (U := proj.obj d.pt)
      (V := proj.obj (F.obj (G.obj a₀).unop)) (proj.map (d.π.app (G.obj a₀).unop))
  let P : ∀ k : D'.LaterIndex, R.W.obj (op k) ⟶ proj.obj (F.obj (G.obj k.1).unop) := fun k =>
    Yoneda.fullyFaithful.preimage (R.p k)
  have hP : ∀ k, yoneda.map (P k) = R.p k := fun k => Yoneda.fullyFaithful.map_preimage _
  let Pc : R.c.pt ⟶ proj.obj d.pt := Yoneda.fullyFaithful.preimage R.pc
  have hPc : yoneda.map Pc = R.pc := Yoneda.fullyFaithful.map_preimage _
  let z₀ : (BigAffineFppf.inclusion B S hS).obj Z ⟶ proj.obj (F.obj (G.obj a₀).unop) :=
    Yoneda.fullyFaithful.preimage z
  have hz₀ : yoneda.map z₀ = z := Yoneda.fullyFaithful.map_preimage _
  have hsq : ∀ k : D'.LaterIndex, IsPullback (P k) (R.q k)
      (proj.map (F.map (G.map (homOfLE (show a₀ ≤ k.1 from k.2))).unop)) z₀ := fun k =>
    .of_yoneda_map (by rw [hP k, hz₀]; exact R.isPullback k)
  have hsqc : IsPullback Pc R.qc (proj.map (d.π.app (G.obj a₀).unop)) z₀ :=
    .of_yoneda_map (by rw [hPc, hz₀]; exact R.isPullback_pt)
  have hp : ∀ (i j : D'.LaterIndex) (h : i ≤ j), R.W.map (homOfLE h).op ≫ P i =
      P j ≫ proj.map (F.map (G.map (homOfLE (show i.1 ≤ j.1 from h))).unop) := fun i j h =>
    yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hP, hP]
      exact R.map_p i j h)
  have hπp : ∀ k : D'.LaterIndex,
      R.c.π.app (op k) ≫ P k = Pc ≫ proj.map (d.π.app (G.obj k.1).unop) := fun k =>
    yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, hP, hPc]
      exact R.π_p k)
  exact AlgebraicGeometry.Space.isLimitOfIsPullbackOfIsLimit
    (Y' := (D'.laterIndexInclusion.op ⋙ G.leftOp) ⋙ F ⋙ proj ⋙ toS) D'.initialLaterIndex
    (fun k => k.2)
    ((Functor.Initial.isLimitWhiskerEquiv (D'.laterIndexInclusion.op ⋙ G.leftOp) _).symm hd)
    (toS.map z₀) (toS.mapCone R.c) (fun k => toS.map (P k)) (fun k => toS.map (R.q k))
    (fun k => (hsq k).map toS)
    (fun i j h => (toS.map_comp _ _).symm.trans
      ((toS.congr_map (hp i j h)).trans (toS.map_comp _ _)))
    (fun i j h => (toS.map_comp _ _).symm.trans (toS.congr_map (R.map_q i j h)))
    (toS.map Pc) (toS.map R.qc) (hsqc.map toS)
    (fun k => (toS.map_comp _ _).symm.trans ((toS.congr_map (hπp k)).trans (toS.map_comp _ _)))
    (fun k => (toS.map_comp _ _).symm.trans (toS.congr_map (R.π_q k)))

/-! ### Reading Stacks 0DKW in the situation -/

section Clauses

variable {F d G}
  (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d))
  (hF : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj i).left)) (a₀ : α)

include hd hF a₀ in
/-- Essential surjectivity in Stacks 0DKW for `descentSituation`, read on the test schemes. -/
theorem descentSituation_essSurj (h : (D.descentSituation F d G hd hF a₀).RelativelyPerfectColimit)
    (E : derivedModules B S hS (D.space d.pt)) (hE : D.IsRelativelyPerfect d.pt E) :
    ∃ (a : α) (Ea : derivedModules B S hS (D.space (F.obj (G.obj a).unop))),
      D.IsRelativelyPerfect (F.obj (G.obj a).unop) Ea ∧
        Nonempty (((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (d.π.app (G.obj a).unop))).obj Ea ≅ E) :=
  let ⟨⟨a, _⟩, Ea, hEa, he⟩ := (h (D.isSchemeLimit_descentSituation hd hF a₀)).2.2.1 E hE
  ⟨a, Ea, hEa, he⟩

include hd hF in
/-- Fullness in Stacks 0DKW for `descentSituation`, at its initial stage, read on the test
schemes. -/
theorem descentSituation_full (h : (D.descentSituation F d G hd hF a₀).RelativelyPerfectColimit)
    (E E' : derivedModules B S hS (D.space (F.obj (G.obj a₀).unop)))
    (hE : D.IsRelativelyPerfect _ E) (hE' : D.IsRelativelyPerfect _ E')
    (φ : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (d.π.app (G.obj a₀).unop))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (d.π.app (G.obj a₀).unop))).obj E') :
    ∃ (b : α) (hab : a₀ ≤ b)
      (ψ : ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (F.map (G.map (homOfLE hab)).unop))).obj E ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (F.map (G.map (homOfLE hab)).unop))).obj E'),
      φ = Functor.conjHom (D.tri (d.w (G.map (homOfLE hab)).unop)) ψ :=
  let ⟨⟨b, _⟩, hab, ψ, hψ⟩ :=
    (h (D.isSchemeLimit_descentSituation hd hF a₀)).2.2.2.1 ⟨a₀, le_refl a₀⟩ E E' hE hE' φ
  ⟨b, hab, ψ, hψ⟩

include hd hF in
/-- Faithfulness in Stacks 0DKW for `descentSituation`, at its initial stage, read on the test
schemes. -/
theorem descentSituation_faithful
    (h : (D.descentSituation F d G hd hF a₀).RelativelyPerfectColimit)
    (E E' : derivedModules B S hS (D.space (F.obj (G.obj a₀).unop)))
    (hE : D.IsRelativelyPerfect _ E) (hE' : D.IsRelativelyPerfect _ E') (ψ ψ' : E ⟶ E')
    (e : ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (d.π.app (G.obj a₀).unop))).map ψ =
      ((smallEtaleDerivedPullbackData B S hS).pull
        (D.relativeMap (d.π.app (G.obj a₀).unop))).map ψ') :
    ∃ (b : α) (hab : a₀ ≤ b),
      ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (F.map (G.map (homOfLE hab)).unop))).map ψ =
        ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (F.map (G.map (homOfLE hab)).unop))).map ψ' :=
  let ⟨⟨b, _⟩, hab, e'⟩ :=
    (h (D.isSchemeLimit_descentSituation hd hF a₀)).2.2.2.2 ⟨a₀, le_refl a₀⟩ E E' hE hE' ψ ψ' e
  ⟨b, hab, e'⟩

end Clauses

section Transfer

variable {F d G}
  (hd : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone d))
  (hF : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj i).left))

/-- The fullness clause at a stage `i` of `F`, from fullness in `descentSituation` over a stage
`F (G a) ⟶ i` of the restricted system. -/
theorem full_of_descentSituation {a : α}
    (h : (D.descentSituation F d G hd hF a).RelativelyPerfectColimit) {i : I}
    (t : (G.obj a).unop ⟶ i) (E E' : derivedModules B S hS (D.space (F.obj i)))
    (hE : D.IsRelativelyPerfect (F.obj i) E) (hE' : D.IsRelativelyPerfect (F.obj i) E')
    (φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).obj E') :
    ∃ (k : I) (s : k ⟶ i)
      (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E ⟶
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).obj E'),
      φ = D.conjAt d s ψ := by
  obtain ⟨b, hab, ψ, hψ⟩ := D.descentSituation_full hd hF a h _ _
    (D.relativelyPerfectBaseChange (F.map t) E hE)
    (D.relativelyPerfectBaseChange (F.map t) E' hE')
    ((D.tri (d.w t)).inv.app E ≫ φ ≫ (D.tri (d.w t)).hom.app E')
  refine ⟨(G.obj b).unop, (G.map (homOfLE hab)).unop ≫ t,
    (D.tri (F.map_comp (G.map (homOfLE hab)).unop t).symm).hom.app E ≫ ψ ≫
      (D.tri (F.map_comp (G.map (homOfLE hab)).unop t).symm).inv.app E', ?_⟩
  refine Iso.eq_of_conj_app_eq (D.tri (d.w t)) (M := E) (N := E') (φ := φ) hψ ?_
  rw [conjAt]
  exact D.conj_tri_eq (M := E) (N := E') (d.w (G.map (homOfLE hab)).unop)
    (F.map_comp (G.map (homOfLE hab)).unop t).symm (d.w ((G.map (homOfLE hab)).unop ≫ t))
    (d.w t) ψ

/-- The faithfulness clause at a stage `i` of `F`, from faithfulness in `descentSituation` over
a stage `F (G a) ⟶ i` of the restricted system. -/
theorem faithful_of_descentSituation {a : α}
    (h : (D.descentSituation F d G hd hF a).RelativelyPerfectColimit) {i : I}
    (t : (G.obj a).unop ⟶ i) (E E' : derivedModules B S hS (D.space (F.obj i)))
    (hE : D.IsRelativelyPerfect (F.obj i) E) (hE' : D.IsRelativelyPerfect (F.obj i) E')
    (ψ ψ' : E ⟶ E')
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ =
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (d.π.app i))).map ψ') :
    ∃ (k : I) (s : k ⟶ i),
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ =
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (F.map s))).map ψ' := by
  obtain ⟨b, hab, e'⟩ := D.descentSituation_faithful hd hF a h _ _
    (D.relativelyPerfectBaseChange (F.map t) E hE)
    (D.relativelyPerfectBaseChange (F.map t) E' hE') _ _ (D.pull_map_eq_of_tri' (d.w t) e)
  exact ⟨(G.obj b).unop, (G.map (homOfLE hab)).unop ≫ t,
    D.pull_map_eq_of_tri'' (F.map_comp (G.map (homOfLE hab)).unop t).symm e'⟩

end Transfer

/-- **Stacks 0DKW for the base changes of Situation 0DLE**, from Stacks 0DKW in Situation 0DKU.
If the category of `Y`-perfect objects is the colimit of the categories of `Yᵢ`-perfect objects
in every Situation 0DKU indexed by a directed preorder (`h0DKW`), then the same holds for the
base changes `X_{F i}` and `X_T` along every cofiltered system `F` of affine test schemes with
limit `T`, in the shape `AlgebraicGeometry.Space.ComplexesSituation.RelativelyPerfectColimit`.

The system is restricted along a final functor from a directed partial order (Stacks 0032).  An
object of a stage `i` of `F` is first pulled back to a stage `F (G a) ⟶ i` of the restricted
system, which keeps it relatively perfect
(`AlgebraicGeometry.Space.ComplexesSituation.relativelyPerfectBaseChange`), and the situation
`AlgebraicGeometry.Space.ComplexesSituation.descentSituation` is formed over that stage.  Its limit
is a limit of schemes
(`AlgebraicGeometry.Space.ComplexesSituation.isSchemeLimit_descentSituation`), which is the
setting in which Stacks 0DKW is stated. -/
theorem relativelyPerfectColimit_of_relativeDescentSituation
    (h0DKW : ∀ (α : Type u) [Preorder α] [IsDirected α (· ≤ ·)]
      (D' : RelativeDescentSituation B S hS B.contains_terminal α), D'.RelativelyPerfectColimit) :
    D.RelativelyPerfectColimit := by
  intro I _ _ F d hd hF _
  obtain ⟨α, _, _, ⟨a₀⟩, G, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  have hfin : ∀ i : I, ∃ a : α, Nonempty ((G.obj a).unop ⟶ i) := fun i => by
    have : IsConnected (StructuredArrow (op i) G) := Functor.Final.out _
    obtain ⟨s⟩ : Nonempty (StructuredArrow (op i) G) := inferInstance
    exact ⟨s.right, ⟨s.hom.unop⟩⟩
  refine ⟨fun E hE => ?_, fun i E E' hE hE' φ => ?_, fun i E E' hE hE' ψ ψ' e => ?_⟩
  · obtain ⟨a, Ea, hEa, he⟩ :=
      D.descentSituation_essSurj hd hF a₀ (h0DKW α (D.descentSituation F d G hd hF a₀)) E hE
    exact ⟨(G.obj a).unop, Ea, hEa, he⟩
  · obtain ⟨a, ⟨t⟩⟩ := hfin i
    exact D.full_of_descentSituation hd hF (h0DKW α (D.descentSituation F d G hd hF a)) t
      E E' hE hE' φ
  · obtain ⟨a, ⟨t⟩⟩ := hfin i
    exact D.faithful_of_descentSituation hd hF (h0DKW α (D.descentSituation F d G hd hF a)) t
      E E' hE hE' ψ ψ' e

end AlgebraicGeometry.Space.ComplexesSituation

end
