module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.AffineTransition
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Descending a finite morphism along a directed limit of algebraic spaces

In the standing situation of Stacks 084W — a directed inverse system `(B_i)` of algebraic
spaces over `S` with affine transition morphisms and algebraic limit `B = lim_i B_i`, a
distinguished stage `0` and a morphism `f₀ : X₀ ⟶ Y₀` of quasi-compact quasi-separated
algebraic spaces over `B₀` — write `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` for the base changes of
`f₀` to a stage `B_i` and to the limit `B`.

This file runs the source's own route for the case where `f₀` is itself affine: if `f` is
finite, `f₀` is locally of finite type and `f₀` is affine, then `f_i` is finite for some
`i ≥ 0`. The affineness of `f₀` is what makes `V_i ×_{Y_i} X_i` a scheme at every stage, which
is how the argument gets to the scheme-level Stacks 01ZO.

Stacks 084Z itself — the same conclusion with no affineness hypothesis, under the chapter's
convention of Section 70.2 (tag 07SD) — is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/FiniteMorphismDescent.lean`, which
first makes some `f_i` affine by Stacks 084Y and then runs the same scheme-level argument.

## Main results

* `AlgebraicGeometry.Space.exists_isFinite_mapAt_of_isAffineHom_map₀`: in the situation of
  Stacks 084W with `f₀` affine and locally of finite type, finiteness of `f` descends to a
  stage.

## Implementation notes

The argument is run over an affine étale chart `V₀ ⟶ Y₀` of the target, as in the source:
finiteness is étale-local on the target (Stacks 03ZQ, conditions (2) and (3)), so it suffices
to make `V_i ×_{Y_i} X_i ⟶ V_i` finite, and that is a morphism of *schemes* over the cofiltered
system `(V_i)`, to which Stacks 01ZO applies. The chart system `(V_i)` is indexed by
`Over (op 0)`, whose cardinality is bounded by the index-size field of Stacks 084W so that its
limit stays inside the site.

Stacks 084W, and therefore every statement below, carries an index-size hypothesis
`Cardinal.mk I < B.cutoff.ord.cof` that the source's Situation 70.6.1 does not state: it is
the explicit form of the all-rings-in-the-site convention under which Stacks 07SF holds, and
the descent statements genuinely need it, here to keep the limit of the affine chart system
`(V_i)` inside the site.

## References

* [Stacks Project, Tag 084Z](https://stacks.math.columbia.edu/tag/084Z)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 084Y](https://stacks.math.columbia.edu/tag/084Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.relative_isStableUnderBaseChange

private local instance schemeCutoffIsClosedUnderIsomorphisms (B : BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => X.size < B.cutoff) where
  of_iso {X Y} e h := by
    change X.size < B.cutoff at h
    rwa [← Scheme.size_congr e]

private local instance schemeCutoffIsClosedUnderPullbacks (B : BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} => X.size < B.cutoff) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

private local instance schemeCategoryHasPullbacks (B : BigFppfSite.{u}) :
    HasPullbacks B.Schemes := inferInstance

section

universe v
variable {A : Type u} [Category.{v} A] [HasPullbacks A]

/-- The base change of a morphism `m : X ⟶ Y` of objects over `B₀` along `g : Bs ⟶ B₀`.

This is the shape of every morphism produced by Stacks 084W: `mapAt` and `mapLimit` are this
construction for the transition morphism and for the projection from the limit. -/
private noncomputable def descentBaseChange
    {B₀ Bs X Y : A} (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} (m : X ⟶ Y)
    (hm : m ≫ sy = sx) : pullback g sx ⟶ pullback g sy :=
  pullback.lift (pullback.fst g sx) (pullback.snd g sx ≫ m)
    (by rw [Category.assoc, hm, pullback.condition])

@[simp]
private theorem descentBaseChange_fst
    {B₀ Bs X Y : A} (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} (m : X ⟶ Y)
    (hm : m ≫ sy = sx) :
    descentBaseChange g m hm ≫ pullback.fst g sy = pullback.fst g sx :=
  pullback.lift_fst _ _ _

@[simp]
private theorem descentBaseChange_snd
    {B₀ Bs X Y : A} (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} (m : X ⟶ Y)
    (hm : m ≫ sy = sx) :
    descentBaseChange g m hm ≫ pullback.snd g sy = pullback.snd g sx ≫ m :=
  pullback.lift_snd _ _ _

end

private theorem overPullback_comp_iff
    {A : Type*} [Category A] [HasPullbacks A]
    (P : MorphismProperty A) [P.IsStableUnderBaseChange]
    {B₀ B₁ B₂ : A} (first : B₁ ⟶ B₀) (second : B₂ ⟶ B₁)
    {X Y : Over B₀} (morphism : X ⟶ Y) :
    P ((Over.pullback (second ≫ first)).map morphism).left ↔
      P ((Over.pullback second).map ((Over.pullback first).map morphism)).left := by
  let comparison := Over.pullbackComp second first
  let sourceIso := (Over.forget B₂).mapIso (comparison.app X)
  let targetIso := (Over.forget B₂).mapIso (comparison.app Y)
  exact P.arrow_mk_iso_iff (Arrow.isoMk sourceIso targetIso
    (congrArg Over.Hom.left (comparison.hom.naturality morphism)).symm)

private theorem overPullback_toId_iff
    {A : Type*} [Category A] [HasPullbacks A]
    (P : MorphismProperty A) [P.RespectsIso]
    {X Y Z : A} (morphism : X ⟶ Y) (baseMap : Z ⟶ Y) :
    P ((Over.pullback baseMap).map
        (Over.homMk morphism (by simp) : Over.mk morphism ⟶ Over.mk (𝟙 Y))).left ↔
      P (pullback.snd morphism baseMap) := by
  have hcomp : ((Over.pullback baseMap).map
        (Over.homMk morphism (by simp) : Over.mk morphism ⟶ Over.mk (𝟙 Y))).left ≫
        pullback.snd (𝟙 Y) baseMap = pullback.snd morphism baseMap := by
    show pullback.lift _ _ _ ≫ pullback.snd (𝟙 Y) baseMap = _
    exact pullback.lift_snd _ _ _
  rw [← hcomp, P.cancel_right_of_respectsIso]

/-- **Stacks 01ZO over an affine cofiltered system.** For a cofiltered system of affine
schemes with affine transition morphisms and a finite-type morphism `source ⟶ target` of
affine schemes, finiteness of the base change of `source ⟶ target` to the limit of the
system descends to a stage. -/
private theorem exists_finite_pullback
    {J : Type u} [Category.{u} J] [IsCofiltered J] [EssentiallySmall.{u} J]
    (diagram : J ⥤ Scheme.{u}) (cone : Cone diagram) (hc : IsLimit cone)
    [∀ {first second : J} (arrow : first ⟶ second), IsAffineHom (diagram.map arrow)]
    [∀ stage, IsAffine (diagram.obj stage)]
    (initial : J) {source target : Scheme.{u}} [IsAffine source] [IsAffine target]
    (morphism : source ⟶ target) [LocallyOfFiniteType morphism]
    (structureMap : diagram ⟶ (Functor.const J).obj target)
    (limitMap : cone.pt ⟶ target)
    (hlimit : ∀ stage, cone.π.app stage ≫ structureMap.app stage = limitMap)
    (hfinite : IsFinite (pullback.snd morphism limitMap)) :
    ∃ stage, IsFinite (pullback.snd morphism (structureMap.app stage)) := by
  let original : Over.mk morphism ⟶ Over.mk (𝟙 target) := Over.homMk morphism (by simp)
  let firstMap := structureMap.app initial
  let model := (Over.pullback firstMap).map original
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) firstMap :=
    ⟨fun sq hf => MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hf⟩
  let : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsAffine (diagram.obj initial) := inferInstance
  have : IsAffineHom morphism := isAffineHom_of_isAffine _
  have : IsAffineHom (pullback.snd morphism firstMap) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) morphism firstMap ‹IsAffineHom morphism›
  have : LocallyOfFiniteType model.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) firstMap original
      (show LocallyOfFiniteType original.left from ‹LocallyOfFiniteType morphism›)
  have : IsAffine ((Over.pullback firstMap).obj (Over.mk morphism)).left :=
    isAffine_of_isAffineHom (pullback.snd morphism firstMap)
  have : IsAffine ((Over.pullback firstMap).obj (Over.mk (𝟙 target))).left :=
    isAffine_of_isAffineHom (pullback.snd (𝟙 target) firstMap)
  have : IsFinite ((Over.pullback (cone.π.app initial)).map model).left := by
    apply (overPullback_comp_iff (@IsFinite) firstMap (cone.π.app initial) original).mp
    apply (overPullback_toId_iff (@IsFinite) morphism _).mpr
    show IsFinite (pullback.snd morphism (cone.π.app initial ≫ structureMap.app initial))
    rwa [hlimit]
  obtain ⟨stage, arrow, hstage⟩ :=
    exists_isFinite_baseChange_of_isLimit diagram cone hc initial _ _ model
  refine ⟨stage, ?_⟩
  have hnat : diagram.map arrow ≫ firstMap = structureMap.app stage :=
    (structureMap.naturality arrow).trans (Category.comp_id _)
  exact hnat ▸ (overPullback_toId_iff (@IsFinite) morphism _).mp
    ((overPullback_comp_iff (@IsFinite) firstMap (diagram.map arrow) original).mpr hstage)

/-- The comma category over an object of a category with few objects and thin hom-sets is
itself small. -/
private theorem mk_over_lt_cof
    {K : Type u} [Category.{u} K] (i : K) (κ : Cardinal.{u})
    (hκ : ℵ₀ < κ.ord.cof) (hObj : Cardinal.mk K < κ.ord.cof)
    (hHom : ∀ j : K, Cardinal.mk (j ⟶ i) < κ.ord.cof) :
    Cardinal.mk (Over i) < κ.ord.cof := by
  classical
  have hObj' : Cardinal.mk K < (κ.ord.cof).ord.cof := by simpa [Ordinal.cof_ord_cof] using hObj
  have hSup : (⨆ j : K, Cardinal.mk (j ⟶ i)) < κ.ord.cof :=
    Cardinal.iSup_lt_of_lt_cof_ord hObj' hHom
  let μ := max ℵ₀ (max (Cardinal.mk K) (⨆ j : K, Cardinal.mk (j ⟶ i)))
  let e : Over i ↪ Σ j : K, (j ⟶ i) :=
    ⟨fun j => ⟨j.left, j.hom⟩, by
      intro j k h
      cases j with
      | mk jl jr jh =>
        cases k with
        | mk kl kr kh =>
          have hh : jl = kl ∧ HEq jh kh := by simpa [Over] using h
          rcases hh with ⟨rfl, hh⟩
          cases hh
          have hr : jr = kr := Subsingleton.elim _ _
          subst kr
          rfl⟩
  calc
    Cardinal.mk (Over i) ≤ Cardinal.mk (Σ j : K, (j ⟶ i)) :=
      Cardinal.mk_le_of_injective e.injective
    _ = Cardinal.sum (fun j : K => Cardinal.mk (j ⟶ i)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.mk K * (⨆ j : K, Cardinal.mk (j ⟶ i)) := Cardinal.sum_le_mk_mul_iSup _
    _ ≤ μ := by
      dsimp [μ]
      simpa [max_assoc, max_left_comm, max_comm] using
        (Cardinal.mul_le_max (Cardinal.mk K) (⨆ j : K, Cardinal.mk (j ⟶ i)))
    _ < κ.ord.cof := max_lt hκ (max_lt hObj hSup)

private theorem size_limit_le_of_affine
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    {K : Type u} [Category.{u} K] [IsCofiltered K]
    (E : K ⥤ Scheme.{u}) [HasLimit E]
    (hAffine : ∀ j, IsAffine (E.obj j))
    (hSize : ∀ j, (E.obj j).size ≤ μ)
    (hIndex : Cardinal.mk K ≤ μ) :
    (limit E).size ≤ μ := by
  classical
  let (j : K) : IsAffine (E.obj j) := hAffine j
  have : IsAffine (limit E) := Scheme.isAffine_of_isLimit _ (limit.isLimit E)
  let R : Kᵒᵖ ⥤ CommRingCat.{u} := E.op ⋙ Scheme.Γ
  let (j : Kᵒᵖ) : IsAffine ((E.op).obj j).unop := hAffine j.unop
  let : PreservesColimit E.op Scheme.Γ := preservesColimit_Γ E.op
  have hR : IsColimit (Scheme.Γ.mapCocone (limit.cone E).op) :=
    isColimitOfPreserves Scheme.Γ (limit.isLimit E).op
  let eR : Scheme.Γ.obj (op (limit E)) ≅ colimit R :=
    hR.coconePointUniqueUpToIso (colimit.isColimit R)
  have hRsize : Cardinal.mk (↑(colimit R)) ≤ μ := by
    let G : Kᵒᵖ ⥤ Type u := R ⋙ forget CommRingCat
    let e : (↑(colimit R) : Type u) ≅ colimit G :=
      (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit R)).coconePointUniqueUpToIso
        (colimit.isColimit G)
    calc
      Cardinal.mk (↑(colimit R)) = Cardinal.mk (colimit G) := Cardinal.mk_congr e.toEquiv
      _ = Cardinal.mk G.ColimitType := Cardinal.mk_congr (Types.colimitEquivColimitType G)
      _ ≤ Cardinal.mk (Σ j, G.obj j) := by
        show Cardinal.mk (Quot G.ColimitTypeRel) ≤ _
        exact Cardinal.mk_quot_le
      _ = Cardinal.sum (fun j => Cardinal.mk (G.obj j)) := Cardinal.mk_sigma _
      _ ≤ Cardinal.mk Kᵒᵖ * (⨆ j, Cardinal.mk (G.obj j)) := Cardinal.sum_le_mk_mul_iSup _
      _ ≤ μ := by
        have hKmu : Cardinal.mk Kᵒᵖ ≤ μ := by
          rw [Cardinal.mk_congr (show Kᵒᵖ ≃ K from
            ⟨unop, op, fun _ => rfl, fun _ => rfl⟩)]
          exact hIndex
        apply Cardinal.mul_le_of_le hμ hKmu
        calc
          (⨆ j : Kᵒᵖ, Cardinal.mk (G.obj j)) ≤
              ⨆ j : Kᵒᵖ, (E.obj j.unop).size := by
            have hLift := Cardinal.lift_iSup_le_lift_iSup'
              (f := fun j : Kᵒᵖ => Cardinal.mk (G.obj j))
              (f' := fun j : Kᵒᵖ => (E.obj j.unop).size)
              Cardinal.bddAbove_of_small Cardinal.bddAbove_of_small
              (fun j => j) (fun j => by
                rw [Cardinal.lift_id, Cardinal.lift_id]
                show Cardinal.mk (Scheme.Γ.obj (op (E.obj j.unop))) ≤ _
                rw [Scheme.size_of_isAffine (E.obj j.unop)]
                exact le_max_right _ _)
            simpa only [Cardinal.lift_id] using hLift
          _ ≤ μ := ciSup_le' fun j => hSize j.unop
  rw [Scheme.size_of_isAffine (limit E)]
  exact max_le hμ ((Cardinal.mk_congr eR.commRingCatIsoToRingEquiv.toEquiv).trans_le hRsize)

private theorem size_limit_lt_of_affine
    (B : BigFppfSite.{u})
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (diagram : J ⥤ Scheme.{u}) [HasLimit diagram]
    (hAffine : ∀ stage, IsAffine (diagram.obj stage))
    (hSize : ∀ stage, (diagram.obj stage).size < B.cutoff)
    (hIndex : Cardinal.mk J < B.cutoff.ord.cof) : (limit diagram).size < B.cutoff := by
  have hSup : (⨆ stage, (diagram.obj stage).size) < B.cutoff :=
    Cardinal.iSup_lt_of_lt_cof_ord hIndex hSize
  let bound := max ℵ₀ (max (Cardinal.mk J) (⨆ stage, (diagram.obj stage).size))
  have hbound : bound < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt (hIndex.trans_le (Ordinal.cof_ord_le _)) hSup)
  exact (size_limit_le_of_affine (le_max_left _ _) diagram hAffine
    (fun stage => (le_ciSup Cardinal.bddAbove_of_small stage).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
    ((le_max_left _ _).trans (le_max_right _ _))).trans_lt hbound

private theorem finite_of_square
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (morphism : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : Space.IsFinite B S hS morphism)
    {source target : BigFppfOver B S hS}
    (represented : source ⟶ target) (sourceMap : yoneda.obj source ⟶ X)
    (targetMap : yoneda.obj target ⟶ Y)
    (hsquare : IsPullback sourceMap (yoneda.map represented) morphism targetMap) :
    IsFinite ((BigFppfOver.toScheme B S hS).map represented) :=
  ((Space.isFinite_iff_representable B S hS morphism hX hY).mp hf).2.property
    targetMap sourceMap represented hsquare

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance hasPullbacks_presheaf_descendingFiniteMorphism {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_descendingFiniteMorphism
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section ChartSquares

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Bs B₀ X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V W : BigFppfOver B S hS}

/-- A chart `U ⟶ Y` of the target, read in the base `B₀` through `sy`, is computed by the chart
`V ⟶ X` of the source along any square exhibiting `V` as the base change of `U` under
`m : X ⟶ Y`. -/
private theorem chart_base_comm {sx : X ⟶ B₀} {sy : Y ⟶ B₀} {m : X ⟶ Y}
    (hm : m ≫ sy = sx) {chart : yoneda.obj U ⟶ Y} {sourceChart : yoneda.obj V ⟶ X}
    {represented : V ⟶ U}
    (hrep : IsPullback sourceChart (yoneda.map represented) m chart) :
    yoneda.map represented ≫ chart ≫ sy = sourceChart ≫ sx := by
  rw [← Category.assoc, ← hrep.w, Category.assoc, hm]

/-- The chart of the base-changed target: a square exhibiting `W` over `Bs` as the base change
of the chart `U ⟶ Y` gives a morphism `W ⟶ Bs ×_{B₀} Y`. -/
private noncomputable def chartTarget (g : Bs ⟶ B₀) (sy : Y ⟶ B₀)
    (chart : yoneda.obj U ⟶ Y) (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    yoneda.obj W ⟶ pullback g sy :=
  pullback.lift pW (yoneda.map qW ≫ chart) (by rw [hsq.w, Category.assoc])

@[simp]
private theorem chartTarget_fst (g : Bs ⟶ B₀) (sy : Y ⟶ B₀) (chart : yoneda.obj U ⟶ Y)
    (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    chartTarget g sy chart pW qW hsq ≫ pullback.fst g sy = pW :=
  pullback.lift_fst _ _ _

@[simp]
private theorem chartTarget_snd (g : Bs ⟶ B₀) (sy : Y ⟶ B₀) (chart : yoneda.obj U ⟶ Y)
    (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    chartTarget g sy chart pW qW hsq ≫ pullback.snd g sy = yoneda.map qW ≫ chart :=
  pullback.lift_snd _ _ _

/-- The chart of the base-changed target is itself a base change of the chart. -/
private theorem isPullback_chartTarget (g : Bs ⟶ B₀) (sy : Y ⟶ B₀)
    (chart : yoneda.obj U ⟶ Y) (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    IsPullback (yoneda.map qW) (chartTarget g sy chart pW qW hsq) chart
      (pullback.snd g sy) := by
  refine IsPullback.of_bot ?_ (chartTarget_snd g sy chart pW qW hsq).symm
    (IsPullback.of_hasPullback g sy).flip
  rw [chartTarget_fst]
  exact hsq.flip

/-- The chart of the base-changed source, over the chart `V ×_U W` of `V`. -/
private noncomputable def chartSource (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} {m : X ⟶ Y}
    (hm : m ≫ sy = sx) (chart : yoneda.obj U ⟶ Y) (sourceChart : yoneda.obj V ⟶ X)
    (represented : V ⟶ U)
    (hrep : IsPullback sourceChart (yoneda.map represented) m chart)
    (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    yoneda.obj (pullback represented qW) ⟶ pullback g sx :=
  pullback.lift (yoneda.map (pullback.snd represented qW) ≫ pW)
    (yoneda.map (pullback.fst represented qW) ≫ sourceChart)
    (calc (yoneda.map (pullback.snd represented qW) ≫ pW) ≫ g
        = yoneda.map (pullback.snd represented qW) ≫ pW ≫ g := Category.assoc _ _ _
      _ = yoneda.map (pullback.snd represented qW) ≫ yoneda.map qW ≫ chart ≫ sy := by
          rw [hsq.w]
      _ = (yoneda.map (pullback.snd represented qW) ≫ yoneda.map qW) ≫ chart ≫ sy :=
          (Category.assoc _ _ _).symm
      _ = yoneda.map (pullback.fst represented qW ≫ represented) ≫ chart ≫ sy := by
          rw [← yoneda.map_comp, pullback.condition]
      _ = yoneda.map (pullback.fst represented qW) ≫ yoneda.map represented ≫ chart ≫ sy := by
          rw [yoneda.map_comp, Category.assoc]
      _ = yoneda.map (pullback.fst represented qW) ≫ sourceChart ≫ sx := by
          rw [chart_base_comm hm hrep]
      _ = (yoneda.map (pullback.fst represented qW) ≫ sourceChart) ≫ sx :=
          (Category.assoc _ _ _).symm)

/-- The chart of the base-changed source is a base change of the chart of the source. -/
private theorem isPullback_chartSource (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} {m : X ⟶ Y}
    (hm : m ≫ sy = sx) (chart : yoneda.obj U ⟶ Y) (sourceChart : yoneda.obj V ⟶ X)
    (represented : V ⟶ U)
    (hrep : IsPullback sourceChart (yoneda.map represented) m chart)
    (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    IsPullback (yoneda.map (pullback.fst represented qW))
      (chartSource g hm chart sourceChart represented hrep pW qW hsq) sourceChart
      (pullback.snd g sx) := by
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
    (IsPullback.of_hasPullback g sx).flip
  have hfst : chartSource g hm chart sourceChart represented hrep pW qW hsq ≫
      pullback.fst g sx = yoneda.map (pullback.snd represented qW) ≫ pW :=
    pullback.lift_fst _ _ _
  rw [hfst]
  have hOuter := ((IsPullback.of_hasPullback represented qW).map yoneda).paste_vert hsq.flip
  rwa [chart_base_comm hm hrep] at hOuter

/-- Over the two charts, the base change of `m` along `g` is the base change of `m` along the
chart: this is the square that transports finiteness between the algebraic space and the
scheme. -/
private theorem isPullback_chartFinite (g : Bs ⟶ B₀) {sx : X ⟶ B₀} {sy : Y ⟶ B₀} {m : X ⟶ Y}
    (hm : m ≫ sy = sx) (chart : yoneda.obj U ⟶ Y) (sourceChart : yoneda.obj V ⟶ X)
    (represented : V ⟶ U)
    (hrep : IsPullback sourceChart (yoneda.map represented) m chart)
    (pW : yoneda.obj W ⟶ Bs) (qW : W ⟶ U)
    (hsq : IsPullback pW (yoneda.map qW) g (chart ≫ sy)) :
    IsPullback (chartSource g hm chart sourceChart represented hrep pW qW hsq)
      (yoneda.map (pullback.snd represented qW)) (descentBaseChange g m hm)
      (chartTarget g sy chart pW qW hsq) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_chartTarget g sy chart pW qW hsq).flip
  · rw [descentBaseChange_snd, ← yoneda.map_comp, ← pullback.condition, yoneda.map_comp]
    exact (isPullback_chartSource g hm chart sourceChart represented hrep pW qW
      hsq).flip.paste_vert hrep
  · apply pullback.hom_ext
    · have hL : (chartSource g hm chart sourceChart represented hrep pW qW hsq ≫
          descentBaseChange g m hm) ≫ pullback.fst g sy =
          yoneda.map (pullback.snd represented qW) ≫ pW := by
        rw [Category.assoc, descentBaseChange_fst]
        exact pullback.lift_fst _ _ _
      have hR : (yoneda.map (pullback.snd represented qW) ≫
          chartTarget g sy chart pW qW hsq) ≫ pullback.fst g sy =
          yoneda.map (pullback.snd represented qW) ≫ pW := by
        rw [Category.assoc, chartTarget_fst]
      rw [hL, hR]
    · have hL : (chartSource g hm chart sourceChart represented hrep pW qW hsq ≫
          descentBaseChange g m hm) ≫ pullback.snd g sy =
          yoneda.map (pullback.snd represented qW) ≫ yoneda.map qW ≫ chart := by
        rw [Category.assoc, descentBaseChange_snd, ← Category.assoc,
          show chartSource g hm chart sourceChart represented hrep pW qW hsq ≫
              pullback.snd g sx = yoneda.map (pullback.fst represented qW) ≫ sourceChart from
            pullback.lift_snd _ _ _, Category.assoc, hrep.w, ← Category.assoc,
          ← yoneda.map_comp, pullback.condition, yoneda.map_comp, Category.assoc]
      have hR : (yoneda.map (pullback.snd represented qW) ≫
          chartTarget g sy chart pW qW hsq) ≫ pullback.snd g sy =
          yoneda.map (pullback.snd represented qW) ≫ yoneda.map qW ≫ chart := by
        rw [Category.assoc, chartTarget_snd]
      rw [hL, hR]

end ChartSquares

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

private theorem exists_isFinite_of_isAffineHom_map₀
    (D : Space.MorphismDescentSituation B S hS hZ I)
    (hI : #I < B.cutoff.ord.cof)
    (hAffine : Space.IsAffineHom B S hS D.map₀)
    (hf : Space.IsFinite B S hS D.mapLimit)
    (hlft : Space.IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (stage : I) (hstage : D.initial ≤ stage),
      Space.IsFinite B S hS (D.mapAt stage hstage) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  let : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : (MorphismProperty.inverseImage (@Etale.{u}) T).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  let : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite : MorphismProperty Scheme.{u}) T) :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _
  obtain ⟨U, chart, hU, hsurj, hetale⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS D.target₀ D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  let Uaff : BigAffineFppf B S hS := ⟨U, hU⟩
  obtain ⟨Vaff, sourceChart, represented, hrepresented⟩ := hAffine Uaff chart
  let V := (BigAffineFppf.inclusion B S hS).obj Vaff
  have hV : IsAffine (T.obj V) := Vaff.property
  have hchartEtale : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf chart := by
    have hid : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
        (𝟙 (yoneda.obj U)) := by
      apply MorphismProperty.relative.of_exists
      intro test arrow
      refine ⟨test, arrow, 𝟙 _, IsPullback.of_id_snd, ?_⟩
      show Etale (T.map (𝟙 test))
      rw [T.map_id]
      infer_instance
    simpa only [Category.id_comp] using hetale U (𝟙 _) hid
  have hsourceEtale : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf sourceChart :=
    MorphismProperty.of_isPullback hrepresented.flip hchartEtale
  have hrepresentedType : LocallyOfFiniteType (T.map represented) :=
    hlft V U sourceChart chart represented hsourceEtale hchartEtale hrepresented.w.symm
  let K := Over (op D.initial)
  let : IsConnected K := IsCofiltered.isConnected K
  let baseChart := chart ≫ D.targetToBase
  let G : K ⥤ Over (yoneda.obj U) := Over.post D.base ⋙ Over.pullback baseChart
  let F := G ⋙ Over.forget (yoneda.obj U)
  let affine (stage : K) := Classical.choose (D.transition_affine stage.hom Uaff baseChart)
  let W (stage : K) := (BigAffineFppf.inclusion B S hS).obj (affine stage)
  let p (stage : K) := Classical.choose (Classical.choose_spec
    (D.transition_affine stage.hom Uaff baseChart))
  let q (stage : K) := Classical.choose (Classical.choose_spec (Classical.choose_spec
    (D.transition_affine stage.hom Uaff baseChart)))
  have hsquare (stage : K) : IsPullback (p stage) (yoneda.map (q stage))
      (D.base.map stage.hom) baseChart :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (D.transition_affine stage.hom Uaff baseChart)))
  let iso (stage : K) : yoneda.obj (W stage) ≅ F.obj stage := (hsquare stage).isoPullback
  let A : K ⥤ BigFppfOver B S hS := {
    obj := W
    map := fun {first second} arrow =>
      yoneda.preimage ((iso first).hom ≫ F.map arrow ≫ (iso second).inv)
    map_id := by
      intro stage
      apply yoneda.map_injective
      simp
    map_comp := by
      intro first second third arrow next
      apply yoneda.map_injective
      simp [Category.assoc] }
  let diagramIso : A ⋙ yoneda ≅ F := NatIso.ofComponents iso (by
    intro first second arrow
    dsimp [A]
    simp [Category.assoc])
  have hiso (stage : K) : (iso stage).hom ≫ (G.obj stage).hom = yoneda.map (q stage) :=
    (hsquare stage).isoPullback_hom_snd
  let E := A ⋙ T
  have hW (stage : K) : IsAffine (E.obj stage) := (affine stage).property
  let (stage : K) : IsAffine (E.obj stage) := hW stage
  have {first second : K} (arrow : first ⟶ second) : IsAffineHom (E.map arrow) :=
    isAffineHom_of_isAffine _
  let : HasLimit E := Scheme.hasLimit_of_isAffine E
  have hIndex : Cardinal.mk K < B.cutoff.ord.cof := mk_over_lt_cof (op D.initial)
    B.cutoff B.aleph0_lt_cutoff_cof
    (by rw [Cardinal.mk_congr (show Iᵒᵖ ≃ I from ⟨unop, op, fun _ => rfl, fun _ => rfl⟩)]
        exact hI)
    (fun stage => (Cardinal.mk_le_of_injective
      (f := fun (_ : stage ⟶ op D.initial) => PUnit.unit)
      (fun _ _ _ => Subsingleton.elim _ _)).trans_lt
        (by simpa only [Cardinal.mk_punit] using
          Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof))
  have hLimitSize : (limit E).size < B.cutoff := size_limit_lt_of_affine B E hW
    (fun stage => (W stage).left.property) hIndex
  let underlying := A ⋙ Over.forget (B.obj hS)
  let limitObject : B.Schemes := ⟨limit E, hLimitSize⟩
  let underlyingCone : Cone underlying := {
    pt := limitObject
    π := {
      app := fun stage => ObjectProperty.homMk (limit.π E stage)
      naturality := by
        intro first second arrow
        apply ObjectProperty.hom_ext
        exact (limit.w E arrow).symm } }
  have hUnderlying : IsLimit underlyingCone := by
    apply isLimitOfReflects B.inclusion
    exact limit.isLimit E
  let siteCone := CostructuredArrow.CreatesConnected.raiseCone underlyingCone
  have hSite : IsLimit siteCone := CostructuredArrow.CreatesConnected.isLimitRaiseCone hUnderlying
  have hScheme : IsLimit (T.mapCone siteCone) := limit.isLimit E
  let canonicalCone := (Over.forget (yoneda.obj U)).mapCone
    ((Over.pullback baseChart).mapCone ((limit.cone D.base).overPost (op D.initial)))
  change Cone F at canonicalCone
  have hCanonical : IsLimit canonicalCone :=
    isLimitOfPreserves (Over.forget (yoneda.obj U))
      (isLimitOfPreserves (Over.pullback baseChart) ((limit.isLimit D.base).overPost _))
  let presheafCone := (Cone.postcompose diagramIso.hom).obj (yoneda.mapCone siteCone)
  have hPresheaf : IsLimit presheafCone :=
    (IsLimit.postcomposeHomEquiv diagramIso _).symm (isLimitOfPreserves yoneda hSite)
  let limitIso := hPresheaf.conePointUniqueUpToIso hCanonical
  let initial : K := Over.mk (𝟙 (op D.initial))
  let qLimit := siteCone.π.app initial ≫ q initial
  let pLimit := limitIso.hom ≫ pullback.fst (limit.π D.base (op D.initial)) baseChart
  have hcone (stage : K) :
      limitIso.hom ≫ pullback.snd (limit.π D.base (op D.initial)) baseChart =
        yoneda.map (siteCone.π.app stage ≫ q stage) := by
    have hfac := hPresheaf.conePointUniqueUpToIso_hom_comp hCanonical stage
    have hproj := Over.w (((Over.pullback baseChart).mapCone
      ((limit.cone D.base).overPost (op D.initial))).π.app stage)
    change canonicalCone.π.app stage ≫ (G.obj stage).hom =
      pullback.snd (limit.π D.base (op D.initial)) baseChart at hproj
    rw [← hproj, ← Category.assoc, hfac]
    change (yoneda.map (siteCone.π.app stage) ≫ (iso stage).hom) ≫ (G.obj stage).hom = _
    exact ((Category.assoc _ _ _).trans
      (congrArg (yoneda.map (siteCone.π.app stage) ≫ ·) (hiso stage))).trans
      (yoneda.map_comp _ _).symm
  have hqLimit := hcone initial
  have hLimitSquare : IsPullback pLimit (yoneda.map qLimit)
      (limit.π D.base (op D.initial)) baseChart := by
    have h0 : IsPullback pLimit
        (limitIso.hom ≫ pullback.snd (limit.π D.base (op D.initial)) baseChart)
        (limit.π D.base (op D.initial)) baseChart :=
      (IsPullback.of_hasPullback _ _).of_iso'
        limitIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rfl)
        (by rfl) (by rfl) (by simp)
    rwa [hqLimit] at h0
  let targetLimitChart := chartTarget (limit.π D.base (op D.initial)) D.targetToBase chart
    pLimit qLimit hLimitSquare
  have hFiniteSquare : IsPullback
      (chartSource (limit.π D.base (op D.initial)) D.map₀_over chart sourceChart represented
        hrepresented pLimit qLimit hLimitSquare)
      (yoneda.map (pullback.snd represented qLimit)) D.mapLimit targetLimitChart :=
    isPullback_chartFinite (limit.π D.base (op D.initial)) D.map₀_over chart sourceChart
      represented hrepresented pLimit qLimit hLimitSquare
  have hcmp {Z : BigFppfOver B S hS} (r : Z ⟶ U) :
      IsFinite (T.map (pullback.snd represented r)) ↔
        IsFinite (pullback.snd (T.map represented) (T.map r)) := by
    let comparison := ((IsPullback.of_hasPullback represented r).map T).isoPullback
    rw [← IsPullback.isoPullback_hom_snd ((IsPullback.of_hasPullback represented r).map T)]
    exact MorphismProperty.cancel_left_of_respectsIso
      (@_root_.AlgebraicGeometry.IsFinite) comparison.hom _
  have hfiniteLimit : IsFinite (T.map (pullback.snd represented qLimit)) :=
    finite_of_square D.mapLimit D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace hf _ _ _ hFiniteSquare
  have hfiniteScheme : IsFinite (pullback.snd (T.map represented) (T.map qLimit)) :=
    (hcmp qLimit).mp hfiniteLimit
  let structureMap : E ⟶ (Functor.const K).obj (T.obj U) := {
    app := fun stage => T.map (q stage)
    naturality := by
      intro first second arrow
      show T.map (A.map arrow) ≫ T.map (q second) = T.map (q first) ≫ 𝟙 _
      rw [Category.comp_id, ← T.map_comp]
      congr 1
      apply yoneda.map_injective
      rw [yoneda.map_comp]
      rw [show yoneda.map (A.map arrow) = (iso first).hom ≫ F.map arrow ≫ (iso second).inv
        from yoneda.map_preimage _]
      rw [← hiso]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      show (iso first).hom ≫ (G.map arrow).left ≫ (G.obj second).hom = _
      rw [Over.w, hiso] }
  have hlimit (stage : K) : (T.mapCone siteCone).π.app stage ≫ structureMap.app stage =
      T.map qLimit := by
    show T.map (siteCone.π.app stage) ≫ T.map (q stage) = T.map qLimit
    refine (T.map_comp (siteCone.π.app stage) (q stage)).symm.trans (congrArg T.map ?_)
    exact yoneda.map_injective ((hcone stage).symm.trans hqLimit)
  have : IsAffine (T.obj U) := hU
  have : IsAffine (T.obj V) := hV
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj Uaff)) := hU
  have : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj Vaff)) := hV
  have : LocallyOfFiniteType (T.map represented) := hrepresentedType
  obtain ⟨stage, hfiniteStage⟩ := exists_finite_pullback E (T.mapCone siteCone) hScheme
    initial (T.map represented) structureMap (T.map qLimit) hlimit hfiniteScheme
  let stageIndex := stage.left.unop
  have hstage : D.initial ≤ stageIndex := leOfHom stage.hom.unop
  have hstageMap : D.baseAtToInitial stageIndex hstage = D.base.map stage.hom := by
    congr 1
  have hsquareStage : IsPullback (p stage) (yoneda.map (q stage))
      (D.baseAtToInitial stageIndex hstage) baseChart := by
    rw [hstageMap]
    exact hsquare stage
  let targetStageChart := chartTarget (D.baseAtToInitial stageIndex hstage) D.targetToBase
    chart (p stage) (q stage) hsquareStage
  have hTargetStage : IsPullback (yoneda.map (q stage)) targetStageChart chart
      (pullback.snd (D.baseAtToInitial stageIndex hstage) D.targetToBase) :=
    isPullback_chartTarget (D.baseAtToInitial stageIndex hstage) D.targetToBase chart
      (p stage) (q stage) hsquareStage
  have hFiniteSquareStage : IsPullback
      (chartSource (D.baseAtToInitial stageIndex hstage) D.map₀_over chart sourceChart
        represented hrepresented (p stage) (q stage) hsquareStage)
      (yoneda.map (pullback.snd represented (q stage))) (D.mapAt stageIndex hstage)
      targetStageChart :=
    isPullback_chartFinite (D.baseAtToInitial stageIndex hstage) D.map₀_over chart sourceChart
      represented hrepresented (p stage) (q stage) hsquareStage
  have hfiniteRelative : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u}) T).presheaf
      (yoneda.map (pullback.snd represented (q stage))) :=
    MorphismProperty.relative_map ((hcmp (q stage)).mpr hfiniteStage)
  have hfinitePullback : Space.IsFinite B S hS
      (pullback.snd (D.mapAt stageIndex hstage) targetStageChart) := by
    let comparison := hFiniteSquareStage.isoPullback
    apply (Space.isFinite_iff_representable B S hS _
      (isAlgebraicSpace_pullback B S hS _ _
        (D.sourceAt_isAlgebraicSpace stageIndex hstage)
        (isAlgebraicSpace_yoneda B S hS (W stage))
        (D.targetAt_isAlgebraicSpace stageIndex hstage))
      (isAlgebraicSpace_yoneda B S hS (W stage))).mpr
    have he : comparison.hom ≫ pullback.snd (D.mapAt stageIndex hstage) targetStageChart =
        yoneda.map (pullback.snd represented (q stage)) :=
      hFiniteSquareStage.isoPullback_hom_snd
    have hcomp : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u}) T).presheaf
        (comparison.hom ≫ pullback.snd (D.mapAt stageIndex hstage) targetStageChart) := by
      rw [he]
      exact hfiniteRelative
    have hrel := (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u}) T).presheaf) comparison.hom _).mp hcomp
    exact ⟨hrel.rep, hrel⟩
  have hStageSurj : (MorphismProperty.inverseImage (@Surjective.{u}) T).presheaf
      targetStageChart := MorphismProperty.of_isPullback hTargetStage hsurj
  have hStageEtale : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
      targetStageChart := MorphismProperty.of_isPullback hTargetStage hchartEtale
  exact ⟨stageIndex, hstage,
    (Space.isFinite_iff_etaleLocal B S hS (D.mapAt stageIndex hstage)
      (D.sourceAt_isAlgebraicSpace stageIndex hstage)
      (D.targetAt_isAlgebraicSpace stageIndex hstage)).mpr
      ⟨W stage, targetStageChart, hStageSurj, hStageEtale, hfinitePullback⟩⟩

end

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **The affine case of Stacks 084Z.** In the situation of Stacks 084W, if the base change
`f` of `f₀` to the limit `B` is finite and `f₀` is affine and locally of finite type, then
the base change `f_i` of `f₀` to some stage `B_i` is finite.

This is the source's own argument for Stacks 084Z, which obtains affineness at a stage from
Stacks 084Y and then runs exactly this: an affine étale chart `V₀ ⟶ Y₀` of the target,
Stacks 01ZO over the chart system, and Stacks 03ZQ to come back from the chart. Stacks 084Z
with no affineness hypothesis is
`AlgebraicGeometry.Space.MorphismDescentSituation.exists_isFinite_mapAt`. -/
theorem exists_isFinite_mapAt_of_isAffineHom_map₀
    (D : MorphismDescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (hAffine : IsAffineHom B S hS D.map₀)
    (hf : IsFinite B S hS D.mapLimit)
    (hlft : IsLocallyOfFiniteType B S hS D.map₀) :
    ∃ (stage : I) (hstage : D.initial ≤ stage), IsFinite B S hS (D.mapAt stage hstage) :=
  exists_isFinite_of_isAffineHom_map₀ D hI hAffine hf hlft

end Space

end AlgebraicGeometry

end
