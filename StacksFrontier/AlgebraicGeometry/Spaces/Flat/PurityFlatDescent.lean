module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreWitness
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.RelativelyPureModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Descent of purity along a flat morphism of pointed algebraic spaces

In the standing situation of Stacks 0CV6, let `(Y₁, y₁) ⟶ (Y, y)` be a morphism of pointed
algebraic spaces with `Y₁ ⟶ Y` flat at `y₁`. Purity and universal purity of the base change
`F_{Y₁}` above `y₁` then descend to `F` above `y`: impurities go *up* along a flat base change,
so their absence upstairs forces their absence downstairs.

## Main definitions

* `AlgebraicGeometry.Space.FlatImpurityAscentData`: the point-theoretic data which the proof
  of Stacks 0CVA extracts from an impurity of `F` above `y` — an étale chart `T₁` of
  `Y₁ ×_Y T` through a point `t₁` above both `y₁` and `t`, a generalization `t₁' ⤳ t₁`, and a
  point `ξ₁` of `X_{T₁}` above `t₁'`.
* `AlgebraicGeometry.Space.FlatImpurityAscentData.compare`: the comparison `X_{T₁} ⟶ X_T` of
  total spaces, with `AlgebraicGeometry.Space.FlatImpurityAscentData.diagram` the impurity
  diagram of the base-changed situation that the data defines.
* `AlgebraicGeometry.Space.HasFlatImpurityAscentData`: the condition that `Y₁ ⟶ Y` is flat
  at `y₁` and that every impurity of `F` above `y` admits such data, with `ξ₁` above `ξ` and
  relatively weakly associated to `F_{T₁}`.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_pullback_fst_of_isQuasiFiniteAt`: the pointwise
  form of Stacks 03XL, quasi-finiteness at a point passes to a base change.
* `AlgebraicGeometry.Space.FlatImpurityAscentData.isImpurity_diagram`: the ascended diagram is
  an impurity, which is the closing step of the proof of Stacks 0CVA.
* `AlgebraicGeometry.Space.FlatImpurityAscentData.exists_of_isFlatAt`: along a pointed base
  change flat at `y₁`, every impurity of `F` above `y` admits ascent data whose lifted point lies
  above `ξ` and is relatively weakly associated to `F_{T₁}`.
* `AlgebraicGeometry.Space.isPureAbove_of_isPureAbove_baseChange_of_isFlatAt`: **Stacks 0CVG,
  part (1).**
* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isUniversallyPureAbove_baseChange_of_isFlatAt`:
  **Stacks 0CVG, part (2)**, registered on its alias
  `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isFlatAt`.

## Implementation notes

Both parts of Stacks 0CVG are contrapositives of Stacks 0CVA, the ascent of impurities along a
flat pointed base change. The point-theoretic output of its proof — the étale chart
`T₁ ⟶ Y₁ ×_Y T` of Properties of Spaces 66.4.3 with a point above `y₁` and `t`, the lift of the
specialization `t' ⤳ t` through the flatness of `T₁ ⟶ T` at `t₁` (Stacks 03HV), and the lift
`ξ₁` of the relatively weakly associated point `ξ` of Divisors on Spaces 71.4.7 (Stacks 0CV2,
at a field-valued representative supplied by Stacks 05DC) — is constructed here, in
`AlgebraicGeometry.Space.FlatImpurityAscentData.exists_of_isFlatAt`. The impurity condition
for the ascended diagram, which is the closing step of the source's proof of Stacks 0CVA, is
`AlgebraicGeometry.Space.FlatImpurityAscentData.isImpurity_diagram`, proved from the
comparison `X_{T₁} ⟶ X_T` constructed below, and part (1) additionally needs quasi-finiteness
of `T₁ ⟶ Y₁` at `t₁`, which the source deduces from Stacks 03XU and Stacks 03XK.

`AlgebraicGeometry.Space.HasFlatImpurityAscentData` packages the flatness of `Y₁ ⟶ Y` at `y₁`
with the existence of that ascent data for every impurity; Stacks 0CVA itself, as an
existence statement for impurities of the base-changed situation, is
`AlgebraicGeometry.Space.exists_isImpurity_baseChange_etale_of_isFlatAt` in
`StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityFlatAscent`.

Purity and universal purity above a point are `AlgebraicGeometry.Space.IsPureAbove` and
`AlgebraicGeometry.Space.IsUniversallyPureAbove` of Stacks 0CVD, and the base change of the
situation along a morphism of pointed algebraic spaces is
`AlgebraicGeometry.Space.PointedOver.baseChange`; as there, it is a situation of Stacks 0CV6
outright, with quasi-coherence and finiteness of type of the base-changed module proved rather
than assumed.

## References

* [Stacks Project, Tag 0CVG](https://stacks.math.columbia.edu/tag/0CVG)
* [Stacks Project, Tag 0CVA](https://stacks.math.columbia.edu/tag/0CVA)
* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 03XK](https://stacks.math.columbia.edu/tag/03XK)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03HV](https://stacks.math.columbia.edu/tag/03HV)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Quasi-finiteness at a point and base change -/

/-- **Stacks 03XL at a point.** A base change of a morphism quasi-finite at `t` is
quasi-finite at every point of the base change lying over `t`. -/
theorem isQuasiFiniteAt_pullback_fst_of_isQuasiFiniteAt (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Y₁ Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (c : Y₁ ⟶ Y) (g : T ⟶ Y) {t : points B S hS T}
    (hg : IsQuasiFiniteAt B S hS g t) (z : points B S hS (pullback c g))
    (hz : pointsMap B S hS (pullback c g) (pullback.snd c g) z = t) :
    IsQuasiFiniteAt B S hS (pullback.fst c g) z := by
  obtain ⟨U, hU, t', ht', hUg⟩ := hg
  have hP : IsAlgebraicSpace B S hS (pullback c g) :=
    isAlgebraicSpace_pullback B S hS c g hY₁ hT hY
  have hW : IsOpenSubspace B S hS (U.preimage (pullback.snd c g)) :=
    isOpenSubspace_preimage B S hS (pullback.snd c g) U hT hP hU
  have hsq : IsPullback (U.fromPreimage (pullback.snd c g))
      (U.preimage (pullback.snd c g)).ι U.ι (pullback.snd c g) :=
    Subfunctor.isPullback_preimage _ U
  obtain ⟨w, _, hw⟩ := exists_points_of_isPullback B S hS hsq t' z (by rw [ht', hz])
  exact ⟨_, hW, w, hw, IsLocallyQuasiFinite.of_isPullback B S hS
    (hsq.flip.paste_horiz (IsPullback.of_hasPullback c g)) hU.1 hY hUg⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### The data ascending an impurity along a flat base change -/

/-- If a square `h ≫ k = f ≫ g` commutes, `f` carries `x` to `ξ` and `k` carries `t₁` to `t`, then
`t` outside the image of the closure of `ξ` under `g` forces `t₁` outside that of `x` under `h`. -/
private theorem notMem_image_closure_of_comm_sq {F G T₁ T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G ⟶ T} {h : F ⟶ T₁} {k : T₁ ⟶ T} (hsq : h ≫ k = f ≫ g)
    {x : points B S hS F} {ξ : points B S hS G} (hx : pointsMap B S hS F f x = ξ)
    {t₁ : points B S hS T₁} {t : points B S hS T} (ht : pointsMap B S hS T₁ k t₁ = t)
    (hξ : t ∉ pointsMap B S hS G g '' closure {ξ}) :
    t₁ ∉ pointsMap B S hS F h '' closure {x} := by
  rintro ⟨θ, hθ, hmap⟩
  refine hξ ⟨pointsMap B S hS F f θ, ?_, ?_⟩
  · have himg := image_closure_subset_closure_image (s := {x})
      (continuous_pointsMap B S hS (F := F) f)
    rw [Set.image_singleton, hx] at himg
    exact himg ⟨θ, hθ, rfl⟩
  · rw [← Function.comp_apply (f := pointsMap B S hS G g), ← pointsMap_comp, ← hsq, pointsMap_comp,
      Function.comp_apply, hmap, ht]

/-- The point-theoretic data which the proof of **Stacks 0CVA** extracts from an impurity `D`
of `F` above `y`: an étale chart `T₁` of `Y₁ ×_Y T` through a point `t₁` above both `y₁` and
`t`, a generalization `t₁' ⤳ t₁`, and a point `ξ₁` of `X_{T₁}` above `t₁'`. -/
structure FlatImpurityAscentData {P : PrePureSituation.{u, u} B S hS} (c : PointedOver P)
    (D : ImpurityDiagram P) where
  /-- The scheme carrying the étale chart of `Y₁ ×_Y T`. -/
  T₁ : BigFppfOver B S hS
  /-- The chart of `Y₁ ×_Y T`. -/
  e : yoneda.obj T₁ ⟶ pullback c.g D.g
  /-- The chart is étale. -/
  etale : IsEtale B S hS e
  /-- The point of the chart above `y₁` and `t`. -/
  t₁ : points B S hS (yoneda.obj T₁)
  /-- The generalization of that point lying above `t'`. -/
  t₁' : points B S hS (yoneda.obj T₁)
  /-- The specialization `t₁' ⤳ t₁`, taken in the scheme representing the chart. -/
  specializes : pointsToScheme B S hS T₁ t₁' ⤳ pointsToScheme B S hS T₁ t₁
  /-- The distinguished point of the chart lies above the chosen point `y₁` of `Y₁`. -/
  mapsToPoint : pointsMap B S hS (yoneda.obj T₁) (e ≫ pullback.fst c.g D.g) t₁ = c.y'
  /-- The distinguished point of the chart lies above the point `t` of `T`. -/
  mapsToT : pointsMap B S hS (yoneda.obj T₁) (e ≫ pullback.snd c.g D.g) t₁ = D.t
  /-- The distinguished point of the total space `X_{T₁} = T₁ ×_{Y₁} X₁`. -/
  xi : points B S hS (pullback (e ≫ pullback.fst c.g D.g) (pullback.fst c.g P.f))
  /-- It lies above the generalization `t₁'`. -/
  xi_liesOver :
    pointsMap B S hS (pullback (e ≫ pullback.fst c.g D.g) (pullback.fst c.g P.f))
      (pullback.fst (e ≫ pullback.fst c.g D.g) (pullback.fst c.g P.f)) xi = t₁'

namespace FlatImpurityAscentData

variable {P : PrePureSituation.{u, u} B S hS} {c : PointedOver P} {D : ImpurityDiagram P}
    (d : FlatImpurityAscentData c D)

/-- The structure morphism `T₁ ⟶ Y₁` of the ascended diagram: the chart of `Y₁ ×_Y T`
followed by the projection to `Y₁`. -/
noncomputable abbrev structureMap : yoneda.obj d.T₁ ⟶ c.Y' := d.e ≫ pullback.fst c.g D.g

/-- The total space `X_{T₁} = T₁ ×_{Y₁} X₁` of the ascended diagram. -/
noncomputable abbrev total : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback d.structureMap (pullback.fst c.g P.f)

/-- The comparison `X_{T₁} ⟶ X_T` of total spaces, induced by `T₁ ⟶ T` and by the projection
`X₁ ⟶ X`. -/
noncomputable def compare : d.total ⟶ pullback D.g P.f :=
  pullback.lift
    (pullback.fst d.structureMap (pullback.fst c.g P.f) ≫ d.e ≫ pullback.snd c.g D.g)
    (pullback.snd d.structureMap (pullback.fst c.g P.f) ≫ pullback.snd c.g P.f)
    (by
      have h₁ : pullback.snd c.g D.g ≫ D.g = pullback.fst c.g D.g ≫ c.g :=
        pullback.condition.symm
      have h₂ : pullback.snd c.g P.f ≫ P.f = pullback.fst c.g P.f ≫ c.g :=
        pullback.condition.symm
      have h₃ : pullback.fst d.structureMap (pullback.fst c.g P.f) ≫ d.structureMap =
          pullback.snd d.structureMap (pullback.fst c.g P.f) ≫ pullback.fst c.g P.f :=
        pullback.condition
      calc (pullback.fst d.structureMap (pullback.fst c.g P.f) ≫
              d.e ≫ pullback.snd c.g D.g) ≫ D.g
          = pullback.fst d.structureMap (pullback.fst c.g P.f) ≫
              d.e ≫ pullback.snd c.g D.g ≫ D.g := by simp
        _ = (pullback.fst d.structureMap (pullback.fst c.g P.f) ≫ d.structureMap) ≫ c.g := by
            rw [h₁]; simp
        _ = (pullback.snd d.structureMap (pullback.fst c.g P.f) ≫
              pullback.fst c.g P.f) ≫ c.g := by rw [h₃]
        _ = (pullback.snd d.structureMap (pullback.fst c.g P.f) ≫
              pullback.snd c.g P.f) ≫ P.f := by rw [Category.assoc, ← h₂]; simp)

/-- The comparison of total spaces is compatible with the projections to the chart and
to `T`. -/
theorem compare_comp_fst :
    d.compare ≫ pullback.fst D.g P.f =
      pullback.fst d.structureMap (pullback.fst c.g P.f) ≫ d.e ≫ pullback.snd c.g D.g :=
  pullback.lift_fst _ _ _

/-- The impurity diagram of the base-changed situation defined by the ascent data. -/
@[reducible] noncomputable def diagram : ImpurityDiagram c.baseChange where
  T := d.T₁
  g := d.structureMap
  t' := d.t₁'
  t := d.t₁
  specializes := d.specializes
  mapsToChosenPoint := d.mapsToPoint
  xi := d.xi
  xi_liesOver := d.xi_liesOver

/-- **The closing step of Stacks 0CVA.** If the lifted point `ξ₁` lies above `ξ` and is
relatively weakly associated to `F_{T₁}`, then the ascended diagram is an impurity of `F₁`
above `y₁`: the closure of `{ξ₁}` maps into that of `{ξ}`, whose image in `T` misses `t`. -/
theorem isImpurity_diagram (hxi : pointsMap B S hS d.total d.compare d.xi = D.xi)
    (hass : d.diagram.IsRelativeWeakAssassinPoint d.diagram.xi)
    (hD : D.IsImpurity) : d.diagram.IsImpurity := by
  exact ⟨hass, notMem_image_closure_of_comm_sq d.compare_comp_fst.symm hxi d.mapsToT hD.2⟩

/-- The structure morphism of the ascended diagram is quasi-finite at `t₁` when `T ⟶ Y` is
quasi-finite at `t`: the chart is étale, hence locally quasi-finite by Stacks 03XU, the
projection `Y₁ ×_Y T ⟶ Y₁` is quasi-finite at the image of `t₁` by Stacks 03XL, and
quasi-finiteness at a point composes by Stacks 03XK. -/
theorem isQuasiFiniteAt_structureMap (hD : IsQuasiFiniteAt B S hS D.g D.t) :
    IsQuasiFiniteAt B S hS d.structureMap d.t₁ := by
  have hT : IsAlgebraicSpace B S hS (yoneda.obj D.T) := isAlgebraicSpace_yoneda B S hS D.T
  have hPB : IsAlgebraicSpace B S hS (pullback c.g D.g) :=
    isAlgebraicSpace_pullback B S hS c.g D.g c.hY' hT P.hY
  refine isQuasiFiniteAt_comp B S hS hPB c.hY' d.e (pullback.fst c.g D.g) d.t₁
    (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS (isAlgebraicSpace_yoneda B S hS d.T₁)
      (isLocallyQuasiFinite_of_isEtale B S hS hPB d.etale) d.t₁) ?_
  refine isQuasiFiniteAt_pullback_fst_of_isQuasiFiniteAt B S hS c.hY' P.hY hT c.g D.g hD _ ?_
  rw [← Function.comp_apply (f := pointsMap B S hS (pullback c.g D.g) (pullback.snd c.g D.g)),
    ← pointsMap_comp]
  exact d.mapsToT

end FlatImpurityAscentData

/-- The output of the proof of **Stacks 0CVA**: `Y₁ ⟶ Y` is flat at `y₁` and every impurity of
`F` above `y` admits ascent data along `(Y₁, y₁) ⟶ (Y, y)` whose lifted point lies above `ξ` and
is relatively weakly associated to `F_{T₁}`. -/
def HasFlatImpurityAscentData {P : PrePureSituation.{u, u} B S hS} (c : PointedOver P) :
    Prop :=
  IsFlatAt B S hS c.g c.y' ∧
    ∀ D : ImpurityDiagram P, D.IsImpurity →
      ∃ d : FlatImpurityAscentData c D,
        pointsMap B S hS d.total d.compare d.xi = D.xi ∧
          d.diagram.IsRelativeWeakAssassinPoint d.diagram.xi

/-! ### The ascent data exists along a flat pointed base change -/

/-- Flatness at a point passes to the other leg of a cartesian square of schemes. -/
theorem isFlatAt_snd_of_isPullback {X Y Z W : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) (w : W)
    (hf : _root_.AlgebraicGeometry.IsFlatAt f.toLRSHom.toShHom (p.base w)) :
    _root_.AlgebraicGeometry.IsFlatAt q.toLRSHom.toShHom w := by
  have hfst : sq.flip.isoPullback.hom ≫ Limits.pullback.fst g f = q :=
    sq.flip.isoPullback_hom_fst
  have hsnd : sq.flip.isoPullback.hom ≫ Limits.pullback.snd g f = p :=
    sq.flip.isoPullback_hom_snd
  have hbase : (Limits.pullback.snd g f).base (sq.flip.isoPullback.hom.base w) = p.base w :=
    congrArg (fun m : W ⟶ X => m.base w) hsnd
  have hflat : _root_.AlgebraicGeometry.IsFlatAt (Limits.pullback.fst g f).toLRSHom.toShHom
      (sq.flip.isoPullback.hom.base w) :=
    _root_.AlgebraicGeometry.isFlatAt_pullback_fst_of_isFlatAt g f
      (sq.flip.isoPullback.hom.base w) (by rw [hbase]; exact hf)
  have key : _root_.AlgebraicGeometry.IsFlatAt
      (sq.flip.isoPullback.hom ≫ Limits.pullback.fst g f).toLRSHom.toShHom w := by
    change ((sq.flip.isoPullback.hom ≫ Limits.pullback.fst g f).stalkMap w).hom.Flat
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.Flat.comp_iff_of_bijective_left
      (ConcreteCategory.bijective_of_isIso (sq.flip.isoPullback.hom.stalkMap w))).mpr hflat
  exact hfst ▸ key

/-- **The test scheme of Stacks 0CVA.** Let `g : Y₁ ⟶ Y` be a morphism of algebraic spaces
flat at a point `y₁`, let `d : T ⟶ Y` be a morphism from a scheme and let `t' ⤳ t` be a
specialization in `T` with `t` lying over the image of `y₁`. Then there is a scheme `T₁` étale
over `Y₁ ×_Y T` carrying a point `t₁` above `y₁` and `t` and a point `t₁'` above `t'` which
specializes to `t₁`.

The chart is `T₁ = U ×_V (V ×_Y T)` for a pointed étale chart `U ⟶ V` of `g` at `y₁`; it is
flat over `T` at `t₁` by the pointwise base change of flatness for schemes and by étaleness of
`V ×_Y T ⟶ T`, and the specialization lifts by Stacks 03HV. -/
theorem exists_flatAscentChart_of_isFlatAt
    {Y₁ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY₁ : IsAlgebraicSpace B S hS Y₁)
    (hY : IsAlgebraicSpace B S hS Y) (g : Y₁ ⟶ Y) {y₁ : points B S hS Y₁}
    (hg : IsFlatAt B S hS g y₁) (T : BigFppfOver B S hS) (d : yoneda.obj T ⟶ Y)
    {t t' : points B S hS (yoneda.obj T)}
    (ht : pointsMap B S hS (yoneda.obj T) d t = pointsMap B S hS Y₁ g y₁)
    (hs : pointsToScheme B S hS T t' ⤳ pointsToScheme B S hS T t) :
    ∃ (T₁ : BigFppfOver B S hS) (e : yoneda.obj T₁ ⟶ pullback g d)
      (t₁ t₁' : points B S hS (yoneda.obj T₁)),
      IsEtale B S hS e ∧
        pointsToScheme B S hS T₁ t₁' ⤳ pointsToScheme B S hS T₁ t₁ ∧
          pointsMap B S hS (yoneda.obj T₁) (e ≫ pullback.fst g d) t₁ = y₁ ∧
            pointsMap B S hS (yoneda.obj T₁) (e ≫ pullback.snd g d) t₁ = t ∧
              pointsMap B S hS (yoneda.obj T₁) (e ≫ pullback.snd g d) t₁' = t' := by
  classical
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨c, hc⟩ := (holdsOnEveryEtaleChartAtPoint_iff_some B S hS
    (@MorphismOfGerms.IsFlat.{u}) MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat
    hY₁ hY g y₁).mp hg
  -- `W = V ×_Y T` and `T₁ = U ×_V W`.
  set wV : c.b_etale.rep.pullback d ⟶ c.V := c.b_etale.rep.fst' d with hwV
  set wT : c.b_etale.rep.pullback d ⟶ T := c.b_etale.rep.snd d with hwT
  have hW : IsPullback (yoneda.map wV) (yoneda.map wT) c.b d := c.b_etale.rep.isPullback' d
  set T₁ := pullback c.h wV with hT₁
  set a : T₁ ⟶ c.U := pullback.fst c.h wV with ha
  set b : T₁ ⟶ c.b_etale.rep.pullback d := pullback.snd c.h wV with hb
  set kk : T₁ ⟶ T := b ≫ wT with hkk
  have hQ : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c.h) (yoneda.map wV) :=
    (IsPullback.of_hasPullback c.h wV).map yoneda
  have houter : IsPullback (yoneda.map a) (yoneda.map kk) (c.a ≫ g) d := by
    simpa only [hkk, ← Functor.map_comp, c.comm] using hQ.paste_vert hW
  set e : yoneda.obj T₁ ⟶ pullback g d :=
    pullback.lift (yoneda.map a ≫ c.a) (yoneda.map kk)
      (by simpa only [Category.assoc] using houter.w) with he
  have heY : e ≫ pullback.fst g d = yoneda.map a ≫ c.a := pullback.lift_fst _ _ _
  have heT : e ≫ pullback.snd g d = yoneda.map kk := pullback.lift_snd _ _ _
  have hecart : IsPullback (yoneda.map a) e c.a (pullback.fst g d) := by
    have ho : IsPullback (yoneda.map a) (e ≫ pullback.snd g d) (c.a ≫ g) d := by rwa [heT]
    exact ho.of_bot heY.symm (IsPullback.of_hasPullback g d)
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have heEtale : IsEtale B S hS e := isEtale_of_presheaf_etale B S hS
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hecart c.a_etale)
  -- The point `t₁` of `T₁` over the chart point and over `t`.
  set u₀ := c.representative.class B S hS (yoneda.obj c.U) with hu₀
  have hcompat : pointsMap B S hS (yoneda.obj c.U) (c.a ≫ g) u₀ =
      pointsMap B S hS (yoneda.obj T) d t := by
    rw [pointsMap_comp, Function.comp_apply, c.maps_to]
    exact ht.symm
  obtain ⟨t₁, ht₁U, ht₁T⟩ := exists_points_of_isPullback B S hS houter u₀ t hcompat
  -- Flatness of `T₁ ⟶ T` at `t₁`, read on schemes.
  have hpt : c.point = IsLocalRing.closedPoint c.representative.carrier := Subsingleton.elim _ _
  have hxU : (BigFppfOver.toScheme B S hS).map a (pointsToScheme B S hS T₁ t₁) =
      c.sourcePoint B S hS := by
    rw [← pointsToScheme_pointsMap_yoneda, ht₁U, hu₀, pointsToScheme_class]
    change schemePoint B S hS c.U c.representative =
      (BigFppfOver.toScheme B S hS).map c.representative.value c.point
    rw [hpt]
    rfl
  have hcflat : _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map c.h).toLRSHom.toShHom (c.sourcePoint B S hS) :=
    (MorphismOfGerms.isFlat_ofSchemeHom_iff ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS)).mp hc
  have hbflat : _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom
      (pointsToScheme B S hS T₁ t₁) :=
    isFlatAt_snd_of_isPullback
      ((IsPullback.of_hasPullback c.h wV).map (BigFppfOver.toScheme B S hS)) _
      (by rw [hxU]; exact hcflat)
  have hwEtale : Etale ((BigFppfOver.toScheme B S hS).map wT) := c.b_etale.property_snd d
  have hkflat : _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map kk).toLRSHom.toShHom
      (pointsToScheme B S hS T₁ t₁) := by
    change (Scheme.Hom.stalkMap ((BigFppfOver.toScheme B S hS).map kk)
      (pointsToScheme B S hS T₁ t₁)).hom.Flat
    rw [hkk, Functor.map_comp, Scheme.Hom.stalkMap_comp]
    exact RingHom.Flat.comp
      (Flat.stalkMap ((BigFppfOver.toScheme B S hS).map wT)
        ((BigFppfOver.toScheme B S hS).map b (pointsToScheme B S hS T₁ t₁))) hbflat
  -- Lifting the specialization.
  have hkx : (BigFppfOver.toScheme B S hS).map kk (pointsToScheme B S hS T₁ t₁) =
      pointsToScheme B S hS T t := by
    rw [← pointsToScheme_pointsMap_yoneda, ht₁T]
  have hgen : pointsToScheme B S hS T t' ⤳
      (BigFppfOver.toScheme B S hS).map kk (pointsToScheme B S hS T₁ t₁) := by
    rw [hkx]; exact hs
  obtain ⟨x', hxx', hx'⟩ := _root_.AlgebraicGeometry.exists_specializes_of_isFlatAt
    ((BigFppfOver.toScheme B S hS).map kk) (pointsToScheme B S hS T₁ t₁) hkflat hgen
  have hval : pointsToScheme B S hS T₁ ((pointsEquivScheme B S hS T₁).symm x') = x' :=
    (pointsEquivScheme B S hS T₁).apply_symm_apply x'
  refine ⟨T₁, e, t₁, (pointsEquivScheme B S hS T₁).symm x', heEtale, by rw [hval]; exact hxx',
    ?_, ?_, ?_⟩
  · rw [heY, pointsMap_comp, Function.comp_apply, ht₁U]
    exact c.maps_to
  · rw [heT]; exact ht₁T
  · refine injective_pointsToScheme B S hS T ?_
    rw [heT, pointsToScheme_pointsMap_yoneda, hval, hx']

/-- **The ascent data of Stacks 0CVA.** Let `(Y', y') ⟶ (Y, y)` be a morphism of pointed
algebraic spaces over `S` with `Y' ⟶ Y` flat at `y'`, and let `D` be an impurity of `F` above
`y`. Then there is an étale chart `T₁` of `Y' ×_Y T` with a point `t₁` above `y'` and `t`, a
generalization `t₁' ⤳ t₁` above `t' ⤳ t` and a point `ξ₁` of `X_{T₁}` above `t₁'` and `ξ` which
lies in the relative weak assassin of `F_{T₁}`.

This is the proof of the source: the chart and the lifted specialization are Stacks 03H4 and
Stacks 03HV through the flatness of `T₁ ⟶ T` at `t₁`, and `ξ₁` is Stacks 0CV2, part (2), at a
field-valued representative of `t₁'` supplied by the algebraic space form of Stacks 05DC,
`AlgebraicGeometry.Space.exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq`. -/
theorem FlatImpurityAscentData.exists_of_isFlatAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y')
    (D : ImpurityDiagram P) (hD : D.IsImpurity) :
    ∃ d : FlatImpurityAscentData c D,
      pointsMap B S hS d.total d.compare d.xi = D.xi ∧
        d.diagram.IsRelativeWeakAssassinPoint d.diagram.xi := by
  classical
  have hDass := hD.1
  unfold ImpurityDiagram.IsImpurity at hD
  obtain ⟨-, hDcl⟩ := hD
  -- A test scheme étale over `Y' ×_Y T`, with the specialization lifted to it.
  obtain ⟨T₁, e, t₁, t₁', heEtale, hspec, hgEt₁, hkt₁, hkt₁'⟩ :=
    exists_flatAscentChart_of_isFlatAt c.hY' P.hY c.g hflat D.T D.g
      (t := D.t) (t' := D.t') (by rw [D.mapsToChosenPoint, c.mapsPoint]) D.specializes
  set gE : yoneda.obj T₁ ⟶ c.Y' := e ≫ pullback.fst c.g D.g with hgE
  set k : yoneda.obj T₁ ⟶ yoneda.obj D.T := e ≫ pullback.snd c.g D.g with hk
  have hcond : gE ≫ c.g = k ≫ D.g := by
    rw [hgE, hk, Category.assoc, Category.assoc, pullback.condition]
  -- The total space `T₁ ×_Y X` is the base change of `X_T` along `T₁ ⟶ T`.
  have tD : IsPullback D.toX D.toT P.f D.g := (IsPullback.of_hasPullback D.g P.f).flip
  have hliftw : pullback.snd (gE ≫ c.g) P.f ≫ P.f =
      (pullback.fst (gE ≫ c.g) P.f ≫ k) ≫ D.g :=
    (pullback.condition (f := gE ≫ c.g) (g := P.f)).symm.trans
      ((congrArg (fun m => pullback.fst (gE ≫ c.g) P.f ≫ m) hcond).trans
        (Category.assoc _ _ _).symm)
  have sN : IsPullback (pullback.snd (gE ≫ c.g) P.f) (pullback.fst (gE ≫ c.g) P.f) P.f
      (k ≫ D.g) := by
    rw [← hcond]
    exact (IsPullback.of_hasPullback (gE ≫ c.g) P.f).flip
  set Ψ := tD.lift (pullback.snd (gE ≫ c.g) P.f) (pullback.fst (gE ≫ c.g) P.f ≫ k) hliftw
    with hΨdef
  have hΨX : Ψ ≫ D.toX = pullback.snd (gE ≫ c.g) P.f := tD.lift_fst _ _ _
  have hΨT : Ψ ≫ D.toT = pullback.fst (gE ≫ c.g) P.f ≫ k := tD.lift_snd _ _ _
  have sq : IsPullback Ψ (pullback.fst (gE ≫ c.g) P.f) D.toT k := IsPullback.of_right' sN tD
  have hN : IsAlgebraicSpace B S hS (pullback (gE ≫ c.g) P.f) :=
    isAlgebraicSpace_pullback B S hS (gE ≫ c.g) P.f
      (isAlgebraicSpace_yoneda B S hS T₁) P.hX P.hY
  set Nspace : AlgebraicSpaces B S hS := ⟨pullback (gE ≫ c.g) P.f, hN⟩ with hNspace
  set T₁space : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj T₁, isAlgebraicSpace_yoneda B S hS T₁⟩ with hT₁space
  set NtoT : Nspace ⟶ T₁space := ObjectProperty.homMk (pullback.fst (gE ≫ c.g) P.f)
    with hNtoT
  set NtoX : Nspace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.homMk (pullback.snd (gE ≫ c.g) P.f) with hNtoX
  set kSpace : T₁space ⟶ (⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩ :
    AlgebraicSpaces B S hS) := ObjectProperty.homMk k with hkSpace
  set ΨSpace : Nspace ⟶ D.baseChangeSpace := ObjectProperty.homMk Ψ with hΨSpace
  -- The projection `X_T ⟶ T`, as a morphism of algebraic spaces.
  let τ : D.baseChangeSpace ⟶ (⟨yoneda.obj D.T, isAlgebraicSpace_yoneda B S hS D.T⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk D.toT
  -- A field-valued representative of `t₁'` over whose image `ξ` is witnessed: the algebraic
  -- space form of Stacks 05DC.
  obtain ⟨q, hqclass, hqwit⟩ : ∃ q : FieldValuedPoint B S hS (yoneda.obj T₁),
      q.class B S hS (yoneda.obj T₁) = t₁' ∧
        IsWeaklyAssociatedOnFibre B S hS τ D.baseChangeModule
          (FieldValuedPoint.map B S hS (yoneda.obj T₁) k q) D.xi :=
    exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq B S hS τ
      D.baseChangeModule
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.toXSpace P.F
        P.moduleQuasicoherent) hDass kSpace (hkt₁'.trans D.xi_liesOver.symm)
  -- The point `ξ₁` of `T₁ ×_Y X`, from Stacks 0CV2, part (2).
  obtain ⟨xi₁, hxi₁ass, hxi₁X, hxi₁T⟩ :=
    exists_isRelativeWeaklyAssociatedPoint_baseChange B S hS (f := τ)
      (g := kSpace) (f' := NtoT) (g' := ΨSpace) sq D.baseChangeModule q hqwit
  have hxi₁X' : pointsMap B S hS (pullback (gE ≫ c.g) P.f) Ψ xi₁ = D.xi := hxi₁X
  have hxi₁T' :
      pointsMap B S hS (pullback (gE ≫ c.g) P.f) (pullback.fst (gE ≫ c.g) P.f) xi₁ =
        q.class B S hS (yoneda.obj T₁) := hxi₁T
  -- The pulled-back module on `T₁ ×_Y X` is the base change of `F`.
  have hpath : ΨSpace ≫ D.toXSpace = NtoX := ObjectProperty.hom_ext _ hΨX
  have hmod : (modulePullback B S hS ΨSpace).obj D.baseChangeModule ≅
      (modulePullback B S hS NtoX).obj P.F :=
    (modulePullbackCompIso B S hS ΨSpace D.toXSpace).app P.F ≪≫
      eqToIso (congrArg (fun m : Nspace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) =>
        (modulePullback B S hS m).obj P.F) hpath)
  have hass : IsRelativeWeaklyAssociatedPoint B S hS NtoT
      ((modulePullback B S hS NtoX).obj P.F) xi₁ :=
    (isRelativeWeaklyAssociatedPoint_congr NtoT hmod xi₁).mp hxi₁ass
  -- Assemble the impurity diagram of the base-changed situation.
  set φ := pullbackRightPullbackFstIso c.g P.f gE with hφ
  have hinv : φ.inv ≫ pullback.fst gE (pullback.fst c.g P.f) =
      pullback.fst (gE ≫ c.g) P.f := by
    rw [hφ, Iso.inv_comp_eq, pullbackRightPullbackFstIso_hom_fst]
  set E : ImpurityDiagram c.baseChange :=
    { T := T₁, g := gE, t' := t₁', t := t₁, specializes := hspec,
      mapsToChosenPoint := hgEt₁
      xi := pointsMap B S hS (pullback (gE ≫ c.g) P.f) φ.inv xi₁
      xi_liesOver := by
        rw [← Function.comp_apply
            (f := pointsMap B S hS _ (pullback.fst gE (pullback.fst c.g P.f))),
          ← pointsMap_comp, hinv, hxi₁T', hqclass] } with hEdef
  have hxieq : (c.alongBaseChange E).xi = xi₁ := by
    change pointsMap B S hS (pullback gE (pullback.fst c.g P.f)) φ.hom
      (pointsMap B S hS (pullback (gE ≫ c.g) P.f) φ.inv xi₁) = xi₁
    rw [← Function.comp_apply (f := pointsMap B S hS _ φ.hom), ← pointsMap_comp,
      Iso.inv_hom_id, pointsMap_id, id_eq]
  have hEimp : E.IsImpurity := by
    refine (c.isImpurity_alongBaseChange_iff E).mp ?_
    unfold ImpurityDiagram.IsImpurity
    rw [hxieq]
    refine ⟨hass, ?_⟩
    exact notMem_image_closure_of_comm_sq hΨT.symm hxi₁X' hkt₁ hDcl
  -- The ascent data, whose diagram is `E`.
  let d : FlatImpurityAscentData c D :=
    { T₁ := T₁, e := e, etale := heEtale, t₁ := t₁, t₁' := t₁', specializes := hspec,
      mapsToPoint := hgEt₁, mapsToT := hkt₁, xi := E.xi, xi_liesOver := E.xi_liesOver }
  have hcmp : d.compare = φ.hom ≫ Ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [FlatImpurityAscentData.compare_comp_fst, Category.assoc]
      change _ = φ.hom ≫ Ψ ≫ D.toT
      rw [hΨT, ← Category.assoc φ.hom, hφ, pullbackRightPullbackFstIso_hom_fst]
    · rw [Category.assoc]
      change d.compare ≫ pullback.snd D.g P.f = φ.hom ≫ Ψ ≫ D.toX
      rw [hΨX, hφ, pullbackRightPullbackFstIso_hom_snd]
      exact pullback.lift_snd _ _ _
  refine ⟨d, ?_, hEimp.1⟩
  rw [hcmp, pointsMap_comp, Function.comp_apply]
  exact (congrArg (pointsMap B S hS _ Ψ) hxieq).trans hxi₁X'

/-! ### Descent of purity -/

/-- **Stacks 0CVG, part (1).** If `(Y₁, y₁) ⟶ (Y, y)` is a morphism of pointed algebraic
spaces with `Y₁ ⟶ Y` flat at `y₁` and the base change `F_{Y₁}` is pure above `y₁`, then `F` is
pure above `y`. -/
@[stacks 0CVG "part (1)"]
theorem isPureAbove_of_isPureAbove_baseChange_of_isFlatAt (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y')
    (hpure : IsPureAbove c.baseChange) :
    IsPureAbove P := by
  intro D hD himp
  obtain ⟨d, hxi, hass⟩ := FlatImpurityAscentData.exists_of_isFlatAt P c hflat D himp
  exact hpure d.diagram (d.isQuasiFiniteAt_structureMap hD)
    (d.isImpurity_diagram hxi hass himp)

/-- **Stacks 0CVG, part (2).** If `(Y₁, y₁) ⟶ (Y, y)` is a morphism of pointed algebraic
spaces with `Y₁ ⟶ Y` flat at `y₁` and the base change `F_{Y₁}` is universally pure above `y₁`,
then `F` is universally pure above `y`. The tag is registered on the alias
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isFlatAt`. -/
theorem isUniversallyPureAbove_of_isUniversallyPureAbove_baseChange_of_isFlatAt
    (P : PrePureSituation.{u, u} B S hS)
    (c : PointedOver P) (hflat : IsFlatAt B S hS c.g c.y')
    (hpure : IsUniversallyPureAbove c.baseChange) :
    IsUniversallyPureAbove P := by
  intro D himp
  obtain ⟨d, hxi, hass⟩ := FlatImpurityAscentData.exists_of_isFlatAt P c hflat D himp
  exact hpure d.diagram (d.isImpurity_diagram hxi hass himp)

end AlgebraicGeometry.Space

end
