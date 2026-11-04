module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap

/-!
# Affineness of a morphism descends to a stage of a limit of bases

Let `B = lim B_i` be a directed inverse limit of algebraic spaces over `S` with affine
transition morphisms, let `f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated
algebraic spaces over one stage `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be the base
changes of `f₀` to `B_i` and to `B`, as in `AlgebraicGeometry.Space.MorphismDescentSituation`.
This file proves that if `f` is affine and the inverse system of bases is small for the site,
then `f_i` is affine for some `i ≥ 0`.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeSnd` is the base change of a morphism over a fixed base
  along a morphism into that base, as a morphism of fibre products with a common first factor.
* `AlgebraicGeometry.Space.MorphismDescentSituation.stagesBaseChangeDescentSituation` is the
  inverse system `B_i ×_{B₀} T` of base changes of a fixed quasi-compact quasi-separated
  algebraic space `T` over `B₀`, as a descent situation.

## Main results

* `MorphismDescentSituation.isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit`: if `f` is
  affine and `V₀ ⟶ Y₀` has affine source, then `B ×_{B₀} (X₀ ×_{Y₀} V₀)` is an affine algebraic
  space.
* `MorphismDescentSituation.isAffineHom_mapAt_of_isAffineSpace_baseChange`: if `V₀ ⟶ Y₀` is
  surjective and étale with affine source and `B_i ×_{B₀} (X₀ ×_{Y₀} V₀)` is an affine algebraic
  space, then `f_i` is affine.
* `MorphismDescentSituation.exists_isAffineHom_mapAt_of_descentAffineStage`: if `f` is affine
  then `f_i` is affine for some `i ≥ 0`, assuming that every directed inverse system of
  quasi-compact quasi-separated algebraic spaces with affine transition morphisms and affine
  limit, small for the site, has an affine stage.
* `MorphismDescentSituation.exists_isAffineHom_mapAt_of_isAffineHom_mapLimit`: if `f` is affine
  and the inverse system of bases is small for the site, then `f_i` is affine for some `i ≥ 0`.

## References

* [Stacks Project, Tag 084Y](https://stacks.math.columbia.edu/tag/084Y)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Base change of the second factor of a fibre product -/

section BaseChangeSnd

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **The base change along `b` of a morphism over a fixed base.** For `x : X ⟶ Z` and
`y : Y ⟶ Z` and a morphism `f : X ⟶ Y` over `Z`, the induced morphism
`A ×_Z X ⟶ A ×_Z Y` of fibre products with common first factor `b : A ⟶ Z`. -/
noncomputable def baseChangeSnd {A Z X Y : C} (b : A ⟶ Z) {x : X ⟶ Z} {y : Y ⟶ Z}
    (f : X ⟶ Y) (hf : f ≫ y = x) : pullback b x ⟶ pullback b y :=
  pullback.lift (pullback.fst b x) (pullback.snd b x ≫ f)
    (by rw [Category.assoc, hf, pullback.condition])

@[reassoc (attr := simp)]
theorem baseChangeSnd_fst {A Z X Y : C} (b : A ⟶ Z) {x : X ⟶ Z} {y : Y ⟶ Z}
    (f : X ⟶ Y) (hf : f ≫ y = x) :
    baseChangeSnd b f hf ≫ pullback.fst b y = pullback.fst b x :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeSnd_snd {A Z X Y : C} (b : A ⟶ Z) {x : X ⟶ Z} {y : Y ⟶ Z}
    (f : X ⟶ Y) (hf : f ≫ y = x) :
    baseChangeSnd b f hf ≫ pullback.snd b y = pullback.snd b x ≫ f :=
  pullback.lift_snd _ _ _

/-- The base change along `b` of a morphism over a fixed base is a base change of it: the
square comparing the two second projections is cartesian. -/
theorem isPullback_baseChangeSnd {A Z X Y : C} (b : A ⟶ Z) {x : X ⟶ Z} {y : Y ⟶ Z}
    (f : X ⟶ Y) (hf : f ≫ y = x) :
    IsPullback (pullback.snd b x) (baseChangeSnd b f hf) f (pullback.snd b y) :=
  (IsPullback.of_right
    (by simpa only [baseChangeSnd_fst, hf] using IsPullback.of_hasPullback b x)
    (baseChangeSnd_snd b f hf) (IsPullback.of_hasPullback b y)).flip

/-- **Base change preserves cartesian squares over the base.** A cartesian square of objects
over `Z` stays cartesian after base change along `b : A ⟶ Z`. -/
theorem isPullback_baseChangeSnd_square {A Z W X V Y : C} (b : A ⟶ Z)
    {w : W ⟶ Z} {x : X ⟶ Z} {v : V ⟶ Z} {y : Y ⟶ Z}
    (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (g : V ⟶ Y)
    (hp : p ≫ x = w) (hq : q ≫ v = w) (hf : f ≫ y = x) (hg : g ≫ y = v)
    (h : IsPullback p q f g) :
    IsPullback (baseChangeSnd b p hp) (baseChangeSnd b q hq)
      (baseChangeSnd b f hf) (baseChangeSnd b g hg) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeSnd b g hg).flip
  · simpa only [baseChangeSnd_snd] using (isPullback_baseChangeSnd b p hp).flip.paste_vert h
  · apply pullback.hom_ext <;> simp [h.w]

end BaseChangeSnd

/-! ### A morphism between affine algebraic spaces -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space affine over an affine algebraic space is affine.** If `f : F ⟶ G` is
affine and `G` is an affine algebraic space, then so is `F`. -/
theorem isAffineSpace_source_of_isAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : IsAffineHom B S hS f) (hG : IsAffineSpace B S hS G) :
    IsAffineSpace B S hS F := by
  obtain ⟨V, hV, ⟨eG⟩⟩ := hG
  obtain ⟨U, p, q, h⟩ := hf ⟨V, hV⟩ eG.inv
  have _ : IsIso p := h.isIso_fst_of_isIso
  exact ⟨U.1, U.2, ⟨(asIso p).symm⟩⟩

namespace MorphismDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : MorphismDescentSituation B S hS hZ I)

/-! ### The stages of a base change of a fixed space over the distinguished stage -/

section BaseChangeSituation

variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : T ⟶ D.base.obj (op D.initial))

/-- The inverse system `B_i ×_{B₀} T` of base changes of a fixed space `T` over the
distinguished stage, indexed by the stages at or beyond that one. -/
noncomputable def stagesBaseChangeSystem : (D.Stages)ᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) t

/-- If the inverse system of bases is small for the site, so is the system `B_i ×_{B₀} T`. -/
theorem isSiteSmall_stagesBaseChangeSystem (hb : IsSiteSmall B S hS D.base) :
    IsSiteSmall B S hS (stagesBaseChangeSystem D t) :=
  isSiteSmall_baseChangeOverSystem B S hS (stagesBase D) (stagesBaseToInitial D) t
    (D.isSiteSmall_stagesBase hb)

/-- The cone over the system `B_i ×_{B₀} T` with vertex the base change `B ×_{B₀} T` of `T` to
the limit. -/
noncomputable def stagesBaseChangeCone : Cone (stagesBaseChangeSystem D t) :=
  baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D) t
    (stagesBaseCone D) (limit.π D.base (op D.initial)) (stagesBaseCone_π_comp D)

/-- **The base changes `B_i ×_{B₀} T`, as a descent situation.** For a quasi-compact
quasi-separated algebraic space `T` over the distinguished stage, the base changes of `T` to
the stages at or beyond that one form a directed inverse system of quasi-compact
quasi-separated algebraic spaces with affine transition morphisms, whose limit is the base
change `B ×_{B₀} T` of `T` to the limit. -/
noncomputable def stagesBaseChangeDescentSituation
    (hT : IsAlgebraicSpace B S hS T) (hTqc : IsQuasiCompactSpace B S hS T)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T) :
    DescentSituation B S hS hZ D.Stages where
  system := stagesBaseChangeSystem D t
  algebraicSpace j := isAlgebraicSpace_pullback B S hS _ _
    (D.base_isAlgebraicSpace j.1) hT (D.base_isAlgebraicSpace D.initial)
  transition_affine {j k} φ := isAffineHom_of_isPullback
    (isPullback_baseChangeOverMap B S hS ((stagesBaseToInitial D).app j)
      ((stagesBaseToInitial D).app k) ((stagesBase D).map φ) (by simp) t).flip
    (D.transition_affine _)
  quasiCompact j := isQuasiCompactSpace_pullback B S hS hZ _ t
    (D.base_isAlgebraicSpace j.1) (D.base_isAlgebraicSpace D.initial)
    (D.isQuasiCompactSpace_base j) hTqc D.base₀_quasiSeparated
  quasiSeparated j := isAbsolutelyQuasiSeparated_pullback B S hS hZ _ t
    (D.base_isAlgebraicSpace j.1) hT (D.base_isAlgebraicSpace D.initial)
    (D.isAbsolutelyQuasiSeparated_base j) hTqs
  limitCone := stagesBaseChangeCone D t
  isLimit := isLimit_baseChangeOverCone B S hS (stagesBase D) (stagesBaseToInitial D) t
    (stagesBaseCone D) (limit.π D.base (op D.initial)) (stagesBaseCone_π_comp D)
    (isLimitStagesBaseCone D)
  limitAlgebraicSpace := isAlgebraicSpace_pullback B S hS _ _
    D.limit_isAlgebraicSpace hT (D.base_isAlgebraicSpace D.initial)
  base := ⟨D.initial, le_refl _⟩

@[simp]
theorem stagesBaseChangeDescentSituation_system_obj
    (hT : IsAlgebraicSpace B S hS T) (hTqc : IsQuasiCompactSpace B S hS T)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T) (j : D.Stages) :
    (D.stagesBaseChangeDescentSituation t hT hTqc hTqs).system.obj (op j) =
      pullback (D.baseAtToInitial j.1 j.2) t := rfl

@[simp]
theorem stagesBaseChangeDescentSituation_limitCone_pt
    (hT : IsAlgebraicSpace B S hS T) (hTqc : IsQuasiCompactSpace B S hS T)
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ T) :
    (D.stagesBaseChangeDescentSituation t hT hTqc hTqs).limitCone.pt =
      pullback (limit.π D.base (op D.initial)) t := rfl

end BaseChangeSituation

/-! ### The chart `T = X₀ ×_{Y₀} V₀` and its base changes -/

section Chart

variable {V₀ : BigFppfOver B S hS} (v : yoneda.obj V₀ ⟶ D.target₀)

/-- The space `T = X₀ ×_{Y₀} V₀` cut out of the source by an étale chart of the target. -/
noncomputable abbrev chartSource : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := pullback D.map₀ v

/-- The projection `X₀ ×_{Y₀} V₀ ⟶ V₀` is a morphism over the distinguished stage `B₀`. -/
theorem chart_snd_comp :
    pullback.snd D.map₀ v ≫ (v ≫ D.targetToBase) =
      pullback.fst D.map₀ v ≫ D.sourceToBase := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, D.map₀_over]

/-- The square `X₀ ×_{Y₀} V₀` defining the chart of the source, base changed along any
`b : A ⟶ B₀`, is cartesian. -/
theorem isPullback_chartSquare {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (b : A ⟶ D.base.obj (op D.initial)) :
    IsPullback (baseChangeSnd b (pullback.fst D.map₀ v) rfl)
      (baseChangeSnd b (pullback.snd D.map₀ v) (D.chart_snd_comp v))
      (baseChangeSnd b D.map₀ D.map₀_over) (baseChangeSnd b v rfl) :=
  isPullback_baseChangeSnd_square b _ _ _ _ rfl (D.chart_snd_comp v) D.map₀_over rfl
    (IsPullback.of_hasPullback D.map₀ v)

/-- The base change `f` of `f₀` to the limit is the base change of `f₀` along the projection
`B ⟶ B₀`. -/
theorem mapLimit_eq_baseChangeSnd :
    D.mapLimit = baseChangeSnd (limit.π D.base (op D.initial)) D.map₀ D.map₀_over := rfl

/-- The base change `f_i` of `f₀` to a stage is the base change of `f₀` along the transition
morphism `B_i ⟶ B₀`. -/
theorem mapAt_eq_baseChangeSnd (i : I) (hi : D.initial ≤ i) :
    D.mapAt i hi = baseChangeSnd (D.baseAtToInitial i hi) D.map₀ D.map₀_over := rfl

/-- **The chart `V = V₀ ×_{Y₀} Y` of the target over the limit is affine.** If the inverse
system of bases is small for the site and `V₀` is affine, then the base change `B ×_{B₀} V₀` is
an affine algebraic space. -/
theorem isAffineSpace_limitChartTarget (hb : IsSiteSmall B S hS D.base)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)) :
    IsAffineSpace B S hS (pullback (limit.π D.base (op D.initial)) ((v ≫ D.targetToBase))) := by
  obtain ⟨W, p, q, hpb⟩ :=
    D.isAffineHom_limit_π_initial hb ⟨V₀, hV₀⟩ (v ≫ D.targetToBase)
  exact ⟨W.obj, W.property, ⟨hpb.isoPullback.symm⟩⟩

/-- **The limit `V ×_Y X` of the system of charts is affine when `f` is.** If the inverse system
of bases is small for the site, `V₀` is affine and `f` is affine, then
`B ×_{B₀} (X₀ ×_{Y₀} V₀)` is an affine algebraic space. -/
theorem isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit (hb : IsSiteSmall B S hS D.base)
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (hf : IsAffineHom B S hS D.mapLimit) :
    IsAffineSpace B S hS
      (pullback (limit.π D.base (op D.initial)) (pullback.fst D.map₀ v ≫ D.sourceToBase)) :=
  isAffineSpace_source_of_isAffineHom
    (isAffineHom_of_isPullback
      (D.isPullback_chartSquare v (limit.π D.base (op D.initial))) hf)
    (D.isAffineSpace_limitChartTarget v hb hV₀)

/-- If `v : V₀ ⟶ Y₀` is surjective and étale with `V₀` affine, and the base change
`B_i ×_{B₀} (X₀ ×_{Y₀} V₀)` is an affine algebraic space, then `f_i` is affine. -/
theorem isAffineHom_mapAt_of_isAffineSpace_baseChange
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (hvSurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf v)
    (hvEtale : IsEtale B S hS v) (i : I) (hi : D.initial ≤ i)
    (haff : IsAffineSpace B S hS
      (pullback (D.baseAtToInitial i hi) (pullback.fst D.map₀ v ≫ D.sourceToBase))) :
    IsAffineHom B S hS (D.mapAt i hi) := by
  set a := D.baseAtToInitial i hi
  obtain ⟨W, p, q, hpb⟩ := D.transition_affine (homOfLE hi).op ⟨V₀, hV₀⟩ (v ≫ D.targetToBase)
  let eV : pullback a (v ≫ D.targetToBase) ≅ yoneda.obj W.obj := hpb.isoPullback.symm
  let g : yoneda.obj W.obj ⟶ pullback a D.targetToBase := eV.inv ≫ baseChangeSnd a v rfl
  let w : pullback a (pullback.fst D.map₀ v ≫ D.sourceToBase) ⟶ yoneda.obj W.obj :=
    baseChangeSnd a (pullback.snd D.map₀ v) (D.chart_snd_comp v) ≫ eV.hom
  have hsq : IsPullback (baseChangeSnd a (pullback.fst D.map₀ v) rfl) w
      (baseChangeSnd a D.map₀ D.map₀_over) g := by
    refine (D.isPullback_chartSquare v a).of_iso' (Iso.refl _) (Iso.refl _) eV.symm
      (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [g, w]
  have hsnd : IsAffineHom B S hS (pullback.snd (baseChangeSnd a D.map₀ D.map₀_over) g) := by
    simpa only [hsq.isoPullback_inv_snd] using isAffineHom_iso_comp hsq.isoPullback.inv
      (isAffineHom_of_isAffineSpace B S hS w haff (isAffineSpace_yoneda B S hS W.obj W.property))
  have hcover : IsPullback (pullback.snd a (v ≫ D.targetToBase))
      (baseChangeSnd a v rfl) v (pullback.snd a D.targetToBase) :=
    isPullback_baseChangeSnd a v rfl
  have hgSurj : IsSurjective B S hS g := by
    let P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    have _ : P.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange P
    exact (presheafSurjective_iff_isSurjective_yoneda B S hS _
      (D.targetAt_isAlgebraicSpace i hi) W.obj g).mp
      (MorphismProperty.RespectsIso.precomp P.presheaf eV.inv _
        (MorphismProperty.of_isPullback hcover hvSurj))
  have hsqEtale : IsPullback (yoneda.map q) g v (pullback.snd a D.targetToBase) := by
    refine hcover.of_iso' eV.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa using (show eV.inv ≫ pullback.snd a (v ≫ D.targetToBase) = yoneda.map q from
        hpb.isoPullback_hom_snd)
    all_goals simp [g]
  have htfae := (isAffineHom_tfae_of_isAlgebraicSpace B S hS (D.mapAt i hi)
    (D.sourceAt_isAlgebraicSpace i hi) (D.targetAt_isAlgebraicSpace i hi)).out 4 2
  exact htfae.mp ⟨W.obj, g, hgSurj, isEtale_of_isPullback_yoneda B S hS hsqEtale hvEtale, hsnd⟩

end Chart

/-! ### Descent of affineness, given an affine stage of an inverse system -/

/-- In the situation of `AlgebraicGeometry.Space.MorphismDescentSituation`, if the base change
`f` of `f₀` to the limit `B` is affine, then the base change `f_i` of `f₀` to some stage `B_i` is
affine. The hypothesis `hstage` asks that every directed inverse system of quasi-compact
quasi-separated algebraic spaces with affine transition morphisms and affine limit, small for
the site, has an affine stage. -/
theorem exists_isAffineHom_mapAt_of_descentAffineStage (hb : IsSiteSmall B S hS D.base)
    (hstage : ∀ {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
      (E : DescentSituation B S hS hZ J), IsSiteSmall B S hS E.system →
      IsAffineSpace B S hS E.limitCone.pt →
      ∃ j : J, E.base ≤ j ∧ IsAffineSpace B S hS (E.system.obj (op j)))
    (hf : IsAffineHom B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsAffineHom B S hS (D.mapAt i hi) := by
  obtain ⟨V₀, v, hV₀, hvSurj, hvEtale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS D.target₀
      D.target₀_isAlgebraicSpace).mp D.target₀_quasiCompact
  have hValg := isAlgebraicSpace_yoneda B S hS V₀
  have hTalg : IsAlgebraicSpace B S hS (D.chartSource v) :=
    isAlgebraicSpace_pullback B S hS D.map₀ v
      D.source₀_isAlgebraicSpace hValg D.target₀_isAlgebraicSpace
  have hTqc : IsQuasiCompactSpace B S hS (D.chartSource v) :=
    isQuasiCompactSpace_pullback B S hS hZ D.map₀ v
      D.source₀_isAlgebraicSpace D.target₀_isAlgebraicSpace D.source₀_quasiCompact
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V₀ hV₀) D.target₀_quasiSeparated
  have hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.chartSource v) :=
    isAbsolutelyQuasiSeparated_pullback B S hS hZ D.map₀ v
      D.source₀_isAlgebraicSpace hValg D.target₀_isAlgebraicSpace D.source₀_quasiSeparated
      (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ _
        (isAbsolutelySeparated_of_isAffineSpace B S hS hZ
          (isAffineSpace_yoneda B S hS V₀ hV₀)))
  obtain ⟨j, -, hj⟩ :=
    hstage (D.stagesBaseChangeDescentSituation (pullback.fst D.map₀ v ≫ D.sourceToBase)
        hTalg hTqc hTqs)
      (D.isSiteSmall_stagesBaseChangeSystem (pullback.fst D.map₀ v ≫ D.sourceToBase) hb)
      (D.isAffineSpace_limitBaseChange_of_isAffineHom_mapLimit v hb hV₀ hf)
  exact ⟨j.1, j.2, D.isAffineHom_mapAt_of_isAffineSpace_baseChange v hV₀ hvSurj hvEtale
    j.1 j.2 hj⟩

/-! ### Descent of affineness -/

/-- **Affineness of a morphism descends to a stage.** Let `B = lim B_i` be a directed inverse
system of algebraic spaces over `S` with affine transition morphisms, small for the site, let
`f₀ : X₀ ⟶ Y₀` be a morphism of quasi-compact quasi-separated algebraic spaces over a
distinguished stage `B₀`, and let `f_i : X_i ⟶ Y_i` and `f : X ⟶ Y` be its base changes to the
stages and to the limit. If `f` is affine, then `f_i` is affine for some `i ≥ 0`. -/
theorem exists_isAffineHom_mapAt_of_isAffineHom_mapLimit (hb : IsSiteSmall B S hS D.base)
    (hf : IsAffineHom B S hS D.mapLimit) :
    ∃ (i : I) (hi : D.initial ≤ i), IsAffineHom B S hS (D.mapAt i hi) :=
  D.exists_isAffineHom_mapAt_of_descentAffineStage hb
    (fun E hJ hE ↦ E.exists_isAffineSpace_system_obj_of_isSiteSmall hJ hE) hf

end MorphismDescentSituation

end AlgebraicGeometry.Space

end
