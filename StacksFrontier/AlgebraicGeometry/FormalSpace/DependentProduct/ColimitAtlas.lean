module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.AffineCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit

/-!
# Atlases of a directed colimit of algebraic spaces along thickenings

Let `S` be a scheme contained in a big fppf site `B`, let `Λ` be a directed preorder with a least
element `o`, and let `E : Λ ⥤ FppfSheaf` be a diagram whose transition morphisms are
monomorphisms and, after base change along every point out of an object of the site,
thickenings. For an étale chart `c : h_W ⟶ E o` of the least stage, the dependent product
`Û = Π_{ι_o} h_W` along the colimit injection `ι_o : E o ⟶ colim E` is the chart of the colimit
of the proof of Stacks 0AIU: it is representable étale over the colimit, its base change to the
stage `E n` is the dependent product of `c` along `E o ⟶ E n`, and it is the colimit of those
base changes.

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.isAffineThickeningOver_colimitι`: the colimit
  injection of the least stage is a thickening over every affine point.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isPullback_stageChart`: the base change of the
  chart of the colimit to a stage.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isAffineFormalAlgebraicSpace_colimitChart`:
  the chart of the colimit is an affine formal algebraic space as soon as its stages are
  represented by affine objects of the site.

## References

* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Postcomposing the right-hand and bottom sides of a cartesian square with a monomorphism
keeps it cartesian. -/
theorem isPullback_comp_mono {C : Type*} [Category* C] {P X Y W Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ W} {g : Y ⟶ W} (h : IsPullback fst snd f g) (m : W ⟶ Z) [Mono m] :
    IsPullback fst snd (f ≫ m) (g ≫ m) := by
  refine ⟨⟨by rw [← Category.assoc, h.w, Category.assoc]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ h.lift s.fst s.snd ((cancel_mono m).1 (by simpa using s.condition)))
    (fun s ↦ h.lift_fst _ _ _) (fun s ↦ h.lift_snd _ _ _) fun s n h₁ h₂ ↦ ?_⟩⟩
  exact h.hom_ext (h₁.trans (h.lift_fst _ _ _).symm) (h₂.trans (h.lift_snd _ _ _).symm)

/-- **A morphism of fppf sheaves whose base changes along points are thickenings is a
monomorphism**: two sections with the same image give two sections of a thickening, which is a
monomorphism. -/
theorem mono_of_relative_isThickening {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} f) : Mono f := by
  refine ⟨fun {Q} g h hgh ↦ GrothendieckTopology.hom_ext_uliftYoneda.{u + 1, u}
    (J := BigFppfOver.topology B S hS) fun T p ↦ ?_⟩
  obtain ⟨T₀, k, i₀, hpb⟩ := hf.1 (p ≫ g ≫ f)
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map k) :=
    (hf.2 _ i₀ k hpb).1
  have : Mono k := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  set l₁ := hpb.lift (p ≫ g) (𝟙 _) (by rw [Category.id_comp, Category.assoc])
  set l₂ := hpb.lift (p ≫ h) (𝟙 _) (by rw [Category.id_comp, Category.assoc, ← hgh])
  have hm : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.preimage l₁ =
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.preimage l₂ := by
    refine (cancel_mono k).1 ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_injective ?_)
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage,
      hpb.lift_snd, hpb.lift_snd]
  have hl : l₁ = l₂ := by
    rw [← (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_preimage l₁,
      ← (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_preimage l₂, hm]
  rw [← hpb.lift_fst (p ≫ g) (𝟙 _) (by rw [Category.id_comp, Category.assoc]),
    ← hpb.lift_fst (p ≫ h) (𝟙 _) (by rw [Category.id_comp, Category.assoc, ← hgh])]
  exact congrArg (· ≫ i₀) hl

/-! ### Base change of a morphism to a cocone, stage by stage -/

section Stages

variable {Λ' : Type (u + 1)} [Preorder Λ'] {D : Λ' ⥤ FppfSheaf B S hS} (cD : Cocone D)
  {Y : FppfSheaf B S hS} (b : Y ⟶ cD.pt)

/-- The base changes of a morphism `b : Y ⟶ cD.pt` to the stages of a cocone, as a diagram. -/
def stageDiagram : Λ' ⥤ FppfSheaf B S hS where
  obj n := pullback b (cD.ι.app n)
  map {n m} f := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ D.map f)
    (by rw [Category.assoc, cD.w, pullback.condition])
  map_id n := pullback.hom_ext (by rw [pullback.lift_fst, Category.id_comp])
    (by rw [pullback.lift_snd, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp])
  map_comp f g := pullback.hom_ext
    (by rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst])
    (by rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.lift_snd, CategoryTheory.Functor.map_comp, Category.assoc])

/-- The transition maps of `stageDiagram` commute with the first projections to `Y`. -/
theorem stageDiagram_map_fst {n m : Λ'} (f : n ⟶ m) :
    (stageDiagram cD b).map f ≫ pullback.fst b (cD.ι.app m) = pullback.fst b (cD.ι.app n) :=
  pullback.lift_fst _ _ _

/-- The transition maps of `stageDiagram` lie over the transition maps of `D` under the second
projections. -/
theorem stageDiagram_map_snd {n m : Λ'} (f : n ⟶ m) :
    (stageDiagram cD b).map f ≫ pullback.snd b (cD.ι.app m) =
      pullback.snd b (cD.ι.app n) ≫ D.map f :=
  pullback.lift_snd _ _ _

/-- The projection of the diagram of base changes to the diagram of stages. -/
def stageDiagramπ : stageDiagram cD b ⟶ D where
  app n := pullback.snd b (cD.ι.app n)
  naturality _ _ f := stageDiagram_map_snd cD b f

/-- The cocone of the base changes over `Y`. -/
def stageCocone : Cocone (stageDiagram cD b) where
  pt := Y
  ι := { app := fun n ↦ pullback.fst b (cD.ι.app n)
         naturality := fun _ _ f ↦ (stageDiagram_map_fst cD b f).trans
           (Category.comp_id _).symm }

/-- The diagram of base changes is equifibered over the diagram of stages. -/
theorem equifibered_stageDiagramπ : NatTrans.Equifibered (stageDiagramπ cD b) := by
  intro n m f
  refine IsPullback.of_right ?_ (stageDiagram_map_snd cD b f) (IsPullback.of_hasPullback b _)
  rw [stageDiagram_map_fst cD b f, cD.w]
  exact IsPullback.of_hasPullback b _

/-- **The base change of a filtered colimit of fppf sheaves is the colimit of the base
changes**, filtered colimits of fppf sheaves being universal. -/
theorem isColimit_stageCocone [IsDirected Λ' (· ≤ ·)] [Nonempty Λ']
    (hcD : IsUniversalColimit cD) : Nonempty (IsColimit (stageCocone cD b)) :=
  hcD (stageCocone cD b) (stageDiagramπ cD b) b
    (NatTrans.ext (funext fun n ↦ (pullback.condition (f := b) (g := cD.ι.app n)).symm))
    (equifibered_stageDiagramπ cD b) fun n ↦ IsPullback.of_hasPullback b (cD.ι.app n)

end Stages

variable {Λ : Type (u + 1)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] {o : Λ} (ho : ∀ n, o ≤ n)
  (E : Λ ⥤ FppfSheaf B S hS) (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
  (hthick : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), (MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} (E.map f))

include ho hmono hthick in
/-- **The colimit injection of the least stage is a thickening over every affine point.** An
affine point of the colimit factors through a stage, the stages being monomorphic and an affine
scheme being a quasi-compact object of the site, and over that stage the injection of the least
stage is a thickening by hypothesis. -/
theorem isAffineThickeningOver_colimitι :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsAffineThickeningOver (colimit.ι E o) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Nonempty Λ := ⟨o⟩
  intro T hT t
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hT
  obtain ⟨n, t', ht⟩ := exists_factor_through_stage_of_compact B S hS E hmono T t
  obtain ⟨T₀, k, i₀, hpb⟩ := (hthick (homOfLE (ho n))).1 t'
  have : Mono (colimit.ι E n) := (colimit.isColimit E).mono_ι_app_of_isFiltered n
  refine ⟨T₀, k, i₀, ?_, (hthick (homOfLE (ho n))).2 t' i₀ k hpb⟩
  have h := isPullback_comp_mono hpb.flip (colimit.ι E n)
  rwa [colimit.w, ← ht] at h

/-! ### The chart of the colimit -/

section Chart

variable {W : BigFppfOver B S hS} (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶
  E.obj o)

include ho hmono in
/-- The square exhibiting the colimit injection of the least stage as a base change of itself
along a later colimit injection. -/
theorem isSectionwisePullback_colimitι (n : Λ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsSectionwisePullback B S hS (E.map (homOfLE (ho n))) (𝟙 (E.obj o)) (colimit.ι E n)
      (colimit.ι E o) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Nonempty Λ := ⟨o⟩
  have : Mono (colimit.ι E n) := (colimit.isColimit E).mono_ι_app_of_isFiltered n
  refine isSectionwisePullback_of_isPullback B S hS ?_
  have h := isPullback_comp_mono (IsPullback.of_id_snd (f := E.map (homOfLE (ho n))))
    (colimit.ι E n)
  rwa [Category.id_comp, colimit.w] at h

include ho hmono in
/-- **The base change of the chart of the colimit to a stage is the dependent product of the
chart along the transition from the least stage.** -/
theorem isPullback_stageChart (n : Λ) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsPullback (liftAlongBaseChange (𝟙 _) (isSectionwisePullback_colimitι ho E hmono n)
        (by rw [Category.id_comp, Category.comp_id]))
      (liftAlongBase B S hS (E.map (homOfLE (ho n))) c)
      (liftAlongBase B S hS (colimit.ι E o) c) (colimit.ι E n) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine isPullback_liftAlongBaseChange (𝟙 _) (isSectionwisePullback_colimitι ho E hmono n)
    (isSectionwisePullback_of_isPullback B S hS (IsPullback.of_id_snd (f := c))) ?_ _
  rw [Category.id_comp, colimit.w]

include ho hmono hthick in
/-- **The chart of the colimit is representable by algebraic spaces and étale.** -/
theorem isRepresentableEtale_colimitChart
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsRepresentableEtale B S hS (liftAlongBase B S hS (colimit.ι E o) c) :=
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  isRepresentableEtale_liftAlongBase (colimit.ι E o) c
    (isAffineThickeningOver_colimitι ho E hmono hthick) (chartBound_monotone W)
    (fun _ hκ ↦ chartBound_lt W hκ) (isEtaleChartBounded_of_relative c hc)

include ho hmono hthick in
/-- **The chart of the colimit is an affine formal algebraic space** as soon as it satisfies
the set-theoretic condition and each of its stages, the dependent product of the chart along a
transition out of the least stage, is represented by an affine object of the site: it is the
colimit of those stages along thickenings (Stacks 0GVM). -/
theorem isAffineFormalAlgebraicSpace_colimitChart
    (hset : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      SatisfiesSetTheoreticCondition B S hS (liftAlong B S hS (colimit.ι E o) c))
    (hstage : ∀ n : Λ, ∃ A : BigFppfOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Nonempty ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A ≅
        liftAlong B S hS (E.map (homOfLE (ho n))) c)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsAffineFormalAlgebraicSpace B S hS (liftAlong B S hS (colimit.ι E o) c) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : Nonempty Λ := ⟨o⟩
  set J := BigFppfOver.topology B S hS
  set b := liftAlongBase B S hS (colimit.ι E o) c
  obtain ⟨hcol⟩ :=
    isColimit_stageCocone (colimit.cocone E) b (sheaf_filteredColimit_isUniversalColimit J E)
  set D' := stageDiagram (colimit.cocone E) b
  refine isAffineFormalAlgebraicSpace_colimit B S hS D' (fun n ↦ ?_) (fun n m f ↦ ?_)
    (liftAlong B S hS (colimit.ι E o) c)
    (hcol.coconePointUniqueUpToIso (colimit.isColimit D')) hset
  · obtain ⟨A, hA, ⟨eA⟩⟩ := hstage n
    have e₁ : D'.obj n ≅ (Sheaf.sheafifiedYoneda J).obj A :=
      (isPullback_stageChart ho E hmono c n).isoPullback.symm ≪≫ eA.symm ≪≫
        (Sheaf.uliftYonedaIsoSheafifiedYoneda J).app A
    exact isAffineFormalAlgebraicSpace_of_iso B S hS e₁.symm
      (isAffineFormalAlgebraicSpace_sheafifiedYoneda B S hS A hA)
  · exact relative_of_natIso (Sheaf.uliftYonedaIsoSheafifiedYoneda J) _ _
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (equifibered_stageDiagramπ (colimit.cocone E) b f).flip (hthick f))

end Chart

/-! ### Joint surjectivity of the charts of the colimit -/

section Cover

variable {K : Type*} {W : K → BigFppfOver B S hS}
  (c : ∀ k, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (W k) ⟶ E.obj o)
  (hcE : ∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (c k).hom)
  (hcov : ∀ (T : BigFppfOver B S hS)
    (x : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ E.obj o)
    (t : (BigFppfOver.toScheme B S hS).obj T),
    ∃ (k : K) (L₀ : BigFppfOver B S hS) (q₀ : L₀ ⟶ T)
      (r₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L₀ ⟶
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (W k)),
      IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q₀) r₀ x (c k) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map q₀))

include ho hmono hthick hcE hcov in
/-- **Over an affine point of the colimit, the charts of the colimit cover every point.** -/
theorem exists_isPullback_colimitChart_of_mem {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶
      (letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize; colimit E))
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (k : K) (L : BigFppfOver B S hS) (q : L ⟶ T)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L ⟶
        liftAlong B S hS (colimit.ι E o) (c k)),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q)
        (liftAlongBase B S hS (colimit.ι E o) (c k)) t ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map q) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨T₀, k₀, i₀, hpb, hk⟩ := isAffineThickeningOver_colimitι ho E hmono hthick T hT t
  obtain ⟨x₀, hx₀⟩ := hk.2 x
  obtain ⟨k, L₀, q₀, r₀, hpb', ⟨y, hy⟩⟩ := hcov T₀ i₀ x₀
  have hpre : IsPullback r₀.hom (uliftYoneda.{u + 1}.map q₀) (c k).hom i₀.hom :=
    (hpb'.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))).flip
  have hq₀ : Etale ((BigFppfOver.toScheme B S hS).map q₀) := (hcE k).2 i₀.hom r₀.hom q₀ hpre
  obtain ⟨L, q, c₀, r, hr, -, hsq⟩ :=
    exists_isPullback_liftAlongBase_of_isThickening (colimit.ι E o) (c k) t k₀ i₀ hpb hk q₀ r₀
      hpb' hq₀
  have hq : (BigFppfOver.toScheme B S hS).map q ((BigFppfOver.toScheme B S hS).map c₀ y) =
      (BigFppfOver.toScheme B S hS).map k₀ x₀ := by
    rw [← Scheme.Hom.comp_apply, ← (BigFppfOver.toScheme B S hS).map_comp, hsq.w,
      (BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_apply, hy]
  exact ⟨k, L, q, r, hr, (BigFppfOver.toScheme B S hS).map c₀ y, hq.trans hx₀⟩

include ho hmono hthick hcE hcov in
/-- **The charts of the colimit are jointly surjective on points.** -/
theorem exists_pointsMapULift_colimitChart_eq
    (p : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Space.pointsULift.{u + 1} B S hS (colimit E).obj) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (k : K) (z : Space.pointsULift.{u + 1} B S hS
        (liftAlong B S hS (colimit.ι E o) (c k)).obj),
      Space.pointsMapULift B S hS _ (liftAlongBase B S hS (colimit.ι E o) (c k)).hom z = p := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  induction p using Quot.ind with | _ pt =>
  let A : BigFppfOver B S hS := pt.siteObject B S hS (colimit E).obj
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of pt.carrier)))
  let ξ : uliftYoneda.{u + 1}.obj A ⟶ (colimit E).obj := uliftYonedaEquiv.{u + 1}.symm pt.value
  obtain ⟨k, L, q, r, hr, ⟨w, -⟩⟩ := exists_isPullback_colimitChart_of_mem ho E hmono hthick c
    hcE hcov hA ⟨ξ⟩ (IsLocalRing.closedPoint pt.carrier : (BigFppfOver.toScheme B S hS).obj A)
  let pW : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj L) :=
    (Space.pointsEquivSchemeULift.{u + 1} B S hS L).symm w
  let q₀ : Space.FieldValuedPointULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj A) :=
    ⟨pt.carrier, pt.contained, pt.toBase, ULift.up (𝟙 A)⟩
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj A) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of pt.carrier)))
  have hAp : Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map q) pW
      = q₀.class B S hS _ :=
    (Space.pointsEquivSchemeULift.{u + 1} B S hS A).injective (Subsingleton.elim _ _)
  have hξpt : Space.pointsMapULift B S hS (uliftYoneda.{u + 1}.obj A) ξ (q₀.class B S hS _)
      = pt.class B S hS (colimit E).obj := by
    refine Quot.sound ⟨pt, ⟨𝟙 _, ?_⟩, ⟨𝟙 _, by simp⟩⟩
    change (colimit E).obj.map (𝟙 A).op (ξ.app (Opposite.op A) (ULift.up (𝟙 A))) = pt.value
    simp [ξ]
  have hw : r.hom ≫ (liftAlongBase B S hS (colimit.ι E o) (c k)).hom =
      uliftYoneda.{u + 1}.map q ≫ ξ :=
    congrArg (fun m ↦ m.hom) hr.w
  refine ⟨k, Space.pointsMapULift B S hS _ r.hom pW, ?_⟩
  change _ = pt.class B S hS (colimit E).obj
  have hc : ∀ {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (α : F ⟶ G) (β : G ⟶ H) z,
      Space.pointsMapULift.{u + 1} B S hS F (α ≫ β) z =
        Space.pointsMapULift B S hS G β (Space.pointsMapULift B S hS F α z) :=
    fun α β z ↦ congrFun (Space.pointsMapULift_comp.{u + 1} B S hS _ α β) z
  refine (hc _ _ pW).symm.trans ((congrArg (fun m ↦ Space.pointsMapULift B S hS _ m pW) hw).trans
    ((hc _ _ pW).trans ?_))
  rw [hAp, hξpt]

end Cover

/-! ### The colimit is a formal algebraic space -/

include ho hmono hthick in
/-- **A directed colimit of algebraic spaces along thickenings, with a least stage, is a formal
algebraic space** as soon as it satisfies the set-theoretic condition and the dependent product
of every affine étale chart of the least stage along every transition out of it is represented
by an affine object of the site.

This is the proof of Stacks 0AIU: the affine étale charts of the least stage are transported to
the colimit by the dependent product along the colimit injection, which is representable étale
over the colimit, is the colimit of its stages, and these charts are jointly surjective. The
affineness of the stages, which the source draws from Stacks 07VT, is the hypothesis `hstage`. -/
theorem isFormalAlgebraicSpace_colimit_of_affineStages
    (halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj o).obj)
    (hset : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      SatisfiesSetTheoreticCondition B S hS (colimit E))
    (hstage : ∀ {W : BigFppfOver B S hS}
      (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ E.obj o),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} c.hom →
      ∀ n : Λ, ∃ A : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Nonempty ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A ≅
          liftAlong B S hS (E.map (homOfLE (ho n))) c)) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    IsFormalAlgebraicSpace B S hS (colimit E) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨ι, W, c, hWaff, hcE, hcov⟩ := exists_affine_etale_charts halg
  let W' : ULift.{u + 1} ι → BigFppfOver B S hS := fun k ↦ W k.down
  let c' : ∀ k, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (W' k) ⟶ E.obj o :=
    fun k ↦ c k.down
  have hrep : ∀ k, IsRepresentableEtale B S hS (liftAlongBase B S hS (colimit.ι E o) (c' k)) :=
    fun k ↦ isRepresentableEtale_colimitChart ho E hmono hthick (c' k) (hcE k.down)
  have haff : ∀ k, IsAffineFormalAlgebraicSpace B S hS (liftAlong B S hS (colimit.ι E o) (c' k)) :=
    fun k ↦ isAffineFormalAlgebraicSpace_colimitChart ho E hmono hthick (c' k)
      (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS _
        (hrep k).1 hset)
      (hstage (c' k) (hWaff k.down) (hcE k.down))
  refine ⟨hset, ULift.{u + 1} ι, fun k ↦ liftAlong B S hS (colimit.ι E o) (c' k),
    fun k ↦ liftAlongBase B S hS (colimit.ι E o) (c' k), haff, hrep, ?_⟩
  refine isLocallySurjective_sigmaDesc_of_jointly_surjective_points B S hS _ haff hrep
    fun p ↦ ?_
  exact exists_pointsMapULift_colimitChart_eq ho E hmono hthick c' (fun k ↦ hcE k.down)
    (fun T x t ↦ by
      obtain ⟨k, L₀, q₀, r₀, h₁, h₂⟩ := hcov T x t
      exact ⟨ULift.up k, L₀, q₀, r₀, h₁, h₂⟩) p

end AlgebraicGeometry.FormalSpace.DependentProduct

end
