module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubfunctorSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings

/-!
# Sections of an algebraic space with image in a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a presheaf on the big fppf site
of `S` and let `T` be a set of points of `X`. This file describes the subfunctor of `X` of the
sections with point-set image in `T`: on a chart `U ⟶ X` a closed `T` pulls back to the points
supported in a closed subset of `U`, the subfunctor agrees with the corresponding subfunctor of
the universe lift of `X`, and for an algebraic space `X` it is an fppf sheaf, so that its
sheafification, the completion `X_{/T}`, does not change it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isClosed_supportedPoints_eq`: the inverse image of a
  closed set of points on a chart is the set of points supported in a closed subset of the
  chart.
* `AlgebraicGeometry.FormalSpace.completionSubfunctor_eq_completionSubfunctorULift`: the
  completion subfunctor of a presheaf of `Type u` is the completion subfunctor of its universe
  lift.
* `AlgebraicGeometry.FormalSpace.isIso_toSheafify_completionSubfunctor`: for an algebraic space
  `X`, the functor of morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` is an fppf sheaf.
* `AlgebraicGeometry.FormalSpace.isIso_toSheafify_completionSubfunctor_affineOver`: the same for
  an affine scheme `X = Spec A` of the site and a subset `T ⊆ |X|`.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u v

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse image of a closed subset on a chart -/

/-- **The inverse image of `T` on a chart is the set of points supported in a closed subset of
the chart.** For a closed set `T` of points of `X` and a morphism `a : U ⟶ X` from a represented
sheaf, the inverse image of `T` is the set of points supported in a closed subset of the scheme
underlying `U`. -/
theorem exists_isClosed_supportedPoints_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    ∃ Ti : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed Ti ∧
      Space.pointsMap B S hS _ a ⁻¹' T = supportedPoints B S hS U Ti := by
  let _ : TopologicalSpace (Space.points B S hS X) := Space.pointTopology B S hS X
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  refine ⟨Space.pointsToScheme B S hS U '' (Space.pointsMap B S hS _ a ⁻¹' T),
    (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS U _).mp
      (hT.preimage (Space.continuous_pointsMap B S hS a)), ?_⟩
  ext x
  exact ((Space.injective_pointsToScheme B S hS U).mem_set_image).symm

/-! ### The set-theoretic condition -/

private theorem relative_map_postcompose
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E]
    (F : C ⥤ D) (H : D ⥤ E) [F.Full] [F.Faithful] [H.Full] [H.Faithful]
    [PreservesLimitsOfShape WalkingCospan H]
    (P : MorphismProperty C) [P.RespectsIso]
    {X Y : D} (f : X ⟶ Y) (hf : P.relative F f) :
    P.relative (F ⋙ H) (H.map f) := by
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨g, rfl⟩ := H.map_surjective g
  exact ⟨hf.rep.pullback g, H.map (hf.rep.fst g), hf.rep.snd g,
    (hf.rep.isPullback g).map H, hf.property_snd g⟩

private theorem relativelyRepresentable_of_comp_mono
    {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D)
    {X Y Z : D} (f : X ⟶ Y) (m : Y ⟶ Z) [Mono m]
    (h : F.relativelyRepresentable (f ≫ m)) : F.relativelyRepresentable f := by
  intro A g
  obtain ⟨R, b, a, hp⟩ := h (g ≫ m)
  refine ⟨R, b, a, IsPullback.mk' ?_ ?_ ?_⟩
  · apply (cancel_mono m).mp
    simpa only [Category.assoc] using hp.w
  · exact fun _ _ _ ↦ hp.hom_ext
  · intro V a' b' hw
    refine ⟨hp.lift a' b' ?_, hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    simpa only [Category.assoc] using congrArg (fun k => k ≫ m) hw

private theorem subfunctor_isPullback {C : Type u} [Category C]
    {F G : C ⥤ Type v} (P : Subfunctor F) (Q : Subfunctor G)
    (f : G ⟶ F) (g : Q.toFunctor ⟶ P.toFunctor)
    (hw : g ≫ P.ι = Q.ι ≫ f)
    (hmem : ∀ U x, x ∈ Q.obj U ↔ f.app U x ∈ P.obj U) :
    IsPullback g Q.ι P.ι f := by
  apply IsPullback.mk' hw
  · exact fun _ _ _ _ ↦ (cancel_mono Q.ι).mp
  · intro Z a b h
    have hb : Subfunctor.range b ≤ Q := by
      rintro U _ ⟨z, rfl⟩
      apply (hmem U _).mpr
      have hz := congrArg (fun k => k z) (NatTrans.congr_app h U)
      change (a.app U z).val = f.app U (b.app U z) at hz
      rw [← hz]
      exact (a.app U z).property
    refine ⟨Subfunctor.lift b hb, ?_, Subfunctor.lift_ι _ _⟩
    apply (cancel_mono P.ι).mp
    rw [Category.assoc, hw, ← Category.assoc, Subfunctor.lift_ι, ← h]

private theorem mk_idealSheafData_le (Y : Scheme.{u}) :
    Cardinal.mk Y.IdealSheafData ≤ 2 ^ Y.size := by
  let A := Σ U : Y.affineOpens, Γ(Y, U.1)
  let f : Y.IdealSheafData → Set A := fun I => {s | s.2 ∈ I.ideal s.1}
  have hf : Function.Injective f := fun I J h =>
    Scheme.IdealSheafData.ext (funext fun U => SetLike.ext fun s => Set.ext_iff.mp h ⟨U, s⟩)
  have hA : Cardinal.mk A ≤ Y.size := by
    calc Cardinal.mk A
        = Cardinal.sum (fun U : Y.affineOpens => Cardinal.mk Γ(Y, U.1)) :=
          Cardinal.mk_sigma _
      _ ≤ Cardinal.sum (fun _ : Y.affineOpens => Y.size) :=
        Cardinal.sum_le_sum _ _ (Y.mk_sections_le_size)
      _ = Cardinal.mk Y.affineOpens * Y.size := Cardinal.sum_const' _ _
      _ ≤ Y.size * Y.size := mul_le_mul' Y.mk_affineOpens_le_size le_rfl
      _ = Y.size := Cardinal.mul_eq_self Y.aleph0_le_size
  exact (Cardinal.mk_le_of_injective hf).trans
    ((Cardinal.mk_set (α := A)).trans_le (Cardinal.power_le_power_left (by simp) hA))

private theorem exists_bounded_closedSubscheme_cover (Y : Scheme.{u}) (hY : B.Contains Y)
    (T : Set Y) (hT : IsClosed T) :
    ∃ (W : Scheme.{u}) (f : W ⟶ Y), B.Contains W ∧ Set.range f ⊆ T ∧
      ∀ (Z : Scheme.{u}) (g : Z ⟶ Y) [QuasiCompact g], Set.range g ⊆ T →
        ∃ a : Z ⟶ W, a ≫ f = g := by
  let I := {J : Y.IdealSheafData // (J.support : Set Y) ⊆ T}
  let D : I → Scheme.{u} := fun J => J.1.subscheme
  let f : (∐ D) ⟶ Y := Sigma.desc (fun J => J.1.subschemeι)
  have hD : B.Contains (∐ D) :=
    (schemeSize_coproduct_le D (2 ^ Y.size) (Y.aleph0_le_size.trans (Cardinal.cantor _).le)
      ((Cardinal.mk_subtype_le _).trans (mk_idealSheafData_le Y)) fun J ↦
        (Scheme.size_le_of_mono_quasiCompact J.1.subschemeι).trans
          (Cardinal.cantor _).le).trans_lt (B.cutoff_isStrongPrelimit hY)
  refine ⟨∐ D, f, hD, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    obtain ⟨⟨J, z⟩, rfl⟩ := (sigmaMk D).surjective w
    rw [sigmaMk_mk]
    change (Sigma.ι D J ≫ f) z ∈ T
    rw [Sigma.ι_desc]
    exact J.2 (J.1.range_subschemeι ▸ Set.mem_range_self z)
  · intro Z g hg hgT
    have hker : (g.ker.support : Set Y) ⊆ T := by
      rw [Scheme.Hom.support_ker]
      exact closure_minimal hgT hT
    refine ⟨g.toImage ≫ Sigma.ι D ⟨g.ker, hker⟩, ?_⟩
    rw [Category.assoc, Sigma.ι_desc]
    exact g.toImage_imageι

/-- The field-valued points of a chart landing in a closed set `T` of points are those whose
underlying scheme point lies in a closed subset of the chart. -/
private theorem exists_isClosed_schemePoint_mem_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T) :
    ∃ T' : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed T' ∧
      ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U),
        (Space.FieldValuedPoint.map B S hS (yoneda.obj U) a p).class B S hS X ∈ T ↔
          Space.schemePoint B S hS U p ∈ T' := by
  obtain ⟨T', hT', hpts⟩ := exists_isClosed_supportedPoints_eq B S hS U a T hT
  refine ⟨T', hT', fun p ↦ ?_⟩
  simpa only [Set.mem_preimage, Space.pointsMap_class, supportedPoints, Set.mem_ofPred_eq,
    show Space.pointsToScheme B S hS U (p.class B S hS (yoneda.obj U)) =
      Space.schemePoint B S hS U p from rfl]
    using Set.ext_iff.mp hpts (p.class B S hS (yoneda.obj U))

/-- An affine section whose scheme-theoretic image lies in the pulled-back closed set defines a
section of the global completion subfunctor. -/
private theorem affineSection_mem_completionSubfunctor
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (A : BigFppfOver B S hS) (T' : Set ((BigFppfOver.toScheme B S hS).obj A))
    (f : yoneda.obj A ⟶ X)
    (hT : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj A),
      (Space.FieldValuedPoint.map B S hS (yoneda.obj A) f p).class B S hS X ∈ T ↔
        Space.schemePoint B S hS A p ∈ T')
    (U : BigFppfOver B S hS) (s : ((uliftYoneda.{u + 1}).obj A).obj (op U))
    (hs : Set.range ((BigFppfOver.toScheme B S hS).map s.down).base ⊆ T') :
    Space.HasImageIn B S hS X T U (f.app (op U) s.down) := by
  intro p
  let g : U ⟶ A := s.down
  let q := Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g) p
  have hqT : Space.schemePoint B S hS A q ∈ T' := hs ⟨Space.schemePoint B S hS U p, rfl⟩
  have hsection : (yoneda.map g ≫ f).app (op U) (𝟙 U) = f.app (op U) s.down := by
    simp [g]
  change (⟨p.carrier, p.contained, p.toBase, X.map p.value.op (f.app (op U) s.down)⟩ :
    Space.FieldValuedPoint B S hS X).class B S hS X ∈ T
  rw [← hsection]
  have hraw : (⟨p.carrier, p.contained, p.toBase,
      X.map p.value.op ((yoneda.map g ≫ f).app (op U) (𝟙 U))⟩ :
        Space.FieldValuedPoint B S hS X) =
      Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map g ≫ f) p := by
    cases p with
    | mk carrier contained toBase value =>
      apply congrArg (fun z ↦
        Space.FieldValuedPoint.mk carrier contained toBase z)
      simpa [Space.FieldValuedPoint.siteObject] using
        (congrArg (fun k ↦ k (𝟙 U)) ((yoneda.map g ≫ f).naturality value.op)).symm
  rw [hraw, Space.FieldValuedPoint.map_comp B S hS (yoneda.obj U) (yoneda.map g) f p]
  exact (hT q).mpr hqT

private theorem affineSection_mem_completionSubfunctor_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (A : BigFppfOver B S hS) (T' : Set ((BigFppfOver.toScheme B S hS).obj A))
    (f : yoneda.obj A ⟶ X)
    (hT : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj A),
      (Space.FieldValuedPoint.map B S hS (yoneda.obj A) f p).class B S hS X ∈ T ↔
        Space.schemePoint B S hS A p ∈ T')
    (U : BigFppfOver B S hS) (s : ((uliftYoneda.{u + 1}).obj A).obj (op U)) :
    Space.HasImageIn B S hS X T U (f.app (op U) s.down) ↔
      Set.range ((BigFppfOver.toScheme B S hS).map s.down).base ⊆ T' := by
  refine ⟨?_, affineSection_mem_completionSubfunctor B S hS T A T' f hT U s⟩
  rintro hs _ ⟨x, rfl⟩
  let p := Space.schemePointRepresentative B S hS U x
  let q := Space.FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map s.down) p
  have hnat := congrArg (fun k ↦ k s.down) (f.naturality p.value.op)
  have hq : (Space.FieldValuedPoint.map B S hS (yoneda.obj A) f q).class B S hS X ∈ T := by
    change (⟨p.carrier, p.contained, p.toBase, f.app _ (p.value ≫ s.down)⟩ :
      Space.FieldValuedPoint B S hS X).class B S hS X ∈ T
    change f.app _ (p.value ≫ s.down) = X.map p.value.op (f.app _ s.down) at hnat
    rw [hnat]
    exact hs p
  have hq' := (hT q).mp hq
  change (BigFppfOver.toScheme B S hS).map s.down
    (Space.schemePoint B S hS U p) ∈ T' at hq'
  simpa only [p, Space.schemePointRepresentative_point] using hq'

/-- **The completion subfunctor of a presheaf of `Type u` is the completion subfunctor of its
universe lift.** The sections of `X` over an object of the site with point-set image in a set
`T` of points of `X` are exactly the sections of the universe lift of `X` with point-set image
in the set of points of that lift corresponding to `T` under
`AlgebraicGeometry.Space.pointsULiftEquiv`. -/
theorem completionSubfunctor_eq_completionSubfunctorULift
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : Set (Space.points B S hS X)) :
    Space.completionSubfunctor B S hS X T =
      Space.completionSubfunctorULift B S hS (X ⋙ uliftFunctor.{u + 1})
        ((Space.pointsULiftEquiv.{u + 1} B S hS X).symm ⁻¹' T) := by
  refine Subfunctor.ext ?_
  funext U
  ext x
  change Space.HasImageIn B S hS X T U.unop x.down ↔
    Space.HasImageInULift B S hS (X ⋙ uliftFunctor.{u + 1}) _ U.unop x
  have key : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U.unop),
      (Space.pointsULiftEquiv.{u + 1} B S hS X).symm
          ((⟨p.carrier, p.contained, p.toBase,
              (X ⋙ uliftFunctor.{u + 1}).map p.value.op x⟩ :
            Space.FieldValuedPointULift.{u + 1} B S hS (X ⋙ uliftFunctor.{u + 1})).class
              B S hS (X ⋙ uliftFunctor.{u + 1})) =
        (⟨p.carrier, p.contained, p.toBase, X.map p.value.op x.down⟩ :
          Space.FieldValuedPoint B S hS X).class B S hS X := fun _ ↦
    (Space.pointsULiftEquiv.{u + 1} B S hS X).symm_apply_eq.mpr rfl
  exact forall_congr' fun p => by rw [Set.mem_preimage, key p]

/-- The subfunctor of sections of an fppf sheaf `X` with point-set image in `T` is an fppf
sheaf. -/
private theorem isSheaf_completionSubfunctor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (T : Set (Space.points B S hS X)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Space.completionSubfunctor B S hS X T).toFunctor := by
  let J := BigFppfOver.topology B S hS
  have hsheaf : Presheaf.IsSheaf J (X ⋙ uliftFunctor.{u + 1}) := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
    exact (isSheaf_iff_isSheaf_of_type J X).mp hX
  rw [completionSubfunctor_eq_completionSubfunctorULift B S hS X T]
  exact Space.isSheaf_completionSubfunctorULift B S hS ⟨X ⋙ uliftFunctor.{u + 1}, hsheaf⟩ _

/-- The sections of `X` pulled back along a morphism `i : W ⟶ U` whose image lies in `T'` lie in
the completion subfunctor. -/
private theorem range_whiskerRight_le_completionSubfunctor
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X))
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ X)
    (T' : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hm : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U),
      (Space.FieldValuedPoint.map B S hS (yoneda.obj U) q p).class B S hS X ∈ T ↔
        Space.schemePoint B S hS U p ∈ T')
    {W : BigFppfOver B S hS} (i : W ⟶ U)
    (hi : Set.range ((BigFppfOver.toScheme B S hS).map i) ⊆ T') :
    Subfunctor.range (Functor.whiskerRight (yoneda.map i ≫ q) uliftFunctor.{u + 1}) ≤
      Space.completionSubfunctor B S hS X T := by
  rintro V _ ⟨t, rfl⟩
  change Space.HasImageIn B S hS X T V.unop (q.app V (t.down ≫ i))
  refine affineSection_mem_completionSubfunctor B S hS T U T' q hm
    V.unop (ULift.up (t.down ≫ i)) ?_
  change Set.range ((BigFppfOver.toScheme B S hS).map (t.down ≫ i)) ⊆ T'
  rw [Functor.map_comp]
  rintro _ ⟨v, rfl⟩
  exact hi ⟨(BigFppfOver.toScheme B S hS).map t.down v, rfl⟩

/-- A morphism over `S` whose underlying scheme morphism factors through `k₀` factors through
`k₀` regarded as a morphism over `S`. -/
private theorem exists_comp_overHomMk_eq {U A : BigFppfOver B S hS} {W₀ : B.Schemes}
    (k₀ : W₀ ⟶ U.left) (g : A ⟶ U)
    (c : (BigFppfOver.toScheme B S hS).obj A ⟶ B.inclusion.obj W₀)
    (hc : c ≫ B.inclusion.map k₀ = (BigFppfOver.toScheme B S hS).map g) :
    ∃ b : A ⟶ Over.mk (k₀ ≫ U.hom), b ≫ Over.homMk k₀ = g := by
  obtain ⟨b₀, rfl⟩ := B.inclusion.map_surjective c
  have hb : b₀ ≫ k₀ = g.left := B.inclusion.map_injective (by rwa [B.inclusion.map_comp])
  refine ⟨Over.homMk b₀ ?_, Over.OverMorphism.ext hb⟩
  change b₀ ≫ (k₀ ≫ U.hom) = A.hom
  rw [← Category.assoc, hb, g.w]

private theorem completionSubfunctor_has_representable_cover
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : Set (Space.points B S hS X))
    (U : BigFppfOver B S hS)
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U)]
    (q : yoneda.obj U ⟶ X)
    [Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q]
    (T' : Set ((BigFppfOver.toScheme B S hS).obj U)) (hT' : IsClosed T')
    (hm : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U),
      (Space.FieldValuedPoint.map B S hS (yoneda.obj U) q p).class B S hS X ∈ T ↔
        Space.schemePoint B S hS U p ∈ T') :
    ∃ (W : BigFppfOver B S hS)
      (p : (uliftYoneda.{u + 1}).obj W ⟶ (Space.completionSubfunctor B S hS X T).toFunctor),
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) p := by
  let J := BigFppfOver.topology B S hS
  let H := BigFppfOver.toScheme B S hS
  let P := Space.completionSubfunctor B S hS X T
  obtain ⟨W₀, k, hW₀, hk, hfactor⟩ :=
    exists_bounded_closedSubscheme_cover B (H.obj U) U.left.property T' hT'
  let k₀ : B.obj hW₀ ⟶ U.left := B.inclusion.preimage k
  let W : BigFppfOver B S hS := Over.mk (k₀ ≫ U.hom)
  let i : W ⟶ U := Over.homMk k₀
  have hi : H.map i = k := B.inclusion.map_preimage _
  let r := Functor.whiskerRight (yoneda.map i ≫ q) uliftFunctor.{u + 1}
  have hr : Subfunctor.range r ≤ P :=
    range_whiskerRight_le_completionSubfunctor B S hS T U q T' hm i (by rwa [hi])
  let p := Subfunctor.lift r hr
  refine ⟨W, p, ⟨fun {V} s => ?_⟩⟩
  apply J.transitive (Presheaf.imageSieve_mem J q s.val.down)
  rintro V₁ j ⟨t, ht⟩
  obtain ⟨I, A, a, hA, hAopen, ha, -⟩ := BigFppfOver.exists_affine_open_cover' B S hS V₁
  refine J.superset_covering ?_ ha
  rw [Sieve.generate_le_iff]
  rintro V₂ b ⟨l⟩
  let g : A l ⟶ U := a l ≫ t
  have he : q.app _ g = X.map (a l ≫ j).op s.val.down := by
    change q.app _ ((yoneda.obj U).map (a l).op t) = _
    rw [q.naturality_apply, ht]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hg : Set.range (H.map g) ⊆ T' := by
    apply (affineSection_mem_completionSubfunctor_iff B S hS T U T' q hm
      (A l) (ULift.up g)).mp
    have hs := (P.toFunctor.map (a l ≫ j).op s).property
    change Space.HasImageIn B S hS X T (A l) (X.map (a l ≫ j).op s.val.down) at hs
    rwa [he]
  have : IsAffine (H.obj (A l)) := hA l
  obtain ⟨c, hc⟩ := hfactor (H.obj (A l)) (H.map g) hg
  obtain ⟨b', hbi'⟩ := exists_comp_overHomMk_eq B S hS k₀ g c (by rwa [← hi] at hc)
  refine ⟨ULift.up b', Subtype.ext (ULift.ext _ _ ?_)⟩
  change q.app _ (b' ≫ i) = X.map (a l ≫ j).op s.val.down
  rwa [hbi']

/-- Let `X` be an algebraic space over `S` and `T` a set of points of `X`. The functor sending
an object `U` of the big fppf site of `S` to the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` is an
fppf sheaf: the map to its sheafification, the completion `X_{/T}` of
`AlgebraicGeometry.Space.completionSheaf`, is an isomorphism. -/
@[stacks 0AIZ "the functor"]
theorem isIso_toSheafify_completionSubfunctor
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) :
    IsIso (toSheafify (BigFppfOver.topology B S hS)
      (Space.completionSubfunctor B S hS X T).toFunctor) :=
  isIso_toSheafify _ (isSheaf_completionSubfunctor B S hS X hX.isSheaf T)

/-- Let `X = Spec A` be an affine scheme over `S` lying in the site and `T ⊆ |X|` a subset. The
functor sending an object `U` of the big fppf site of `S` to the morphisms `f : U ⟶ X` with
`f(|U|) ⊆ T` is an fppf sheaf: the map to its sheafification, the completion of
`AlgebraicGeometry.Space.completionSheaf`, is an isomorphism. -/
@[stacks 0AIY "the functor"]
theorem isIso_toSheafify_completionSubfunctor_affineOver {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) (f : Spec (.of A) ⟶ S)
    (T : Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA f))) :
    IsIso (toSheafify (BigFppfOver.topology B S hS)
      (Space.completionSubfunctor B S hS (yoneda.obj (affineOver B S hS hA f))
        (supportedPoints B S hS (affineOver B S hS hA f) T)).toFunctor) :=
  isIso_toSheafify_completionSubfunctor B S hS _
    (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hA f)) _

end AlgebraicGeometry.FormalSpace

end
