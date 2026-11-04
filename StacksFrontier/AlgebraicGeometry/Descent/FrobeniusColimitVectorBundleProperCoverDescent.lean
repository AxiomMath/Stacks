module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleStack
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidFibrationStack
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquareIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Topologies.H.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverProperQcqs
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictNatTrans
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonDescentAlongTransformation
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# Descending a Frobenius-colimit vector bundle along a proper surjective cover of the base

Let `p` be a prime, `Y` a quasi-compact quasi-separated scheme in characteristic `p`,
`f : X ⟶ Y` proper and surjective with geometrically connected fibres, and `g : Y' ⟶ Y` proper,
surjective and of finite presentation, so that `{g}` is an h covering (Stacks 0ETW). Suppose that
the transition functors of finite locally free `colim_F 𝒪`-modules along proper surjective
morphisms with geometrically connected fibres onto quasi-compact quasi-separated schemes are fully
faithful (this is part (1) of Stacks Tag 0EXH, read through Stacks Tag 0EXB). Then **a finite
locally free `colim_F 𝒪_X`-module `ℰ` whose pullback to `Y' ×_Y X` comes from `Y'` comes from
`Y`**.

This is the reduction "it suffices to construct a descent of `ℰ` after replacing `Y` by the
members of an h covering and `X` by the corresponding base change" in the proof of Stacks Tag
0EXH. The proof is the source's: the finite locally free `colim_F 𝒪`-modules form an h stack
(Stacks Tag 0EXE), so the descent datum of `ℰ` relative to `Y' ×_Y X ⟶ X`, carried to `Y'` along
full faithfulness over `Y'`, `Y' ×_Y Y'` and `Y' ×_Y Y' ×_Y Y'`, descends to `Y`.

The formal argument takes place in a big h site over `Y` containing `X` and `Y'`
(`AlgebraicGeometry.BigHSite.exists_containing`). The base change `U ↦ U ×_Y X` is a functor of
that site, its first projection a natural transformation to the identity, and inverse image along
it a strong transformation from the stack of Stacks Tag 0EXE to its restriction along the base
change (`CategoryTheory.Pseudofunctor.restrictNatTrans`). The descent itself is
`CategoryTheory.Pseudofunctor.SinglePreDatum.exists_app_obj_iso_of_map_obj_iso`.

## Main results

* `AlgebraicGeometry.full_frobeniusVectorBundleGroupoidPseudofunctor_map` and
  `AlgebraicGeometry.faithful_frobeniusVectorBundleGroupoidPseudofunctor_map`: the transition
  functors of the groupoid pseudofunctor of Stacks Tag 0EXE are full, resp. faithful, as soon as
  those of the finite locally free modules are.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

section Groupoid

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

/-- The transition functor of the groupoid pseudofunctor of Stacks Tag 0EXE along `u` is full as
soon as the transition functor of finite locally free `colim_F 𝒪`-modules along the underlying
morphism of schemes is fully faithful: an isomorphism between two pullbacks is the pullback of a
morphism, which is an isomorphism because a fully faithful functor reflects them. -/
lemma full_frobeniusVectorBundleGroupoidPseudofunctor_map {U V : BigHOver B S hS} (u : V ⟶ U)
    [(frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map u)
      (isInCharacteristic_bigHOver B S hS p hpS V)
      (isInCharacteristic_bigHOver B S hS p hpS U)).Full]
    [(frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map u)
      (isInCharacteristic_bigHOver B S hS p hpS V)
      (isInCharacteristic_bigHOver B S hS p hpS U)).Faithful] :
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map u.op.toLoc).toFunctor.Full := by
  constructor
  intro M N c
  let Φ := frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map u)
    (isInCharacteristic_bigHOver B S hS p hpS V) (isInCharacteristic_bigHOver B S hS p hpS U)
  let PM : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U) := ⟨M.obj.of, M.property⟩
  let PN : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U) := ⟨N.obj.of, N.property⟩
  let e : Φ.obj PM ≅ Φ.obj PN := ObjectProperty.isoMk _ c.hom.iso
  let a := (Functor.FullyFaithful.ofFullyFaithful Φ).preimageIso e
  exact ⟨ObjectProperty.homMk (Core.isoMk ((ObjectProperty.ι _).mapIso a)).hom,
    ObjectProperty.hom_ext _ (Core.hom_ext (congrArg (fun t ↦ t.hom)
      ((Functor.FullyFaithful.ofFullyFaithful Φ).map_preimage e.hom)))⟩

/-- The transition functor of the groupoid pseudofunctor of Stacks Tag 0EXE along `u` is
faithful as soon as the transition functor of finite locally free `colim_F 𝒪`-modules along the
underlying morphism of schemes is. -/
lemma faithful_frobeniusVectorBundleGroupoidPseudofunctor_map {U V : BigHOver B S hS} (u : V ⟶ U)
    [(frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map u)
      (isInCharacteristic_bigHOver B S hS p hpS V)
      (isInCharacteristic_bigHOver B S hS p hpS U)).Faithful] :
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map
      u.op.toLoc).toFunctor.Faithful := by
  constructor
  intro M N c c' h
  let Φ := frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map u)
    (isInCharacteristic_bigHOver B S hS p hpS V) (isInCharacteristic_bigHOver B S hS p hpS U)
  let PM : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U) := ⟨M.obj.of, M.property⟩
  let PN : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U) := ⟨N.obj.of, N.property⟩
  have h' : Φ.map (ObjectProperty.homMk c.hom.iso.hom : PM ⟶ PN) =
      Φ.map (ObjectProperty.homMk c'.hom.iso.hom) :=
    ObjectProperty.hom_ext _ (congrArg (fun t ↦ t.hom.iso.hom) h)
  exact ObjectProperty.hom_ext _ (Core.hom_ext (congrArg (fun t ↦ t.hom) (Φ.map_injective h')))

/-- The transition functor of the groupoid pseudofunctor of Stacks Tag 0EXE along a proper
surjective `u` with geometrically connected fibres onto a quasi-compact quasi-separated object is
full and faithful, granted the same of finite locally free `colim_F 𝒪`-modules (`hff`). -/
private lemma full_faithful_frobeniusVectorBundleGroupoidPseudofunctor_map_of_isProper
    (hff : ∀ ⦃W T : Scheme.{u}⦄ (a : W ⟶ T) (hW : IsInCharacteristic W p)
      (hT : IsInCharacteristic T p) [CompactSpace T] [QuasiSeparatedSpace T] [IsProper a]
      [Surjective a] [GeometricallyConnected a],
        (frobeniusColimitVectorBundlesPullback p a hW hT).Full ∧
          (frobeniusColimitVectorBundlesPullback p a hW hT).Faithful)
    {U V : BigHOver B S hS} (u : V ⟶ U) [CompactSpace ((BigHOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj U)]
    [IsProper ((BigHOver.toScheme B S hS).map u)] [Surjective ((BigHOver.toScheme B S hS).map u)]
    [GeometricallyConnected ((BigHOver.toScheme B S hS).map u)] :
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map u.op.toLoc).toFunctor.Full ∧
      ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map
        u.op.toLoc).toFunctor.Faithful := by
  obtain ⟨_, _⟩ := hff ((BigHOver.toScheme B S hS).map u)
    (isInCharacteristic_bigHOver B S hS p hpS V) (isInCharacteristic_bigHOver B S hS p hpS U)
  exact ⟨full_frobeniusVectorBundleGroupoidPseudofunctor_map B S hS p hpS u,
    faithful_frobeniusVectorBundleGroupoidPseudofunctor_map B S hS p hpS u⟩

/-- Inverse image along the projection `U ×_S X ⟶ U`, for `f : X ⟶ S` proper and surjective with
geometrically connected fibres and `U` quasi-compact quasi-separated, is full and faithful on the
groupoid pseudofunctor of Stacks Tag 0EXE, granted the same of finite locally free
`colim_F 𝒪`-modules (`hff`). -/
private lemma full_faithful_frobeniusVectorBundleGroupoidPseudofunctor_map_counit {X : Scheme.{u}}
    {hX : B.Contains X} (f : X ⟶ S) [IsProper f] [Surjective f] [GeometricallyConnected f]
    (hff : ∀ ⦃W T : Scheme.{u}⦄ (a : W ⟶ T) (hW : IsInCharacteristic W p)
      (hT : IsInCharacteristic T p) [CompactSpace T] [QuasiSeparatedSpace T] [IsProper a]
      [Surjective a] [GeometricallyConnected a],
        (frobeniusColimitVectorBundlesPullback p a hW hT).Full ∧
          (frobeniusColimitVectorBundlesPullback p a hW hT).Faithful)
    (U : BigHOver B S hS) [CompactSpace ((BigHOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj U)] :
    ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map
        ((Over.mapPullbackAdj (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).counit.app
          U).op.toLoc).toFunctor.Full ∧
      ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).map
        ((Over.mapPullbackAdj (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).counit.app
          U).op.toLoc).toFunctor.Faithful := by
  have hpb := ((IsPullback.of_hasPullback U.hom
    (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).map B.inclusion).flip
  have key (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (hf : P f) :
      P ((BigHOver.toScheme B S hS).map
        ((Over.mapPullbackAdj (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).counit.app U)) :=
    by simpa using MorphismProperty.of_isPullback hpb hf
  have := key @IsProper ‹_›
  have := key @Surjective ‹_›
  have := key @GeometricallyConnected ‹_›
  exact full_faithful_frobeniusVectorBundleGroupoidPseudofunctor_map_of_isProper B S hS p hpS hff
    (U := U) _

end Groupoid

section Site

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A proper surjective morphism locally of finite presentation of the big h site over `S`
generates a covering sieve. -/
private lemma BigHOver.ofArrows_mem_topology_of_isProper {A A' : BigHOver B S hS} (k : A ⟶ A')
    (h₁ : IsProper ((BigHOver.toScheme B S hS).map k))
    (h₂ : Surjective ((BigHOver.toScheme B S hS).map k))
    (h₃ : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map k)) :
    Sieve.ofArrows (fun _ : PUnit.{1} ↦ A) (fun _ ↦ k) ∈ BigHOver.topology B S hS A' := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
  simpa using BigHOver.sieve₀_mem_topology_of_isHCovering B S hS (PreZeroHypercover.singleton k)
    ((surjective_proper_isHCovering ((BigHOver.toScheme B S hS).map k)
      ⟨h₃, inferInstance, inferInstance⟩).reindex Equiv.punitEquivPUnit)

/-- The base change along `f` of a morphism `k` of the big h site over `S` is a base change of
`k.left`. -/
private lemma BigHOver.isPullback_map_pullback_map_left {X : Scheme.{u}} {hX : B.Contains X}
    (f : B.obj X hX ⟶ B.obj S hS) {A A' : BigHOver B S hS} (k : A ⟶ A') :
    IsPullback ((Over.pullback f ⋙ Over.map f).map k).left (pullback.fst A.hom f)
      (pullback.fst A'.hom f) k.left := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback A'.hom f).flip
  rw [show ((Over.pullback f ⋙ Over.map f).map k).left ≫ pullback.snd A'.hom f =
    pullback.snd A.hom f from pullback.lift_snd _ _ _]
  exact (IsPullback.of_hasPullback A.hom f).flip.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end Site

section Descent

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

/-- Descent data of the groupoid pseudofunctor of Stacks Tag 0EXE, restricted along a functor
preserving pullbacks, are effective along a morphism whose image is proper, surjective and locally
of finite presentation. -/
private lemma isEquivalence_toDescentData_restrict_frobeniusVectorBundleGroupoidPseudofunctor
    (F : BigHOver B S hS ⥤ BigHOver B S hS) [PreservesLimitsOfShape WalkingCospan F]
    {A A' : BigHOver B S hS} (k : A ⟶ A')
    (h₁ : IsProper ((BigHOver.toScheme B S hS).map (F.map k)))
    (h₂ : Surjective ((BigHOver.toScheme B S hS).map (F.map k)))
    (h₃ : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map (F.map k))) :
    (((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).restrict F).toDescentData
      (fun _ : PUnit.{1} ↦ k)).IsEquivalence := by
  have : (frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).IsStack
      (BigHOver.topology B S hS) :=
    (isStack_frobeniusVectorBundleGroupoidFibration_iff B S hS p hpS _).1
      (Functor.isStack_of_isStackInGroupoids
        (frobeniusVectorBundleGroupoidFibration_isStackInGroupoids B S hS p hpS))
  exact (Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves _ F
    (fun _ : PUnit.{1} ↦ k)).2
      ((frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS).isEquivalence_toDescentData
        (J := BigHOver.topology B S hS) _
        (BigHOver.ofArrows_mem_topology_of_isProper (F.map k) h₁ h₂ h₃))

/-- For `f : X ⟶ S` proper and surjective with geometrically connected fibres and `k : A ⟶ A'`
proper, surjective and locally of finite presentation onto a quasi-compact quasi-separated `A'`, a
bundle on `A' ×_S X` whose pullback to `A ×_S X` comes from `A` comes from `A'`, granted `hff`. -/
private lemma exists_frobeniusColimitVectorBundlesPullback_counit_obj_iso {X : Scheme.{u}}
    {hX : B.Contains X} (f : X ⟶ S) [IsProper f] [Surjective f] [GeometricallyConnected f]
    (hff : ∀ ⦃W T : Scheme.{u}⦄ (a : W ⟶ T) (hW : IsInCharacteristic W p)
      (hT : IsInCharacteristic T p) [CompactSpace T] [QuasiSeparatedSpace T] [IsProper a]
      [Surjective a] [GeometricallyConnected a],
        (frobeniusColimitVectorBundlesPullback p a hW hT).Full ∧
          (frobeniusColimitVectorBundlesPullback p a hW hT).Faithful)
    {A A' : BigHOver B S hS} (k : A ⟶ A') [CompactSpace ((BigHOver.toScheme B S hS).obj A')]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj A')]
    (h₁ : IsProper ((BigHOver.toScheme B S hS).map k))
    (h₂ : Surjective ((BigHOver.toScheme B S hS).map k))
    (h₃ : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map k))
    (N : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj
      ((Over.pullback (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS) ⋙
        Over.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).obj A')) p
      (isInCharacteristic_bigHOver B S hS p hpS _))
    (M : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj A) p
      (isInCharacteristic_bigHOver B S hS p hpS A))
    (e : (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map
        ((Over.mapPullbackAdj (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).counit.app A))
        (isInCharacteristic_bigHOver B S hS p hpS _)
        (isInCharacteristic_bigHOver B S hS p hpS A)).obj M ≅
      (frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map
        ((Over.pullback (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS) ⋙
          Over.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).map k))
        (isInCharacteristic_bigHOver B S hS p hpS _)
        (isInCharacteristic_bigHOver B S hS p hpS _)).obj N) :
    ∃ L : frobeniusColimitVectorBundles ((BigHOver.toScheme B S hS).obj A') p
        (isInCharacteristic_bigHOver B S hS p hpS A'),
      Nonempty ((frobeniusColimitVectorBundlesPullback p ((BigHOver.toScheme B S hS).map
        ((Over.mapPullbackAdj (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj S hS)).counit.app A'))
        (isInCharacteristic_bigHOver B S hS p hpS _)
        (isInCharacteristic_bigHOver B S hS p hpS A')).obj L ≅ N) := by
  let T := BigHOver.toScheme B S hS
  let fB : B.obj X hX ⟶ B.obj S hS := ObjectProperty.homMk f
  let BC : BigHOver B S hS ⥤ BigHOver B S hS := Over.pullback fB ⋙ Over.map fB
  let 𝒢 := frobeniusVectorBundleGroupoidPseudofunctor B S hS p hpS
  have : PreservesLimitsOfShape WalkingCospan (Over.map fB) :=
    have : PreservesLimitsOfShape WalkingCospan (Over.map fB ⋙ Over.forget (B.obj S hS)) :=
      inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget (B.obj X hX)))
    preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget (B.obj S hS))
  have hsq := ((BigHOver.isPullback_map_pullback_map_left fB k).map B.inclusion).flip
  have hF := isEquivalence_toDescentData_restrict_frobeniusVectorBundleGroupoidPseudofunctor p hpS
    (𝟭 _) k h₁ h₂ h₃
  have := isEquivalence_toDescentData_restrict_frobeniusVectorBundleGroupoidPseudofunctor p hpS
    BC k (MorphismProperty.of_isPullback (P := @IsProper) hsq h₁)
    (MorphismProperty.of_isPullback (P := @Surjective) hsq h₂)
    (MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsq h₃)
  let τ := 𝒢.restrictNatTrans (Over.mapPullbackAdj fB).counit
  let sq := ChosenPullback.ofHasPullback k k
  let sq₃ := ChosenPullback₃.ofHasPullbacks sq sq sq
  have : CompactSpace (T.obj A) := BigHOver.compactSpace_of_isProper k h₁
  have : QuasiSeparatedSpace (T.obj A) := BigHOver.quasiSeparatedSpace_of_isProper k h₁
  have : CompactSpace (T.obj sq.pullback) :=
    BigHOver.compactSpace_of_isProper _ (BigHOver.isProper_chosenPullback_p₁ k h₁)
  have : QuasiSeparatedSpace (T.obj sq.pullback) :=
    BigHOver.quasiSeparatedSpace_of_isProper _ (BigHOver.isProper_chosenPullback_p₁ k h₁)
  have : CompactSpace (T.obj sq₃.pullback) :=
    BigHOver.compactSpace_of_isProper _ (BigHOver.isProper_chosenPullback₃_p₁₂ k h₁)
  have : QuasiSeparatedSpace (T.obj sq₃.pullback) :=
    BigHOver.quasiSeparatedSpace_of_isProper _ (BigHOver.isProper_chosenPullback₃_p₁₂ k h₁)
  have hτff (U : BigHOver B S hS) [CompactSpace (T.obj U)] [QuasiSeparatedSpace (T.obj U)] :
      (τ.app ⟨op U⟩).toFunctor.Full ∧ (τ.app ⟨op U⟩).toFunctor.Faithful :=
    full_faithful_frobeniusVectorBundleGroupoidPseudofunctor_map_counit B S hS p hpS
      (hX := hX) f hff U
  obtain ⟨-, _⟩ := hτff A
  obtain ⟨_, _⟩ := hτff sq.pullback
  obtain ⟨-, _⟩ := hτff sq₃.pullback
  let toG : ∀ {U : BigHOver B S hS}, frobeniusColimitVectorBundles (T.obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U) → 𝒢.obj ⟨op U⟩ :=
    fun A ↦ ⟨⟨A.obj⟩, A.property⟩
  let toGIso : ∀ {U : BigHOver B S hS} {A A' : frobeniusColimitVectorBundles (T.obj U) p
      (isInCharacteristic_bigHOver B S hS p hpS U)}, (A ≅ A') → (toG A ≅ toG A') :=
    fun i ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      (Core.isoMk ((ObjectProperty.ι _).mapIso i))
  let N' : (𝒢.restrict BC).obj ⟨op A'⟩ := toG (U := BC.obj A') N
  let M' : (𝒢.restrict (𝟭 _)).obj ⟨op A⟩ := toG (U := A) M
  let e' : (τ.app ⟨op A⟩).toFunctor.obj M' ≅ ((𝒢.restrict BC).map k.op.toLoc).toFunctor.obj N' :=
    toGIso (U := BC.obj A) e
  obtain ⟨L, ⟨ε⟩⟩ := Pseudofunctor.SinglePreDatum.exists_app_obj_iso_of_map_obj_iso τ sq sq₃
    hF.essSurj N' M' e'
  exact ⟨⟨L.obj.of, L.property⟩,
    ⟨ObjectProperty.isoMk _ ((Core.inclusion _).mapIso ((ObjectProperty.ι _).mapIso ε))⟩⟩

end Descent

section Cover

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (hsq : IsPullback g' f' f g) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hX' : IsInCharacteristic X' p)
  (hY' : IsInCharacteristic Y' p)

/-- A Frobenius-colimit vector bundle `E` on `X` comes from `Y` as soon as its pullback along an
isomorphism `z : Z ⟶ X` is the pullback of a bundle `ξ` on `Y` along `z ≫ f`. -/
private lemma nonempty_frobeniusColimitVectorBundlesPullback_obj_iso_of_isIso {Z : Scheme.{u}}
    (z : Z ⟶ X) [IsIso z] (hZ : IsInCharacteristic Z p) (ξ : frobeniusColimitVectorBundles Y p hY)
    (E : frobeniusColimitVectorBundles X p hX)
    (e : (frobeniusColimitVectorBundlesPullback p (z ≫ f) hZ hY).obj ξ ≅
      (frobeniusColimitVectorBundlesPullback p z hZ hX).obj E) :
    Nonempty ((frobeniusColimitVectorBundlesPullback p f hX hY).obj ξ ≅ E) :=
  ⟨(frobeniusColimitVectorBundlesPullbackEquivalence p z hZ hX).fullyFaithfulFunctor.preimageIso
    ((frobeniusColimitVectorBundlesPullbackComp p z f hZ hX hY).app ξ ≪≫ e)⟩

include hsq in
/-- The isomorphism `e₀` of pullbacks to `X'`, pulled back along the morphism `W ⟶ X'` with
components `b ≫ s : W ⟶ X` and `a : W ⟶ Y'`. -/
private def frobeniusColimitVectorBundlesPullbackIsoOfIsPullback {W Z : Scheme.{u}} (a : W ⟶ Y')
    (b : W ⟶ Z) (s : Z ⟶ X) (h : (b ≫ s) ≫ f = a ≫ g) (hW : IsInCharacteristic W p)
    (hZ : IsInCharacteristic Z p) (E : frobeniusColimitVectorBundles X p hX)
    (ξ' : frobeniusColimitVectorBundles Y' p hY')
    (e₀ : (frobeniusColimitVectorBundlesPullback p f' hX' hY').obj ξ' ≅
      (frobeniusColimitVectorBundlesPullback p g' hX' hX).obj E) :
    (frobeniusColimitVectorBundlesPullback p a hW hY').obj ξ' ≅
      (frobeniusColimitVectorBundlesPullback p b hW hZ).obj
        ((frobeniusColimitVectorBundlesPullback p s hZ hX).obj E) :=
  eqToIso (congrArg (fun k ↦ (frobeniusColimitVectorBundlesPullback p k hW hY').obj ξ')
      (hsq.lift_snd _ _ h).symm) ≪≫
    ((frobeniusColimitVectorBundlesPullbackComp p (hsq.lift _ _ h) f' hW hX' hY').app ξ').symm ≪≫
    (frobeniusColimitVectorBundlesPullback p (hsq.lift _ _ h) hW hX').mapIso e₀ ≪≫
    (frobeniusColimitVectorBundlesPullbackComp p (hsq.lift _ _ h) g' hW hX' hX).app E ≪≫
    eqToIso (congrArg (fun k ↦ (frobeniusColimitVectorBundlesPullback p k hW hX).obj E)
      (hsq.lift_fst _ _ h)) ≪≫
    ((frobeniusColimitVectorBundlesPullbackComp p b s hW hZ hX).app E).symm

include hsq in
/-- **A Frobenius-colimit vector bundle on `X` whose pullback to `X' = Y' ×_Y X` comes from `Y'`
comes from `Y`**, for `f : X ⟶ Y` proper and surjective with geometrically connected fibres onto
a quasi-compact quasi-separated `Y`, `g : Y' ⟶ Y` proper, surjective and locally of finite
presentation, granted that the transition functors of finite locally free `colim_F 𝒪`-modules
along proper surjective morphisms with geometrically connected fibres onto quasi-compact
quasi-separated schemes are fully faithful (`hff`, which is part (1) of Stacks Tag 0EXH). -/
theorem exists_frobeniusColimitVectorBundlesPullback_obj_iso_of_proper_cover
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Surjective f]
    [GeometricallyConnected f] [IsProper g] [Surjective g] [LocallyOfFinitePresentation g]
    (hff : ∀ ⦃W T : Scheme.{u}⦄ (a : W ⟶ T) (hW : IsInCharacteristic W p)
      (hT : IsInCharacteristic T p) [CompactSpace T] [QuasiSeparatedSpace T] [IsProper a]
      [Surjective a] [GeometricallyConnected a],
        (frobeniusColimitVectorBundlesPullback p a hW hT).Full ∧
          (frobeniusColimitVectorBundlesPullback p a hW hT).Faithful)
    (E : frobeniusColimitVectorBundles X p hX) (ξ' : frobeniusColimitVectorBundles Y' p hY')
    (e₀ : (frobeniusColimitVectorBundlesPullback p f' hX' hY').obj ξ' ≅
      (frobeniusColimitVectorBundlesPullback p g' hX' hX).obj E) :
    ∃ ξ : frobeniusColimitVectorBundles Y p hY,
      Nonempty ((frobeniusColimitVectorBundlesPullback p f hX hY).obj ξ ≅ E) := by
  obtain ⟨B, hB⟩ := BigHSite.exists_containing ({Y, Y', X} : Set Scheme.{u})
  have hYB : B.Contains Y := hB Y (by simp)
  have hY'B : B.Contains Y' := hB Y' (by simp)
  have hXB : B.Contains X := hB X (by simp)
  let T := BigHOver.toScheme B Y hYB
  let fB : B.obj X hXB ⟶ B.obj Y hYB := ObjectProperty.homMk f
  let gB : B.obj Y' hY'B ⟶ B.obj Y hYB := ObjectProperty.homMk g
  let Yo : BigHOver B Y hYB := Over.mk (𝟙 (B.obj Y hYB))
  let Y'o : BigHOver B Y hYB := Over.mk gB
  let gC : Y'o ⟶ Yo := Over.homMk gB (Category.comp_id gB)
  let BC : BigHOver B Y hYB ⥤ BigHOver B Y hYB := Over.pullback fB ⋙ Over.map fB
  let α : BC ⟶ 𝟭 _ := (Over.mapPullbackAdj fB).counit
  have : CompactSpace ((BigHOver.toScheme B Y hYB).obj Yo) := ‹CompactSpace Y›
  have : QuasiSeparatedSpace ((BigHOver.toScheme B Y hYB).obj Yo) := ‹QuasiSeparatedSpace Y›
  have hαU (U : BigHOver B Y hYB) : T.map (α.app U) = B.inclusion.map (pullback.fst U.hom fB) := by
    simp [T, α]
  have hZ := isInCharacteristic_bigHOver B Y hYB p hY (BC.obj Yo)
  have hW' := isInCharacteristic_bigHOver B Y hYB p hY (BC.obj Y'o)
  let sndZ : T.obj (BC.obj Yo) ⟶ X := B.inclusion.map (pullback.snd Yo.hom fB)
  let sndW : T.obj (BC.obj Y'o) ⟶ X := B.inclusion.map (pullback.snd Y'o.hom fB)
  have hcond : sndW ≫ f = T.map (α.app Y'o) ≫ g := by
    rw [hαU]
    exact ((IsPullback.of_hasPullback Y'o.hom fB).map B.inclusion).w.symm
  have hm : (BC.map gC).left ≫ pullback.snd Yo.hom fB = pullback.snd Y'o.hom fB :=
    pullback.lift_snd _ _ _
  have hb : T.map (BC.map gC) ≫ sndZ = sndW :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hm)
  obtain ⟨ξ, ⟨ε⟩⟩ := exists_frobeniusColimitVectorBundlesPullback_counit_obj_iso p hY
    (hX := hXB) f hff gC ‹IsProper g› ‹Surjective g› ‹LocallyOfFinitePresentation g›
    ((frobeniusColimitVectorBundlesPullback p sndZ hZ hX).obj E) ξ'
    (frobeniusColimitVectorBundlesPullbackIsoOfIsPullback hsq p hX hX' hY' (T.map (α.app Y'o))
      (T.map (BC.map gC)) sndZ (by rwa [hb]) hW' hZ E ξ' e₀)
  have ha₀ : T.map (α.app Yo) = sndZ ≫ f := by
    rw [hαU]
    exact (Category.comp_id _).symm.trans ((IsPullback.of_hasPullback Yo.hom fB).map B.inclusion).w
  have : IsIso Yo.hom := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso sndZ := Functor.map_isIso B.inclusion _
  exact ⟨ξ, nonempty_frobeniusColimitVectorBundlesPullback_obj_iso_of_isIso p hX hY sndZ hZ ξ E
    (eqToIso (congrArg (fun k ↦ (frobeniusColimitVectorBundlesPullback p k hZ hY).obj ξ)
      ha₀.symm) ≪≫ ε)⟩

end Cover

end AlgebraicGeometry

end
