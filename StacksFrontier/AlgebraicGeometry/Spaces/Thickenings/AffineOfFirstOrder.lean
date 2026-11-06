module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineOfCartesianChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceChartRings
public import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NilpotentApproximation
public import StacksFrontier.RingTheory.Etale.AffineStageCore

/-!
# Affineness of a first-order (finite-order) thickening of an affine algebraic space

Work over the terminal scheme. Let `W` be an algebraic space with an affine surjective étale chart
`φ : V ⟶ W` whose relation `t, s : R ⟶ V` is affine. This file holds the geometric half of
the finite-order case of Stacks 05ZR. The source's second proof exhibits `X'` as
`Spec Γ(X', 𝒪)`.

* `AlgebraicGeometry.Space.isAffineSpace_of_chartKer_pow_eq_bot`: a closed subspace `Z ⊆ W`
  with all the points of `W` and nilpotent ideal on the chart, if affine, makes `W` affine. The
  chart groupoid of `Z` is effective, being that of an affine space
  (`AlgebraicGeometry.Space.exists_effective_of_isAffineSpace`). It deforms along the nilpotent
  invariant ideal to an effective groupoid
  (`Module.Descent.SquareZero.isEffective_of_pow_eq_bot`), which is the chart groupoid of `W`.
* `AlgebraicGeometry.Space.isAffineSpace_of_isPushout_chart`: if a faithfully flat ring map
  `α : A → Γ(V)` makes `Γ(R)` the pushout `Γ(V) ⊗_A Γ(V)` along `t^♯, s^♯`, then `W` is affine
  (it is `Spec A`). The chart square over `Spec A` is then cartesian, and
  `AlgebraicGeometry.Space.isAffineSpace_of_isIso_lift` (effective fpqc descent) applies.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hT : B.Contains (⊤_ Scheme.{u})}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_AffineOfFirstOrder
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_AffineOfFirstOrder
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_AffineOfFirstOrder B S hS).has_limit _

/-- Pullbacks in `BigFppfOver B S hS`, given directly: instance search for them times out under
Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_bigFppfOver_AffineOfFirstOrder
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks (BigFppfOver B S hS) :=
  hasPullbacks_bigFppfOver B S hS

local instance (priority := high) hasPullback_bigFppfOver_AffineOfFirstOrder
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_bigFppfOver_AffineOfFirstOrder B S hS).has_limit _

/-- **An algebraic space over `Spec ℤ` whose affine chart is the Čech cover of a faithfully flat
ring map is affine.** Let `φ : V ⟶ W` be a surjective étale chart with `V` affine and with
relation `t, s : R ⟶ V`, `R` affine. Let `A → Γ(V)` be faithfully flat with
`t^♯ ∘ α = s^♯ ∘ α`, and suppose `Γ(R) = Γ(V) ⊗_A Γ(V)` along `t^♯, s^♯` (a pushout square).
Then `W ≅ Spec A`. -/
theorem isAffineSpace_of_isPushout_chart {W : (BigFppfOver B (⊤_ Scheme.{u}) hT)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B _ hT W) {V R : BigFppfOver B (⊤_ Scheme.{u}) hT}
    (φ : yoneda.obj V ⟶ W) (t s : R ⟶ V) (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    [IsAffine ((BigFppfOver.toScheme B _ hT).obj V)]
    [IsAffine ((BigFppfOver.toScheme B _ hT).obj R)]
    (A : CommRingCat.{u}) (α : A ⟶ Γ((BigFppfOver.toScheme B _ hT).obj V, ⊤))
    (hff : α.hom.FaithfullyFlat)
    (hpush : IsPushout α α ((BigFppfOver.toScheme B _ hT).map t).appTop
      ((BigFppfOver.toScheme B _ hT).map s).appTop) :
    IsAffineSpace B _ hT W := by
  let G := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hT
  have hA : B.Contains (Spec A) :=
    Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hff.injective V.left.2
  let SA : BigFppfOver B (⊤_ Scheme.{u}) hT := terminalObj B hT hA
  let a : V ⟶ SA := terminalHomMk B hT ((G.obj V).toSpecΓ ≫ Spec.map α)
  have happ : (G.map a).appTop = (Scheme.ΓSpecIso A).hom ≫ α := by
    show ((G.obj V).toSpecΓ ≫ Spec.map α).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have hSA : IsAffine (G.obj SA) := inferInstanceAs (IsAffine (Spec A))
  have hsa : s ≫ a = t ≫ a := by
    apply G.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, happ]
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => (Scheme.ΓSpecIso A).hom ≫ k)
      hpush.w.symm).trans (Category.assoc _ _ _).symm)
  obtain ⟨hflat, hsurja⟩ : Flat (G.map a) ∧ Surjective (G.map a) := by
    obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff α).2 hff
    exact ⟨inferInstanceAs (Flat ((G.obj V).toSpecΓ ≫ Spec.map α)),
      inferInstanceAs (Surjective ((G.obj V).toSpecΓ ≫ Spec.map α))⟩
  have hpush' : IsPushout (G.map a).appTop (G.map a).appTop (G.map t).appTop (G.map s).appTop := by
    rw [happ]
    exact hpush.of_iso (Scheme.ΓSpecIso A).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hpb : IsPullback (G.map t) (G.map s) (G.map a) (G.map a) :=
    isPullback_of_isPushout_appTop hpush'
  have hab : 𝟙 V ≫ a = a := Category.id_comp a
  have hlift : pullback.lift (G.map s) (G.map t ≫ G.map (𝟙 V)) (lift_condition hab hsa) =
      hpb.flip.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd, CategoryTheory.Functor.map_id,
        Category.comp_id]
  exact isAffineSpace_of_isIso_lift hW φ t s hR hsurj het a a (𝟙 V) hab hsa
    inferInstance hSA inferInstance (by rw [hlift]; infer_instance)

/-- **A bijective tensor comparison is a pushout square.** If `A → D` and the two ring maps
`σ τ : D → F` agree on `A`, and `D ⊗_A D → F`, `d ⊗ d' ↦ σ d * τ d'`, is bijective, then
`A → D ⇉ F` is a pushout square of commutative rings. -/
theorem isPushout_of_bijective_tensorLift {A D F : Type u} [CommRing A] [CommRing D]
    [CommRing F] [Algebra A D] (σ τ : D →+* F)
    (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D))
    (hbij : Function.Bijective (Stacks.AffineStageCore.tensorLift σ τ hστ)) :
    IsPushout (CommRingCat.ofHom (algebraMap A D)) (CommRingCat.ofHom (algebraMap A D))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom τ) := by
  refine (CommRingCat.isPushout_tensorProduct A D D).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (RingEquiv.ofBijective _ hbij).toCommRingCatIso (by simp) (by simp) ?_ ?_ <;>
    ext d <;> simp [Stacks.AffineStageCore.tensorLift_tmul]

/-- **An algebraic space over `Spec ℤ` whose chart groupoid is effective is affine.** This is
`AlgebraicGeometry.Space.isAffineSpace_of_isPushout_chart`, with the pushout square given by a
faithfully flat `A → Γ(V)` over which `t^♯` and `s^♯` agree, the comparison
`Γ(V) ⊗_A Γ(V) → Γ(R)`, `x ⊗ y ↦ t^♯ x * s^♯ y`, being bijective. -/
theorem isAffineSpace_of_bijective_tensorLift_chart
    {W : (BigFppfOver B (⊤_ Scheme.{u}) hT)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B _ hT W) {V R : BigFppfOver B (⊤_ Scheme.{u}) hT}
    (φ : yoneda.obj V ⟶ W) (t s : R ⟶ V) (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    [IsAffine ((BigFppfOver.toScheme B _ hT).obj V)]
    [IsAffine ((BigFppfOver.toScheme B _ hT).obj R)]
    (A : Type u) [CommRing A] [Algebra A Γ((BigFppfOver.toScheme B _ hT).obj V, ⊤)]
    [Module.FaithfullyFlat A Γ((BigFppfOver.toScheme B _ hT).obj V, ⊤)]
    (hts : ((BigFppfOver.toScheme B _ hT).map t).appTop.hom.comp
        (algebraMap A Γ((BigFppfOver.toScheme B _ hT).obj V, ⊤)) =
      ((BigFppfOver.toScheme B _ hT).map s).appTop.hom.comp
        (algebraMap A Γ((BigFppfOver.toScheme B _ hT).obj V, ⊤)))
    (hbij : Function.Bijective (Stacks.AffineStageCore.tensorLift
      ((BigFppfOver.toScheme B _ hT).map t).appTop.hom
      ((BigFppfOver.toScheme B _ hT).map s).appTop.hom hts)) :
    IsAffineSpace B _ hT W :=
  isAffineSpace_of_isPushout_chart hW φ t s hR hsurj het (CommRingCat.of A)
    (CommRingCat.ofHom (algebraMap A _))
    ((RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance)
    (isPushout_of_bijective_tensorLift _ _ hts hbij)

/-- **A pushout square of commutative rings is a tensor product.** If `C ← B → D` is completed
to a pushout square by `pC : C → T` and `pD : D → T`, then `T ≅ C ⊗_B D`, compatibly with the two
inclusions. -/
theorem exists_ringEquiv_tensorProduct_of_isPushout {R C D T : Type u} [CommRing R] [CommRing C]
    [CommRing D] [CommRing T] [Algebra R C] [Algebra R D] (pC : C →+* T) (pD : D →+* T)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R D))
      (CommRingCat.ofHom pC) (CommRingCat.ofHom pD)) :
    ∃ e : T ≃+* C ⊗[R] D, (∀ c, e (pC c) = c ⊗ₜ 1) ∧ (∀ d, e (pD d) = 1 ⊗ₜ d) := by
  have ht := CommRingCat.isPushout_tensorProduct R C D
  exact ⟨(hpush.isoIsPushout _ _ ht).commRingCatIsoToRingEquiv,
    fun c => congrArg (fun f => f.hom c) (hpush.inl_isoIsPushout_hom _ _ ht),
    fun d => congrArg (fun f => f.hom d) (hpush.inr_isoIsPushout_hom _ _ ht)⟩

/-! ### The ring groupoid of a chart -/

section ChartGroupoid

variable {S : Scheme.{u}} {hS : B.Contains S} {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ W}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- The diagonal `V ⟶ R = V ×_W V` of a chart. -/
noncomputable def atlasRelationDiag : V ⟶ atlasRelation B S hS hs :=
  hs.rep.lift' (𝟙 V) (𝟙 V) rfl

/-- The diagonal of a chart followed by the target map is the identity. -/
@[reassoc (attr := simp)]
theorem atlasRelationDiag_target : atlasRelationDiag hs ≫ atlasRelationTarget B S hS hs = 𝟙 V :=
  hs.rep.lift'_fst _ _ _

/-- The diagonal of a chart followed by the source map is the identity. -/
@[reassoc (attr := simp)]
theorem atlasRelationDiag_source : atlasRelationDiag hs ≫ atlasRelationSource B S hS hs = 𝟙 V :=
  hs.rep.lift'_snd _ _ _

/-- The object `R ×_{s, V, t} R` of composable pairs of the relation of a chart: pairs
`((x, y), (y, z))`, where a point `(x, y)` of `R` has target `x` and source `y`. -/
noncomputable abbrev atlasRelationPairs : BigFppfOver B S hS :=
  pullback (atlasRelationSource B S hS hs) (atlasRelationTarget B S hS hs)

/-- The composition `R ×_{s, V, t} R ⟶ R`, `((x, y), (y, z)) ↦ (x, z)`, of the relation of a
chart. -/
noncomputable def atlasRelationComp : atlasRelationPairs hs ⟶ atlasRelation B S hS hs :=
  hs.rep.lift' (pullback.fst _ _ ≫ atlasRelationTarget B S hS hs)
    (pullback.snd _ _ ≫ atlasRelationSource B S hS hs) (by
      have hw := (isPullback_yoneda_map_atlasRelation B S hS hs).w
      rw [Functor.map_comp, Category.assoc, hw, ← Category.assoc, ← Functor.map_comp,
        pullback.condition, Functor.map_comp, Category.assoc, hw, ← Category.assoc,
        ← Functor.map_comp, Functor.map_comp, Category.assoc])

/-- The target of the composite `(x, z)` of a composable pair `((x, y), (y, z))` is the target of
`(x, y)`. -/
@[reassoc (attr := simp)]
theorem atlasRelationComp_target : atlasRelationComp hs ≫ atlasRelationTarget B S hS hs =
    pullback.fst _ _ ≫ atlasRelationTarget B S hS hs :=
  hs.rep.lift'_fst _ _ _

/-- The source of the composite `(x, z)` of a composable pair `((x, y), (y, z))` is the source of
`(y, z)`. -/
@[reassoc (attr := simp)]
theorem atlasRelationComp_source : atlasRelationComp hs ≫ atlasRelationSource B S hS hs =
    pullback.snd _ _ ≫ atlasRelationSource B S hS hs :=
  hs.rep.lift'_snd _ _ _

/-- The object of composable pairs has as underlying scheme the fibre product of schemes. -/
theorem isPullback_toScheme_atlasRelationPairs :
    IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst (atlasRelationSource B S hS hs)
        (atlasRelationTarget B S hS hs)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (atlasRelationSource B S hS hs)
        (atlasRelationTarget B S hS hs)))
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs))
      ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)) := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact (IsPullback.of_hasPullback _ _).map _

/-- A type synonym for a commutative ring, to carry a second algebra structure. -/
def SecondRing (C : Type u) : Type u := C

/-- `SecondRing C` carries the commutative ring structure of `C`. -/
instance (C : Type u) [CommRing C] : CommRing (SecondRing C) := ‹CommRing C›

end ChartGroupoid

/-! ### The finite-order thickening step -/

open Module.Descent.SquareZero in
/-- **A finite-order thickening of an affine algebraic space is affine** (over `Spec ℤ`; Stacks
05ZR, the case of finite-order thickenings, read on one chart). Let `φ : V ⟶ W` be an affine
surjective étale chart and `Z ⊆ W` a closed subspace with all the points of `W` whose chart ideal
is nilpotent. If `Z` is affine, so is `W`. -/
theorem isAffineSpace_of_chartKer_pow_eq_bot
    (W : AlgebraicSpaces B (⊤_ Scheme.{u}) hT) (Z : ClosedSubspaces B _ hT W.1)
    {V : BigFppfOver B (⊤_ Scheme.{u}) hT} (φ : yoneda.obj V ⟶ W.1)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hT))) φ)
    (hV : IsAffine ((BigFppfOver.toScheme B _ hT).obj V))
    (hsurjZ : IsSurjective B _ hT Z.1.ι) {n : ℕ}
    (hn : chartKer B _ hT W Z φ ^ n = ⊥)
    (hZ : IsAffineSpace B _ hT Z.1.toFunctor) : IsAffineSpace B _ hT W.1 := by
  let G := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hT
  let Zs : AlgebraicSpaces B _ hT := ⟨Z.1.toFunctor, Z.2.1⟩
  let V₀ : SpacesEtale B _ hT Zs := ⟨Over.mk (𝟙 Zs), fun U φ hφ ↦ hφ⟩
  have hZqcsep := isQuasiCompactSeparated_of_isAffineSpace B _ hT hT Zs V₀ hZ
  have hWsep : IsAbsolutelySeparated B _ hT hT W.1 :=
    isAbsolutelySeparated_of_isSurjective_of_universallyClosed B _ hT hT Z.2.1 W.2 Z.1.ι hsurjZ
      (universallyClosed_of_isClosedImmersion B _ hT Z.2.1 W.2 Z.1.ι Z.2.2) hZqcsep.2
  have hR := isPullback_yoneda_map_atlasRelation B _ hT hs
  have : IsAffine (G.obj V) := hV
  have : IsAffine (G.obj (atlasRelation B _ hT hs)) :=
    isAffine_of_isAbsolutelySeparated B _ hT hT hWsep hR hV hV
  set tg := (G.map (atlasRelationTarget B _ hT hs)).appTop.hom
  set sc := (G.map (atlasRelationSource B _ hT hs)).appTop.hom
  let _ : Algebra Γ(G.obj V, ⊤) Γ(G.obj (atlasRelation B _ hT hs), ⊤) := sc.toAlgebra
  have hetS : Etale (G.map (atlasRelationSource B _ hT hs)) :=
    he.property φ (hs.rep.fst φ) (hs.rep.snd φ) (hs.rep.isPullback φ)
  have : Module.Flat Γ(G.obj V, ⊤) Γ(G.obj (atlasRelation B _ hT hs), ⊤) :=
    (G.map (atlasRelationSource B _ hT hs)).flat_appTop
  let _ : Algebra Γ(G.obj V, ⊤) (SecondRing Γ(G.obj (atlasRelation B _ hT hs), ⊤)) :=
    tg.toAlgebra
  let σ : Γ(G.obj (atlasRelation B _ hT hs), ⊤) ≃+*
      SecondRing Γ(G.obj (atlasRelation B _ hT hs), ⊤) := RingEquiv.refl _
  let e := (G.map (atlasRelationDiag hs)).appTop.hom
  have hcomp : ∀ {X Y T : BigFppfOver B _ hT} (a : X ⟶ Y) (b : Y ⟶ T) {c : X ⟶ T},
      a ≫ b = c → ∀ x, (G.map a).appTop.hom ((G.map b).appTop.hom x) = (G.map c).appTop.hom x := by
    rintro - - - a b - rfl x
    exact (Γ_map_toScheme_comp_apply B _ hT a b x).symm
  have hes : ∀ b, e (tg b) = b := fun b =>
    (hcomp _ _ (atlasRelationDiag_target hs) b).trans (by simp)
  have het : ∀ b, e (sc b) = b :=
    fun b => (hcomp _ _ (atlasRelationDiag_source hs) b).trans (by simp)
  have hpush := isPushout_appTop_of_isPullback (isPullback_toScheme_atlasRelationPairs hs)
  obtain ⟨eQ, heQl, heQr⟩ := exists_ringEquiv_tensorProduct_of_isPushout
    (R := Γ(G.obj V, ⊤)) (C := Γ(G.obj (atlasRelation B _ hT hs), ⊤))
    (D := SecondRing Γ(G.obj (atlasRelation B _ hT hs), ⊤))
    (G.map (pullback.fst _ _)).appTop.hom (G.map (pullback.snd _ _)).appTop.hom hpush
  let m := eQ.toRingHom.comp (G.map (atlasRelationComp hs)).appTop.hom
  have hms : ∀ b, m (tg b) = tg b ⊗ₜ 1 := fun b =>
    (congrArg eQ ((hcomp _ _ (atlasRelationComp_target hs) b).trans
      (hcomp (pullback.fst _ _) _ rfl b).symm)).trans (heQl _)
  have hmt : ∀ b, m (sc b) = 1 ⊗ₜ σ (sc b) := fun b =>
    (congrArg eQ ((hcomp _ _ (atlasRelationComp_source hs) b).trans
      (hcomp (pullback.snd _ _) _ rfl b).symm)).trans (heQr _)
  have hK : (chartIdealAt B _ hT W he Z).map tg =
      extJ Γ(G.obj (atlasRelation B _ hT hs), ⊤) (chartIdealAt B _ hT W he Z) :=
    map_definingIdealAt_atlasRelationTarget_eq B _ hT he hs Z
  have hKn : chartIdealAt B _ hT W he Z ^ n = ⊥ := by
    have h := etaleChartKer_chart B _ hT he Z
    change chartKer B _ hT W Z φ = Scheme.IdealSheafData.ofIdealTop _ at h
    rw [h, ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, ← map_pow] at hn
    let eo := (Scheme.IdealSheafData.equivOfIsAffine (X := G.obj V)).symm.toOrderIso
    exact le_bot_iff.1 (eo.le_iff_le.1 (hn.le.trans (OrderIso.map_bot eo).ge))
  obtain ⟨CD⟩ := nonempty_closedChartData (Y := W) (he := he) hs hR Z
  obtain ⟨A₀, _, _, -, _, hst, hbij₀⟩ := exists_effective_of_isAffineSpace hR.w CD hZ
  obtain ⟨A, _, _, hA, hff, hbij⟩ := isEffective_of_pow_eq_bot tg σ (fun _ => rfl) e hes het m
    hms hmt _ hK hKn (isEffective_s₀_of_bijective_tensorLift tg _ hK hst hbij₀)
  refine isAffineSpace_of_bijective_tensorLift_chart W.2 φ (atlasRelationSource B _ hT hs)
    (atlasRelationTarget B _ hT hs) hR.flip hs he A (RingHom.ext fun a => (hA a).symm) ?_
  convert hbij using 1
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgebraicGeometry.Space

end
