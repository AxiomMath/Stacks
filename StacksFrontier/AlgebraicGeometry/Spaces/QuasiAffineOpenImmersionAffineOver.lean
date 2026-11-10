module

public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsDirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineDirectImageFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp

/-!
# Quasi-affineness and open immersions into an algebraic space affine over the target

Let `f : Y ⟶ X` be a quasi-compact morphism of algebraic spaces over a scheme `S`, let `P` be an
algebraic space affine over `X` by `p`, and let `g : Y ⟶ P` be a morphism over `X` whose map
`p_* 𝒪_P ⟶ f_* 𝒪_Y` on direct-image algebras is an isomorphism. Then `f` is quasi-affine if and
only if `g` is an open immersion (Stacks 086S). This file proves both directions, and their forms
at the relative spectrum produced by the bounded anti-equivalence of Stacks 081V.

## Main results

* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isOpenImmersion_affineOver`: a quasi-compact
  morphism which factors over `X` through an algebraic space affine over `X` by an open immersion
  is quasi-affine.
* `AlgebraicGeometry.Space.isOpenImmersion_of_isQuasiAffineHom_affineOver`: conversely, if `f` is
  quasi-affine, `P` is affine over `X` by `p`, and `g : Y ⟶ P` over `X` has
  `p_* 𝒪_P ⟶ f_* 𝒪_Y` an isomorphism, then `g` is an open immersion.
* `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_affineOver`: the two together.
* `AlgebraicGeometry.Space.isQuasiAffineHom_of_isOpenImmersion_boundedRelativeSpecDirectImage`,
  `AlgebraicGeometry.Space.isOpenImmersion_of_isQuasiAffineHom_boundedRelativeSpecDirectImage`
  and
  `AlgebraicGeometry.Space.isQuasiAffineHom_iff_isOpenImmersion_boundedRelativeSpecDirectImage`:
  those three statements at the relative spectrum produced by the bounded anti-equivalence of
  Stacks 081V.
* `isQuasiAffineHom_of_isOpenImmersion_qcqsDirectImageFactorizationMap_unconditional`: a
  quasi-compact, quasi-separated morphism whose canonical morphism of Stacks 081X is an open
  immersion is quasi-affine, for an inhabitant of
  `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`; that structure is uninhabited, by
  `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
* [Stacks Project, Tag 03WN](https://stacks.math.columbia.edu/tag/03WN)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081X](https://stacks.math.columbia.edu/tag/081X)
* [Stacks Project, Tag 086S](https://stacks.math.columbia.edu/tag/086S)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for `HasPullbacks` of presheaves on the big fppf site is deep
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_QuasiAffineOpenImmersionAffineOver :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for limits of cospans of presheaves on the big fppf site. -/
local instance (priority := high) hasPullback_presheaf_QuasiAffineOpenImmersionAffineOver
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### An open immersion into an affine space over the target, from quasi-affineness -/

/-- A morphism of schemes out of a quasi-affine scheme into an affine scheme which is an
isomorphism on global regular functions is an open immersion. -/
theorem isOpenImmersion_of_isQuasiAffine_of_isIso_appTop {V W : Scheme.{u}} (g : V ⟶ W)
    [Scheme.IsQuasiAffine V] [IsAffine W] [IsIso g.appTop] :
    _root_.AlgebraicGeometry.IsOpenImmersion g := by
  have : _root_.AlgebraicGeometry.IsOpenImmersion (g ≫ W.toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    infer_instance
  exact _root_.AlgebraicGeometry.IsOpenImmersion.of_comp g W.toSpecΓ

/-- A morphism `g : V ⟶ W` of schemes over `T` whose base change along each member of an open
cover of `T` is an open immersion is an open immersion. -/
theorem isOpenImmersion_of_openCover_of_isPullback {T V W : Scheme.{u}} (g : V ⟶ W) (p : W ⟶ T)
    (𝒰 : T.OpenCover)
    (h : ∀ i : 𝒰.I₀, ∃ (W' V' : Scheme.{u}) (v : W' ⟶ W) (q : W' ⟶ 𝒰.X i)
      (w : V' ⟶ V) (r : V' ⟶ W'),
      IsPullback v q p (𝒰.f i) ∧ IsPullback w r g v ∧
        _root_.AlgebraicGeometry.IsOpenImmersion r) :
    _root_.AlgebraicGeometry.IsOpenImmersion g := by
  classical
  choose W' V' v q w r hp hg hr using h
  let 𝒱 : W.OpenCover := Scheme.Cover.copy (𝒰.pullback₁ p) 𝒰.I₀ W' v (Equiv.refl _)
    (fun i ↦ (hp i).isoPullback) (fun i ↦ (hp i).isoPullback_hom_fst.symm)
  apply IsZariskiLocalAtTarget.of_openCover
    (P := @_root_.AlgebraicGeometry.IsOpenImmersion) 𝒱
  intro i
  dsimp only [𝒱, Scheme.Cover.copy] at i ⊢
  change _root_.AlgebraicGeometry.IsOpenImmersion (pullback.snd g (v i))
  rw [← (hg i).isoPullback_inv_snd]
  have := hr i
  infer_instance

/-- A square of objects of the big fppf site which is cartesian after the Yoneda embedding is
cartesian on the underlying schemes. -/
theorem isPullback_map_toScheme_of_isPullback_yoneda {A C D E' : BigFppfOver B S hS}
    {a : A ⟶ C} {b : A ⟶ D} {c : C ⟶ E'} {d : D ⟶ E'}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map d) := by
  apply (IsPullback.of_map yoneda _ h).map (BigFppfOver.toScheme B S hS)
  apply yoneda.map_injective
  simpa only [Functor.map_comp] using h.w

/-- If the map on direct-image algebras attached to a morphism `g` over `X` is an isomorphism,
then so is the direct image along the structure morphism of the target of the structure map of
`g`. -/
theorem isIso_pushforwardCommRing_map_fSharp {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (g : Y ⟶ Z) (hg : IsIso (pushforwardRingMap B S hS g)) :
    IsIso ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Z.hom).toToposHom).map
      (smallEtaleRingedToposHom B S hS g.left).fSharp) := by
  let e := Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso
      (smallEtaleRingedToposHom B S hS g.left).toToposHom
      (smallEtaleRingedToposHom B S hS Z.hom).toToposHom
      (smallEtaleRingedTopos B S hS Y.left).O ≪≫
    (smallEtaleRingedToposHom_compRingIso B S hS g.left Z.hom).app
      (smallEtaleRingedTopos B S hS Y.left).O ≪≫
    eqToIso (congrArg
      (fun q : Y.left ⟶ X ↦
        (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS Y.left).O)
      (Over.w g))
  exact (isIso_comp_right_iff _ e.hom).mp hg

/-- For a representable `f : X ⟶ Y`, if the direct image along `f` of a map of sheaves of
commutative rings on the small étale site of `X` is an isomorphism, then that map is an
isomorphism over every base-changed chart. -/
theorem isIso_fSharp_app_smallBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    {M N : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (a : M ⟶ N)
    (ha : IsIso ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS f).toToposHom).map a))
    (V : SmallEtale B S hS Y.1) :
    IsIso (a.hom.app (op ((smallBaseChange B S hS f hf).obj V))) := by
  let := (smallBaseChange_isMorphismOfSites B S hS f hf).toIsContinuous
  let e := smallEtaleRingedToposHom_representableRing B S hS f hf
  let F := (smallBaseChange B S hS f hf).sheafPushforwardContinuous CommRingCat.{u}
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)
  have : IsIso (F.map a) := by
    rw [← NatIso.naturality_1 e a]
    infer_instance
  change IsIso ((F.map a).hom.app (op V))
  infer_instance

/-- If the structure map of a representable morphism `f : X ⟶ Y` is an isomorphism on the
sections over an étale chart `V` of the target, then the cartesian projection `X ×_Y V ⟶ V` of
schemes is an isomorphism on global regular functions. -/
theorem isIso_appTop_cartesianProjection {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (hiso : IsIso ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op V))) :
    IsIso ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop := by
  let := isContinuous_smallBaseChange B S hS f hf
  have h1 : IsIso ((cartesianProjectionSharp B S hS f hf).hom.app (op V)) := by
    rw [← fSharp_comp_chartProjectionSharpDirectImage B S hS f hf]
    have i1 : IsIso (((sheafCompose (SmallEtale.topology B S hS Y.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharp).hom.app (op V)) := by
      change IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map
        ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op V)))
      infer_instance
    have i2 : IsIso ((chartProjectionSharpDirectImage B S hS f hf).hom.app (op V)) := by
      change IsIso ((sheafToPresheaf (SmallEtale.topology B S hS Y.1) RingCat.{u} ⋙
        (evaluation _ _).obj (op V)).map (chartProjectionSharpDirectImage B S hS f hf))
      infer_instance
    exact IsIso.comp_isIso' i1 i2
  change IsIso ((forget₂ CommRingCat.{u} RingCat.{u}).map
    ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop) at h1
  exact isIso_of_reflects_iso _ (forget₂ CommRingCat.{u} RingCat.{u})

/-- Given pullback squares over `z` with bottom maps `u₀` and `u₁ = F j ≫ u₀`, the comparison map
between the tops exists and makes the left square cartesian. -/
private theorem exists_hom_isPullback_of_isPullback_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {T₀ T₁ V₀ V₁ : C} {Z W : D} {z : Z ⟶ W}
    {u₀ : F.obj V₀ ⟶ W} {u₁ : F.obj V₁ ⟶ W} {a₀ : F.obj T₀ ⟶ Z} {a₁ : F.obj T₁ ⟶ Z}
    (b₁ : T₁ ⟶ V₁) (j : V₁ ⟶ V₀) (hj : F.map j ≫ u₀ = u₁) {b₀ : T₀ ⟶ V₀}
    (h₀ : IsPullback a₀ (F.map b₀) z u₀) (h₁ : IsPullback a₁ (F.map b₁) z u₁) :
    ∃ v : T₁ ⟶ T₀, F.map v ≫ a₀ = a₁ ∧ IsPullback (F.map v) (F.map b₁) (F.map b₀) (F.map j) := by
  subst hj
  obtain ⟨v, hv⟩ : ∃ v : T₁ ⟶ T₀, F.map v = h₀.lift a₁ (F.map b₁ ≫ F.map j)
      (by rw [h₁.w, Category.assoc]) := ⟨F.preimage _, F.map_preimage _⟩
  have h₁' : F.map v ≫ a₀ = a₁ := by rw [hv]; exact h₀.lift_fst _ _ _
  have h₂ : F.map v ≫ F.map b₀ = F.map b₁ ≫ F.map j := by rw [hv]; exact h₀.lift_snd _ _ _
  exact ⟨v, h₁', IsPullback.of_right (by rwa [h₁']) h₂ h₀⟩

/-- For a morphism `g : Y ⟶ P` over `X`, the composite of `g` and the structure map of `P` is the
structure map of `Y`. -/
private theorem comp_hom_eq_of_over_hom {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (P : AffineOver B S hS X) (g : Over.mk f ⟶ P.obj) : g.left.hom ≫ P.obj.hom.hom = f.hom := by
  rw [← ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun m : Y ⟶ X ↦ m.hom) (Over.w g)

/-- Let `g : Y ⟶ Z` be a representable morphism of algebraic spaces and `p : Z ⟶ X` an affine one
whose composite with `g` is quasi-affine, and suppose that the direct image along `p` of the
structure map of `g` is an isomorphism.  Then over every *affine* étale chart `U` of `X` the
cartesian projection `Y ×_X U ⟶ Z ×_X U` of schemes is an open immersion. -/
theorem isOpenImmersion_cartesianProjection_of_isAffine_chart
    {X Y Z : AlgebraicSpaces B S hS} (g : Y ⟶ Z) (p : Z ⟶ X)
    (hgrep : yoneda.relativelyRepresentable g.hom)
    (hpaff : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p.hom)
    (hqa : IsQuasiAffineHom B S hS (g.hom ≫ p.hom))
    (hiso : IsIso ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS p).toToposHom).map
      (smallEtaleRingedToposHom B S hS g).fSharp))
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom)) := by
  have hqpb : IsPullback ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom
      (yoneda.map (hpaff.rep.snd U.1.hom)) p.hom U.1.hom := hpaff.rep.isPullback U.1.hom
  have hrpb : IsPullback
      ((smallBaseChange B S hS g hgrep).obj
        ((smallBaseChange B S hS p hpaff.rep).obj U)).1.hom
      (yoneda.map (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom)) g.hom
      ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom :=
    hgrep.isPullback ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom
  have hqaff : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (hpaff.rep.snd U.1.hom)) :=
    hpaff.property U.1.hom ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom
      (hpaff.rep.snd U.1.hom) hqpb
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS p hpaff.rep).obj U).1.left) :=
    @isAffine_of_isAffineHom _ _ ((BigFppfOver.toScheme B S hS).map (hpaff.rep.snd U.1.hom))
      hqaff hU
  obtain ⟨T, hT, ⟨eT⟩⟩ := hqa ⟨U.1.left, hU⟩ U.1.hom
  have e : ((smallBaseChange B S hS g hgrep).obj
      ((smallBaseChange B S hS p hpaff.rep).obj U)).1.left ≅ T :=
    yoneda.preimageIso ((hrpb.paste_vert hqpb).flip.isoPullback ≪≫ eT.symm)
  have hWqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS g hgrep).obj
        ((smallBaseChange B S hS p hpaff.rep).obj U)).1.left) :=
    @Scheme.IsQuasiAffine.of_isAffineHom _ _ ((BigFppfOver.toScheme B S hS).map e.hom)
      (by infer_instance) hT
  have hisor : IsIso ((BigFppfOver.toScheme B S hS).map
      (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom)).appTop :=
    isIso_appTop_cartesianProjection B S hS g hgrep
      ((smallBaseChange B S hS p hpaff.rep).obj U)
      (isIso_fSharp_app_smallBaseChange B S hS p hpaff.rep
        (smallEtaleRingedToposHom B S hS g).fSharp hiso U)
  exact @isOpenImmersion_of_isQuasiAffine_of_isIso_appTop _ _
    ((BigFppfOver.toScheme B S hS).map
      (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom)) hWqa hVaff hisor

/-- Let `g : Y ⟶ Z` be a representable morphism of algebraic spaces and `p : Z ⟶ X` an affine one
whose composite with `g` is quasi-affine, and suppose that the direct image along `p` of the
structure map of `g` is an isomorphism. Then over every étale chart `U₀` of `X` the cartesian
projection `Y ×_X U₀ ⟶ Z ×_X U₀` of schemes is an open immersion. -/
theorem isOpenImmersion_cartesianProjection {X Y Z : AlgebraicSpaces B S hS} (g : Y ⟶ Z)
    (p : Z ⟶ X) (hgrep : yoneda.relativelyRepresentable g.hom)
    (hpaff : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p.hom)
    (hqa : IsQuasiAffineHom B S hS (g.hom ≫ p.hom))
    (hiso : IsIso ((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      (smallEtaleRingedToposHom B S hS p).toToposHom).map
      (smallEtaleRingedToposHom B S hS g).fSharp))
    (U₀ : SmallEtale B S hS X.1) :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U₀).1.hom)) := by
  classical
  let : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS inferInstance
  let : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have hq₀ : IsPullback ((smallBaseChange B S hS p hpaff.rep).obj U₀).1.hom
      (yoneda.map (hpaff.rep.snd U₀.1.hom)) p.hom U₀.1.hom := hpaff.rep.isPullback U₀.1.hom
  have hr₀ : IsPullback ((smallBaseChange B S hS g hgrep).obj
        ((smallBaseChange B S hS p hpaff.rep).obj U₀)).1.hom
      (yoneda.map (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U₀).1.hom)) g.hom
      ((smallBaseChange B S hS p hpaff.rep).obj U₀).1.hom := hgrep.isPullback _
  let 𝒰 : ((BigFppfOver.toScheme B S hS).obj U₀.1.left).OpenCover :=
    Scheme.Cover.mkOfCovers
      ((BigFppfOver.toScheme B S hS).obj U₀.1.left).affineOpens (fun A => A.1.toScheme)
      (fun A => A.1.ι) (by
        intro x
        obtain ⟨A, hA, hx, _⟩ := exists_isAffineOpen_mem_and_subset
          (X := (BigFppfOver.toScheme B S hS).obj U₀.1.left) (x := x) (U := ⊤) trivial
        exact ⟨⟨A, hA⟩, ⟨x, hx⟩, rfl⟩)
  apply isOpenImmersion_of_openCover_of_isPullback _
    ((BigFppfOver.toScheme B S hS).map (hpaff.rep.snd U₀.1.hom)) 𝒰
  intro A
  let As : B.Schemes := ⟨A.1.toScheme,
    (Scheme.size_coe_opens_le _ A.1).trans_lt U₀.1.left.left.property⟩
  let j' : As ⟶ U₀.1.left.left := ObjectProperty.homMk A.1.ι
  let AU : BigFppfOver B S hS := Over.mk (j' ≫ U₀.1.left.hom)
  let j : AU ⟶ U₀.1.left := Over.homMk j'
  have hj : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) := by
    apply MorphismProperty.relative_map
    change _root_.AlgebraicGeometry.Etale A.1.ι
    infer_instance
  let U : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map j ≫ U₀.1.hom),
      MorphismProperty.comp_mem _ _ _ hj U₀.property⟩
  have hUhom : U.1.hom = yoneda.map j ≫ U₀.1.hom := rfl
  have hq : IsPullback ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom
      (yoneda.map (hpaff.rep.snd U.1.hom)) p.hom U.1.hom := hpaff.rep.isPullback U.1.hom
  have hr : IsPullback ((smallBaseChange B S hS g hgrep).obj
        ((smallBaseChange B S hS p hpaff.rep).obj U)).1.hom
      (yoneda.map (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom)) g.hom
      ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom := hgrep.isPullback _
  have hopen := isOpenImmersion_cartesianProjection_of_isAffine_chart B S hS g p hgrep hpaff
    hqa hiso U A.property
  obtain ⟨v, hv₁, hv⟩ := exists_hom_isPullback_of_isPullback_comp yoneda (hpaff.rep.snd U.1.hom)
    j hUhom.symm hq₀ hq
  obtain ⟨w, -, hw⟩ := exists_hom_isPullback_of_isPullback_comp yoneda
    (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom) v hv₁ hr₀ hr
  exact ⟨(BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS p hpaff.rep).obj U).1.left,
    (BigFppfOver.toScheme B S hS).obj ((smallBaseChange B S hS g hgrep).obj
      ((smallBaseChange B S hS p hpaff.rep).obj U)).1.left,
    (BigFppfOver.toScheme B S hS).map v,
    (BigFppfOver.toScheme B S hS).map (hpaff.rep.snd U.1.hom),
    (BigFppfOver.toScheme B S hS).map w,
    (BigFppfOver.toScheme B S hS).map
      (hgrep.snd ((smallBaseChange B S hS p hpaff.rep).obj U).1.hom),
    isPullback_map_toScheme_of_isPullback_yoneda B S hS hv,
    isPullback_map_toScheme_of_isPullback_yoneda B S hS hw, hopen⟩

/-- Let `f : Y ⟶ X` be a quasi-affine morphism of algebraic spaces over `S`, let `P` be an
algebraic space affine over `X`, and let `g : Y ⟶ P` be a morphism over `X` whose map on
direct-image algebras `p_* 𝒪_P ⟶ f_* 𝒪_Y` is an isomorphism. Then `g` is an open immersion. -/
theorem isOpenImmersion_of_isQuasiAffineHom_affineOver {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hfqa : IsQuasiAffineHom B S hS f.hom) (P : AffineOver B S hS X)
    (g : Over.mk f ⟶ P.obj) (hring : IsIso (pushforwardRingMap B S hS g)) :
    IsOpenImmersion B S hS g.left.hom := by
  have hfac := comp_hom_eq_of_over_hom B S hS f P g
  have hpaff := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS P.obj.hom.hom
    P.obj.left.2 X.2).out 2 1).mp P.property
  have hfpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f.hom :=
    ((isQuasiAffineHom_tfae_of_isAlgebraicSpace Y.2 X.2 f.hom).out 2 1).mp hfqa
  have hgrep : yoneda.relativelyRepresentable g.left.hom :=
    relativelyRepresentable_of_comp B S hS P.obj.left.2.diagonal_representable
      g.left.hom P.obj.hom.hom (by rw [hfac]; exact hfpre.rep)
  have hqa : IsQuasiAffineHom B S hS (g.left.hom ≫ P.obj.hom.hom) := hfac ▸ hfqa
  have hiso := isIso_pushforwardCommRing_map_fSharp B S hS g hring
  obtain ⟨U', u, husurj, huetale⟩ := X.2.exists_atlas
  let U₀ : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk u, huetale⟩
  have hq₀ : IsPullback ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.hom
      (yoneda.map (hpaff.2.rep.snd U₀.1.hom)) P.obj.hom.hom U₀.1.hom :=
    hpaff.2.rep.isPullback U₀.1.hom
  have hr₀ : IsPullback ((smallBaseChange B S hS g.left hgrep).obj
        ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀)).1.hom
      (yoneda.map (hgrep.snd
        ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.hom)) g.left.hom
      ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.hom := hgrep.isPullback _
  have hopen := isOpenImmersion_cartesianProjection B S hS g.left P.obj.hom hgrep hpaff.2
    hqa hiso U₀
  apply ((isOpenImmersion_tfae_of_isAlgebraicSpace Y.2
    P.obj.left.2 g.left.hom).out 4 1).mp
  refine ⟨((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.left,
    ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.hom, ?_,
    ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).property, ?_⟩
  · let : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hq₀.flip husurj
  · let : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      inverseImage_isStableUnderBaseChange B S hS inferInstance
    have hopen' : IsOpenImmersion B S hS
        (yoneda.map (hgrep.snd
          ((smallBaseChange B S hS P.obj.hom hpaff.2.rep).obj U₀).1.hom)) :=
      MorphismProperty.relative_map hopen
    rw [← hr₀.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp _ hr₀.isoPullback.inv _ hopen'

/-! ### Quasi-affineness from an open immersion into an affine space over the target -/

/-- A quasi-compact morphism `f : Y ⟶ X` of algebraic spaces which factors over `X` through
an algebraic space `P` affine over `X` by a morphism `g : Y ⟶ P` that is an open immersion is
quasi-affine. -/
theorem isQuasiAffineHom_of_isOpenImmersion_affineOver {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (P : AffineOver B S hS X) (g : Over.mk f ⟶ P.obj)
    (hoi : IsOpenImmersion B S hS g.left.hom) :
    IsQuasiAffineHom B S hS f.hom := by
  have hfac := comp_hom_eq_of_over_hom B S hS f P g
  have hpaff : IsAffineHom B S hS P.obj.hom.hom := P.property
  have hpqs : IsQuasiSeparated B S hS P.obj.hom.hom :=
    isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isAffineHom B S hS _ P.obj.left.2 X.2 hpaff)
  have hgqc : IsQuasiCompact B S hS g.left.hom :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ Y.2 X.2 (hfac ▸ hfqc) hpqs
  rw [← hfac]
  exact IsQuasiAffineHom.comp Y.2 P.obj.left.2 X.2
    (isQuasiAffineHom_of_isOpenImmersion B S hS _ hoi hgqc)
    (isQuasiAffineHom_of_isAffineHom hpaff)

/-- Let `f : Y ⟶ X` be a quasi-compact morphism of algebraic spaces over `S`, let `P` be an
algebraic space affine over `X` by `p`, and let `g : Y ⟶ P` be a morphism over `X` whose map on
direct-image algebras `p_* 𝒪_P ⟶ f_* 𝒪_Y` is an isomorphism. Then `f` is quasi-affine if and only
if `g` is an open immersion. -/
@[stacks 086S "both directions, for every P affine over X by p and every g : Y ⟶ P over X whose \
map on direct-image algebras p_* O_P ⟶ f_* O_Y is an isomorphism: a quasi-compact f is \
quasi-affine iff g is an open immersion; this is the general form, and the canonical morphism \
of 081X is one such g"]
theorem isQuasiAffineHom_iff_isOpenImmersion_affineOver {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (P : AffineOver B S hS X) (g : Over.mk f ⟶ P.obj)
    (hring : IsIso (pushforwardRingMap B S hS g)) :
    IsQuasiAffineHom B S hS f.hom ↔ IsOpenImmersion B S hS g.left.hom :=
  ⟨fun hfqa ↦ isOpenImmersion_of_isQuasiAffineHom_affineOver B S hS f hfqa P g hring,
    fun hoi ↦ isQuasiAffineHom_of_isOpenImmersion_affineOver B S hS f hfqc P g hoi⟩

/-! ### The sufficiency direction of Stacks 086S, with 03M9 supplied -/

variable (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
  {X Y : AlgebraicSpaces B S hS}

/-- A quasi-compact, quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over `S` whose
canonical morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` of Stacks 081X is an open immersion is
quasi-affine.

The hypothesis `E` is an inhabitant of `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`,
which `AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`
proves uninhabited, so the statement is vacuous. -/
@[stacks 086S "proves only: the factorization is an open immersion implies f is quasi-affine — \
and presupposes AffineAlgebraAntiEquivalence, which this development proves uninhabited \
(not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart), so the statement is \
vacuous; the non-vacuous form is \
isQuasiAffineHom_of_isOpenImmersion_boundedRelativeSpecDirectImage"]
theorem isQuasiAffineHom_of_isOpenImmersion_qcqsDirectImageFactorizationMap_unconditional
    (f : Y ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (hoi : IsOpenImmersion B S hS
      (qcqsDirectImageFactorizationMap_unconditional B S hS E C f hfqc hfqs).left.hom) :
    IsQuasiAffineHom B S hS f.hom :=
  isQuasiAffineHom_of_isOpenImmersion_qcqsDirectImageFactorizationMap B S hS E C f hfqc hfqs hoi

/-! ### The sufficiency direction of Stacks 086S, for the bounded anti-equivalence -/

/-- Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces
over `S` whose direct-image algebra `f_* 𝒪_Y` has fewer than the big fppf site's cutoff sections
at every étale chart of `X`.  If some morphism `Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` over `X` is an
open immersion, then `f` is quasi-affine. -/
theorem isQuasiAffineHom_of_isOpenImmersion_boundedRelativeSpecDirectImage
    (Eb : BoundedAffineAlgebraAntiEquivalence B S hS) (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hbd : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (g : Over.mk f ⟶
      (Eb.relativeSpec (directImageAlgebra B S hS f
        (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs)) hbd).obj)
    (hoi : IsOpenImmersion B S hS g.left.hom) :
    IsQuasiAffineHom B S hS f.hom :=
  isQuasiAffineHom_of_isOpenImmersion_affineOver B S hS f hfqc _ g hoi

/-- Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces
over `S` whose direct-image algebra `f_* 𝒪_Y` has fewer than the big fppf site's cutoff sections
at every étale chart of `X`, and let `g : Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` be a morphism over
`X` whose map on direct-image algebras is an isomorphism.  If `f` is quasi-affine then `g` is an
open immersion. -/
theorem isOpenImmersion_of_isQuasiAffineHom_boundedRelativeSpecDirectImage
    (Eb : BoundedAffineAlgebraAntiEquivalence B S hS) (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hbd : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (g : Over.mk f ⟶
      (Eb.relativeSpec (directImageAlgebra B S hS f
        (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs)) hbd).obj)
    (hring : IsIso (pushforwardRingMap B S hS g))
    (hfqa : IsQuasiAffineHom B S hS f.hom) :
    IsOpenImmersion B S hS g.left.hom :=
  isOpenImmersion_of_isQuasiAffineHom_affineOver B S hS f hfqa _ g hring

/-- Let `f : Y ⟶ X` be a quasi-compact, quasi-separated morphism of algebraic spaces over `S` whose
direct-image algebra `f_* 𝒪_Y` has fewer than the big fppf site's cutoff sections at every étale
chart of `X`, and let `g : Y ⟶ \underline{Spec}_X(f_* 𝒪_Y)` be a morphism over `X` whose map on
direct-image algebras is an isomorphism. Then `f` is quasi-affine if and only if `g` is an open
immersion. -/
theorem isQuasiAffineHom_iff_isOpenImmersion_boundedRelativeSpecDirectImage
    (Eb : BoundedAffineAlgebraAntiEquivalence B S hS) (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hbd : AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS (Over.mk f)))
    (g : Over.mk f ⟶
      (Eb.relativeSpec (directImageAlgebra B S hS f
        (isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS f hfqc hfqs)) hbd).obj)
    (hring : IsIso (pushforwardRingMap B S hS g)) :
    IsQuasiAffineHom B S hS f.hom ↔ IsOpenImmersion B S hS g.left.hom :=
  isQuasiAffineHom_iff_isOpenImmersion_affineOver B S hS f hfqc _ g hring

end AlgebraicGeometry.Space

end
