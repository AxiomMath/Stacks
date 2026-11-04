module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FreeSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FreeSectionsPurity
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocallyProjectivePurity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover

/-!
# Purity along a flat fibre is universal

Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type quasi-coherent `𝒪_X`-module which is
flat over `S` at every point of the fibre `X_s`, and suppose `ℱ` is pure along `X_s`. Then `ℱ` is
universally pure along `X_s`.

## Main results

* `AlgebraicGeometry.isUniversallyPureAlong_of_isPureAlong` is Tag 05L5.

## Implementation notes

The proof is the source's. Purity along a fibre descends through a pointed base change which is
flat at the new distinguished point (Tag 05J9), and it ascends along a base change which is
quasi-finite at that point (Tag 05J7); an elementary étale neighbourhood `(S', s')` of `(S, s)`
and then the localization `Spec 𝒪_{S', s'}` are both of this kind, so it suffices to prove
universal purity over `Spec 𝒪_{S', s'}`.

Over that local base, Tag 05L1 supplies an affine `X'` with `X' ⟶ X ×_S Spec 𝒪_{S', s'}` étale,
with `X_s = g((X')_{s'})`, and with `Γ(X', g^*ℱ)` free. A free module over the global sections of
an affine scheme is projective, hence `g^*ℱ` has locally projective direct image and is
universally pure over `Spec 𝒪_{S', s'}` by Tag 05K6.

Purity along `X_s` makes every point of the relative assassin specialize into the fibre, so
Tag 05L1's covering of the fibre by the image of `X'` forces the whole relative assassin of the
localized situation into that image, the image of an étale morphism being open. Tag 05L4, applied
to the trivial elementary étale neighbourhood of each pointed base change, then turns that
containment into purity after the base change; the containment itself survives base change by the
unconditional half of Tag 05KL.

## References

* [Stacks Project, Tag 05L5](https://stacks.math.columbia.edu/tag/05L5)
* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
* [Stacks Project, Tag 05L1](https://stacks.math.columbia.edu/tag/05L1)
* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
* [Stacks Project, Tag 05KL](https://stacks.math.columbia.edu/tag/05KL)
* [Stacks Project, Tag 05J9](https://stacks.math.columbia.edu/tag/05J9)
* [Stacks Project, Tag 05J7](https://stacks.math.columbia.edu/tag/05J7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Quasi-coherence and finiteness of a pullback -/

/-- The pullback of a finite type module along a morphism of schemes is of finite type. -/
private lemma pullback_isFiniteType' {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) [F.IsFiniteType] :
    ((Scheme.Modules.pullback g).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F

/-- The pullback of a pullback of a module along composable morphisms is the pullback along the
composite. -/
private def pullbackPullbackIso {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z}
    (h : a ≫ b = c) (F : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj F) ≅
      (Scheme.Modules.pullback c).obj F :=
  (Scheme.Modules.pullbackComp a b).app F ≪≫ (Scheme.Modules.pullbackCongr h).app F

/-- Flatness of a module over the base at every point of a fibre is inherited by the pullback
along a base change, at every point of the corresponding fibre. -/
private lemma isFlatOverAt_fiberι_of_isPullback {X S S' X' : Scheme.{u}} {f : X ⟶ S}
    {b : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (hpb : IsPullback g' f' f b)
    (F : X.Modules) [F.IsQuasicoherent] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (s' : S') (hs : b.base s' = s) (x' : f'.fiber s') :
    IsFlatOverAt f'.toLRSHom.toShHom
      ((Scheme.Modules.pullback g').obj F) (f'.fiberι s' x') := by
  have hfx : f (g' (f'.fiberι s' x')) = s := by
    have hfiber : f' (f'.fiberι s' x') = s' := by
      have h := congrArg (fun k : f'.fiber s' ⟶ S' => k x') (f'.fiber_fac s')
      simpa [Scheme.Hom.comp_apply] using h
    calc
      f (g' (f'.fiberι s' x')) = b (f' (f'.fiberι s' x')) :=
        congrArg (fun k : X' ⟶ S => k (f'.fiberι s' x')) hpb.w
      _ = b s' := by rw [hfiber]
      _ = s := hs
  have hflatx := hflat ((f.fiberHomeo s).symm ⟨g' (f'.fiberι s' x'), hfx⟩)
  rw [f.fiberι_fiberHomeo_symm s ⟨_, hfx⟩] at hflatx
  let F₀ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := F
  let : F₀.IsQuasicoherent := show F.IsQuasicoherent from inferInstance
  exact modulePullback_isFlatOverAt hpb F₀ (f'.fiberι s' x') hflatx

/-! ### From free sections to local projectivity -/

/-- A quasi-coherent module on an affine scheme whose global sections are projective is locally
projective. -/
private alias isLocallyProjective_of_projective_globalSections :=
  Scheme.Modules.isLocallyProjective_of_projective_globalSections

/-- A module which is free over a ring is projective over the global sections of its spectrum,
the two actions being identified by the canonical isomorphism. -/
private lemma projective_of_free_over_spec_globalSections
    (R : CommRingCat.{u}) (N : Type u) [AddCommMonoid N] [Module R N]
    [Module Γ(Spec R, ⊤) N] [Module.Free R N]
    (hcompat : ∀ (r : R) (x : N), r • x = (Scheme.ΓSpecIso R).inv.hom r • x) :
    Module.Projective Γ(Spec R, ⊤) N := by
  let σ := CommRingCat.Hom.hom (Scheme.ΓSpecIso R).inv
  let σ' := CommRingCat.Hom.hom (Scheme.ΓSpecIso R).hom
  let : RingHomInvPair σ σ' := by
    constructor <;> ext x <;> simp [σ, σ']
  let : RingHomInvPair σ' σ := by
    constructor <;> ext x <;> simp [σ, σ']
  let e : N ≃ₛₗ[σ] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := hcompat }
  exact Module.Projective.of_equiv e

/-! ### Residue fields and fibres of a localized base -/

/-- The morphism of fibres induced by a chart of the base change, presented through the
factorization of its structure morphism. -/
private def chartFiberMap' {X S T Y : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S)
    (e : Y ⟶ pullback f a) (p : Y ⟶ T) (heq : e ≫ pullback.snd f a = p) (t : T) :
    p.fiber t ⟶ (pullback.snd f a).fiber t :=
  pullback.map p (T.fromSpecResidueField t) (pullback.snd f a)
    (T.fromSpecResidueField t) e (𝟙 _) (𝟙 _) (by simpa using heq.symm) (by simp)

/-- The morphism of fibres induced by a chart is compatible with the inclusions of the fibres. -/
private lemma chartFiberMap'_fiberι {X S T Y : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ S)
    (e : Y ⟶ pullback f a) (p : Y ⟶ T) (heq : e ≫ pullback.snd f a = p) (t : T) :
    chartFiberMap' f a e p heq t ≫ (pullback.snd f a).fiberι t = p.fiberι t ≫ e := by
  dsimp [chartFiberMap', Scheme.Hom.fiberι, pullback.map]
  exact pullback.lift_fst _ _ _

/-- A chart whose image over the closed point covers the fibre `X_s` covers the whole fibre of
the localized base change over that closed point. -/
private lemma closedFiber_chart_covers {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (U : EtaleNeighborhood S s) [U.IsElementary]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (.of (U.scheme.presheaf.stalk U.point))) (g : Y ⟶ X)
    (hcomm : g ≫ f = p ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
    (hcover : f ⁻¹' {s} =
      g '' (p ⁻¹' {IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)})) :
    ∀ x : (pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).fiber
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)),
      ∃ y : p.fiber (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)),
        (pullback.lift g p hcomm) (p.fiberι (IsLocalRing.closedPoint _) y) =
          (pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).fiberι _ x := by
  let a := U.scheme.fromSpecStalk U.point ≫ U.toBase
  let t : Spec (.of (U.scheme.presheaf.stalk U.point)) :=
    IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)
  let e := pullback.lift g p hcomm
  have heq : e ≫ pullback.snd f a = p := pullback.lift_snd _ _ _
  have hfst : e ≫ pullback.fst f a = g := pullback.lift_fst _ _ _
  have : IsIso (a.residueFieldMap t) := neighborhood_base_residueFieldMap_isIso U
  have : IsIso (baseChangeFiberMap f a t) := isIso_baseChangeFiberMap f a t
  intro x
  let z := baseChangeFiberMap f a t x
  have hat : a t = s := by
    show U.toBase (U.scheme.fromSpecStalk U.point t) = s
    rw [Scheme.fromSpecStalk_closedPoint, U.map_point]
  obtain ⟨y₀, hy₀, hgy₀⟩ : f.fiberι (a t) z ∈ g ''
      (p ⁻¹' {IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)}) := by
    rw [← hcover]
    show f (f.fiberι (a t) z) = s
    exact (Set.mem_singleton_iff.mp (f.fiberHomeo (a t) z).2).trans hat
  have hy₀' : p y₀ = t := hy₀
  let y : p.fiber t := (p.fiberHomeo t).symm ⟨y₀, hy₀'⟩
  have hyι : p.fiberι t y = y₀ := p.fiberι_fiberHomeo_symm t ⟨y₀, hy₀'⟩
  have hm : (chartFiberMap' f a e p heq t ≫ baseChangeFiberMap f a t) ≫
      f.fiberι (a t) = p.fiberι t ≫ e ≫ pullback.fst f a := by
    calc
      _ = chartFiberMap' f a e p heq t ≫ ((pullback.snd f a).fiberι t ≫
          pullback.fst f a) := by
        rw [Category.assoc, baseChangeFiberMap_comp_fiberι]
      _ = (p.fiberι t ≫ e) ≫ pullback.fst f a := by
        rw [← Category.assoc, chartFiberMap'_fiberι f a e p heq t]
  have hzchart : baseChangeFiberMap f a t (chartFiberMap' f a e p heq t y) = z := by
    apply (f.fiberι (a t)).isEmbedding.injective
    calc
      _ = ((chartFiberMap' f a e p heq t ≫ baseChangeFiberMap f a t) ≫
          f.fiberι (a t)) y := by simp [Category.assoc]
      _ = (p.fiberι t ≫ e ≫ pullback.fst f a) y :=
        congrArg (fun k : p.fiber t ⟶ X => k y) hm
      _ = (p.fiberι t ≫ g) y := by rw [hfst]
      _ = g y₀ := by simp [hyι]
      _ = f.fiberι (a t) z := hgy₀
  have hchart : chartFiberMap' f a e p heq t y = x :=
    (ConcreteCategory.bijective_of_isIso (baseChangeFiberMap f a t).base).1 hzchart
  refine ⟨y, ?_⟩
  have hh := congrArg (fun k : p.fiber t ⟶ pullback f a => k y)
    (chartFiberMap'_fiberι f a e p heq t)
  change (pullback.snd f a).fiberι t (chartFiberMap' f a e p heq t y) =
    e (p.fiberι t y) at hh
  rw [hchart] at hh
  exact hh.symm

/-! ### Specialization of the relative assassin under purity -/

/-- Over a localized base, purity along the closed fibre pulls the whole relative assassin into
any open set containing the closed fibre — here the image of an étale chart. -/
private lemma relativeAssassin_subset_range_of_closedFiber_subset
    {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S)
    (hpure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (e : Y ⟶ pullback f (S.fromSpecStalk s)) [Etale e]
    (hcover : ∀ x : (pullback.snd f (S.fromSpecStalk s)).fiber
        (IsLocalRing.closedPoint (S.presheaf.stalk s)),
      (pullback.snd f (S.fromSpecStalk s)).fiberι _ x ∈ Set.range e) :
    Stacks.Divisors.relativeAssassin (pullback.snd f (S.fromSpecStalk s))
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj F) ⊆
      Set.range e := by
  intro x hx
  let a := S.fromSpecStalk s
  let q := pullback.fst f a
  let fL := pullback.snd f a
  let t := IsLocalRing.closedPoint (S.presheaf.stalk s)
  have hx' : q x ∈ Stacks.Divisors.relativeAssassin f F :=
    relativeAssassin_pullback_subset_preimage f a F hx
  have hsp : f.base (q x) ⤳ s := by
    have h := (IsLocalRing.specializes_closedPoint (fL x)).map a.continuous
    have hw : f (q x) = a (fL x) :=
      congrArg (fun k : pullback f a ⟶ S => k x) pullback.condition
    rw [hw]
    simpa [a, Scheme.fromSpecStalk_closedPoint] using h
  obtain ⟨y, hxy⟩ := exists_specializes_fiberι_of_isPureAlong
    ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) hpure hx' hsp
  obtain ⟨z, hzq, hzf⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := a) (f.fiberι s y) t (by
      rw [show a t = s from Scheme.fromSpecStalk_closedPoint]
      exact (f.fiberHomeo s y).2)
  have hxz : x ⤳ z :=
    (inferInstance : IsPreimmersion q).isEmbedding.isInducing.specializes_iff.mp (by rwa [hzq])
  obtain ⟨y, hy⟩ := hcover ((fL.fiberHomeo t).symm ⟨z, hzf⟩)
  exact hxz.mem_open e.isOpenMap.isOpen_range
    ⟨y, hy.trans (fL.fiberι_fiberHomeo_symm t ⟨z, hzf⟩)⟩

/-! ### Purity from an étale cover of the relative assassin -/

/-- Universal purity along a fibre can be tested on the canonical pullbacks. -/
private lemma isUniversallyPureAlong_of_canonical_baseChange (P : PrePureSituation.{u})
    (h : ∀ (T : Scheme.{u}) (b : T ⟶ P.S) (t : T), b.base t = P.s →
      ∃ (hFT : ((Scheme.Modules.pullback (pullback.fst P.f b)).obj P.F).IsFiniteType)
        (hQC : ((Scheme.Modules.pullback (pullback.fst P.f b)).obj P.F).IsQuasicoherent),
        IsPureAlong
          ({ S := T, X := pullback P.f b, f := pullback.snd P.f b
             locallyOfFiniteType := inferInstance
             F := (Scheme.Modules.pullback (pullback.fst P.f b)).obj P.F
             isFiniteType := hFT, isQuasicoherent := hQC, s := t } :
            PrePureSituation.{u})) :
    IsUniversallyPureAlong P := by
  intro D hD
  obtain ⟨hFT, hQC, hp⟩ := h D.T D.g D.t D.mapsToChosenPoint
  have : LocallyOfFiniteType (pullback.snd P.f D.g) :=
    inferInstance
  let Q : PrePureSituation.{u} :=
    { S := D.T, X := pullback P.f D.g, f := pullback.snd P.f D.g
      F := (Scheme.Modules.pullback (pullback.fst P.f D.g)).obj P.F
      isFiniteType := hFT, isQuasicoherent := hQC, s := D.t }
  let j := pullback.lift D.toX D.toT D.isPullback.w
  have hj : j ≫ pullback.snd P.f D.g = D.toT := pullback.lift_snd _ _ _
  have hjpb : IsPullback j D.toT (pullback.snd P.f D.g) (𝟙 D.T) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst P.f D.g)
      (h₂₂ := D.g) (v₁₃ := P.f)
    · simpa only [j, pullback.lift_fst, Category.id_comp] using D.isPullback
    · simpa using hj
    · exact IsPullback.of_hasPullback _ _
  let E : ImpurityDiagram Q :=
    { T := D.T, g := 𝟙 _, t' := D.t', t := D.t
      specializes := D.specializes, mapsToChosenPoint := rfl
      X_T := D.X_T, toX := j, toT := D.toT, isPullback := hjpb
      xi := D.xi, xi_liesOver := D.xi_liesOver }
  refine hp E inferInstance (EtaleNeighborhood.isElementary_self D.T D.t) ⟨?_, hD.2⟩
  show D.xi ∈ Stacks.Divisors.relativeAssassin D.toT ((Scheme.Modules.pullback j).obj Q.F)
  have e : (Scheme.Modules.pullback j).obj Q.F ≅ D.pulledBack P :=
    pullbackPullbackIso (pullback.lift_fst _ _ _) P.F
  rw [relativeAssassin_eq_of_moduleIso _ e]
  exact hD.1

/-- **Tag 05L4 at the trivial neighbourhood.** If a finite type quasi-coherent module is flat
along the chosen fibre, its relative assassin is covered by an étale morphism over the base along
which its pullback is pure along the corresponding fibre, then it is pure along that fibre. -/
private lemma isPureAlong_of_etale_cover_of_relativeAssassin_subset
    {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S)
    (p : Y ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p]
    (e : Y ⟶ X) [Etale e] (he : e ≫ f = p)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hFT : ((Scheme.Modules.pullback e).obj F).IsFiniteType)
    (hQC : ((Scheme.Modules.pullback e).obj F).IsQuasicoherent)
    (hp : IsPureAlong
      ({ S := S, X := Y, f := p, F := (Scheme.Modules.pullback e).obj F
         isFiniteType := hFT, isQuasicoherent := hQC, s := s } : PrePureSituation.{u}))
    (hcover : Stacks.Divisors.relativeAssassin f F ⊆ Set.range e) :
    IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) := by
  let U : EtaleNeighborhood S s :=
    { scheme := S, point := s, toBase := 𝟙 S, map_point := rfl }
  have hcomm : e ≫ f = p ≫ U.toBase := by simpa [U] using he
  have hiso : IsIso U.toBase := show IsIso (𝟙 S) from inferInstance
  have : IsIso (pullback.fst f U.toBase) :=
    (IsPullback.of_hasPullback f U.toBase).isIso_fst_of_isIso
  have key : ∀ z ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F),
      ∃ y, pullback.lift e p hcomm y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hcover (relativeAssassin_pullback_subset_preimage f U.toBase F hz)
    refine ⟨y, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (pullback.fst f U.toBase).base).1
    simpa only [← Scheme.Hom.comp_apply, pullback.lift_fst] using hy
  refine (isPureAlong_iff_relativeAssassin_specializing_mem_range f F s U
    (EtaleNeighborhood.isElementary_self S s) p e hcomm hflat hp ?_).2 ?_
  · intro x hx
    exact key _ ((Stacks.Divisors.mem_relativeAssassin _ _ _).2 ⟨U.point, x, hx, rfl⟩)
  · intro z hz _
    exact key z hz

/-- Universal purity along the chosen fibre from an étale cover of the relative assassin along
which the module is universally pure relative to the base. -/
private lemma isUniversallyPureAlong_of_etale_cover_of_relativeAssassin_subset
    {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S)
    (p : Y ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p]
    (e : Y ⟶ X) [Etale e] (he : e ≫ f = p)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    [hFT : ((Scheme.Modules.pullback e).obj F).IsFiniteType]
    [hQC : ((Scheme.Modules.pullback e).obj F).IsQuasicoherent]
    (hp : IsUniversallyPureRelative p ((Scheme.Modules.pullback e).obj F))
    (hcover : Stacks.Divisors.relativeAssassin f F ⊆ Set.range e) :
    IsUniversallyPureAlong ({ S := S, X := X, f := f, F := F, s := s } :
      PrePureSituation.{u}) := by
  apply isUniversallyPureAlong_of_canonical_baseChange
  intro B b t ht
  let q := pullback.fst f b
  let fB := pullback.snd f b
  let FB := (Scheme.Modules.pullback q).obj F
  have : FB.IsFiniteType := pullback_isFiniteType' q F
  have : FB.IsQuasicoherent := pullback_isQuasicoherent' q F
  let pB := pullback.snd p b
  let r := pullback.fst p b
  let eB : pullback p b ⟶ pullback f b :=
    pullback.map p b f b e (𝟙 B) (𝟙 S) (by simpa using he.symm) (by simp)
  have heB : eB ≫ fB = pB := by
    simp only [eB, fB, pB, pullback.map, pullback.lift_snd, Category.comp_id]
  have heBq : eB ≫ q = r ≫ e := by
    simp only [eB, q, r, pullback.map, pullback.lift_fst]
  have hpb : IsPullback r eB e q := by
    apply IsPullback.of_bot (v₂₂ := f) (v₂₁ := fB) (h₃₁ := b)
    · simpa only [he, heB] using (IsPullback.of_hasPullback p b)
    · exact heBq.symm
    · exact IsPullback.of_hasPullback f b
  have : Etale eB := MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb inferInstance
  let G := (Scheme.Modules.pullback e).obj F
  let GB := (Scheme.Modules.pullback eB).obj FB
  have : G.IsFiniteType := hFT
  have : G.IsQuasicoherent := hQC
  have : GB.IsFiniteType := pullback_isFiniteType' eB FB
  have : GB.IsQuasicoherent := pullback_isQuasicoherent' eB FB
  have eG : GB ≅ (Scheme.Modules.pullback r).obj G :=
    pullbackPullbackIso heBq F ≪≫ (pullbackPullbackIso rfl F).symm
  have hpB : IsPureAlong ({ S := B, X := pullback p b, f := pB, F := GB, s := t } :
      PrePureSituation.{u}) :=
    (isUniversallyPureRelative_iff_forall_baseChange_isPureRelative p G).1
      hp pB GB b r (IsPullback.of_hasPullback p b) eG t
  refine ⟨inferInstance, inferInstance,
    isPureAlong_of_etale_cover_of_relativeAssassin_subset fB FB t pB eB heB
      (isFlatOverAt_fiberι_of_isPullback (IsPullback.of_hasPullback f b) F s hflat t ht)
      inferInstance inferInstance hpB ?_⟩
  intro x hx
  have hx' := hcover (relativeAssassin_pullback_subset_preimage f b F hx)
  show x ∈ Set.range eB
  dsimp only [eB]
  rw [Scheme.Pullback.range_map]
  exact ⟨hx', ⟨pullback.snd f b x, rfl⟩⟩

/-! ### Tag 05L5 -/

/-- **Stacks Project, Tag 05L5.** Let `f : X ⟶ S` be of finite type, let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module, and let `s : S`. If `ℱ` is flat over `S` at every point of the fibre
`X_s` and pure along `X_s`, then `ℱ` is universally pure along `X_s`.

The inputs are Tag 05L1, which produces an affine étale chart of the whole fibre with free
sections after an elementary étale localization of the base, Tag 05K6, which makes that chart
universally pure over the local base, Tag 05L4, which converts the resulting containment of the
relative assassin into purity after an arbitrary base change, the unconditional half of Tag 05KL,
which propagates that containment along a base change, and Tags 05J7 and 05J9, which transport
purity and universal purity along the elementary étale neighbourhood and the localization. -/
@[stacks 05L5]
public theorem isUniversallyPureAlong_of_isPureAlong
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})) :
    IsUniversallyPureAlong ({ S := S, X := X, f := f, F := F, s := s } :
      PrePureSituation.{u}) := by
  classical
  obtain ⟨U, hU, X', q, g, hcomm, hEtale, hfiber, hAffine, hfree⟩ :=
    exists_elementaryEtaleNeighborhood_free_sections_along_fibre_of_finiteType f F s hflat
  have : U.IsElementary := hU
  have : IsAffine X' := hAffine
  let R := CommRingCat.of (U.scheme.presheaf.stalk U.point)
  let F' := (Scheme.Modules.pullback g).obj F
  let : Module R Γ(F', ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  have : F'.IsFiniteType := pullback_isFiniteType' g F
  have : F'.IsQuasicoherent := pullback_isQuasicoherent' g F
  have : IsAffineHom q := inferInstance
  let aU := U.scheme.fromSpecStalk U.point
  let fU := pullback.snd f U.toBase
  let qU := pullback.fst f U.toBase
  let FU := (Scheme.Modules.pullback qU).obj F
  have : FU.IsFiniteType := pullback_isFiniteType' qU F
  have : FU.IsQuasicoherent := pullback_isQuasicoherent' qU F
  let fT := pullback.snd fU aU
  let r := pullback.fst fU aU
  let FT := (Scheme.Modules.pullback r).obj FU
  have : FT.IsFiniteType := pullback_isFiniteType' r FU
  have : FT.IsQuasicoherent := pullback_isQuasicoherent' r FU
  let eU : X' ⟶ pullback f U.toBase :=
    pullback.lift g (q ≫ aU) (by simpa [aU, Category.assoc] using hcomm)
  have heU : eU ≫ fU = q ≫ aU := pullback.lift_snd _ _ _
  have heUq : eU ≫ qU = g := pullback.lift_fst _ _ _
  let eT : X' ⟶ pullback fU aU := pullback.lift eU q heU
  have heT : eT ≫ fT = q := pullback.lift_snd _ _ _
  have heTr : eT ≫ r = eU := pullback.lift_fst _ _ _
  have houter : IsPullback (r ≫ qU) fT f (aU ≫ U.toBase) :=
    (IsPullback.of_hasPullback fU aU).paste_horiz (IsPullback.of_hasPullback f U.toBase)
  let n := houter.isoPullback.hom
  have hnq : n ≫ pullback.fst f (aU ≫ U.toBase) = r ≫ qU := by simp [n]
  have hnf : n ≫ pullback.snd f (aU ≫ U.toBase) = fT := by simp [n]
  have heTn : eT ≫ n = pullback.lift g q hcomm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnq, ← Category.assoc, heTr, heUq, pullback.lift_fst]
    · rw [Category.assoc, hnf, heT, pullback.lift_snd]
  have heT_eq : eT = pullback.lift g q hcomm ≫ inv n := by
    rw [← heTn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Etale eT := by rw [heT_eq]; infer_instance
  have hpLFT : LocallyOfFiniteType q := by
    have hcomp : LocallyOfFiniteType (eT ≫ fT) := by rw [heT_eq]; infer_instance
    rwa [heT] at hcomp
  have : LocallyOfFiniteType q := hpLFT
  have hfreePush : Module.Free (R := R) Γ((Scheme.Modules.pushforward q).obj F', ⊤) := by
    show Module.Free (R := R) Γ(F', ⊤)
    exact hfree
  let : Module.Free (R := R) Γ((Scheme.Modules.pushforward q).obj F', ⊤) := hfreePush
  have : ((Scheme.Modules.pushforward q).obj F').IsQuasicoherent := inferInstance
  have hproj : Module.Projective Γ(Spec R, ⊤)
      Γ((Scheme.Modules.pushforward q).obj F', ⊤) := by
    apply projective_of_free_over_spec_globalSections R
    intro _ _
    rfl
  have hlocproj : Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pushforward q).obj F') :=
    isLocallyProjective_of_projective_globalSections _ hproj
  have hpureRel : IsUniversallyPureRelative q F' :=
    isUniversallyPureRelative_of_pushforward_isLocallyProjective q F' hlocproj
  let FTChart := (Scheme.Modules.pullback eT).obj FT
  have : FTChart.IsFiniteType := pullback_isFiniteType' eT FT
  have : FTChart.IsQuasicoherent := pullback_isQuasicoherent' eT FT
  have hFTChartIso : FTChart ≅ F' :=
    pullbackPullbackIso heTr FU ≪≫ pullbackPullbackIso heUq F
  have hpureRelT : IsUniversallyPureRelative q FTChart := by
    intro t D hD
    refine hpureRel t
      { T := D.T, g := D.g, t' := D.t', t := D.t, specializes := D.specializes
        mapsToChosenPoint := D.mapsToChosenPoint, X_T := D.X_T, toX := D.toX
        toT := D.toT, isPullback := D.isPullback, xi := D.xi
        xi_liesOver := D.xi_liesOver } ⟨?_, hD.2⟩
    show D.xi ∈ Stacks.Divisors.relativeAssassin D.toT
      ((Scheme.Modules.pullback D.toX).obj F')
    rw [← relativeAssassin_eq_of_moduleIso D.toT
      ((Scheme.Modules.pullback D.toX).mapIso hFTChartIso)]
    exact hD.1
  have hqfU : quasiFiniteAt U.toBase U.point :=
    (forall_quasiFiniteAt_iff U.toBase).2 (locallyQuasiFinite_of_etale U.toBase) U.point
  have hpureU : IsPureAlong
      ({ S := U.scheme, X := pullback f U.toBase, f := fU, F := FU, s := U.point } :
        PrePureSituation.{u}) :=
    isPureAlong_of_quasiFiniteAt_of_isPureAlong
      (P := ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
      U.toBase U.map_point qU (IsPullback.of_hasPullback f U.toBase) (Iso.refl _) hqfU hpure
  let t : Spec R := IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)
  have hcoverT : ∀ x : fT.fiber t, fT.fiberι t x ∈ Set.range eT := by
    intro x
    let z := n (fT.fiberι t x)
    have hzf : (pullback.snd f (aU ≫ U.toBase)) z = t := by
      show (n ≫ pullback.snd f (aU ≫ U.toBase)) (fT.fiberι t x) = t
      rw [hnf]
      exact (fT.fiberHomeo t x).2
    let zf := ((pullback.snd f (aU ≫ U.toBase)).fiberHomeo t).symm ⟨z, hzf⟩
    obtain ⟨y, hy⟩ := closedFiber_chart_covers f s U X' q g hcomm hfiber zf
    refine ⟨q.fiberι t y, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso n.base).1
    show (eT ≫ n) (q.fiberι t y) = z
    rw [heTn]
    calc
      _ = (pullback.snd f (aU ≫ U.toBase)).fiberι t zf := hy
      _ = z := Scheme.Hom.fiberι_fiberHomeo_symm _ _ _
  have hcover : Stacks.Divisors.relativeAssassin fT FT ⊆ Set.range eT :=
    relativeAssassin_subset_range_of_closedFiber_subset fU FU U.point hpureU eT hcoverT
  have hflatU := isFlatOverAt_fiberι_of_isPullback (IsPullback.of_hasPullback f U.toBase)
    F s hflat U.point U.map_point
  have hflatT := isFlatOverAt_fiberι_of_isPullback (IsPullback.of_hasPullback fU aU)
    FU U.point hflatU t Scheme.fromSpecStalk_closedPoint
  have hUniversalT := isUniversallyPureAlong_of_etale_cover_of_relativeAssassin_subset
    fT FT t q eT heT hflatT hpureRelT hcover
  have : Flat aU := flat_fromSpecStalk U.scheme U.point
  have hUniversalU :=
    universallyPureAlong_of_flatPointedBaseChange
      ({ X := pullback f U.toBase, S := U.scheme, f := fU, F := FU, s := U.point
         S' := Spec R, s' := t, g := aU, mapsTo := Scheme.fromSpecStalk_closedPoint
         flatAt := Flat.stalkMap aU t } : FlatPointedBaseChangeSituation.{u}) hUniversalT
  exact universallyPureAlong_of_flatPointedBaseChange
    ({ X := X, S := S, f := f, F := F, s := s, S' := U.scheme, s' := U.point
       g := U.toBase, mapsTo := U.map_point
       flatAt := Flat.stalkMap U.toBase U.point } : FlatPointedBaseChangeSituation.{u})
    hUniversalU

end AlgebraicGeometry

end
