module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quotient that is an algebraic space is presented by its relation

Let `S` be a scheme, let `U` and `R` be objects of the big fppf site of `S`, and let
`s, t : R ⟶ U` be a pair of morphisms whose associated pre-relation on `U ×_S U` is an étale
equivalence relation. Then `R` is the fibre product `U ×_{U/R} U`, unconditionally; and as
soon as the canonical map `U ⟶ U/R` is relatively representable it is surjective and étale
after every representable base change. When `U/R` is an algebraic space over `S` the canonical
map is relatively representable, and those three facts are the data of a presentation of `U/R`
by `U` and `R`.

## Main definitions

* `AlgebraicGeometry.Space.relation` is the pre-relation `R ⟶ U ×_S U` determined by `t`
  and `s`.
* `AlgebraicGeometry.Space.quotientMap` is the canonical map `h_U ⟶ U/R`.
* `AlgebraicGeometry.Space.quotientPresentation` is the resulting presentation.

## Main results

* `AlgebraicGeometry.Space.quotientMap_surjective` and
  `AlgebraicGeometry.Space.quotientMap_etale` are surjectivity and étaleness of the quotient
  map.
* `AlgebraicGeometry.Space.quotientMap_isPullback` identifies the relation with the kernel
  pair of the quotient map.
* `AlgebraicGeometry.Space.quotientPresheaf_isPullback` is the same statement before
  sheafification, where the quotient is a pointwise quotient of sets.

## Implementation notes

The quotient map is obtained from the identity point of `U` by Yoneda, so that its value on
a point `f : T ⟶ U` of the site is the class of `f` in the quotient sheaf.

Surjectivity and étaleness are stated with relative representability of the quotient map as
their hypothesis, which
`AlgebraicGeometry.Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace` derives from
algebraicity of the quotient. The kernel-pair statement has no hypothesis on the quotient.

## References

* [Stacks Project, Tag 02WV](https://stacks.math.columbia.edu/tag/02WV)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-- A commuting square of presheaves of types is a pullback as soon as, at each object, the
two maps out of the top left corner are jointly injective and every pair of elements with the
same image is hit. -/
private theorem isPullback_of_jointly_injective_of_exists
    {C : Type v} [Category.{w} C] {P X Z : Cᵒᵖ ⥤ Type u} (t s : P ⟶ X) (q : X ⟶ Z)
    (hcomm : t ≫ q = s ≫ q)
    (hinj : ∀ T (a b : P.obj T), t.app T a = t.app T b → s.app T a = s.app T b → a = b)
    (hex : ∀ T (x y : X.obj T), q.app T x = q.app T y → ∃ r, t.app T r = x ∧ s.app T r = y) :
    IsPullback t s q q := by
  let c : PullbackCone q q := PullbackCone.mk t s hcomm
  apply IsPullback.of_isLimit (c := c)
  apply evaluationJointlyReflectsLimits c
  intro T
  let ct : PullbackCone (q.app T) (q.app T) :=
    PullbackCone.mk (t.app T) (s.app T) (congr_app hcomm T)
  have hct : IsLimit ct := by
    apply (PullbackCone.isLimitEquivBijective ct).2
    constructor
    · intro a b hab
      exact hinj T a b (congrArg (fun x => x.val.1) hab) (congrArg (fun x => x.val.2) hab)
    · rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨r, hr₁, hr₂⟩ := hex T a b hab
      exact ⟨r, Subtype.ext (Prod.ext hr₁ hr₂)⟩
  exact (IsLimit.equivOfNatIsoOfIso
    (cospanCompIso ((evaluation Cᵒᵖ (Type u)).obj T) q q)
    (((evaluation Cᵒᵖ (Type u)).obj T).mapCone c) ct
    (PullbackCone.ext (Iso.refl _) (by
      change t.app T = 𝟙 _ ≫ t.app T
      simp) (by
      change s.app T = 𝟙 _ ≫ s.app T
      simp))).symm hct

/-- An internal equivalence relation is the kernel pair of the projection onto its quotient
presheaf. -/
theorem quotientPresheaf_isPullback
    {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] :
    IsPullback (targetMap F j) (sourceMap F j)
      (toQuotientPresheaf F j) (toQuotientPresheaf F j) := by
  let t := targetMap F j
  let s := sourceMap F j
  let q := toQuotientPresheaf F j
  have hj := (isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1
    (inferInstance : IsEquivalenceRelation j.target j.source)
  let e : EquivalenceRelation j.target j.source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  have hcomm : t ≫ q = s ≫ q :=
    (coequalizer.condition (sourceMap F j) (targetMap F j)).symm
  refine isPullback_of_jointly_injective_of_exists t s q hcomm ?_ ?_
  · intro X a b ht hs
    exact e.right_cancellation a b ht hs
  · intro X a b hab
    obtain ⟨r, hr₁, hr₂⟩ := (toQuotientPresheaf_apply_eq_iff_related F j hj.2 X.unop a b).1 hab
    exact ⟨r, hr₁, hr₂⟩

/-- Étaleness of morphisms of schemes is local on the target for the fppf precoverage. -/
@[sga "3 VIB 2.1.2" "special case", sga "4 IV 8.5.5" "special case"]
private theorem etale_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Etale.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  have : IsZariskiLocalAtTarget (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@Etale.{u} : MorphismProperty Scheme.{u})
  have : MorphismProperty.IsLocalAtTarget (@Etale.{u} : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
variable {R U : BigFppfOver B S hS} (s t : R ⟶ U)

/-- The pre-relation on `U` over `S` determined by a pair of morphisms `s, t : R ⟶ U` of
objects of the big fppf site of `S`, with `t` the target map and `s` the source map. -/
public noncomputable abbrev relation : PreRelation
    ((Over.post B.inclusion).obj R) ((Over.post B.inclusion).obj U) :=
  prod.lift ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)

/-- The canonical map from the presenting scheme to the quotient sheaf of its relation. -/
@[stacks 02WW "canonical quotient map"]
public noncomputable def quotientMap :
    yoneda.obj U ⟶
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj :=
  yonedaEquiv.symm
    ((toQuotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)).app (op U)
      (𝟙 ((Over.post B.inclusion).obj U)))

/-- The source map of the relation is the image of `s` in `Over S`. -/
private theorem relation_source
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (relation B S hS s t).source = (Over.post (X := B.obj hS) B.inclusion).map s :=
  prod.lift_snd _ _

/-- The target map of the relation is the image of `t` in `Over S`. -/
private theorem relation_target
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    (relation B S hS s t).target = (Over.post (X := B.obj hS) B.inclusion).map t :=
  prod.lift_fst _ _

/-- The quotient map sends a point `f : T ⟶ U` of the site to the class of `f` in the
quotient sheaf. -/
private theorem quotientMap_app_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    {T : BigFppfOver B S hS} (f : T ⟶ U) :
    (quotientMap B S hS s t).app (op T) f =
      (toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).app (op T)
        ((Over.post B.inclusion).map f) := by
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  change (quotientSheaf J F j).obj.map f.op
      ((toQuotientSheaf J F j).app (op U) (𝟙 (F.obj U))) =
    (toQuotientSheaf J F j).app (op T) (F.map f)
  exact (NatTrans.naturality_apply (toQuotientSheaf J F j) (op f) (𝟙 (F.obj U))).symm

/-- Two points of `U` with the same image under the quotient map are the target and the
source of a point of the relation scheme. -/
private theorem quotient_relation_lift
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    {T : BigFppfOver B S hS} (x y : T ⟶ U)
    (hxy : (quotientMap B S hS s t).app (op T) x =
      (quotientMap B S hS s t).app (op T) y) :
    ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = y := by
  classical
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  let : F.Full := by
    change (Over.post (X := B.obj hS) B.inclusion).Full
    infer_instance
  let : F.Faithful := by
    change (Over.post (X := B.obj hS) B.inclusion).Faithful
    infer_instance
  have hsource : j.source = F.map s := relation_source B S hS s t
  have htarget : j.target = F.map t := relation_target B S hS s t
  have hq : (toQuotientSheaf J F j).app (op T) (F.map y) =
      (toQuotientSheaf J F j).app (op T) (F.map x) := by
    rw [← quotientMap_app_eq B S hS s t y, ← quotientMap_app_eq B S hS s t x]
    exact hxy.symm
  have hRp : Presheaf.IsSheaf J (points F (F.obj R)) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS (F.obj R)
  have hUp : Presheaf.IsSheaf J (points F (F.obj U)) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS (F.obj U)
  have hpb := (isPullback_toQuotientSheaf_self J F j hRp hUp).map
    ((evaluation _ (Type u)).obj (op T))
  obtain ⟨r, hrt, hrs⟩ := Types.exists_of_isPullback hpb (F.map x) (F.map y) hq.symm
  change r ≫ j.target = F.map x at hrt
  change r ≫ j.source = F.map y at hrs
  refine ⟨F.preimage r, ?_, ?_⟩
  · apply F.map_injective
    simpa only [Functor.map_comp, Functor.map_preimage, ← htarget] using hrt
  · apply F.map_injective
    simpa only [Functor.map_comp, Functor.map_preimage, ← hsource] using hrs

/-- The quotient map coequalizes the two projections of the relation: a point of `R` has the
same class in the quotient sheaf whether it is read through the target or the source map. -/
private theorem yoneda_map_comp_quotientMap_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    yoneda.map t ≫ quotientMap B S hS s t = yoneda.map s ≫ quotientMap B S hS s t := by
  let J := BigFppfOver.topology B S hS
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  ext X f
  change (quotientMap B S hS s t).app X (f ≫ t) = (quotientMap B S hS s t).app X (f ≫ s)
  rw [quotientMap_app_eq B S hS s t (f ≫ t), quotientMap_app_eq B S hS s t (f ≫ s)]
  have h := congrArg (fun g => g (F.map f))
    (NatTrans.congr_app (sourceMap_toQuotientSheaf J F j) X)
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  simp only [sourceMap, targetMap, points, Functor.whiskerLeft_app, yoneda_map_app] at h
  change ((toQuotientSheaf J F j).app X) (F.map f ≫ j.source) =
    ((toQuotientSheaf J F j).app X) (F.map f ≫ j.target) at h
  rw [relation_source B S hS s t, relation_target B S hS s t] at h
  simpa only [Functor.map_comp] using h.symm

/-- The target and the source map of an étale equivalence relation are jointly injective on
points: two points of `R` with the same target and the same source agree. -/
private theorem relation_jointly_injective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    {T : BigFppfOver B S hS} {a b : T ⟶ R}
    (ht : a ≫ t = b ≫ t) (hs : a ≫ s = b ≫ s) : a = b := by
  classical
  let e : EquivalenceRelation (relation B S hS s t).target
      (relation B S hS s t).source :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  apply Functor.map_injective (Over.post (X := B.obj hS) B.inclusion)
  refine e.right_cancellation _ _ ?_ ?_
  · rw [relation_target B S hS s t, ← Functor.map_comp, ← Functor.map_comp, ht]
  · rw [relation_source B S hS s t, ← Functor.map_comp, ← Functor.map_comp, hs]

/-- The relation is the fibre product `U ×_{U/R} U`. Nothing is assumed about the quotient. -/
@[stacks 02WV "kernel pair"]
theorem quotientMap_isPullback
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    IsPullback (yoneda.map t) (yoneda.map s)
      (quotientMap B S hS s t) (quotientMap B S hS s t) := by
  classical
  let c := quotientMap B S hS s t
  have hcomm : yoneda.map t ≫ c = yoneda.map s ≫ c :=
    yoneda_map_comp_quotientMap_eq B S hS s t
  refine isPullback_of_jointly_injective_of_exists _ _ c hcomm ?_ ?_
  · intro X a b ht hs
    exact relation_jointly_injective B S hS s t ht hs
  · intro X x y hxy
    exact quotient_relation_lift B S hS s t x y hxy

/-- Any property of morphisms of schemes which is stable under base change and local at the
target for the fppf precoverage passes from the source map of the relation to the quotient
map. -/
private theorem quotientMap_property
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {R U : BigFppfOver B S hS} (s t : R ⟶ U)
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t))
    (hPs : P ((BigFppfOver.toScheme B S hS).map s)) :
    MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))
      (quotientMap B S hS s t) := by
  classical
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let Tsite := BigFppfOver.toScheme B S hS
  let F : C ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  let c := quotientMap B S hS s t
  let Q := (quotientSheaf J F j).obj
  let : F.Full := by
    change (Over.post (X := B.obj hS) B.inclusion).Full
    infer_instance
  let : F.Faithful := by
    change (Over.post (X := B.obj hS) B.inclusion).Faithful
    infer_instance
  have hlocalQ : Presheaf.IsLocallySurjective J (toQuotientSheaf J F j) :=
    quotientPoint_locally_surjective J F j
  let Qprop : MorphismProperty C := P.inverseImage Tsite
  apply MorphismProperty.relative_of_snd (F := yoneda) (P := Qprop) hrep
  intro V g
  let ξ := yonedaEquiv g
  let I : Sieve V := Presheaf.imageSieve (toQuotientSheaf J F j) ξ
  have hI : I ∈ J V := Presheaf.imageSieve_mem J (toQuotientSheaf J F j) ξ
  have hIbase : (Sieve.overEquiv V) I ∈ B.topology V.left := by
    change I ∈ B.topology.over (B.obj hS) V at hI
    exact (GrothendieckTopology.mem_over_iff B.topology I).1 hI
  obtain ⟨E, hE, hRefine⟩ := exists_covering_refining_sieve B hIbase
  have hEfp : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj V.left) := by
    have hEfppf : IsFppfCovering ⟨V.left, E⟩ := B.isFppfCovering_of_isCovering hE
    simpa [IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using hEfppf
  have hlocalComponent (i : E.I₀) :
      P (pullback.snd (Tsite.map (hrep.snd g)) (B.inclusion.map (E.f i))) := by
    let W : C := Over.mk (E.f i ≫ V.hom)
    let k : W ⟶ V := Over.homMk (E.f i)
    have hkI : I k := by
      apply (Sieve.overEquiv_iff I (E.f i)).1
      exact hRefine _ _ ⟨i⟩
    obtain ⟨z, hz⟩ := hkI
    let a : W ⟶ U := F.preimage z
    have hFa : F.map a = z := Functor.map_preimage F z
    have hLift : c.app (op W) a = Q.map k.op ξ := by
      rw [quotientMap_app_eq B S hS s t a, hFa]
      exact hz
    have hbase : yoneda.map a ≫ c = yoneda.map k ≫ g := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, ← yonedaEquiv_naturality g k, yonedaEquiv_yoneda_map]
      exact hLift
    let v := hrep.snd g
    have hV : IsPullback (hrep.fst g) (yoneda.map v) c g := hrep.isPullback g
    have hP₁C : IsPullback (pullback.fst v k) (pullback.snd v k) v k :=
      IsPullback.of_hasPullback v k
    have hP₁D : IsPullback (yoneda.map (pullback.fst v k))
        (yoneda.map (pullback.snd v k)) (yoneda.map v) (yoneda.map k) := hP₁C.map yoneda
    have hP₁F : IsPullback
        (yoneda.map (pullback.fst v k) ≫ hrep.fst g)
        (yoneda.map (pullback.snd v k)) c (yoneda.map k ≫ g) := hP₁D.paste_horiz hV
    have hP₂C : IsPullback (pullback.fst s a) (pullback.snd s a) s a :=
      IsPullback.of_hasPullback s a
    have hP₂D : IsPullback (yoneda.map (pullback.fst s a))
        (yoneda.map (pullback.snd s a)) (yoneda.map s) (yoneda.map a) := hP₂C.map yoneda
    have hKernel := quotientMap_isPullback B S hS s t
    have hP₂F : IsPullback
        (yoneda.map (pullback.fst s a) ≫ yoneda.map t)
        (yoneda.map (pullback.snd s a)) c (yoneda.map a ≫ c) := hP₂D.paste_horiz hKernel
    let eD := hP₁F.isoIsPullback _ _ (by simpa only [hbase] using hP₂F)
    let e := yoneda.preimageIso eD
    have he_snd : e.hom ≫ pullback.snd s a = pullback.snd v k := by
      apply yoneda.map_injective
      simp [e, eD]
    have hP₂Scheme : IsPullback (Tsite.map (pullback.fst s a))
        (Tsite.map (pullback.snd s a)) (Tsite.map s) (Tsite.map a) := hP₂C.map Tsite
    have hPs₂ : P (Tsite.map (pullback.snd s a)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hP₂Scheme hPs
    have he_snd' : Tsite.map e.hom ≫ Tsite.map (pullback.snd s a) =
        Tsite.map (pullback.snd v k) := by rw [← Tsite.map_comp, he_snd]
    have hP₁ : P (Tsite.map (pullback.snd v k)) :=
      (P.arrow_mk_iso_iff (Arrow.isoMk (Tsite.mapIso e) (Iso.refl _) he_snd')).2 hPs₂
    have hP₁Scheme : IsPullback (Tsite.map (pullback.fst v k))
        (Tsite.map (pullback.snd v k)) (Tsite.map v) (Tsite.map k) := hP₁C.map Tsite
    let eScheme := hP₁Scheme.isoIsPullback _ _
      (IsPullback.of_hasPullback (Tsite.map v) (Tsite.map k))
    have heScheme : eScheme.hom ≫ pullback.snd (Tsite.map v) (Tsite.map k) =
        Tsite.map (pullback.snd v k) := by
      simp [eScheme]
    exact (P.arrow_mk_iso_iff
      (Arrow.isoMk (f := Arrow.mk (Tsite.map (pullback.snd v k)))
        (g := Arrow.mk (pullback.snd (Tsite.map v) (Tsite.map k)))
        eScheme (Iso.refl _) heScheme)).1 hP₁
  have hdesc := MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (P := P) hEfp (f := Tsite.map (hrep.snd g))
  change P (Tsite.map (hrep.snd g))
  apply hdesc.mpr
  intro W e hp he
  rcases he with ⟨i₀⟩
  simpa [PreZeroHypercover.map] using hlocalComponent i₀

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The source map of an étale equivalence relation is surjective. -/
private theorem relation_source_surjective
    [IsEtaleEquivalenceRelation (relation B S hS s t)] :
    Surjective ((BigFppfOver.toScheme B S hS).map s) := by
  classical
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := relation B S hS s t
  let Tsite := BigFppfOver.toScheme B S hS
  let : F.Full := by
    change (Over.post (X := B.obj hS) B.inclusion).Full
    infer_instance
  let : F.Faithful := by
    change (Over.post (X := B.obj hS) B.inclusion).Faithful
    infer_instance
  have hEquiv : IsEquivalenceRelation j.target j.source := inferInstance
  obtain ⟨er⟩ := hEquiv.nonempty_equivalenceRelation
  let r : U ⟶ R := F.preimage er.r
  have hr : F.map r = er.r := Functor.map_preimage F er.r
  have hrs : r ≫ s = 𝟙 U := by
    apply Functor.map_injective F
    calc
      F.map (r ≫ s) = F.map r ≫ F.map s := by rw [Functor.map_comp]
      _ = er.r ≫ j.source := by
        rw [hr]
        exact (congrArg (fun q => er.r ≫ q) (relation_source B S hS s t)).symm
      _ = 𝟙 _ := er.reflexivity₂
      _ = F.map (𝟙 U) := by rfl
  have hcomp : Tsite.map r ≫ Tsite.map s = 𝟙 _ := by
    rw [← Tsite.map_comp, hrs]
    simp
  have : Surjective (Tsite.map r ≫ Tsite.map s) := by
    rw [hcomp]
    infer_instance
  exact Surjective.of_comp (Tsite.map r) (Tsite.map s)

/-- If the quotient sheaf is an algebraic space, then the quotient map is relatively
representable. -/
theorem relativelyRepresentable_quotientMap_of_isAlgebraicSpace
    (hQ : IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj) :
    yoneda.relativelyRepresentable (quotientMap B S hS s t) :=
  (Functor.relativelyRepresentable.diag_iff (F := yoneda)
    (X := (quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)).obj)).1
    hQ.diagonal_representable _

/-- The quotient map of an étale equivalence relation is surjective after every representable
base change, as soon as it is representable. -/
@[stacks 02WV "surjective"]
theorem quotientMap_surjective
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) :=
  quotientMap_property (@Surjective.{u}) B S hS s t hrep
    (relation_source_surjective B S hS s t)

/-- The quotient map of an étale equivalence relation is étale after every representable base
change, as soon as it is representable. -/
@[stacks 02WV "étale"]
theorem quotientMap_etale
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hrep : yoneda.relativelyRepresentable (quotientMap B S hS s t)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (quotientMap B S hS s t) := by
  let Tsite := BigFppfOver.toScheme B S hS
  have hsourceEtale : Etale (Tsite.map s) := by
    have hEt : Etale (relation B S hS s t).source.left := inferInstance
    rwa [relation_source B S hS s t] at hEt
  have := etale_isLocalAtTarget_fppf.{u}
  exact quotientMap_property (@Etale.{u}) B S hS s t hrep hsourceEtale

/-- An étale equivalence relation whose quotient sheaf is an algebraic space presents that
algebraic space. -/
@[stacks 02WV "presentation"]
noncomputable def quotientPresentation
    [IsEtaleEquivalenceRelation (relation B S hS s t)]
    (hQ : IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t)).obj) :
    Presentation B S hS _ hQ where
  U := U
  R := R
  target := t
  source := s
  isEtaleEquivalenceRelation := inferInstance
  toSpace := quotientMap B S hS s t
  surjective := quotientMap_surjective B S hS s t
    (relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t hQ)
  etale := quotientMap_etale B S hS s t
    (relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS s t hQ)
  isPullback := quotientMap_isPullback B S hS s t

end AlgebraicGeometry.Space

end
