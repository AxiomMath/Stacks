module

public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePointsBaseChangeRing
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePointsFiniteAutomorphisms

/-!
# The glued curve over the dual numbers and its infinitesimal automorphism

Let `k` be a field, `a₀, a₁, a₂ ∈ k` pairwise distinct, and `X = ℙ¹_k ⨿_T ℙ¹_k` the curve obtained
by gluing two projective lines along the three double points `T = ∐ᵢ Spec(k[t]/(t - aᵢ)²)`. Let
`A = k[ε]` be the dual numbers and `X_A = X ×_{Spec k} Spec A`.

**`X_A` is again two projective lines glued along three double points**, now over `A`: it is the
pushout of `ℙ¹_A ← T_A → ℙ¹_A`, where `T_A = ∐ᵢ Spec(A[t]/(t - aᵢ)²)`.

When `k` has characteristic `2`, the translation `t ↦ t + ε` of `ℙ¹_A` maps `T_A` into itself,
because `(t + ε - a)² = (t - a)² + 2 ε (t - a) + ε² = (t - a)²`. It therefore induces an
automorphism of the pushout `X_A` over `A`: **the automorphism `t ↦ t + ε` of the equalizer
diagram extends to an automorphism of `X` over `A`.** It is not the identity, since it moves the
`A`-point `t = 0` of the first copy of `ℙ¹_A` to the `A`-point `t = ε`.

## Main definitions

* `AlgebraicGeometry.gluedCurveDualNumbers`: the base change `X_A`.
* `AlgebraicGeometry.gluedCurveDualNumbersComponent`: the two copies of `ℙ¹_A` in `X_A`.
* `AlgebraicGeometry.doublePointsDualNumbersToProjectiveLine`: the three double points over `A`
  inside `ℙ¹_A`.
* `AlgebraicGeometry.gluedCurveDualNumbersAut`: **the automorphism of `X_A` over `A` extending
  `t ↦ t + ε`.**

## Main results

* `AlgebraicGeometry.isPullback_gluedCurveDualNumbersComponent`: the copies of `ℙ¹_A` are the base
  changes of the copies of `ℙ¹_k`.
* `AlgebraicGeometry.isPullback_doublePointsDualNumbers`: the three double points over `A` are the
  base change of the three double points over `k`.
* `AlgebraicGeometry.isPushout_gluedCurveDualNumbers`: `X_A` is the pushout of two copies of
  `ℙ¹_A` along the three double points over `A`.
* `AlgebraicGeometry.gluedCurveDualNumbersComponent_comp_aut`: the automorphism is the
  translation on each copy of `ℙ¹_A`.
* `AlgebraicGeometry.projectiveLineXChart_comp_gluedCurveDualNumbersAut`: on the affine lines the
  automorphism is the substitution `t ↦ t + ε` of the equalizer diagram.
* `AlgebraicGeometry.gluedCurveDualNumbersAut_ne_one`: the automorphism is not the identity.

## References

* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (pts : Fin 3 → k) (hpts : Function.Injective pts)

/-- The structure morphism `Spec k[ε] ⟶ Spec k` of the dual numbers. -/
abbrev dualNumbersToBase : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- `Spec k[ε] ⟶ Spec k` is flat. -/
theorem flat_dualNumbersToBase : Flat (dualNumbersToBase k) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

/-- `Spec k[ε] ⟶ Spec k` is finite. -/
theorem isFinite_dualNumbersToBase : IsFinite (dualNumbersToBase k) := by
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact inferInstanceAs (Module.Finite k (k × k))

/-- **The glued curve over the dual numbers**, `X_A = X ×_{Spec k} Spec k[ε]`. -/
abbrev gluedCurveDualNumbers : Scheme.{u} :=
  pullback (gluedCurveToBase k pts hpts) (dualNumbersToBase k)

/-- The base change morphism `ℙ¹_{k[ε]} ⟶ ℙ¹_k`. -/
abbrev projectiveLineDualNumbersMap : projectiveLine (DualNumber k) ⟶ projectiveLine k :=
  projectiveLineMap (algebraMap k (DualNumber k))

/-- The two copies of `ℙ¹_{k[ε]}` in `X_A`, the base changes of the two copies of `ℙ¹_k`. -/
def gluedCurveDualNumbersComponent (b : Bool) :
    projectiveLine (DualNumber k) ⟶ gluedCurveDualNumbers k pts hpts :=
  pullback.lift (projectiveLineDualNumbersMap k ≫ gluedCurveComponent k pts hpts b)
    (projectiveLine (DualNumber k) ↘ Spec (.of (DualNumber k))) (by
      rw [Category.assoc, gluedCurveComponent_comp_toBase,
        projectiveLineMap_comp_structureMorphism])

/-- The first projection of `X_A` restricted to a copy of `ℙ¹_{k[ε]}` is the base change map to
`ℙ¹_k` followed by the corresponding copy in `X`. -/
@[reassoc (attr := simp)]
theorem gluedCurveDualNumbersComponent_fst (b : Bool) :
    gluedCurveDualNumbersComponent k pts hpts b ≫ pullback.fst _ _ =
      projectiveLineDualNumbersMap k ≫ gluedCurveComponent k pts hpts b :=
  pullback.lift_fst _ _ _

/-- The structure morphism of `X_A` to `Spec k[ε]` restricts on each copy of `ℙ¹_{k[ε]}` to its
structure morphism. -/
@[reassoc (attr := simp)]
theorem gluedCurveDualNumbersComponent_snd (b : Bool) :
    gluedCurveDualNumbersComponent k pts hpts b ≫ pullback.snd _ _ =
      projectiveLine (DualNumber k) ↘ Spec (.of (DualNumber k)) :=
  pullback.lift_snd _ _ _

/-- **The copies of `ℙ¹_{k[ε]}` are the base changes of the copies of `ℙ¹_k`.** -/
theorem isPullback_gluedCurveDualNumbersComponent (b : Bool) :
    IsPullback (gluedCurveDualNumbersComponent k pts hpts b) (projectiveLineDualNumbersMap k)
      (pullback.fst (gluedCurveToBase k pts hpts) (dualNumbersToBase k))
      (gluedCurveComponent k pts hpts b) := by
  refine IsPullback.of_right ?_ (gluedCurveDualNumbersComponent_fst k pts hpts b)
    (IsPullback.of_hasPullback (gluedCurveToBase k pts hpts) (dualNumbersToBase k)).flip
  rw [gluedCurveDualNumbersComponent_snd, gluedCurveComponent_comp_toBase]
  exact (isPullback_projectiveLineMap (algebraMap k (DualNumber k))).flip

/-! ### The three double points over the dual numbers -/

/-- The three double points `∐ᵢ Spec(k[ε][t]/(t - aᵢ)²)` over the dual numbers. -/
abbrev doublePointsDualNumbers : Scheme.{u} :=
  Spec (.of (DoublePoints (algebraMap k (DualNumber k) ∘ pts)))

/-- The three double points over the dual numbers inside `ℙ¹_{k[ε]}`. -/
def doublePointsDualNumbersToProjectiveLine :
    doublePointsDualNumbers k pts ⟶ projectiveLine (DualNumber k) :=
  Spec.map (CommRingCat.ofHom (doublePointsMk _)) ≫ projectiveLineXChart (DualNumber k)

/-- The projection of the three double points over the dual numbers to those over `k`. -/
def doublePointsDualNumbersProjection : doublePointsDualNumbers k pts ⟶ doublePointsScheme k pts :=
  Spec.map (CommRingCat.ofHom (doublePointsMap (algebraMap k (DualNumber k)) pts))

include hpts in
/-- The pairwise differences of distinct points of a field are units. -/
theorem isUnit_sub_of_injective (i j : Fin 3) (hij : i ≠ j) : IsUnit (pts j - pts i) :=
  isUnit_iff_ne_zero.2 (sub_ne_zero.2 (hpts.ne hij.symm))

include hpts in
/-- **The three double points over the dual numbers are the base change of the three double
points over `k`**: the preimage of `T ⊂ ℙ¹_k` in `ℙ¹_{k[ε]}`. -/
theorem isPullback_doublePointsDualNumbers :
    IsPullback (doublePointsDualNumbersToProjectiveLine k pts)
      (doublePointsDualNumbersProjection k pts) (projectiveLineDualNumbersMap k)
      (doublePointsToProjectiveLine k pts) := by
  have hc := isPullback_projectiveLineXChart_projectiveLineHom (algebraMap k (DualNumber k)) X X
    toLaurent_X_mul_overlapInverseCoordinate_X (dvd_refl X)
  rw [eval₂RingHom_C_comp_X] at hc
  have ha := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_doublePointsMk
    (algebraMap k (DualNumber k)) pts (isUnit_sub_of_injective k pts hpts))).flip
  exact ha.paste_horiz hc

/-! ### The glued curve over the dual numbers is a pushout -/

/-- The projection `X_A ⟶ X`, followed by the identification of `X` with the pushout scheme
`pushoutScheme (gluedCurveSituation k pts hpts)`. -/
abbrev gluedCurveDualNumbersOver : gluedCurveDualNumbers k pts hpts ⟶
    pushoutScheme (gluedCurveSituation k pts hpts) :=
  pullback.fst (gluedCurveToBase k pts hpts) (dualNumbersToBase k) ≫
    (gluedCurveIsoPushoutScheme k pts hpts).inv

/-- The morphism `X_A ⟶ X` is flat, separated, locally of finite type and locally quasi-finite. -/
theorem gluedCurveDualNumbersOver_properties :
    Flat (gluedCurveDualNumbersOver k pts hpts) ∧
      IsSeparated (gluedCurveDualNumbersOver k pts hpts) ∧
        LocallyOfFiniteType (gluedCurveDualNumbersOver k pts hpts) ∧
          LocallyQuasiFinite (gluedCurveDualNumbersOver k pts hpts) := by
  have := flat_dualNumbersToBase k
  have := isFinite_dualNumbersToBase k
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A copy of `ℙ¹_{k[ε]}` is the preimage in `X_A` of a copy of `ℙ¹_k` in the pushout scheme, if
the latter is the copy in `X` followed by the identification with the pushout scheme. -/
private theorem isPullback_gluedCurveDualNumbersComponent_over (b : Bool)
    {g : projectiveLine k ⟶ pushoutScheme (gluedCurveSituation k pts hpts)}
    (e : g = gluedCurveComponent k pts hpts b ≫ (gluedCurveIsoPushoutScheme k pts hpts).inv) :
    IsPullback (gluedCurveDualNumbersComponent k pts hpts b) (projectiveLineDualNumbersMap k)
      (gluedCurveDualNumbersOver k pts hpts) g := by
  rw [e]
  exact (isPullback_gluedCurveDualNumbersComponent k pts hpts b).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (gluedCurveIsoPushoutScheme k pts hpts).symm (by simp) (by simp)
    (by simp) (by simp)

/-- The first copy of `ℙ¹_{k[ε]}` is the preimage in `X_A` of the first copy of `ℙ¹_k` in the
pushout scheme. -/
theorem isPullback_gluedCurveDualNumbersComponent_over_false :
    IsPullback (gluedCurveDualNumbersComponent k pts hpts false) (projectiveLineDualNumbersMap k)
      (gluedCurveDualNumbersOver k pts hpts) (pushoutInl (gluedCurveSituation k pts hpts)) :=
  isPullback_gluedCurveDualNumbersComponent_over k pts hpts false
    ((Iso.comp_inv_eq _).2 (pushoutInl_gluedCurveIsoPushoutScheme_hom k pts hpts).symm).symm

/-- The second copy of `ℙ¹_{k[ε]}` is the preimage in `X_A` of the second copy of `ℙ¹_k` in the
pushout scheme. -/
theorem isPullback_gluedCurveDualNumbersComponent_over_true :
    IsPullback (gluedCurveDualNumbersComponent k pts hpts true) (projectiveLineDualNumbersMap k)
      (gluedCurveDualNumbersOver k pts hpts) (pushoutInr (gluedCurveSituation k pts hpts)) :=
  isPullback_gluedCurveDualNumbersComponent_over k pts hpts true
    ((Iso.comp_inv_eq _).2 (pushoutInr_gluedCurveIsoPushoutScheme_hom k pts hpts).symm).symm

/-- The two copies of `ℙ¹_{k[ε]}` agree on the three double points. -/
theorem doublePointsDualNumbersToProjectiveLine_comp_component :
    doublePointsDualNumbersToProjectiveLine k pts ≫
        gluedCurveDualNumbersComponent k pts hpts false =
      doublePointsDualNumbersToProjectiveLine k pts ≫
        gluedCurveDualNumbersComponent k pts hpts true := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, gluedCurveDualNumbersComponent_fst,
      gluedCurveDualNumbersComponent_fst, ← Category.assoc, ← Category.assoc,
      (isPullback_doublePointsDualNumbers k pts hpts).w, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (doublePointsToProjectiveLine_comp_gluedCurveInl k pts hpts)
  · simp

/-- **The glued curve over the dual numbers is the pushout of two copies of `ℙ¹_{k[ε]}` along
the three double points over the dual numbers.** -/
theorem isPushout_gluedCurveDualNumbers :
    IsPushout (doublePointsDualNumbersToProjectiveLine k pts)
      (doublePointsDualNumbersToProjectiveLine k pts)
      (gluedCurveDualNumbersComponent k pts hpts false)
      (gluedCurveDualNumbersComponent k pts hpts true) := by
  set s := gluedCurveSituation k pts hpts
  have hw := gluedCurveDualNumbersOver_properties k pts hpts
  let w : Over (pushoutScheme s) := Over.mk (gluedCurveDualNumbersOver k pts hpts)
  let d := pushoutBaseChangeDiagram s w hw
  have := isIso_pushoutBaseChangeMap s w hw
  let c := asIso (pushoutBaseChangeMap s w hw)
  have hP := (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout
  have hX : IsPullback (gluedCurveDualNumbersComponent k pts hpts false)
      (projectiveLineDualNumbersMap k) w.hom (pushoutInl s) :=
    isPullback_gluedCurveDualNumbersComponent_over_false k pts hpts
  have hY : IsPullback (gluedCurveDualNumbersComponent k pts hpts true)
      (projectiveLineDualNumbersMap k) w.hom (pushoutInr s) :=
    isPullback_gluedCurveDualNumbersComponent_over_true k pts hpts
  let eX := hX.isoPullback
  let eY := hY.isoPullback
  have hZ : IsPullback (doublePointsDualNumbersToProjectiveLine k pts ≫ eX.hom)
      (doublePointsDualNumbersProjection k pts) (pullback.snd w.hom (pushoutInl s))
      (doublePointsToProjectiveLine k pts) :=
    (isPullback_doublePointsDualNumbers k pts hpts).of_iso (Iso.refl _) eX (Iso.refl _)
      (Iso.refl _) (by simp) (by simp)
      ((Category.comp_id _).trans (IsPullback.isoPullback_hom_snd hX).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let eZ := hZ.isoIsPullback _ _ d.left_isPullback
  have hZi : eZ.hom ≫ d.i' = doublePointsDualNumbersToProjectiveLine k pts ≫ eX.hom :=
    hZ.isoIsPullback_hom_fst _ _ d.left_isPullback
  have hZh : eZ.hom ≫ d.h = doublePointsDualNumbersProjection k pts :=
    hZ.isoIsPullback_hom_snd _ _ d.left_isPullback
  have hcl : pushoutInl (inducedSituation s d) ≫ c.hom = pullback.fst w.hom (pushoutInl s) :=
    pushoutInl_comp_pushoutBaseChangeMap s w hw
  have hcr : pushoutInr (inducedSituation s d) ≫ c.hom = pullback.fst w.hom (pushoutInr s) :=
    pushoutInr_comp_pushoutBaseChangeMap s w hw
  have hji : d.i' ≫ pullback.fst w.hom (pushoutInl s) =
      d.j' ≫ pullback.fst w.hom (pushoutInr s) := by
    rw [← hcl, ← hcr, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ c.hom) hP.w
  let jj : d.Z' ⟶ pullback w.hom (pushoutInr s) := d.j'
  have hji' : d.i' ≫ pullback.fst w.hom (pushoutInl s) = jj ≫ pullback.fst w.hom (pushoutInr s) :=
    hji
  have hjg : jj ≫ pullback.snd w.hom (pushoutInr s) = d.h ≫ doublePointsToProjectiveLine k pts :=
    d.right_isPullback.w
  have hZj' : eZ.hom ≫ jj = doublePointsDualNumbersToProjectiveLine k pts ≫ eY.hom := by
    apply pullback.hom_ext
    · calc (eZ.hom ≫ jj) ≫ pullback.fst w.hom (pushoutInr s)
          = eZ.hom ≫ (jj ≫ pullback.fst w.hom (pushoutInr s)) := Category.assoc _ _ _
        _ = eZ.hom ≫ (d.i' ≫ pullback.fst w.hom (pushoutInl s)) :=
            congrArg (eZ.hom ≫ ·) hji'.symm
        _ = (eZ.hom ≫ d.i') ≫ pullback.fst w.hom (pushoutInl s) := (Category.assoc _ _ _).symm
        _ = (doublePointsDualNumbersToProjectiveLine k pts ≫ eX.hom) ≫
              pullback.fst w.hom (pushoutInl s) :=
            congrArg (· ≫ pullback.fst w.hom (pushoutInl s)) hZi
        _ = doublePointsDualNumbersToProjectiveLine k pts ≫
              (eX.hom ≫ pullback.fst w.hom (pushoutInl s)) := Category.assoc _ _ _
        _ = doublePointsDualNumbersToProjectiveLine k pts ≫
              gluedCurveDualNumbersComponent k pts hpts false :=
            congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_fst hX)
        _ = doublePointsDualNumbersToProjectiveLine k pts ≫
              gluedCurveDualNumbersComponent k pts hpts true :=
            doublePointsDualNumbersToProjectiveLine_comp_component k pts hpts
        _ = doublePointsDualNumbersToProjectiveLine k pts ≫
              (eY.hom ≫ pullback.fst w.hom (pushoutInr s)) :=
            congrArg (_ ≫ ·) (IsPullback.isoPullback_hom_fst hY).symm
        _ = (doublePointsDualNumbersToProjectiveLine k pts ≫ eY.hom) ≫
              pullback.fst w.hom (pushoutInr s) := (Category.assoc _ _ _).symm
    · let sndY : pullback w.hom (pushoutInr s) ⟶ projectiveLine k :=
        pullback.snd w.hom (pushoutInr s)
      show (eZ.hom ≫ jj) ≫ sndY = (doublePointsDualNumbersToProjectiveLine k pts ≫ eY.hom) ≫ sndY
      let hh : d.Z' ⟶ doublePointsScheme k pts := d.h
      have hjg' : jj ≫ sndY = hh ≫ doublePointsToProjectiveLine k pts := hjg
      have hZh' : eZ.hom ≫ hh = doublePointsDualNumbersProjection k pts := hZh
      have hYsnd : eY.hom ≫ sndY = projectiveLineDualNumbersMap k :=
        IsPullback.isoPullback_hom_snd hY
      rw [Category.assoc, hjg', ← Category.assoc, hZh']
      exact ((isPullback_doublePointsDualNumbers k pts hpts).w.symm.trans
        (congrArg (_ ≫ ·) hYsnd.symm)).trans (Category.assoc _ _ _).symm
  have hZj : eZ.hom ≫ d.j' = doublePointsDualNumbersToProjectiveLine k pts ≫ eY.hom := hZj'
  refine hP.of_iso' eZ eX eY c.symm hZi hZj ?_ ?_
  · rw [Iso.symm_hom, ← cancel_mono c.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, hcl]
    exact IsPullback.isoPullback_hom_fst hX
  · rw [Iso.symm_hom, ← cancel_mono c.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, hcr]
    exact IsPullback.isoPullback_hom_fst hY

/-! ### The translation `t ↦ t + c` -/

/-- The `R`-algebra endomorphism of `R[t]` sending `t` to `t + c` is the translation by `c`. -/
theorem eval₂RingHom_X_add_C {R : Type u} [CommRing R] (c : R) :
    eval₂RingHom (C.comp (RingHom.id R)) (X + C c) = (translate c).toRingHom :=
  Polynomial.ringHom_ext (fun r ↦ by simp) (by simp)

/-- The translation of `ℙ¹` maps the three double points into themselves. -/
theorem doublePointsDualNumbersToProjectiveLine_comp_translation {c : DualNumber k}
    (h2 : (2 : DualNumber k) = 0) (hc : c * c = 0) :
    doublePointsDualNumbersToProjectiveLine k pts ≫ projectiveLineTranslation c hc =
      Spec.map (CommRingCat.ofHom (doublePointsTranslate _ h2 hc)) ≫
        doublePointsDualNumbersToProjectiveLine k pts := by
  rw [doublePointsDualNumbersToProjectiveLine, Category.assoc, projectiveLineTranslation,
    projectiveLineXChart_comp_projectiveLineHom, ← Category.assoc, ← Category.assoc,
    Spec_map_ofHom_comp_Spec_map_ofHom, Spec_map_ofHom_comp_Spec_map_ofHom,
    eval₂RingHom_X_add_C, doublePointsTranslate_comp_doublePointsMk]

/-- The endomorphism of `X_A` induced by the translation `t ↦ t + c` of both copies of `ℙ¹_A`,
for `2 = 0` and `c² = 0`. -/
def gluedCurveDualNumbersTranslation {c : DualNumber k} (h2 : (2 : DualNumber k) = 0)
    (hc : c * c = 0) : gluedCurveDualNumbers k pts hpts ⟶ gluedCurveDualNumbers k pts hpts :=
  (isPushout_gluedCurveDualNumbers k pts hpts).desc
    (projectiveLineTranslation c hc ≫ gluedCurveDualNumbersComponent k pts hpts false)
    (projectiveLineTranslation c hc ≫ gluedCurveDualNumbersComponent k pts hpts true) (by
      rw [← Category.assoc, ← Category.assoc,
        doublePointsDualNumbersToProjectiveLine_comp_translation k pts h2 hc, Category.assoc,
        Category.assoc, (isPushout_gluedCurveDualNumbers k pts hpts).w])

/-- The endomorphism `gluedCurveDualNumbersTranslation` is the translation on each copy of
`ℙ¹_{k[ε]}`. -/
@[reassoc (attr := simp)]
theorem gluedCurveDualNumbersComponent_comp_translation {c : DualNumber k}
    (h2 : (2 : DualNumber k) = 0) (hc : c * c = 0) (b : Bool) :
    gluedCurveDualNumbersComponent k pts hpts b ≫
        gluedCurveDualNumbersTranslation k pts hpts h2 hc =
      projectiveLineTranslation c hc ≫ gluedCurveDualNumbersComponent k pts hpts b := by
  cases b
  exacts [(isPushout_gluedCurveDualNumbers k pts hpts).inl_desc _ _ _,
    (isPushout_gluedCurveDualNumbers k pts hpts).inr_desc _ _ _]

/-- Two morphisms out of `X_A` agree if they agree on both copies of `ℙ¹_{k[ε]}`. -/
theorem gluedCurveDualNumbers_hom_ext {Y : Scheme.{u}} {f g : gluedCurveDualNumbers k pts hpts ⟶ Y}
    (h : ∀ b, gluedCurveDualNumbersComponent k pts hpts b ≫ f =
      gluedCurveDualNumbersComponent k pts hpts b ≫ g) : f = g :=
  (isPushout_gluedCurveDualNumbers k pts hpts).hom_ext (h false) (h true)

/-- The translation by `-c` is inverse to the translation by `c`. -/
theorem gluedCurveDualNumbersTranslation_comp_neg {c : DualNumber k} (h2 : (2 : DualNumber k) = 0)
    (hc : c * c = 0) :
    gluedCurveDualNumbersTranslation k pts hpts h2 hc ≫
      gluedCurveDualNumbersTranslation k pts hpts h2 (c := -c) (by rw [neg_mul_neg, hc]) = 𝟙 _ := by
  refine gluedCurveDualNumbers_hom_ext k pts hpts fun b ↦ ?_
  rw [gluedCurveDualNumbersComponent_comp_translation_assoc,
    gluedCurveDualNumbersComponent_comp_translation, ← Category.assoc,
    projectiveLineTranslation_comp_neg, Category.id_comp, Category.comp_id]

/-- The translation lies over the dual numbers. -/
@[reassoc (attr := simp)]
theorem gluedCurveDualNumbersTranslation_comp_snd {c : DualNumber k}
    (h2 : (2 : DualNumber k) = 0) (hc : c * c = 0) :
    gluedCurveDualNumbersTranslation k pts hpts h2 hc ≫ pullback.snd _ _ = pullback.snd _ _ := by
  refine gluedCurveDualNumbers_hom_ext k pts hpts fun b ↦ ?_
  rw [gluedCurveDualNumbersComponent_comp_translation_assoc, gluedCurveDualNumbersComponent_snd,
    projectiveLineTranslation_comp_structureMorphism]

/-- The translation `t ↦ t + c` of `X_A`, as an automorphism over `Spec A`. -/
def gluedCurveDualNumbersTranslationAut {c : DualNumber k} (h2 : (2 : DualNumber k) = 0)
    (hc : c * c = 0) :
    Aut (Over.mk (pullback.snd (gluedCurveToBase k pts hpts) (dualNumbersToBase k))) :=
  Over.isoMk
    { hom := gluedCurveDualNumbersTranslation k pts hpts h2 hc
      inv := gluedCurveDualNumbersTranslation k pts hpts h2 (c := -c) (by rw [neg_mul_neg, hc])
      hom_inv_id := gluedCurveDualNumbersTranslation_comp_neg k pts hpts h2 hc
      inv_hom_id := by
        have := gluedCurveDualNumbersTranslation_comp_neg k pts hpts h2 (c := -c)
          (by rw [neg_mul_neg, hc])
        simp only [neg_neg] at this
        exact this }
    (gluedCurveDualNumbersTranslation_comp_snd k pts hpts h2 hc)

/-- The copies of `ℙ¹_A` are closed subschemes of `X_A`. -/
instance isClosedImmersion_gluedCurveDualNumbersComponent (b : Bool) :
    IsClosedImmersion (gluedCurveDualNumbersComponent k pts hpts b) :=
  MorphismProperty.of_isPullback (isPullback_gluedCurveDualNumbersComponent k pts hpts b).flip
    inferInstance

variable [CharP k 2]

/-- **The automorphism `t ↦ t + ε` of the equalizer diagram extends to an automorphism of `X`
over `A = k[ε]`.** For `k` of characteristic `2`, the automorphism of
`X_A = X ×_{Spec k} Spec k[ε]` over `Spec k[ε]` which is the translation `t ↦ t + ε` on both
copies of `ℙ¹_{k[ε]}`. -/
@[stacks 0DSU "the automorphism t ↦ t + ε extends to an automorphism of X over A = k[ε]"]
def gluedCurveDualNumbersAut :
    Aut (Over.mk (pullback.snd (gluedCurveToBase k pts hpts) (dualNumbersToBase k))) :=
  gluedCurveDualNumbersTranslationAut k pts hpts (two_eq_zero_dualNumber k) DualNumber.eps_mul_eps

/-- The automorphism is the translation `t ↦ t + ε` on both copies of `ℙ¹_{k[ε]}`. -/
theorem gluedCurveDualNumbersComponent_comp_aut (b : Bool) :
    gluedCurveDualNumbersComponent k pts hpts b ≫ (gluedCurveDualNumbersAut k pts hpts).hom.left =
      projectiveLineTranslation DualNumber.eps DualNumber.eps_mul_eps ≫
        gluedCurveDualNumbersComponent k pts hpts b :=
  gluedCurveDualNumbersComponent_comp_translation k pts hpts (two_eq_zero_dualNumber k)
    DualNumber.eps_mul_eps b

/-- **The automorphism of `X_A` restricts on the two affine lines `Spec k[ε][t]` to the
substitution `t ↦ t + ε`** of the equalizer diagram
`O(U_A) ⟶ k[ε][t] × k[ε][t] ⇉ ∏ᵢ k[ε][t]/(t - aᵢ)²`; on the equalizer itself this substitution is
`AlgebraicGeometry.epsTranslate`. -/
@[stacks 0DSU "the automorphism of X_A is the substitution t ↦ t + ε on the two affine lines"]
theorem projectiveLineXChart_comp_gluedCurveDualNumbersAut (b : Bool) :
    projectiveLineXChart (DualNumber k) ≫ gluedCurveDualNumbersComponent k pts hpts b ≫
        (gluedCurveDualNumbersAut k pts hpts).hom.left =
      Spec.map (CommRingCat.ofHom (translate (DualNumber.eps : DualNumber k)).toRingHom) ≫
        projectiveLineXChart (DualNumber k) ≫ gluedCurveDualNumbersComponent k pts hpts b := by
  rw [gluedCurveDualNumbersComponent_comp_aut, projectiveLineTranslation,
    projectiveLineXChart_comp_projectiveLineHom_assoc, eval₂RingHom_X_add_C]

/-- On the equalizer, the substitution `t ↦ t + ε` of the first coordinate is
`AlgebraicGeometry.epsTranslate`. -/
theorem gluingSubringFst_comp_epsTranslate (pts : Fin 3 → DualNumber k) :
    (gluingSubringFst pts).comp (epsTranslate k pts).toRingHom =
      (translate (DualNumber.eps : DualNumber k)).toRingHom.comp (gluingSubringFst pts) :=
  rfl

/-- On the equalizer, the substitution `t ↦ t + ε` of the second coordinate is
`AlgebraicGeometry.epsTranslate`. -/
theorem gluingSubringSnd_comp_epsTranslate (pts : Fin 3 → DualNumber k) :
    (gluingSubringSnd pts).comp (epsTranslate k pts).toRingHom =
      (translate (DualNumber.eps : DualNumber k)).toRingHom.comp (gluingSubringSnd pts) :=
  rfl

/-- **The automorphism of `X_A` is not the identity**: it moves the `k[ε]`-point
`t = 0` of the first copy of `ℙ¹_{k[ε]}` to the point `t = ε`. -/
@[stacks 0DSU "the automorphism of X over A is nontrivial"]
theorem gluedCurveDualNumbersAut_ne_one : gluedCurveDualNumbersAut k pts hpts ≠ 1 := by
  intro h
  have h1 : (gluedCurveDualNumbersAut k pts hpts).hom.left = 𝟙 _ := by
    rw [h]
    rfl
  have e := gluedCurveDualNumbersComponent_comp_aut k pts hpts false
  rw [h1] at e
  replace e := (Category.comp_id _).symm.trans e
  have e' : projectiveLineXChartPoint (0 : DualNumber k) ≫
      gluedCurveDualNumbersComponent k pts hpts false =
      projectiveLineXChartPoint 0 ≫
        projectiveLineTranslation DualNumber.eps DualNumber.eps_mul_eps ≫
        gluedCurveDualNumbersComponent k pts hpts false := congrArg (_ ≫ ·) e
  rw [← Category.assoc, projectiveLineXChartPoint_comp_projectiveLineTranslation, zero_add,
    cancel_mono] at e'
  have e'' := (cancel_mono (projectiveLineXChart (DualNumber k))).1 e'
  have := congrArg (fun φ : CommRingCat.of (DualNumber k)[X] ⟶ CommRingCat.of (DualNumber k) ↦
    φ.hom X) (Spec.map_injective e'')
  simp only [CommRingCat.hom_ofHom, coe_evalRingHom, eval_X] at this
  have h' := congrArg TrivSqZeroExt.snd this
  rw [DualNumber.snd_eps, TrivSqZeroExt.snd_zero] at h'
  exact zero_ne_one h'

end AlgebraicGeometry
