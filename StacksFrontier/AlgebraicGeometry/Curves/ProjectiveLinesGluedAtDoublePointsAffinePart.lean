module

public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePointsDualNumbers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine part of two projective lines glued at three double points

Let `k` be a field, `a₀, a₁, a₂ ∈ k` pairwise distinct, and `X = ℙ¹_k ⨿_T ℙ¹_k` the curve obtained
by gluing two projective lines along the three double points `T = ∐ᵢ Spec(k[t]/(t - aᵢ)²)`. The
images of the two affine lines `𝔸¹_k ⊂ ℙ¹_k` form an open subscheme `U ⊂ X`, the complement of
the two points at infinity. **`U` is affine, and its ring of functions is the equalizer**

`O_X(U) ⟶ k[t] × k[t] ⇉ ∏ᵢ k[t]/(t - aᵢ)²`.

## Main definitions

* `AlgebraicGeometry.gluedCurveAffinePart`: the open subscheme `U`.
* `AlgebraicGeometry.gluedCurveAffinePartIso`: the identification of `U` with the spectrum of the
  equalizer.
* `AlgebraicGeometry.gluedCurveAffinePartSectionsEquiv`: `O_X(U) ≅` the equalizer.

## Main results

* `AlgebraicGeometry.coe_gluedCurveAffinePart`: `U` is the image of the two affine lines.
* `AlgebraicGeometry.isPushout_gluedCurveAffinePart`: `U` is the pushout of the two affine lines
  along the three double points.
* `AlgebraicGeometry.isAffineOpen_gluedCurveAffinePart`: `U` is an affine open.

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

/-- A point of `ℙ¹_k` lies on the affine line `𝔸¹_k` if and only if it is not the point at
infinity. -/
theorem mem_range_projectiveLineXChart_iff (y : projectiveLine k) :
    y ∈ Set.range (projectiveLineXChart k).base ↔ y ≠ projectiveLineInfinity k :=
  ⟨fun hy h ↦ projectiveLineInfinity_notMem_range_projectiveLineXChart k (h ▸ hy),
    (mem_range_projectiveLineXChart_or_eq_infinity y).resolve_right⟩

/-- The point at infinity of `ℙ¹_k` is closed. -/
@[ega "II 7.4.14" "∞ is a closed point"]
theorem isClosed_projectiveLineInfinity : IsClosed {projectiveLineInfinity k} := by
  rw [← isOpen_compl_iff]
  convert (projectiveLineXChart k).isOpenEmbedding.isOpen_range using 1
  ext y
  exact (mem_range_projectiveLineXChart_iff k y).symm

/-- The two points at infinity of the glued curve. -/
def gluedCurveInfinities : Set (gluedCurve k pts hpts) :=
  {(gluedCurveComponent k pts hpts false).base (projectiveLineInfinity k),
    (gluedCurveComponent k pts hpts true).base (projectiveLineInfinity k)}

/-- The two points at infinity form a closed subset of the glued curve. -/
theorem isClosed_gluedCurveInfinities : IsClosed (gluedCurveInfinities k pts hpts) := by
  have h (b : Bool) :
      IsClosed {(gluedCurveComponent k pts hpts b).base (projectiveLineInfinity k)} := by
    rw [← Set.image_singleton]
    exact (gluedCurveComponent k pts hpts b).isClosedEmbedding.isClosedMap _
      (isClosed_projectiveLineInfinity k)
  exact (h false).union (h true)

/-- **The affine part `U` of the glued curve**: the complement of the two points at infinity. -/
def gluedCurveAffinePart : (gluedCurve k pts hpts).Opens :=
  ⟨(gluedCurveInfinities k pts hpts)ᶜ, (isClosed_gluedCurveInfinities k pts hpts).isOpen_compl⟩

/-- The preimage of the affine part in each copy of `ℙ¹_k` is the affine line. -/
theorem preimage_gluedCurveAffinePart (b : Bool) :
    (gluedCurveComponent k pts hpts b).base ⁻¹' (gluedCurveAffinePart k pts hpts : Set _) =
      Set.range (projectiveLineXChart k).base := by
  ext y
  rw [mem_range_projectiveLineXChart_iff]
  change (gluedCurveComponent k pts hpts b).base y ∉ gluedCurveInfinities k pts hpts ↔ _
  have hinj := (gluedCurveComponent k pts hpts b).isClosedEmbedding.injective
  have hother : (gluedCurveComponent k pts hpts b).base y ≠
      (gluedCurveComponent k pts hpts (!b)).base (projectiveLineInfinity k) := fun h ↦
    gluedCurveComponent_infinity_notMem k pts hpts (!b) (by rw [Bool.not_not]; exact ⟨y, h⟩)
  cases b <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
    simp [gluedCurveInfinities, hinj.eq_iff, hother]

private theorem projectiveLineXChart_comp_mem_gluedCurveAffinePart (b : Bool)
    (w : Spec (.of k[X])) :
    (projectiveLineXChart k ≫ gluedCurveComponent k pts hpts b).base w ∈
      (gluedCurveAffinePart k pts hpts : Set (gluedCurve k pts hpts)) := by
  change (gluedCurveComponent k pts hpts b).base ((projectiveLineXChart k).base w) ∈ _
  rw [← Set.mem_preimage, preimage_gluedCurveAffinePart]
  exact ⟨w, rfl⟩

/-- **`U` is the image of the two affine lines `𝔸¹_k ⨿ 𝔸¹_k`.** -/
theorem coe_gluedCurveAffinePart :
    (gluedCurveAffinePart k pts hpts : Set (gluedCurve k pts hpts)) =
      Set.range (projectiveLineXChart k ≫ gluedCurveComponent k pts hpts false).base ∪
        Set.range (projectiveLineXChart k ≫ gluedCurveComponent k pts hpts true).base := by
  ext p
  constructor
  · intro hp
    obtain ⟨b, y, rfl⟩ := gluedCurveComponent_jointly_surjective k pts hpts p
    obtain ⟨w, rfl⟩ : y ∈ Set.range (projectiveLineXChart k).base := by
      rwa [← preimage_gluedCurveAffinePart k pts hpts b]
    cases b
    exacts [Or.inl ⟨w, rfl⟩, Or.inr ⟨w, rfl⟩]
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩) <;>
      exact projectiveLineXChart_comp_mem_gluedCurveAffinePart k pts hpts _ w

/-- The affine line of a copy of `ℙ¹_k`, as a morphism into `U`. -/
def gluedCurveAffinePartChart (b : Bool) :
    Spec (.of k[X]) ⟶ (gluedCurveAffinePart k pts hpts).toScheme :=
  IsOpenImmersion.lift (gluedCurveAffinePart k pts hpts).ι
    (projectiveLineXChart k ≫ gluedCurveComponent k pts hpts b) (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact projectiveLineXChart_comp_mem_gluedCurveAffinePart k pts hpts b w)

/-- The affine line of a copy of `ℙ¹_k`, followed by the inclusion of `U`, is the affine chart of
`ℙ¹_k` followed by the map of that copy into the glued curve. -/
@[reassoc (attr := simp)]
theorem gluedCurveAffinePartChart_ι (b : Bool) :
    gluedCurveAffinePartChart k pts hpts b ≫ (gluedCurveAffinePart k pts hpts).ι =
      projectiveLineXChart k ≫ gluedCurveComponent k pts hpts b :=
  IsOpenImmersion.lift_fac _ _ _

/-- The affine line is the preimage of `U` in each copy of `ℙ¹_k`. -/
theorem isPullback_gluedCurveAffinePartChart (b : Bool) :
    IsPullback (gluedCurveAffinePartChart k pts hpts b) (projectiveLineXChart k)
      (gluedCurveAffinePart k pts hpts).ι (gluedCurveComponent k pts hpts b) := by
  let e := IsOpenImmersion.isoOfRangeEq (projectiveLineXChart k)
    (pullback.snd (gluedCurveAffinePart k pts hpts).ι (gluedCurveComponent k pts hpts b)) (by
      rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι, preimage_gluedCurveAffinePart])
  refine IsPullback.of_iso_pullback ⟨by simp⟩ e ?_ (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
  rw [← cancel_mono (gluedCurveAffinePart k pts hpts).ι, Category.assoc, pullback.condition,
    ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, gluedCurveAffinePartChart_ι]

/-- The three double points are the preimage of the affine line `𝔸¹_k ⊂ ℙ¹_k`. -/
theorem isPullback_doublePointsToAffineLine :
    IsPullback (doublePointsToAffineLine k pts) (𝟙 _) (projectiveLineXChart k)
      (doublePointsToProjectiveLine k pts) :=
  IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]; rfl⟩

/-- The two affine lines agree on the three double points. -/
theorem doublePointsToAffineLine_comp_gluedCurveAffinePartChart :
    doublePointsToAffineLine k pts ≫ gluedCurveAffinePartChart k pts hpts false =
      doublePointsToAffineLine k pts ≫ gluedCurveAffinePartChart k pts hpts true := by
  rw [← cancel_mono (gluedCurveAffinePart k pts hpts).ι, Category.assoc, Category.assoc,
    gluedCurveAffinePartChart_ι, gluedCurveAffinePartChart_ι, ← Category.assoc, ← Category.assoc]
  exact doublePointsToProjectiveLine_comp_gluedCurveInl k pts hpts

/-- **`U` is the pushout of the two affine lines along the three double points.** -/
theorem isPushout_gluedCurveAffinePart :
    IsPushout (doublePointsToAffineLine k pts) (doublePointsToAffineLine k pts)
      (gluedCurveAffinePartChart k pts hpts false) (gluedCurveAffinePartChart k pts hpts true) := by
  set s := gluedCurveSituation k pts hpts
  let p : (gluedCurveAffinePart k pts hpts).toScheme ⟶ pushoutScheme s :=
    (gluedCurveAffinePart k pts hpts).ι ≫ (gluedCurveIsoPushoutScheme k pts hpts).inv
  have hw : Flat p ∧ IsSeparated p ∧ LocallyOfFiniteType p ∧ LocallyQuasiFinite p :=
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let w : Over (pushoutScheme s) := Over.mk p
  let d := pushoutBaseChangeDiagram s w hw
  have := isIso_pushoutBaseChangeMap s w hw
  let c := asIso (pushoutBaseChangeMap s w hw)
  have hP := (pushoutAlongClosedImmersionAndIntegral (inducedSituation s d)).isPushout
  have hcomp : ∀ (b : Bool) (f : projectiveLine k ⟶ pushoutScheme s),
      f ≫ (gluedCurveIsoPushoutScheme k pts hpts).hom = gluedCurveComponent k pts hpts b →
      IsPullback (gluedCurveAffinePartChart k pts hpts b) (projectiveLineXChart k) w.hom f := by
    intro b f hf
    rw [(Iso.eq_comp_inv _).2 hf]
    exact (isPullback_gluedCurveAffinePartChart k pts hpts b).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (gluedCurveIsoPushoutScheme k pts hpts).symm (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.id_comp]; rfl) (by simp)
  have hX := hcomp false _ (pushoutInl_gluedCurveIsoPushoutScheme_hom k pts hpts)
  have hY := hcomp true _ (pushoutInr_gluedCurveIsoPushoutScheme_hom k pts hpts)
  have hZ : IsPullback (doublePointsToAffineLine k pts ≫ hX.isoPullback.hom) (𝟙 _)
      (pullback.snd w.hom (pushoutInl s)) (doublePointsToProjectiveLine k pts) :=
    (isPullback_doublePointsToAffineLine k pts).of_iso (Iso.refl _) hX.isoPullback (Iso.refl _)
      (Iso.refl _) (by simp) (by simp)
      ((Category.comp_id _).trans (IsPullback.isoPullback_hom_snd hX).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let eZ := hZ.isoIsPullback _ _ d.left_isPullback
  let ii : d.Z' ⟶ pullback w.hom (pushoutInl s) := d.i'
  have hZi : eZ.hom ≫ ii = doublePointsToAffineLine k pts ≫ hX.isoPullback.hom :=
    hZ.isoIsPullback_hom_fst _ _ d.left_isPullback
  have hcl : pushoutInl (inducedSituation s d) ≫ c.hom = pullback.fst w.hom (pushoutInl s) :=
    pushoutInl_comp_pushoutBaseChangeMap s w hw
  have hcr : pushoutInr (inducedSituation s d) ≫ c.hom = pullback.fst w.hom (pushoutInr s) :=
    pushoutInr_comp_pushoutBaseChangeMap s w hw
  have hji₀ : d.i' ≫ pullback.fst w.hom (pushoutInl s) =
      d.j' ≫ pullback.fst w.hom (pushoutInr s) := by
    rw [← hcl, ← hcr, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ c.hom) hP.w
  let jj : d.Z' ⟶ pullback w.hom (pushoutInr s) := d.j'
  have hji : ii ≫ pullback.fst w.hom (pushoutInl s) = jj ≫ pullback.fst w.hom (pushoutInr s) :=
    hji₀
  have hZj : eZ.hom ≫ jj = doublePointsToAffineLine k pts ≫ hY.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← hji, ← Category.assoc, hZi]
      exact (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) hX.isoPullback_hom_fst).trans <|
        (doublePointsToAffineLine_comp_gluedCurveAffinePartChart k pts hpts).trans <|
          (congrArg (_ ≫ ·) hY.isoPullback_hom_fst.symm).trans (Category.assoc _ _ _).symm
    · let sndY : pullback w.hom (pushoutInr s) ⟶ projectiveLine k :=
        pullback.snd w.hom (pushoutInr s)
      change (eZ.hom ≫ jj) ≫ sndY = (doublePointsToAffineLine k pts ≫ hY.isoPullback.hom) ≫ sndY
      let hh : d.Z' ⟶ doublePointsScheme k pts := d.h
      have hjg : jj ≫ sndY = hh ≫ doublePointsToProjectiveLine k pts := d.right_isPullback.w
      have hZh : eZ.hom ≫ hh = 𝟙 _ := hZ.isoIsPullback_hom_snd _ _ d.left_isPullback
      have hYsnd : hY.isoPullback.hom ≫ sndY = projectiveLineXChart k := hY.isoPullback_hom_snd
      rw [Category.assoc, hjg, ← Category.assoc, hZh, Category.id_comp]
      exact (congrArg (_ ≫ ·) hYsnd.symm).trans (Category.assoc _ _ _).symm
  refine hP.of_iso' eZ hX.isoPullback hY.isoPullback c.symm hZi hZj ?_ ?_ <;>
    rw [Iso.symm_hom, ← cancel_mono c.hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exacts [hcl ▸ hX.isoPullback_hom_fst, hcr ▸ hY.isoPullback_hom_fst]

/-- **The affine part of the glued curve is the spectrum of the equalizer**
`O ⟶ k[t] × k[t] ⇉ ∏ᵢ k[t]/(t - aᵢ)²`, compatibly with the two affine lines. -/
def gluedCurveAffinePartIso :
    (gluedCurveAffinePart k pts hpts).toScheme ≅ gluingScheme k pts :=
  (isPushout_gluedCurveAffinePart k pts hpts).isoIsPushout _ _ (isPushout_gluingScheme k pts hpts)

/-- Under `gluedCurveAffinePartIso`, the affine line of the first copy of `ℙ¹_k` is the spectrum
of the second coordinate `gluingSubringSnd` of the equalizer. -/
@[reassoc (attr := simp)]
theorem gluedCurveAffinePartChart_false_comp_iso :
    gluedCurveAffinePartChart k pts hpts false ≫ (gluedCurveAffinePartIso k pts hpts).hom =
      Spec.map (CommRingCat.ofHom (gluingSubringSnd pts)) :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- Under `gluedCurveAffinePartIso`, the affine line of the second copy of `ℙ¹_k` is the spectrum
of the first coordinate `gluingSubringFst` of the equalizer. -/
@[reassoc (attr := simp)]
theorem gluedCurveAffinePartChart_true_comp_iso :
    gluedCurveAffinePartChart k pts hpts true ≫ (gluedCurveAffinePartIso k pts hpts).hom =
      Spec.map (CommRingCat.ofHom (gluingSubringFst pts)) :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

/-- **`U` is an affine open of the glued curve.** -/
@[stacks 0DSU "the affine open part U of X, the image of the two affine lines"]
theorem isAffineOpen_gluedCurveAffinePart : IsAffineOpen (gluedCurveAffinePart k pts hpts) :=
  IsAffine.of_isIso (gluedCurveAffinePartIso k pts hpts).hom

/-- **The functions on `U` are the equalizer** `O_X(U) ⟶ k[t] × k[t] ⇉ ∏ᵢ k[t]/(t - aᵢ)²`: the
ring of sections of `X` over the affine part is the ring of pairs of polynomials agreeing to first
order at the three points. -/
@[stacks 0DSU "O_X(U) is the equalizer of k[t] × k[t] ⇉ ∏ k[t]/(t - a_i)²"]
def gluedCurveAffinePartSectionsEquiv :
    Γ(gluedCurve k pts hpts, gluedCurveAffinePart k pts hpts) ≃+* gluingSubring pts :=
  ((gluedCurveAffinePart k pts hpts).topIso.symm ≪≫
    Scheme.Γ.mapIso (gluedCurveAffinePartIso k pts hpts).op.symm ≪≫
      Scheme.ΓSpecIso (.of (gluingSubring pts))).commRingCatIsoToRingEquiv

end AlgebraicGeometry
