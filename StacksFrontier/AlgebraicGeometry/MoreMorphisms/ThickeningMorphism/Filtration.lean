module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability

/-!
# Filtering a finite-order thickening by first-order thickenings

Let `t : S ⟶ S'` be a closed immersion with ideal sheaf `I = t.ker`. The closed subschemes cut
out by the successive powers `I ^ (i + 1)` form a filtration

`S = V(I) ⟶ V(I ^ 2) ⟶ V(I ^ 3) ⟶ ⋯ ⟶ S'`

of `S'` by closed subschemes, in which every step is a *first-order* thickening, because the
square of the ideal of `V(I ^ (i + 2))` inside `V(I ^ (i + 1))` is contained in zero. If
`I ^ (n + 1) = 0`, the filtration reaches `S'` at step `n`. Base changing it along a morphism
`f : X' ⟶ S'` gives a cartesian filtration of `X'`, again by first-order thickenings.

This is what reduces a statement about a finite-order thickening of the base to the first-order
case.

## Main definitions

* `Stacks.Thickenings.PowerFiltration.baseLevel` and
  `Stacks.Thickenings.PowerFiltration.baseInclusion`: the closed subscheme cut out by the
  `(i + 1)`st power of the ideal sheaf, and its inclusion into `S'`.
* `Stacks.Thickenings.PowerFiltration.baseStep`: the inclusion of one level into the next.
* `Stacks.Thickenings.PowerFiltration.baseInitialMap`: the identification of `S` with level
  zero.
* `Stacks.Thickenings.PowerFiltration.totalLevel`,
  `Stacks.Thickenings.PowerFiltration.totalInclusion`,
  `Stacks.Thickenings.PowerFiltration.totalProjection` and
  `Stacks.Thickenings.PowerFiltration.totalStep`: the base change of the filtration along
  `f : X' ⟶ S'`.

## Main results

* `Stacks.Thickenings.PowerFiltration.baseStep_firstOrder` and
  `Stacks.Thickenings.PowerFiltration.totalStep_firstOrder`: every step of either filtration
  is a first-order thickening.
* `Stacks.Thickenings.PowerFiltration.totalStep_isPullback`: each square of the base-changed
  filtration over the corresponding base step is cartesian.
* `Stacks.Thickenings.PowerFiltration.baseInitialMap_isIso`,
  `Stacks.Thickenings.PowerFiltration.baseInitialMap_comp_inclusion` and
  `Stacks.Thickenings.PowerFiltration.totalLevel_zero_iso`: the initial level is canonically
  the given closed subscheme, respectively its base change.
* `Stacks.Thickenings.PowerFiltration.baseInclusion_isIso` and
  `Stacks.Thickenings.PowerFiltration.totalInclusion_isIso`: once the relevant power of the
  ideal sheaf vanishes, the level is the ambient scheme.

## Implementation notes

The index `i` stands for the quotient by `I ^ (i + 1)`, so level zero is the scheme-theoretic
image of the original closed immersion and the last level has vanishing defining ideal. The
endpoint identifications are therefore isomorphisms compatible with the structure morphisms
rather than equalities of schemes.

That a step is a first-order thickening is checked on the affine charts of the subscheme glue
data: on a chart the step is the quotient map `Γ(X, U) ⧸ I ^ (i + 2) ⟶ Γ(X, U) ⧸ I ^ (i + 1)`,
whose kernel is the image of `I ^ (i + 1)` and therefore has square contained in the image of
`I ^ (2i + 2) ⊆ I ^ (i + 2)`, which is zero.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings.PowerFiltration

universe u

/-- The closed subscheme cut out by the `(i + 1)`st power of the ideal sheaf of `t`. -/
abbrev baseLevel {S S' : Scheme.{u}} (t : S ⟶ S') (i : ℕ) : Scheme.{u} :=
  (t.ker ^ (i + 1)).subscheme

/-- The inclusion of a level of the filtration into the ambient scheme. -/
abbrev baseInclusion {S S' : Scheme.{u}} (t : S ⟶ S') (i : ℕ) :
    baseLevel t i ⟶ S' :=
  (t.ker ^ (i + 1)).subschemeι

/-- The canonical map from the original closed subscheme to level zero of the filtration. -/
def baseInitialMap {S S' : Scheme.{u}} (t : S ⟶ S') :
    S ⟶ baseLevel t 0 :=
  t.toImage ≫ eqToHom (show t.image = baseLevel t 0 by
    simp [baseLevel, Scheme.Hom.image])

/-- The canonical inclusion of one level of the filtration into the next. -/
def baseStep {S S' : Scheme.{u}} (t : S ⟶ S') (i : ℕ) :
    baseLevel t i ⟶ baseLevel t (i + 1) :=
  Scheme.IdealSheafData.inclusion (by
    intro U
    exact Ideal.pow_le_pow_right (Nat.le_succ (i + 1)))

/-- The base change of a level of the filtration along `f : X' ⟶ S'`. -/
abbrev totalLevel {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) : Scheme.{u} :=
  pullback f (baseInclusion t i)

/-- The map from a base-changed level to the original total space. -/
abbrev totalInclusion {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) : totalLevel t f i ⟶ X' :=
  pullback.fst f (baseInclusion t i)

/-- The map from a base-changed level to the corresponding level of the base. -/
abbrev totalProjection {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) : totalLevel t f i ⟶ baseLevel t i :=
  pullback.snd f (baseInclusion t i)

/-- Consecutive base-level inclusions commute with their maps to the ambient scheme. -/
lemma baseStep_comp_inclusion {S S' : Scheme.{u}} (t : S ⟶ S') (i : ℕ) :
    baseStep t i ≫ baseInclusion t (i + 1) = baseInclusion t i := by
  change Scheme.IdealSheafData.inclusion _ ≫ _ = _
  exact Scheme.IdealSheafData.inclusion_subschemeι _

/-- The canonical map between consecutive base-changed levels. -/
def totalStep {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) : totalLevel t f i ⟶ totalLevel t f (i + 1) :=
  pullback.lift (totalInclusion t f i) (totalProjection t f i ≫ baseStep t i)
    (by
      rw [Category.assoc, baseStep_comp_inclusion]
      exact pullback.condition)

/-- The base-changed steps are inclusions over the original total space. -/
lemma totalStep_comp_inclusion {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) :
    totalStep t f i ≫ totalInclusion t f (i + 1) = totalInclusion t f i := by
  rw [totalStep, pullback.lift_fst]

/-- Pulling back an ideal along a bijective ring map preserves and reflects having zero square. -/
private lemma comap_pow_two_eq_bot_iff {R T : Type*} [CommRing R] [CommRing T] (e : R →+* T)
    (he : Function.Bijective e) (K : Ideal T) : (K.comap e) ^ 2 = ⊥ ↔ K ^ 2 = ⊥ := by
  rw [← Ideal.map_eq_bot_iff_of_injective he.1, Ideal.map_pow,
    Ideal.map_comap_of_surjective e he.2]

/-- The map `V(J) ⟶ V(I)` of affine charts for `I ≤ J` is a closed immersion. -/
private lemma isClosedImmersion_glueDataObjHom {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) (U : X.affineOpens) :
    IsClosedImmersion (Scheme.IdealSheafData.glueDataObjHom h U) :=
  IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective (h U))

/-- On an affine chart of the glue data of `V(I)`, the step `V(J) ⟶ V(I)` for `I ≤ J` with
`J * J ≤ I` has square-zero kernel ideal sheaf. -/
private lemma glueDataObjHom_ker_sq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : I ≤ J) (hsq : J * J ≤ I) (U : X.affineOpens) :
    (Scheme.IdealSheafData.glueDataObjHom h U).ker ^ 2 = ⊥ := by
  let q : (Γ(X, U) ⧸ I.ideal U) →+* (Γ(X, U) ⧸ J.ideal U) :=
    Ideal.Quotient.factor (h U)
  let f := Scheme.IdealSheafData.glueDataObjHom h U
  have _ : IsAffine (I.glueDataObj U) := inferInstanceAs (IsAffine (Spec _))
  have _ : IsAffine (J.glueDataObj U) := inferInstanceAs (IsAffine (Spec _))
  have _ : IsClosedImmersion f := isClosedImmersion_glueDataObjHom h U
  let Wtop : (I.glueDataObj U).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let WtopJ : (J.glueDataObj U).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let eI : Γ(I.glueDataObj U, Wtop) ≃+* (Γ(X, U) ⧸ I.ideal U) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I.ideal U))).commRingCatIsoToRingEquiv
  let eJ : Γ(J.glueDataObj U, WtopJ) ≃+* (Γ(X, U) ⧸ J.ideal U) :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J.ideal U))).commRingCatIsoToRingEquiv
  have hmap : eJ.toRingHom.comp f.appTop.hom = q.comp eI.toRingHom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  have hker : RingHom.ker f.appTop.hom = Ideal.comap eI.toRingHom (RingHom.ker q) := by
    ext x
    have hh : eJ (f.appTop.hom x) = q (eI x) := RingHom.congr_fun hmap x
    change f.appTop.hom x = 0 ↔ eI x ∈ RingHom.ker q
    exact ⟨fun hx => RingHom.mem_ker.mpr (by rw [← hh, hx, map_zero]),
      fun hx => eJ.injective (by rw [hh, RingHom.mem_ker.mp hx, map_zero])⟩
  have hfac : (RingHom.ker q) ^ 2 = ⊥ := by
    rw [Ideal.Quotient.factor_ker (h U), ← Ideal.map_pow]
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk (I.ideal U))
        (hf := Ideal.Quotient.mk_surjective)).mp hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hsq U (by simpa [pow_two] using hy))
  apply Scheme.IdealSheafData.ext_of_isAffine
  change (f.ker.ideal Wtop) ^ 2 = ⊥
  have hkerApply : f.ker.ideal Wtop = RingHom.ker f.appTop.hom := Scheme.Hom.ker_apply f Wtop
  rw [hkerApply, hker]
  exact (comap_pow_two_eq_bot_iff _ eI.bijective _).mpr hfac

/-- For ideal sheaves `I ≤ J` with `J * J ≤ I`, the inclusion `V(J) ⟶ V(I)` of closed
subschemes has square-zero kernel ideal sheaf. -/
private lemma idealSheafInclusion_ker_sq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : I ≤ J) (hsq : J * J ≤ I) :
    (Scheme.IdealSheafData.inclusion h).ker ^ 2 = ⊥ := by
  let f := Scheme.IdealSheafData.inclusion h
  have _ : ∀ U : X.affineOpens, IsOpenImmersion (I.subschemeCover.f U) :=
    fun U => I.subschemeCover.map_prop U
  have _ : ∀ U : X.affineOpens, IsOpenImmersion (J.subschemeCover.f U) :=
    fun U => J.subschemeCover.map_prop U
  have _ : ∀ U : X.affineOpens, IsAffine (I.glueDataObj U) :=
    fun _ => inferInstanceAs (IsAffine (Spec _))
  have _ : ∀ U : X.affineOpens, IsAffine (J.glueDataObj U) :=
    fun _ => inferInstanceAs (IsAffine (Spec _))
  let V (U : X.affineOpens) : I.subscheme.affineOpens :=
    ⟨(I.subschemeCover.f U) ''ᵁ (⊤ : (Spec (I.subschemeCover.X U)).Opens),
      (I.subschemeCover.f U).isAffineOpen_iff_of_isOpenImmersion.mpr (isAffineOpen_top _)⟩
  have hV : (⨆ U : X.affineOpens, (V U).1) = ⊤ := by
    calc
      (⨆ U : X.affineOpens, (V U).1) = ⨆ U : X.affineOpens, I.subschemeι ⁻¹ᵁ U.1 :=
        iSup_congr fun U => by
          rw [← I.opensRange_subschemeCover_map U, ← Scheme.Hom.image_top_eq_opensRange]
      _ = ⊤ := I.subschemeι.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hV
  intro (U : X.affineOpens)
  let chartI := I.subschemeCover.f U
  let chartJ := J.subschemeCover.f U
  let g := Scheme.IdealSheafData.glueDataObjHom h U
  let Wtop : (Spec (I.subschemeCover.X U)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have _ : IsOpenImmersion chartI := I.subschemeCover.map_prop U
  have _ : IsOpenImmersion chartJ := J.subschemeCover.map_prop U
  have _ : IsClosedImmersion g := isClosedImmersion_glueDataObjHom h U
  have hrange : f ⁻¹ᵁ chartI.opensRange = chartJ.opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map,
      Scheme.IdealSheafData.opensRange_subschemeCover_map, ← Scheme.Hom.comp_preimage,
      Scheme.IdealSheafData.inclusion_subschemeι]
  have hpull : IsPullback g chartJ chartI f :=
    @IsOpenImmersion.isPullback _ _ _ _ g chartJ chartI f
      (J.subschemeCover.map_prop U) (I.subschemeCover.map_prop U)
      (Scheme.IdealSheafData.subSchemeCover_map_inclusion h U) hrange
  have hker := @Scheme.ker_ideal_of_isPullback_of_isOpenImmersion _ _ _ _
    f g chartJ chartI (I.subschemeCover.map_prop U) inferInstance hpull Wtop
  have hlocal : (g.ker.ideal Wtop) ^ 2 = ⊥ :=
    congrArg (fun K : (I.glueDataObj U).IdealSheafData => K.ideal Wtop)
      (glueDataObjHom_ker_sq I J h hsq U)
  have hcomapSq : ((f.ker.ideal (V U)).comap (chartI.appIso Wtop).inv.hom) ^ 2 = ⊥ :=
    (congrArg (fun K => K ^ 2) hker).symm.trans hlocal
  exact (comap_pow_two_eq_bot_iff _
    (ConcreteCategory.bijective_of_isIso (chartI.appIso Wtop).inv) _).mp hcomapSq

/-- Every step of the filtration of the base is a first-order thickening. -/
lemma baseStep_firstOrder {S S' : Scheme.{u}} (t : S ⟶ S') (i : ℕ) :
    IsFirstOrderThickening (baseStep t i) := by
  refine ⟨?_, ?_⟩
  · change IsClosedImmersion (Scheme.IdealSheafData.inclusion _)
    infer_instance
  · let J := t.ker ^ (i + 1)
    let I := t.ker ^ (i + 2)
    have hIJ : I ≤ J := fun _ => Ideal.pow_le_pow_right (Nat.le_succ (i + 1))
    have hsq : J * J ≤ I := by
      intro U
      change J.ideal U * J.ideal U ≤ I.ideal U
      dsimp [J, I]
      rw [← Submodule.pow_add _ (by omega)]
      exact Ideal.pow_le_pow_right (by omega)
    change (Scheme.IdealSheafData.inclusion hIJ).ker ^ 2 = ⊥
    exact idealSheafInclusion_ker_sq I J hIJ hsq

/-- Each step of the base-changed filtration is the base change of the corresponding base
step. -/
lemma totalStep_isPullback {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) :
    IsPullback (totalStep t f i) (totalProjection t f i)
      (totalProjection t f (i + 1)) (baseStep t i) := by
  have hbig : IsPullback (totalInclusion t f i) (totalProjection t f i)
      f (baseInclusion t i) := IsPullback.of_hasPullback f (baseInclusion t i)
  have hfac : totalStep t f i ≫ totalProjection t f (i + 1) =
      totalProjection t f i ≫ baseStep t i := by
    rw [totalStep, pullback.lift_snd]
  apply (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback _ _) hfac).mp
  simpa [Category.assoc, totalStep_comp_inclusion, baseStep_comp_inclusion] using hbig

/-- Every step of the base-changed filtration is a first-order thickening. -/
lemma totalStep_firstOrder {S S' X' : Scheme.{u}} (t : S ⟶ S')
    (f : X' ⟶ S') (i : ℕ) :
    IsFirstOrderThickening (totalStep t f i) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (@IsFirstOrderThickening : MorphismProperty Scheme.{u}))
    (totalStep_isPullback t f i).flip (baseStep_firstOrder t i)

/-- The initial level of the filtration of the base is canonically the given closed
subscheme. -/
lemma baseInitialMap_isIso {S S' : Scheme.{u}} (t : S ⟶ S')
    (ht : IsClosedImmersion t) : IsIso (baseInitialMap t) := by
  dsimp [baseInitialMap]
  infer_instance

/-- The initial identification respects the map into the ambient scheme. -/
lemma baseInitialMap_comp_inclusion {S S' : Scheme.{u}} (t : S ⟶ S') :
    baseInitialMap t ≫ baseInclusion t 0 = t := by
  dsimp [baseInitialMap, baseInclusion, baseLevel]
  have hcomm := eqToHom_naturality
    (fun I : S'.IdealSheafData => I.subschemeι) (by simp : t.ker ^ (0 + 1) = t.ker).symm
  calc
    (t.toImage ≫ eqToHom (show t.image = (t.ker ^ (0 + 1)).subscheme by
      simp [Scheme.Hom.image])) ≫ (t.ker ^ (0 + 1)).subschemeι =
        t.toImage ≫ (eqToHom (show t.image = (t.ker ^ (0 + 1)).subscheme by
          simp [Scheme.Hom.image]) ≫ (t.ker ^ (0 + 1)).subschemeι) := by
            rw [Category.assoc]
    _ = t.toImage ≫ t.ker.subschemeι := by
      rw [← hcomm]
      simp only [eqToHom_refl, Category.comp_id]
    _ = t := t.toImage_imageι

/-- At a vanishing power of the ideal sheaf, the level of the filtration is the whole ambient
base scheme. -/
lemma baseInclusion_isIso {S S' : Scheme.{u}} (t : S ⟶ S')
    {n : ℕ} (hn : t.ker ^ (n + 1) = ⊥) : IsIso (baseInclusion t n) := by
  change IsIso ((t.ker ^ (n + 1)).subschemeι)
  rwa [Scheme.isIso_subschemeι_iff_eq_bot]

/-- The initial level of the base-changed filtration is canonically the given cartesian base
change. -/
lemma totalLevel_zero_iso {S S' X X' : Scheme.{u}}
    (t : S ⟶ S') (f : X' ⟶ S') (j : X ⟶ X') (g : X ⟶ S)
    (h : IsPullback j g f t) (ht : IsClosedImmersion t) :
    ∃ e : X ≅ totalLevel t f 0,
      e.hom ≫ totalInclusion t f 0 = j ∧
      e.hom ≫ totalProjection t f 0 = g ≫ baseInitialMap t := by
  have _ : IsIso (baseInitialMap t) := baseInitialMap_isIso t ht
  let e₀ : S ≅ baseLevel t 0 := asIso (baseInitialMap t)
  have hp : IsPullback j (g ≫ baseInitialMap t) f (baseInclusion t 0) := by
    apply h.of_iso (Iso.refl X) (Iso.refl X') e₀ (Iso.refl S') <;>
      simp [e₀, baseInitialMap_comp_inclusion]
  let e := hp.isoIsPullback _ _ (IsPullback.of_hasPullback f (baseInclusion t 0))
  exact ⟨e, by simp [e], by simp [e]⟩

/-- The final level of the base-changed filtration is canonically the original total space. -/
lemma totalInclusion_isIso {S S' X' : Scheme.{u}}
    (t : S ⟶ S') (f : X' ⟶ S') {n : ℕ}
    (hn : t.ker ^ (n + 1) = ⊥) : IsIso (totalInclusion t f n) := by
  have _ := baseInclusion_isIso t hn
  exact (IsPullback.of_hasPullback f (baseInclusion t n)).isIso_fst_of_isIso

end Stacks.Thickenings.PowerFiltration

end
