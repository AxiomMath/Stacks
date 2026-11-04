module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RXFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent

/-!
# Gluing cartesian spans across a pushout along a thickening

Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y` an affine morphism and `Y' = Y ⨿_X X'` the pushout
of [Stacks Project, Tag 07RT]. A *cartesian span* over `Y ⟵ X ⟶ X'` is a diagram
`Z_Y ⟵ Z_X ⟶ Z_{X'}` of schemes over `Y`, `X` and `X'` whose two squares over `f` and over `i`
are cartesian. This file reads Tags 07RV and 07RX in that language, which is how they are used
for the stack of polarized schemes (Stacks Tag 0D44):

* **gluing**: every cartesian span is the restriction of a scheme `Z` over `Y'` along cartesian
  squares, and `Z` is the pushout `Z_Y ⨿_{Z_X} Z_{X'}`; if both legs of the span are flat
  (and locally of finite presentation), so is `Z` over `Y'`, and if moreover `Z_Y ⟶ Y` is
  proper then so is `Z ⟶ Y'`;
* **descent of the gluing**: conversely, for `Z` flat over `Y'` and any commutative cube over
  the square of the base with cartesian vertical faces, the top face is a pushout.

The second statement is the closing paragraph of Tag 07RX — the counit `G(F(W')) ⟶ W'` is an
isomorphism for `W'` flat — for an arbitrary cube instead of the canonical base changes.

## Main definitions

* `Stacks.Pushout.spanGluingData`: the compatible pair of Tag 07RV attached to a cartesian span.

## Main results

* `Stacks.Pushout.exists_glue_of_cartesianSpan`: the gluing of a cartesian span.
* `Stacks.Pushout.isPushout_of_cartesianCube`: the top face of a cartesian cube over a flat
  scheme is a pushout.
* `Stacks.Pushout.isProper_of_isPullback_inr`: properness over `Y'` is detected over `Y`, for a
  morphism locally of finite type.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)

/-- A morphism of compatible pairs is an isomorphism as soon as its two underlying morphisms of
schemes are. -/
theorem isIso_of_isIso_left_left_of_isIso_right_left {T S : gluingData i f} (φ : T ⟶ S)
    (h₁ : IsIso φ.hom.left.left) (h₂ : IsIso φ.hom.right.left) : IsIso φ := by
  have : IsIso ((Over.forget Y).map φ.hom.left) := h₁
  have : IsIso ((Over.forget X').map φ.hom.right) := h₂
  have : IsIso φ.hom.left := isIso_of_reflects_iso φ.hom.left (Over.forget Y)
  have : IsIso φ.hom.right := isIso_of_reflects_iso φ.hom.right (Over.forget X')
  let e := Comma.isoMk (asIso φ.hom.left) (asIso φ.hom.right) φ.hom.w
  have he : e.hom = φ.hom := by apply Comma.hom_ext <;> rfl
  have : IsIso φ.hom := he ▸ e.isIso_hom
  exact (ObjectProperty.isIso_hom_iff φ).mp inferInstance

section Span

variable {ZY ZX' ZX : Scheme.{u}} {qY : ZY ⟶ Y} {qX' : ZX' ⟶ X'} {qX : ZX ⟶ X}
  {u : ZX ⟶ ZY} {v : ZX ⟶ ZX'}

/-- The identification of the two base changes to `X` of the legs of a cartesian span, both being
the middle term of the span. -/
noncomputable def spanComparison (hu : IsPullback u qX qY f) (hv : IsPullback v qX qX' i) :
    (Over.pullback f).obj (Over.mk qY) ≅ (Over.pullback i).obj (Over.mk qX') :=
  Over.isoMk (hu.isoPullback.symm ≪≫ hv.isoPullback) (by
    change (hu.isoPullback.inv ≫ hv.isoPullback.hom) ≫ pullback.snd qX' i = pullback.snd qY f
    rw [Category.assoc, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd])

/-- **The compatible pair of a cartesian span**: its two legs, identified over `X` through the
middle term. -/
noncomputable def spanGluingData (hu : IsPullback u qX qY f) (hv : IsPullback v qX qX' i) :
    gluingData i f :=
  ⟨⟨Over.mk qY, Over.mk qX', (spanComparison i f hu hv).hom⟩, inferInstance⟩

/-- The middle term of a cartesian span maps to the common restriction of its compatible pair
compatibly with the map to the `Y`-leg. -/
theorem spanComparison_gluingSourceMap (hu : IsPullback u qX qY f)
    (hv : IsPullback v qX qX' i) :
    hv.isoPullback.hom ≫ gluingSourceMap i f (spanGluingData i f hu hv) = u := by
  have : IsIso (spanGluingData i f hu hv).obj.hom := (spanGluingData i f hu hv).property
  have hinv : inv (spanGluingData i f hu hv).obj.hom = (spanComparison i f hu hv).inv :=
    IsIso.inv_eq_of_hom_inv_id (spanComparison i f hu hv).hom_inv_id
  have hsrc : gluingSourceMap i f (spanGluingData i f hu hv) =
      (inv (spanGluingData i f hu hv).obj.hom).left ≫ pullback.fst qY f := rfl
  rw [hsrc, hinv]
  show hv.isoPullback.hom ≫ (hv.isoPullback.inv ≫ hu.isoPullback.hom) ≫ pullback.fst qY f = u
  simp

variable (hi : IsThickening i) [IsAffineHom f]

omit [IsAffineHom f] in
/-- The glued scheme of a cartesian span is the pushout of the span. -/
theorem isPushout_spanGlue (hu : IsPullback u qX qY f) (hv : IsPullback v qX qX' i)
    [HasPushout i f]
    [HasPushout (pullback.fst (spanGluingData i f hu hv).obj.right.hom i)
      (gluingSourceMap i f (spanGluingData i f hu hv))] :
    IsPushout u v
      (pushout.inr (pullback.fst (spanGluingData i f hu hv).obj.right.hom i)
        (gluingSourceMap i f (spanGluingData i f hu hv)))
      (pushout.inl (pullback.fst (spanGluingData i f hu hv).obj.right.hom i)
        (gluingSourceMap i f (spanGluingData i f hu hv))) :=
  (IsPushout.of_hasPushout (pullback.fst (spanGluingData i f hu hv).obj.right.hom i)
    (gluingSourceMap i f (spanGluingData i f hu hv))).flip.of_iso' hv.isoPullback (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
    ((spanComparison_gluingSourceMap i f hu hv).trans (Category.comp_id u).symm)
    (hv.isoPullback_hom_fst.trans (Category.comp_id v).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- **The gluing of a cartesian span** (Tags 07RV and 07RX). A cartesian span
`Z_Y ⟵ Z_X ⟶ Z_{X'}` over `Y ⟵ X ⟶ X'` is the restriction of a scheme `Z` over `Y' = Y ⨿_X X'`
along two cartesian squares, `Z` is the pushout `Z_Y ⨿_{Z_X} Z_{X'}`, the map `Z_Y ⟶ Z` is a
thickening, and `Z` is flat (and locally of finite presentation) over `Y'` as soon as both legs
of the span are. -/
theorem exists_glue_of_cartesianSpan (hu : IsPullback u qX qY f) (hv : IsPullback v qX qX' i) :
    letI := hasPushout_of_isThickening i f hi
    ∃ (Z : Scheme.{u}) (q : Z ⟶ pushout i f) (c : ZY ⟶ Z) (d : ZX' ⟶ Z),
      IsPullback c qY q (pushout.inr i f) ∧ IsPullback d qX' q (pushout.inl i f) ∧
        IsPushout u v c d ∧ IsThickening c ∧ (Flat qY → Flat qX' → Flat q) ∧
        (Flat qY → LocallyOfFinitePresentation qY → Flat qX' →
          LocallyOfFinitePresentation qX' → LocallyOfFinitePresentation q) := by
  let := hasPushout_of_isThickening i f hi
  let T := spanGluingData i f hu hv
  let := gluingHasPushout i f hi T
  obtain ⟨hc, hd⟩ := gluing_components_isPullback i f hi T
  exact ⟨_, ((gluingFunctor i f hi).obj T).hom, _, _, hc, hd, isPushout_spanGlue i f hu hv,
    gluing_inr_isThickening i f hi T,
    fun h₁ h₂ ↦ (flat_gluingFunctor_obj_iff i f hi T).mpr ⟨h₁, h₂⟩,
    fun h₁ h₂ h₃ h₄ ↦ ((flat_and_locallyOfFinitePresentation_gluingFunctor_obj_iff i f hi T).mpr
      ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩).2⟩

/-- A morphism into a pullback square's pullback, with the components of the cartesian cone, is
an isomorphism. -/
private theorem isIso_of_comp_eq_isoPullback {A B C D : Scheme.{u}} {c : A ⟶ B} {a : A ⟶ C}
    {q : B ⟶ D} {g : C ⟶ D} (h : IsPullback c a q g) (e : A ⟶ pullback q g)
    (h₁ : e ≫ pullback.fst q g = c) (h₂ : e ≫ pullback.snd q g = a) : IsIso e := by
  have : e = h.isoPullback.hom :=
    pullback.hom_ext (by rw [h₁, h.isoPullback_hom_fst]) (by rw [h₂, h.isoPullback_hom_snd])
  rw [this]
  infer_instance

/-- **The top face of a cartesian cube over a flat scheme is a pushout** (the closing paragraph
of Tag 07RX, for an arbitrary cube). Let `Z` be flat over `Y' = Y ⨿_X X'`, and let `Z_Y ⟶ Z` and
`Z_{X'} ⟶ Z` be cartesian over `Y ⟶ Y'` and `X' ⟶ Y'`. Then for any scheme `Z_X` over `X` with
morphisms to `Z_Y` (cartesian over `f`) and to `Z_{X'}` (over `i`) making the cube commute, the
square `Z_X, Z_Y, Z_{X'}, Z` is a pushout. -/
theorem isPushout_of_cartesianCube :
    letI := hasPushout_of_isThickening i f hi
    ∀ {Z : Scheme.{u}} (q : Z ⟶ pushout i f) {c : ZY ⟶ Z} {d : ZX' ⟶ Z},
      Flat q → IsPullback c qY q (pushout.inr i f) → IsPullback d qX' q (pushout.inl i f) →
      IsPullback u qX qY f → v ≫ qX' = qX ≫ i → u ≫ c = v ≫ d → IsPushout u v c d := by
  let := hasPushout_of_isThickening i f hi
  intro Z q c d hq hc hd hu hvi huv
  have hv : IsPullback v qX qX' i := by
    have h := hu.paste_horiz hc
    rw [huv, ← pushout.condition] at h
    exact IsPullback.of_right h hvi hd
  let T := spanGluingData i f hu hv
  let := gluingHasPushout i f hi T
  let cG : ZY ⟶ pushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    pushout.inr (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)
  let dG : ZX' ⟶ pushout (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T) :=
    pushout.inl (pullback.fst T.obj.right.hom i) (gluingSourceMap i f T)
  have hP : IsPushout u v cG dG := isPushout_spanGlue i f hu hv
  let k := hP.desc c d huv
  have hkc : cG ≫ k = c := hP.inl_desc c d huv
  have hkd : dG ≫ k = d := hP.inr_desc c d huv
  have hkq : k ≫ q = ((gluingFunctor i f hi).obj T).hom := by
    apply hP.hom_ext
    · rw [reassoc_of% hkc, hc.w]
      exact (gluingPushoutData_inr i f T).symm
    · rw [reassoc_of% hkd, hd.w]
      exact (gluingPushoutData_inl i f T).symm
  let K : (gluingFunctor i f hi).obj T ⟶ Over.mk q := Over.homMk k hkq
  have : IsIso K := isIso_of_isIso_gluingToPair i f hi K hq
    (isIso_of_isIso_left_left_of_isIso_right_left i f _
      (isIso_of_comp_eq_isoPullback hc _ ((gluingToPair_left_comp_fst i f hi K).trans hkc)
        (gluingToPair_left_comp_snd i f hi K))
      (isIso_of_comp_eq_isoPullback hd _ ((gluingToPair_right_comp_fst i f hi K).trans hkd)
        (gluingToPair_right_comp_snd i f hi K)))
  have : IsIso k := inferInstanceAs (IsIso ((Over.forget _).map K))
  exact hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso k)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (hkc.trans (Category.id_comp c).symm) (hkd.trans (Category.id_comp d).symm)

include hi in
/-- **Properness over the pushout is detected over `Y`.** If `Z ⟶ Y'` is locally of finite type
and its base change `Z_Y ⟶ Y` along `Y ⟶ Y'` is proper, then `Z ⟶ Y'` is proper: the map
`Z_Y ⟶ Z` is a thickening, hence a surjective closed immersion, across which universal closedness
and separatedness descend. -/
theorem isProper_of_isPullback_inr [HasPushout i f] {Z : Scheme.{u}} {q : Z ⟶ pushout i f}
    {c : ZY ⟶ Z} (hc : IsPullback c qY q (pushout.inr i f)) [LocallyOfFiniteType q]
    [IsProper qY] : IsProper q := by
  have hinr := pushout_inr_isThickening forall_isAffine_of_isThickening i f hi
  have hcth : IsThickening c := isThickening_of_isPullback hc hinr
  have : IsClosedImmersion (pushout.inr i f) := hinr.1
  have : IsClosedImmersion c := hcth.1
  have : Surjective c := ⟨hcth.2⟩
  have : UniversallyClosed (c ≫ q) := by
    rw [hc.w]
    infer_instance
  have : UniversallyClosed q :=
    universallyClosed_of_jointly_surjective c c q (fun x ↦ .inl (c.surjective x))
  let cO : (Over.mk (qY ≫ pushout.inr i f) : Over (pushout i f)) ⟶ Over.mk q :=
    Over.homMk c hc.w
  have : Surjective cO.left := inferInstanceAs (Surjective c)
  have : UniversallyClosed cO.left := inferInstanceAs (UniversallyClosed c)
  have : IsSeparated (Over.mk (qY ≫ pushout.inr i f) : Over (pushout i f)).hom :=
    inferInstanceAs (IsSeparated (qY ≫ pushout.inr i f))
  have : IsSeparated q := isSeparated_of_surjective_universallyClosed cO
  exact ⟨⟩

end Span

end Stacks.Pushout

end
