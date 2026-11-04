module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction
public import StacksFrontier.AlgebraicGeometry.Gluing.TwoChart

/-!
# Gluing two charts over an open of the base rather than over the whole base

`AlgebraicGeometry.exists_finitePresentation_isPullback_of_overPullbackIso` glues two schemes of
finite presentation over two opens `U`, `W` of `S` whose join is **all** of `S`.  The iteration
Tag 0E8Q needs runs over a *growing* open — the complement of the closed points together with the
charts already glued in — so the join is an arbitrary open `T ⊔ W`, and this file supplies that
form: the two-chart theorem applied with `S` replaced by the open subscheme `T ⊔ W`, the charts
carried along `AlgebraicGeometry.Scheme.Opens.isoPreimage`.

The two output squares are stated with the open immersions `T.ι` and `W.ι` **into `S`**, not with
the inclusions into `T ⊔ W`; by `AlgebraicGeometry.isPullback_comp_mono_iff` the two forms are
equivalent, and the form over `S` is the one that composes across the iteration, where the
ambient open changes at every step.

## Main results

* `AlgebraicGeometry.isPullback_comp_mono_iff`: cancelling a monomorphism out of the bottom-right
  corner of a cartesian square.
* `AlgebraicGeometry.Scheme.Opens.isoPreimage_hom_homOfLE`: the identifications of two nested
  opens with the opens they cut out of a third are compatible with the inclusion.
* `AlgebraicGeometry.exists_finitePresentation_isPullback_sup`: **the two-chart gluing over
  `T ⊔ W`.**
* `AlgebraicGeometry.exists_finitePresentation_isPullback_sup_of_eq`: the same with the overlap
  named by an open equal to `T ⊓ W`, which is the form the iteration consumes.

## Implementation notes

`AlgebraicGeometry.Scheme.Opens.isoPreimage` was already in the tree — it is the transport the
Noetherian-approximation induction of Tag 07RN runs on, which climbs the same chain of opens
`V ⊆ V ⊔ Y₁ ⊆ ⋯ ⊆ ⊤` for a different purpose.  Only its `inv` half and the compatibility with the
inclusion of a smaller open are added here.

No `@[stacks]` attribute is attached.  Tag 0E8Q's `equivalence` label has the single
`CategoryTheory.Functor.IsEquivalence` assertion as its covering set, so a gluing lemma earns no
part of it.

## References

* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A monomorphism cancels out of the bottom-right corner of a cartesian square.**  The square
`f ≫ (k ≫ m) = g ≫ (l ≫ m)` is cartesian exactly when `f ≫ k = g ≫ l` is, provided `m` is a
monomorphism. -/
lemma isPullback_comp_mono_iff {C : Type*} [Category C] {P X Y Z Z' : C} {f : P ⟶ X} {g : P ⟶ Y}
    {k : X ⟶ Z} {l : Y ⟶ Z} (m : Z ⟶ Z') [Mono m] :
    IsPullback f g (k ≫ m) (l ≫ m) ↔ IsPullback f g k l := by
  constructor
  · intro h
    refine ⟨⟨(cancel_mono m).mp (by simpa using h.w)⟩, ⟨PullbackCone.IsLimit.mk _
      (fun c ↦ h.lift c.fst c.snd (by rw [← Category.assoc, ← Category.assoc, c.condition]))
      (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _) fun c u hu₁ hu₂ ↦ ?_⟩⟩
    exact h.hom_ext (by rw [hu₁, h.lift_fst]) (by rw [hu₂, h.lift_snd])
  · intro h
    refine ⟨⟨by rw [← Category.assoc, ← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
      (fun c ↦ h.lift c.fst c.snd ((cancel_mono m).mp (by simpa using c.condition)))
      (fun c ↦ h.lift_fst _ _ _) (fun c ↦ h.lift_snd _ _ _) fun c u hu₁ hu₂ ↦ ?_⟩⟩
    exact h.hom_ext (by rw [hu₁, h.lift_fst]) (by rw [hu₂, h.lift_snd])

/-- Finite presentation is unchanged by composing with an isomorphism on the target. -/
lemma FinitePresentation.comp_isIso {X Y Z : Scheme.{u}} {f : X ⟶ Y} (e : Y ⟶ Z) [IsIso e]
    (hf : FinitePresentation f) : FinitePresentation (f ≫ e) := by
  obtain ⟨_, _, _⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

namespace Scheme.Opens

variable {S : Scheme.{u}} (T : S.Opens) {U : S.Opens} (hU : U ≤ T)

/-- The inverse of `isoPreimage T hU` followed by the inclusion of `U` into `T` is the open
immersion of `T.ι ⁻¹ᵁ U` into `T`. -/
@[reassoc]
lemma isoPreimage_inv_homOfLE :
    (isoPreimage T hU).inv ≫ S.homOfLE hU = (T.ι ⁻¹ᵁ U : (T : Scheme.{u}).Opens).ι := by
  rw [← isoPreimage_hom_ι T hU, Iso.inv_hom_id_assoc]

/-- **The identifications of two nested opens with the opens they cut out of a third are
compatible with the inclusion.** -/
@[reassoc]
lemma isoPreimage_hom_homOfLE {V : S.Opens} (hV : V ≤ T) (hUV : U ≤ V) :
    (isoPreimage T hU).hom ≫ (T : Scheme.{u}).homOfLE
        (show T.ι ⁻¹ᵁ U ≤ T.ι ⁻¹ᵁ V from fun _ hx ↦ hUV hx) =
      S.homOfLE hUV ≫ (isoPreimage T hV).hom := by
  rw [← cancel_mono (T.ι ⁻¹ᵁ V : (T : Scheme.{u}).Opens).ι, Category.assoc, Category.assoc,
    Scheme.homOfLE_ι, isoPreimage_hom_ι, isoPreimage_hom_ι, Scheme.homOfLE_homOfLE]

end Scheme.Opens

section Relative

variable {S : Scheme.{u}} (T W : S.Opens)

private lemma sup_preimage_sup : (T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊔ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W = ⊤ :=
  top_unique fun x _ ↦ x.2

private lemma preimage_inf_eq :
    ((T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊓ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W : (T ⊔ W : S.Opens).toScheme.Opens) =
      (T ⊔ W : S.Opens).ι ⁻¹ᵁ (T ⊓ W) :=
  rfl

/-- The identification of the open subscheme `T ⊓ W` of `S` with the intersection of the
preimages of `T` and of `W` in `T ⊔ W`. -/
private noncomputable def infPreimageIso :
    ((T ⊓ W : S.Opens) : Scheme.{u}) ≅
      (((T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊓ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W :
        (T ⊔ W : S.Opens).toScheme.Opens) : Scheme.{u}) :=
  Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) (inf_le_left.trans le_sup_left : T ⊓ W ≤ T ⊔ W)

/-- The identifications of the overlap and of `V` with their preimages in `T ⊔ W` are compatible
with the inclusion of `T ⊓ W` into `V`, for `V` one of the two opens. -/
private lemma infPreimageIso_hom_homOfLE {V : S.Opens} (hV : V ≤ T ⊔ W) (h : T ⊓ W ≤ V)
    (hle : (T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊓ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W ≤ (T ⊔ W : S.Opens).ι ⁻¹ᵁ V) :
    (infPreimageIso T W).hom ≫ ((T ⊔ W : S.Opens) : Scheme.{u}).homOfLE hle =
      S.homOfLE h ≫ (Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) hV).hom :=
  Scheme.Opens.isoPreimage_hom_homOfLE _ _ _ _

/-- The inverse image of `T ⊓ W` along a chart over `V`, computed twice: as the inverse image of
the overlap of the two preimages inside `T ⊔ W`, and as the range of the chosen base change. -/
private lemma preimage_opensRange_homOfLE_sup {V : S.Opens} (hV : V ≤ T ⊔ W) (h : T ⊓ W ≤ V)
    (hle : (T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊓ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W ≤ (T ⊔ W : S.Opens).ι ⁻¹ᵁ V)
    {A : Scheme.{u}} (a : A ⟶ (V : Scheme.{u})) :
    (a ≫ (Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) hV).hom) ⁻¹ᵁ
        (((T ⊔ W : S.Opens) : Scheme.{u}).homOfLE hle).opensRange =
      (pullback.fst a (S.homOfLE h)).opensRange := by
  rw [← preimage_opensRange_of_isPullback (IsPullback.of_hasPullback a (S.homOfLE h)),
    Scheme.Hom.comp_preimage]
  congr 1
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage,
    Scheme.Opens.isoPreimage_hom_ι, preimage_inf_eq, ← Scheme.Hom.comp_preimage,
    Scheme.homOfLE_ι]

/-- **The two-chart gluing over `T ⊔ W`.**  Two opens of `S`, a scheme of finite presentation
over each and an isomorphism of their base changes to `T ⊓ W` produce a scheme of finite
presentation over `T ⊔ W` whose restrictions to `T` and to `W` are the two given schemes,
compatibly with the given isomorphism; the two cartesian squares are stated over `S`. -/
theorem exists_finitePresentation_isPullback_sup {A B : Scheme.{u}} (a : A ⟶ (T : Scheme.{u}))
    (b : B ⟶ (W : Scheme.{u})) (ha : FinitePresentation a) (hb : FinitePresentation b)
    (φ : (Over.pullback (S.homOfLE (inf_le_left : T ⊓ W ≤ T))).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE (inf_le_right : T ⊓ W ≤ W))).obj (Over.mk b)) :
    ∃ (X : Scheme.{u}) (p : X ⟶ ((T ⊔ W : S.Opens) : Scheme.{u})) (jA : A ⟶ X) (jB : B ⟶ X),
      FinitePresentation p ∧ IsPullback a jA T.ι (p ≫ (T ⊔ W : S.Opens).ι) ∧
        IsPullback b jB W.ι (p ≫ (T ⊔ W : S.Opens).ι) ∧
        pullback.fst a (S.homOfLE (inf_le_left : T ⊓ W ≤ T)) ≫ jA =
          φ.hom.left ≫ pullback.fst b (S.homOfLE (inf_le_right : T ⊓ W ≤ W)) ≫ jB := by
  have hiso : IsIso φ.hom.left := ((Over.forget _).mapIso φ).isIso_hom
  have hw : φ.hom.left ≫ pullback.snd b (S.homOfLE (inf_le_right : T ⊓ W ≤ W)) =
      pullback.snd a (S.homOfLE (inf_le_left : T ⊓ W ≤ T)) := Over.w φ.hom
  have hf : pullback.fst a (S.homOfLE (inf_le_left : T ⊓ W ≤ T)) ≫
        (a ≫ (Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) (le_sup_left : T ≤ T ⊔ W)).hom) =
      (pullback.snd a (S.homOfLE (inf_le_left : T ⊓ W ≤ T)) ≫ (infPreimageIso T W).hom) ≫
        ((T ⊔ W : S.Opens) : Scheme.{u}).homOfLE inf_le_left := by
    simp only [Category.assoc]
    rw [infPreimageIso_hom_homOfLE T W le_sup_left inf_le_left, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  have hg : (φ.hom.left ≫ pullback.fst b (S.homOfLE (inf_le_right : T ⊓ W ≤ W))) ≫
        (b ≫ (Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) (le_sup_right : W ≤ T ⊔ W)).hom) =
      (pullback.snd a (S.homOfLE (inf_le_left : T ⊓ W ≤ T)) ≫ (infPreimageIso T W).hom) ≫
        ((T ⊔ W : S.Opens) : Scheme.{u}).homOfLE inf_le_right := by
    simp only [Category.assoc]
    rw [infPreimageIso_hom_homOfLE T W le_sup_right inf_le_right,
      ← Category.assoc (pullback.fst b _) b, pullback.condition]
    simp only [Category.assoc]
    rw [← Category.assoc φ.hom.left, hw]
  have hgr : (b ≫ (Scheme.Opens.isoPreimage (T ⊔ W : S.Opens) (le_sup_right : W ≤ T ⊔ W)).hom) ⁻¹ᵁ
        (((T ⊔ W : S.Opens) : Scheme.{u}).homOfLE
          (inf_le_right : (T ⊔ W : S.Opens).ι ⁻¹ᵁ T ⊓ (T ⊔ W : S.Opens).ι ⁻¹ᵁ W ≤
            (T ⊔ W : S.Opens).ι ⁻¹ᵁ W)).opensRange =
      (φ.hom.left ≫ pullback.fst b (S.homOfLE (inf_le_right : T ⊓ W ≤ W))).opensRange := by
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact preimage_opensRange_homOfLE_sup T W _ inf_le_right _ b
  refine ⟨_, glueChartsHom _ _ _ _ _ hf hg, Scheme.gluePairInl _ _, Scheme.gluePairInr _ _,
    finitePresentation_glueCharts_hom _ _ _ _ _ hf hg (sup_preimage_sup T W)
      (preimage_opensRange_homOfLE_sup T W _ inf_le_left _ a) hgr (ha.comp_isIso _)
      (hb.comp_isIso _),
    ?_, ?_, ?_⟩
  · refine IsOpenImmersion.isPullback a _ T.ι _ ?_ ?_
    · rw [← Category.assoc, gluePairInl_glueChartsHom]
      simp only [Category.assoc]
      rw [Scheme.Opens.isoPreimage_hom_ι_assoc, Scheme.homOfLE_ι]
    · rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]
      exact preimage_glueChartsHom_left _ _ _ _ _ hf hg hgr
  · refine IsOpenImmersion.isPullback b _ W.ι _ ?_ ?_
    · rw [← Category.assoc, gluePairInr_glueChartsHom]
      simp only [Category.assoc]
      rw [Scheme.Opens.isoPreimage_hom_ι_assoc, Scheme.homOfLE_ι]
    · rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage]
      exact preimage_glueChartsHom_right _ _ _ _ _ hf hg
        (preimage_opensRange_homOfLE_sup T W _ inf_le_left _ a)
  · exact (Scheme.gluePair_condition _ _).trans (Category.assoc _ _ _)

/-- **The two-chart gluing over `T ⊔ W`, with the overlap named.**  The statement of
`AlgebraicGeometry.exists_finitePresentation_isPullback_sup` with the overlap given as an open `O`
equal to `T ⊓ W`. -/
theorem exists_finitePresentation_isPullback_sup_of_eq (O : S.Opens) (hOT : O ≤ T) (hOW : O ≤ W)
    (hO : T ⊓ W = O) {A B : Scheme.{u}} (a : A ⟶ (T : Scheme.{u})) (b : B ⟶ (W : Scheme.{u}))
    (ha : FinitePresentation a) (hb : FinitePresentation b)
    (φ : (Over.pullback (S.homOfLE hOT)).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE hOW)).obj (Over.mk b)) :
    ∃ (X : Scheme.{u}) (p : X ⟶ ((T ⊔ W : S.Opens) : Scheme.{u})) (jA : A ⟶ X) (jB : B ⟶ X),
      FinitePresentation p ∧ IsPullback a jA T.ι (p ≫ (T ⊔ W : S.Opens).ι) ∧
        IsPullback b jB W.ι (p ≫ (T ⊔ W : S.Opens).ι) ∧
        pullback.fst a (S.homOfLE hOT) ≫ jA =
          φ.hom.left ≫ pullback.fst b (S.homOfLE hOW) ≫ jB := by
  subst hO
  exact exists_finitePresentation_isPullback_sup T W a b ha hb φ

end Relative

end AlgebraicGeometry

end
