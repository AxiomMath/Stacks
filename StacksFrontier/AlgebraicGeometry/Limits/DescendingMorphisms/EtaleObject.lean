module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale schemes over a limit come from a stage

Let `S = lim S_i` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms. This file records, in the form in which
the small étale sites of the `S_i` and of `S` use them, the three facts which make the category
of quasi-compact and quasi-separated schemes étale over `S` the colimit of the corresponding
categories over the `S_i`:

* a quasi-compact and quasi-separated scheme `A` étale over `S` is the base change of a
  quasi-compact and quasi-separated scheme étale over some stage (Stacks 01ZM and 07RP);
* such a presentation of `A` as a base change persists along the later stages;
* a morphism from `A` to a scheme locally of finite presentation over a stage `S_i`, over `S_i`,
  comes from a morphism defined over a later stage (Stacks 01ZC).

Presentations are recorded as cartesian squares `IsPullback θ v p (c.π.app i)` rather than as
isomorphisms with a chosen fibre product, which makes them independent of the orientation of the
fibre product; the base changes along later stages are formed as `pullback p (D.map e)`, which
is the orientation of base change on small étale sites.

## Main results

* `AlgebraicGeometry.exists_isPullback_etale_of_isLimit`: the descent of a quasi-compact and
  quasi-separated scheme étale over the limit.
* `AlgebraicGeometry.exists_isAffineOpen_isPullback_etale_of_isLimit`: every point of a scheme
  étale over the limit has an affine open neighbourhood coming from a stage, with no hypotheses
  on the stages.
* `AlgebraicGeometry.exists_isPullback_etale_of_isLimit_of_hom`: the same without hypotheses on
  the stages, for a scheme lying over the base change of a quasi-compact and quasi-separated
  scheme étale over a stage.
* `AlgebraicGeometry.isPullback_lift_of_isPullback`: the transport of a presentation to a later
  stage.
* `AlgebraicGeometry.exists_hom_of_isPullback_of_isLimit`: the descent of a morphism to a scheme
  locally of finite presentation over a stage.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A pair of points with the same image in the base comes from a point of any pullback
square. -/
lemma IsPullback.exists_preimage_scheme {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ z : P, fst z = x ∧ snd z = y := by
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv w, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw₁]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hw₂]

/-- **Base changes of a morphism over a stage.** Let `ζ : Z ⟶ W` be a morphism over `S_i`, from
`p ≫ e : Z ⟶ S_l ⟶ S_i` to `w : W ⟶ S_i`. Base changing along `φ : S_{l'} ⟶ S_l` gives a
pullback square
`Z ×_{S_l} S_{l'} ⟶ Z`, `W ×_{S_i} S_{l'} ⟶ W ×_{S_i} S_l`. -/
lemma isPullback_pullback_lift_of_comp {C : Type*} [Category* C] [HasPullbacks C]
    {Z W Sl Sl' Si : C} (p : Z ⟶ Sl) (w : W ⟶ Si) (e : Sl ⟶ Si) (φ : Sl' ⟶ Sl) (e' : Sl' ⟶ Si)
    (he' : φ ≫ e = e') (ζ : Z ⟶ W) (hζ : ζ ≫ w = p ≫ e) :
    IsPullback (pullback.fst p φ)
      (pullback.lift (pullback.fst p φ ≫ ζ) (pullback.snd p φ)
        (by rw [Category.assoc, hζ, ← he', pullback.condition_assoc]))
      (pullback.lift ζ p hζ)
      (pullback.lift (pullback.fst w e') (pullback.snd w e' ≫ φ)
        (by rw [pullback.condition, Category.assoc, he'])) := by
  have hbot : IsPullback (pullback.lift (pullback.fst w e') (pullback.snd w e' ≫ φ)
        (by rw [pullback.condition, Category.assoc, he'])) (pullback.snd w e')
      (pullback.snd w e) φ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst w e) (h₂₂ := e) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback w e)
    rw [pullback.lift_fst, he']
    exact IsPullback.of_hasPullback w e'
  refine IsPullback.of_bot ?_ ?_ hbot
  · rw [pullback.lift_snd, pullback.lift_snd]
    exact IsPullback.of_hasPullback p φ
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, pullback.condition]

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)

omit [IsCofiltered I] in
/-- **A presentation as a base change persists along later stages.** If `A` is the base change
of `p : Y ⟶ S_i` along the projection `S ⟶ S_i`, then for every later stage `e : S_j ⟶ S_i` it is
the base change of the base change `Y ×_{S_i} S_j ⟶ S_j` along `S ⟶ S_j`. -/
lemma isPullback_lift_of_isPullback {i : I} {A Y : Scheme.{u}} {θ : A ⟶ Y} {v : A ⟶ c.pt}
    {p : Y ⟶ D.obj i} (h : IsPullback θ v p (c.π.app i)) {j : I} (e : j ⟶ i) :
    IsPullback (pullback.lift θ (v ≫ c.π.app j) (by rw [h.w, Category.assoc, c.w]))
      v (pullback.snd p (D.map e)) (c.π.app j) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p (D.map e)) (h₂₂ := D.map e) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p (D.map e))
  rw [pullback.lift_fst, c.w]
  exact h

variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

section QcqsStages

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **Quasi-compact and quasi-separated schemes étale over the limit come from a stage** (Stacks
01ZM and 07RP). Let `S = lim S_i` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, and let `v : A ⟶ S` be étale with `A`
quasi-compact and quasi-separated. Then `A` is the base change of a morphism `p : Y ⟶ S_i` which
is étale, with `Y` quasi-compact and quasi-separated. -/
theorem exists_isPullback_etale_of_isLimit (hc : IsLimit c) {A : Scheme.{u}} [CompactSpace A]
    [QuasiSeparatedSpace A] (v : A ⟶ c.pt) [Etale v] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (θ : A ⟶ Y),
      Etale p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsPullback θ v p (c.π.app i) := by
  obtain ⟨i₁⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c.π.app i₁) := isAffineHom_π_app D c hc i₁
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₁)
  obtain ⟨i₀, Y₀, p₀, g, ⟨_, _, _⟩, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation D c hc v
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : CompactSpace (Over.mk p₀).left := QuasiCompact.compactSpace_of_compactSpace p₀
  have : QuasiSeparatedSpace (Over.mk p₀).left := quasiSeparatedSpace_of_quasiSeparated p₀
  have : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (CompactSpace (D.obj i₀))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have : LocallyOfFinitePresentation
      (Over.homMk p₀ (Category.comp_id _) : Over.mk p₀ ⟶ Over.mk (𝟙 _)).left :=
    inferInstanceAs (LocallyOfFinitePresentation p₀)
  have : Etale ((Over.pullback (c.π.app i₀)).map
      (Over.homMk p₀ (Category.comp_id _) : Over.mk p₀ ⟶ Over.mk (𝟙 _))).left := by
    rw [etale_overPullback_map_homMk_iff, ← hpb.isoPullback_inv_snd]
    infer_instance
  obtain ⟨ψ, hψ⟩ := exists_etale_pullback_of_isLimit D c hc i₀ _ _
    (Over.homMk p₀ (Category.comp_id _) : Over.mk p₀ ⟶ Over.mk (𝟙 _))
  rw [etale_overPullback_map_homMk_iff] at hψ
  have : QuasiCompact (pullback.snd p₀ (D.map ψ.hom)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  have : QuasiSeparated (pullback.snd p₀ (D.map ψ.hom)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
  exact ⟨ψ.left, pullback p₀ (D.map ψ.hom), pullback.snd _ _, _, hψ,
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p₀ (D.map ψ.hom)),
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p₀ (D.map ψ.hom)),
    isPullback_lift_of_isPullback D c hpb ψ.hom⟩

end QcqsStages

private instance isAffineHom_baseChangeDiagram_map_mk {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {a b : Over i} (g : a ⟶ b) : IsAffineHom ((baseChangeDiagram D i (Over.mk p)).map g) :=
  isAffineHom_baseChangeDiagram_map D i (Over.mk p) g

private instance compactSpace_baseChangeDiagram_obj_mk {i : I} {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [CompactSpace Y] (a : Over i) : CompactSpace ((baseChangeDiagram D i (Over.mk p)).obj a) :=
  have : CompactSpace (Over.mk p).left := ‹_›
  compactSpace_baseChangeDiagram_obj D i (Over.mk p) a

private instance quasiSeparatedSpace_baseChangeDiagram_obj_mk {i : I} {Y : Scheme.{u}}
    (p : Y ⟶ D.obj i) [QuasiSeparatedSpace Y] (a : Over i) :
    QuasiSeparatedSpace ((baseChangeDiagram D i (Over.mk p)).obj a) :=
  have : QuasiSeparatedSpace (Over.mk p).left := ‹_›
  quasiSeparatedSpace_baseChangeDiagram_obj D i (Over.mk p) a

/-- **Morphisms out of a base change to the limit come from a stage** (Stacks 01ZC). Let
`S = lim S_i` be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, let `A` be the base change of `p : Y ⟶ S_i` along the
projection, with `Y` quasi-compact and quasi-separated, and let `x : T ⟶ S_i` be locally of
finite presentation. A morphism `h : A ⟶ T` over `S_i` is the composite of the projection
`A ⟶ Y ×_{S_i} S_j` with a morphism `Y ×_{S_i} S_j ⟶ T` over `S_i`, for some later stage `S_j`. -/
@[ega "IV 8.13.1" "surjectivity"]
lemma exists_hom_of_isPullback_of_isLimit (hc : IsLimit c) {i : I} {A Y T : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] {θ : A ⟶ Y} {v : A ⟶ c.pt} {p : Y ⟶ D.obj i}
    (hθ : IsPullback θ v p (c.π.app i)) (x : T ⟶ D.obj i) [LocallyOfFinitePresentation x]
    (h : A ⟶ T) (hh : h ≫ x = v ≫ c.π.app i) :
    ∃ (j : I) (e : j ⟶ i) (g : pullback p (D.map e) ⟶ T),
      pullback.lift θ (v ≫ c.π.app j) (by rw [hθ.w, Category.assoc, c.w]) ≫ g = h ∧
        g ≫ x = pullback.fst p (D.map e) ≫ p := by
  let Xp : Over (D.obj i) := Over.mk p
  let e₀ : A ≅ pullback (c.π.app i) p := hθ.flip.isoPullback
  obtain ⟨a, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D i Xp) (baseChangeStructureMap D i Xp) x
    (baseChangeCone D c i Xp) (baseChangeConeIsLimit D hc i Xp) (e₀.inv ≫ h) (by
      ext a
      have e : baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp ≫
          pullback.snd (D.map a.hom) p = pullback.snd (c.π.app i) p :=
        baseChangeTransition_snd (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp
      show baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp ≫
        pullback.snd (D.map a.hom) p ≫ p = (e₀.inv ≫ h) ≫ x
      rw [← Category.assoc, e, Category.assoc, hh, ← Category.assoc,
        hθ.flip.isoPullback_inv_fst]
      exact pullback.condition.symm)
  let tr : pullback (c.π.app i) p ⟶ pullback (D.map a.hom) p := (baseChangeCone D c i Xp).π.app a
  have tr_fst : tr ≫ pullback.fst (D.map a.hom) p = pullback.fst (c.π.app i) p ≫ c.π.app a.left :=
    baseChangeTransition_fst (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp
  have tr_snd : tr ≫ pullback.snd (D.map a.hom) p = pullback.snd (c.π.app i) p :=
    baseChangeTransition_snd (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp
  let g' : pullback (D.map a.hom) p ⟶ T := g
  have hg₁' : tr ≫ g' = e₀.inv ≫ h := hg₁
  have hg₂' : g' ≫ x = pullback.snd (D.map a.hom) p ≫ p := hg₂
  refine ⟨a.left, a.hom, (pullbackSymmetry p (D.map a.hom)).hom ≫ g', ?_, ?_⟩
  · have hlift : pullback.lift θ (v ≫ c.π.app a.left) (by rw [hθ.w, Category.assoc, c.w]) ≫
        (pullbackSymmetry p (D.map a.hom)).hom = e₀.hom ≫ tr := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd, Category.assoc,
          tr_fst, ← Category.assoc, hθ.flip.isoPullback_hom_fst]
      · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst, Category.assoc,
          tr_snd, hθ.flip.isoPullback_hom_snd]
    rw [reassoc_of% hlift, hg₁', Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hg₂', ← Category.assoc, pullbackSymmetry_hom_comp_snd]

/-- **Morphisms out of a base change to the limit come from a stage**, with the target over an
earlier stage than the presentation: the variant of
`AlgebraicGeometry.exists_hom_of_isPullback_of_isLimit` in which `x : T ⟶ S_i` and the
presentation of `A` lives over a later stage `S_j`, `e : S_j ⟶ S_i`. -/
lemma exists_hom_of_isPullback_of_isLimit' (hc : IsLimit c) {i j : I} (e : j ⟶ i)
    {A Y T : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {θ : A ⟶ Y} {v : A ⟶ c.pt}
    {p : Y ⟶ D.obj j} (hθ : IsPullback θ v p (c.π.app j)) (x : T ⟶ D.obj i)
    [LocallyOfFinitePresentation x] (h : A ⟶ T) (hh : h ≫ x = v ≫ c.π.app i) :
    ∃ (l : I) (b : l ⟶ j) (g : pullback p (D.map b) ⟶ T),
      pullback.lift θ (v ≫ c.π.app l) (by rw [hθ.w, Category.assoc, c.w]) ≫ g = h ∧
        g ≫ x = pullback.fst p (D.map b) ≫ p ≫ D.map e := by
  obtain ⟨l, b, g, hg₁, hg₂⟩ := exists_hom_of_isPullback_of_isLimit D c hc hθ
    (pullback.snd x (D.map e)) (pullback.lift h (v ≫ c.π.app j) (by rw [hh, Category.assoc, c.w]))
    (pullback.lift_snd _ _ _)
  refine ⟨l, b, g ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [reassoc_of% hg₁, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, reassoc_of% hg₂]

/-- **Quasi-compact and quasi-separated schemes étale over the base change of a stage object come
from a stage.** Let `S = lim S_i` be the limit of a cofiltered inverse system of schemes with
affine transition morphisms, let `p₀ : Y₀ ⟶ S_i` be étale with `Y₀` quasi-compact and
quasi-separated, and let `v : A ⟶ S` be étale with `A` quasi-compact and quasi-separated, such
that `v` lifts to `Y₀ ×_{S_i} S`. Then `A` is the base change of a morphism `p : Y ⟶ S_j` which is
étale, with `Y` quasi-compact and quasi-separated, at some later stage `j`. No hypothesis is put
on the stages `S_i`: the descent takes place in the inverse system `Y₀ ×_{S_i} S_j` of
quasi-compact and quasi-separated schemes, whose limit is `Y₀ ×_{S_i} S`
(`AlgebraicGeometry.exists_isPullback_etale_of_isLimit` for that system). -/
theorem exists_isPullback_etale_of_isLimit_of_hom (hc : IsLimit c) {i : I} {Y₀ : Scheme.{u}}
    (p₀ : Y₀ ⟶ D.obj i) [Etale p₀] [CompactSpace Y₀] [QuasiSeparatedSpace Y₀] {A : Scheme.{u}}
    [CompactSpace A] [QuasiSeparatedSpace A] (v : A ⟶ c.pt) [Etale v] (w : A ⟶ Y₀)
    (hw : w ≫ p₀ = v ≫ c.π.app i) :
    ∃ (j : I) (_ : j ⟶ i) (Y : Scheme.{u}) (p : Y ⟶ D.obj j) (θ : A ⟶ Y),
      Etale p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsPullback θ v p (c.π.app j) := by
  let Xp : Over (D.obj i) := Over.mk p₀
  let v' : A ⟶ pullback (c.π.app i) p₀ := pullback.lift v w hw.symm
  have : Etale (pullback.fst (c.π.app i) p₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (c.π.app i) p₀).flip inferInstance
  have : Etale (v' ≫ pullback.fst (c.π.app i) p₀) := by
    rw [pullback.lift_fst]
    infer_instance
  have : Etale v' := Etale.of_comp v' (pullback.fst (c.π.app i) p₀)
  have : @Etale A (baseChangeCone D c i Xp).pt v' := this
  obtain ⟨a, Y, p, θ, hp, hYc, hYs, hθ⟩ :=
    exists_isPullback_etale_of_isLimit (baseChangeDiagram D i Xp) (baseChangeCone D c i Xp)
      (baseChangeConeIsLimit D hc i Xp) (A := A) v'
  have : Etale (pullback.fst (D.map a.hom) p₀) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D.map a.hom) p₀).flip
      inferInstance
  have hbot : IsPullback (baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left)
      (by simp) Xp) (pullback.fst (c.π.app i) p₀) (pullback.fst (D.map a.hom) p₀)
      (c.π.app a.left) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd (D.map a.hom) p₀) (h₂₂ := D.map a.hom) ?_
      (baseChangeTransition_fst _ _ _ _ _) (IsPullback.of_hasPullback (D.map a.hom) p₀).flip
    have e₁ : baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp ≫
        pullback.snd (D.map a.hom) p₀ = pullback.snd (c.π.app i) p₀ :=
      baseChangeTransition_snd _ _ _ _ Xp
    rw [e₁, c.w]
    exact (IsPullback.of_hasPullback (c.π.app i) p₀).flip
  have e₂ : v' ≫ pullback.fst (c.π.app i) p₀ = v := pullback.lift_fst _ _ _
  let p' : Y ⟶ pullback (D.map a.hom) p₀ := p
  have : Etale p' := hp
  have h' : IsPullback θ v (p' ≫ pullback.fst (D.map a.hom) p₀) (c.π.app a.left) :=
    e₂ ▸ hθ.paste_vert hbot
  exact ⟨a.left, a.hom, Y, p' ≫ pullback.fst (D.map a.hom) p₀, θ, inferInstance, hYc, hYs, h'⟩

/-- **Every point of a scheme étale over the limit has an affine open neighbourhood which comes
from a stage.** Let `S = lim S_i` be the limit of a cofiltered inverse system of schemes with
affine transition morphisms and let `v : U ⟶ S` be étale. Every point of `U` has an affine open
neighbourhood `U''` such that `U'' ⟶ S` is the base change of an étale morphism `p : Y ⟶ S_j`
with `Y` quasi-compact and quasi-separated. -/
theorem exists_isAffineOpen_isPullback_etale_of_isLimit (hc : IsLimit c) {U : Scheme.{u}}
    (v : U ⟶ c.pt) [Etale v] (x : U) :
    ∃ U'' : U.Opens, IsAffineOpen U'' ∧ x ∈ U'' ∧ ∃ (j : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj j)
      (θ : (U'' : Scheme.{u}) ⟶ Y), Etale p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
        IsPullback θ (U''.ι ≫ v) p (c.π.app j) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let h := v ≫ c.π.app i₀
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (h x))
  obtain ⟨U'', hU'', hxU'', hle⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ h ⁻¹ᵁ W from hxW)
  have : IsAffine U''.toScheme := hU''
  have : IsAffine W.toScheme := hW
  obtain ⟨j, -, Y, p, θ, hp, hYc, hYs, hθ⟩ := exists_isPullback_etale_of_isLimit_of_hom D c hc
    (i := i₀) W.ι (A := U''.toScheme) (U''.ι ≫ v) (h.resLE W U'' hle)
    ((Scheme.Hom.resLE_comp_ι h hle).trans (Category.assoc _ _ _).symm)
  exact ⟨U'', hU'', hxU'', j, Y, p, θ, hp, hYc, hYs, hθ⟩

end AlgebraicGeometry
