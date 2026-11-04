module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale

/-!
# Étale coverings and morphisms out of base changes of a limit come from a finite stage

Let `S = lim S_i` be the limit of a cofiltered inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, and let `{E_k → S}` be a jointly
surjective family of étale morphisms.  Then there are a stage `S_i` and finitely many
quasi-compact and quasi-separated schemes `Y_a` étale over `S_i` whose base changes
`Y_a ×_{S_i} S` cover `S` and each factor through some member `E_k` of the given family.  So
every étale covering of `S` is refined by the base change of a finite family of étale morphisms
to a stage; that family becomes jointly surjective after a further base change.

Two companion statements are about the base change `Y ×_{S_i} S` of a scheme `Y` over a stage:
an open of `Y` containing its image already contains the image of `Y ×_{S_i} S_j` for a later
stage `S_j` (Stacks 01Z4), and a morphism from it to a scheme locally of finite presentation
over a common base factors through `Y ×_{S_i} S_j` for a later stage (Stacks 01ZC).

## Main results

* `AlgebraicGeometry.exists_etale_stage_of_etale_cover_of_isLimit`: the descent of étale
  coverings described above.
* `AlgebraicGeometry.exists_range_pullback_snd_subset_of_isLimit`: an open of `Y` containing the
  image of `Y ×_{S_i} S` contains the image of `Y ×_{S_i} S_j` for some later stage.
* `AlgebraicGeometry.exists_hom_pullback_comp_eq_of_isLimit`: a morphism over the base from
  `Y ×_{S_i} S` to a scheme locally of finite presentation over the base is defined on
  `Y ×_{S_i} S_j` for some later stage.
* `AlgebraicGeometry.exists_etale_isPullback_of_isLimit` and
  `AlgebraicGeometry.exists_stage_forall_etale_isPullback_of_isLimit`: an affine scheme étale
  over a limit of affine schemes is the base change of an affine scheme étale over a stage, and
  finitely many of them are base changes from one stage.
* `AlgebraicGeometry.etale_overPullback_map_homMk_iff`: the base change of a morphism `p`, viewed
  as a morphism to the final object of the slice, is étale exactly when the base change
  `pullback.snd p g` is.

## Implementation notes

The descent of étale coverings follows the source.  Around every point of `S` choose an affine
open of a member of the family; its image is an open neighbourhood of the point and, `S` being
quasi-compact, finitely many of them cover `S`.  Each such affine scheme is étale, hence of finite
presentation, over the quasi-compact and quasi-separated scheme `S`, so it is the base change of
a scheme of finite presentation over a stage (Stacks 01ZM), which becomes étale over a later
stage (Stacks 07RP).  A common later stage of the finitely many stages so obtained is the stage of
the statement.

The two companion statements are Mathlib's `AlgebraicGeometry.exists_map_preimage_le_map_preimage`
and `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` applied to the
inverse system `j ↦ Y ×_{S_i} S_j` of `AlgebraicGeometry.baseChangeDiagram`, whose limit is
`Y ×_{S_i} S`.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change along `g` of a morphism `p : Y ⟶ Z`, viewed as a morphism of `Over Z` to the
final object, is étale exactly when the base change `pullback.snd p g` of `p` is étale. -/
lemma etale_overPullback_map_homMk_iff {Y Z Z' : Scheme.{u}} (p : Y ⟶ Z) (g : Z' ⟶ Z) :
    Etale ((Over.pullback g).map
        (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 Z))).left ↔
      Etale (pullback.snd p g) := by
  have h : ((Over.pullback g).map
      (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 Z))).left ≫
        pullback.snd (𝟙 Z) g = pullback.snd p g :=
    Over.w ((Over.pullback g).map
      (Over.homMk p (Category.comp_id p) : Over.mk p ⟶ Over.mk (𝟙 Z)))
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← h, MorphismProperty.cancel_right_of_respectsIso (@Etale)]

/-- A scheme `X` of finite presentation over a stage `S_i` whose base change to the limit is
étale has étale base change to some later stage. -/
private lemma exists_etale_overPullback_of_etale_pullback_snd
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] {i : I} {X : Scheme.{u}}
    (f : X ⟶ D.obj i) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace (D.obj i)]
    [QuasiSeparatedSpace (D.obj i)] [LocallyOfFinitePresentation f]
    (h : Etale (pullback.snd f (c.π.app i))) :
    ∃ ψ : Over i, Etale ((Over.pullback (D.map ψ.hom)).map
      (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 (D.obj i)))).left := by
  have : CompactSpace (Over.mk f).left := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (Over.mk f).left := inferInstanceAs (QuasiSeparatedSpace X)
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation
      (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (LocallyOfFinitePresentation f)
  have : Etale ((Over.pullback (c.π.app i)).map
      (Over.homMk f (Category.comp_id f) : Over.mk f ⟶ Over.mk (𝟙 (D.obj i)))).left :=
    (etale_overPullback_map_homMk_iff f _).2 h
  exact exists_etale_pullback_of_isLimit D c hc i _ _ _

variable {I : Type u} [SmallCategory I] [IsCofiltered I]

/-- **Étale coverings of a limit come from a finite stage.** Let `S = lim S_i` be a cofiltered
limit of quasi-compact and quasi-separated schemes with affine transition morphisms and let
`{E_k → S}` be a jointly surjective family of étale morphisms.  Then there are a stage `i` and a
finite family of quasi-compact and quasi-separated schemes `Y_a` étale over `S_i` such that the
base changes `Y_a ×_{S_i} S → S` are jointly surjective and each factors through a member of the
family. -/
theorem exists_etale_stage_of_etale_cover_of_isLimit
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    {ι : Type*} (E : ι → Scheme.{u}) (f : ∀ k, E k ⟶ c.pt) [∀ k, Etale (f k)]
    (hE : ∀ x : c.pt, ∃ k, x ∈ Set.range (f k)) :
    ∃ (i : I) (A : Type u) (_ : Finite A) (Y : A → Scheme.{u}) (p : ∀ a, Y a ⟶ D.obj i)
      (k : A → ι) (e : ∀ a, pullback (c.π.app i) (p a) ⟶ E (k a)),
      (∀ a, Etale (p a)) ∧ (∀ a, CompactSpace (Y a)) ∧ (∀ a, QuasiSeparatedSpace (Y a)) ∧
      (∀ a, e a ≫ f (k a) = pullback.fst _ _) ∧
      ∀ x : c.pt, ∃ a, x ∈ Set.range (pullback.fst (c.π.app i) (p a)) := by
  classical
  obtain ⟨i₁⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (c.π.app i₁) := isAffineHom_π_app D c hc i₁
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₁)
  have h₁ : ∀ x : c.pt, ∃ (k : ι) (U : (E k).affineOpens),
      x ∈ Set.range ((U : (E k).Opens).ι ≫ f k) := by
    intro x
    obtain ⟨k, e₀, rfl⟩ := hE x
    obtain ⟨U, hU, he₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (E k).isBasis_affineOpens) (show e₀ ∈ (⊤ : (E k).Opens) from trivial)
    obtain ⟨w, hw⟩ : e₀ ∈ Set.range (Scheme.Opens.ι U) := by rwa [Scheme.Opens.range_ι]
    exact ⟨k, ⟨U, hU⟩, w, by rw [Scheme.Hom.comp_apply, hw]⟩
  choose k U hU using h₁
  let V (x : c.pt) : Scheme.{u} := ((U x : (E (k x)).Opens) : Scheme.{u})
  let v (x : c.pt) : V x ⟶ c.pt := (U x : (E (k x)).Opens).ι ≫ f (k x)
  have : ∀ x, IsAffine (V x) := fun x => (U x).2
  have : ∀ x, Etale (v x) := fun x => inferInstanceAs (Etale (_ ≫ _))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (v x))
    (fun x => (v x).isOpenMap.isOpen_range) (fun x _ => Set.mem_iUnion.mpr ⟨x, hU x⟩)
  choose i₀ Y₀ p₀ g hp₀ hpb using fun x => LimitDescent.exists_isPullback_of_finitePresentation
    D c hc (v x) ⟨inferInstance, inferInstance, inferInstance⟩
  have h₃ : ∀ x : c.pt, ∃ ψ : Over (i₀ x), Etale ((Over.pullback (D.map ψ.hom)).map
      (Over.homMk (p₀ x) (Category.comp_id _) : Over.mk (p₀ x) ⟶ Over.mk (𝟙 _))).left := by
    intro x
    have : LocallyOfFinitePresentation (p₀ x) := (hp₀ x).1
    have : QuasiCompact (p₀ x) := (hp₀ x).2.1
    have : QuasiSeparated (p₀ x) := (hp₀ x).2.2
    have : CompactSpace (Y₀ x) := QuasiCompact.compactSpace_of_compactSpace (p₀ x)
    have : QuasiSeparatedSpace (Y₀ x) := quasiSeparatedSpace_of_quasiSeparated (p₀ x)
    exact exists_etale_overPullback_of_etale_pullback_snd D c hc (p₀ x)
      (by rw [← (hpb x).isoPullback_inv_snd]; infer_instance)
  choose ψ hψ using h₃
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (t.image fun x => (ψ x).left)
  have hm : ∀ x : t, Nonempty (i ⟶ (ψ x.1).left) := fun x =>
    hi (Finset.mem_image_of_mem _ x.2)
  let φ (x : t) : i ⟶ i₀ x.1 := (hm x).some ≫ (ψ x.1).hom
  have hφ : ∀ x : t, Etale (pullback.snd (p₀ x.1) (D.map (φ x))) := by
    intro x
    rw [← etale_overPullback_map_homMk_iff]
    have h := overPullback_map_comp (@Etale) (D.map (ψ x.1).hom) (D.map (hm x).some)
      (Over.homMk (p₀ x.1) (Category.comp_id _) : Over.mk (p₀ x.1) ⟶ Over.mk (𝟙 _)) (hψ x.1)
    rwa [← D.map_comp] at h
  refine ⟨i, t, inferInstance, fun x => pullback (D.map (φ x)) (p₀ x.1),
    fun x => pullback.fst (D.map (φ x)) (p₀ x.1), fun x => k x.1,
    fun x => (hpb x.1).lift (pullback.snd _ _ ≫ pullback.snd _ _) (pullback.fst _ _) ?_ ≫
      (U x.1 : (E (k x.1)).Opens).ι, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition,
      Category.assoc, c.w]
  · intro x
    show Etale (pullback.fst _ _)
    rw [← pullbackSymmetry_hom_comp_snd]
    have := hφ x
    infer_instance
  · intro x
    have : QuasiCompact (p₀ x.1) := (hp₀ x.1).2.1
    have : QuasiCompact (pullback.fst (D.map (φ x)) (p₀ x.1)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map (φ x)) (p₀ x.1))
  · intro x
    have : QuasiSeparated (p₀ x.1) := (hp₀ x.1).2.2
    have : QuasiSeparated (pullback.fst (D.map (φ x)) (p₀ x.1)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map (φ x)) (p₀ x.1))
  · exact fun x => (Category.assoc _ _ _).trans ((hpb x.1).lift_snd _ _ _)
  · intro y
    obtain ⟨x, hx, w, rfl⟩ : ∃ x ∈ t, y ∈ Set.range (v x) := by
      simpa using ht (Set.mem_univ y)
    have h₄ : p₀ x (g x w) = D.map (φ ⟨x, hx⟩) (c.π.app i (v x w)) := by
      rw [← Scheme.Hom.comp_apply, (hpb x).w, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        c.w]
    obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₄.symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (v x w) q hq.symm
    exact ⟨⟨x, hx⟩, z, hz⟩

/-- The range of the base change of `r` along `f'` lies in that along `f` when `f'` factors
through `f`. -/
lemma range_pullback_snd_subset_of_fac {A A' B Z : Scheme.{u}} (f : A ⟶ B) (f' : A' ⟶ B)
    (h : A' ⟶ A) (hh : h ≫ f = f') (r : Z ⟶ B) :
    Set.range (pullback.snd f' r) ⊆ Set.range (pullback.snd f r) := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
  refine Set.preimage_mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨h a, by rw [← Scheme.Hom.comp_apply, hh]⟩

/-- **Opens containing the base change of a limit.** Let `S = lim S_i` be a cofiltered limit
with affine transition morphisms, `r : Z ⟶ S_i` a morphism with quasi-compact source and `O` an
open of `Z` containing the image of `Z ×_{S_i} S`.  Then `O` contains the image of
`Z ×_{S_i} S_j` for some stage `j` over `i`. -/
lemma exists_range_pullback_snd_subset_of_isLimit
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i : I} {Z : Scheme.{u}} [CompactSpace Z]
    (r : Z ⟶ D.obj i) (O : Z.Opens)
    (hO : Set.range (pullback.snd (c.π.app i) r) ⊆ O) :
    ∃ (j : I) (f : j ⟶ i), Set.range (pullback.snd (D.map f) r) ⊆ O := by
  let X : Over (D.obj i) := Over.mk r
  have : CompactSpace X.left := inferInstanceAs (CompactSpace Z)
  have : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i X).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i X g
  have : ∀ a : Over i, CompactSpace ((baseChangeDiagram D i X).obj a) :=
    fun a => compactSpace_baseChangeDiagram_obj D i X a
  let j₀ : Over i := Over.mk (𝟙 i)
  have e₀ : (baseChangeCone D c i X).π.app j₀ ≫ pullback.snd (D.map j₀.hom) r =
      pullback.snd (c.π.app i) r := by
    rw [baseChangeCone_π_app]
    exact baseChangeTransition_snd _ _ _ _ X
  obtain ⟨j, g, hg⟩ := exists_map_preimage_le_map_preimage (baseChangeDiagram D i X)
    (baseChangeCone D c i X) (baseChangeConeIsLimit D hc i X) (i := j₀) (U := ⊤)
    (V := pullback.snd (D.map j₀.hom) r ⁻¹ᵁ O)
    (by
      rw [TopologicalSpace.Opens.coe_top]
      exact @isCompact_univ _ _ (this j₀)) (by
      intro x _
      show ((baseChangeCone D c i X).π.app j₀ ≫ pullback.snd (D.map j₀.hom) r) x ∈ O
      rw [e₀]
      exact hO (Set.mem_range_self x))
  refine ⟨j.left, j.hom, ?_⟩
  rintro _ ⟨y, rfl⟩
  have e₁ : (baseChangeDiagram D i X).map g ≫ pullback.snd (D.map j₀.hom) r =
      pullback.snd (D.map j.hom) r := by
    rw [baseChangeDiagram_map]
    exact baseChangeTransition_snd _ _ _ _ X
  have hy : ((baseChangeDiagram D i X).map g ≫ pullback.snd (D.map j₀.hom) r) y ∈ O :=
    hg (show y ∈ (baseChangeDiagram D i X).map g ⁻¹ᵁ ⊤ from trivial)
  rwa [e₁] at hy

/-- **Morphisms out of the base change of a limit come from a stage.** Let `S = lim S_i` be a
cofiltered limit of quasi-compact and quasi-separated schemes with affine transition morphisms,
all over a base `B` through `τ`, let `p : Y ⟶ S_i` have quasi-compact and quasi-separated
source and let `x : X ⟶ B` be locally of finite presentation.  A morphism
`Y ×_{S_i} S ⟶ X` over `B` is the composite of the projection to `Y ×_{S_i} S_j` with a
morphism `Y ×_{S_i} S_j ⟶ X` over `B`, for some stage `j` over `i` (Stacks 01ZC). -/
lemma exists_hom_pullback_comp_eq_of_isLimit
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {B X : Scheme.{u}} (τ : D ⟶ (Functor.const I).obj B)
    (x : X ⟶ B) [LocallyOfFinitePresentation x] {i : I} {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (p : Y ⟶ D.obj i) (h : pullback (c.π.app i) p ⟶ X)
    (hh : h ≫ x = pullback.fst _ _ ≫ c.π.app i ≫ τ.app i) :
    ∃ (j : I) (f : j ⟶ i) (g : pullback (D.map f) p ⟶ X),
      pullback.lift (pullback.fst _ _ ≫ c.π.app j) (pullback.snd _ _)
          (by rw [Category.assoc, c.w, pullback.condition]) ≫ g = h ∧
        g ≫ x = pullback.fst _ _ ≫ τ.app j := by
  let Xp : Over (D.obj i) := Over.mk p
  have : CompactSpace Xp.left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace Xp.left := inferInstanceAs (QuasiSeparatedSpace Y)
  have : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i Xp).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i Xp g
  have : ∀ a : Over i, CompactSpace ((baseChangeDiagram D i Xp).obj a) :=
    fun a => compactSpace_baseChangeDiagram_obj D i Xp a
  have : ∀ a : Over i, QuasiSeparatedSpace ((baseChangeDiagram D i Xp).obj a) :=
    fun a => quasiSeparatedSpace_baseChangeDiagram_obj D i Xp a
  obtain ⟨a, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (baseChangeDiagram D i Xp)
    (baseChangeStructureMap D i Xp ≫ (Functor.const (Over i)).map (τ.app i)) x
    (baseChangeCone D c i Xp) (baseChangeConeIsLimit D hc i Xp) h (by
      ext a
      have e : baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp ≫
          pullback.snd (D.map a.hom) Xp.hom = pullback.snd (c.π.app i) Xp.hom :=
        baseChangeTransition_snd _ _ _ _ Xp
      show baseChangeTransition (D.map a.hom) (c.π.app i) (c.π.app a.left) (by simp) Xp ≫
        (pullback.snd (D.map a.hom) Xp.hom ≫ p) ≫ τ.app i = h ≫ x
      rw [hh, ← Category.assoc, ← Category.assoc, e]
      show (pullback.snd (c.π.app i) p ≫ p) ≫ τ.app i = _
      rw [← pullback.condition, Category.assoc])
  refine ⟨a.left, a.hom, g, hg₁, hg₂.trans ?_⟩
  have hτ : D.map a.hom ≫ τ.app i = τ.app a.left := by simp
  show (pullback.snd (D.map a.hom) p ≫ p) ≫ τ.app i = pullback.fst (D.map a.hom) p ≫ τ.app a.left
  rw [Category.assoc, ← pullback.condition_assoc, hτ]

/-- A pullback square exhibiting a scheme over the limit as the base change of a scheme over a
stage `S_i` stays a pullback square after base change to a later stage `S_b`. -/
lemma isPullback_pullback_lift_of_isPullback {J : Type*} [Category* J] (D : J ⥤ Scheme.{u})
    (c : Cone D) {i b : J} (h : b ⟶ i) {V W : Scheme.{u}} {e : V ⟶ c.pt} {w : W ⟶ D.obj i}
    {g : V ⟶ W} (H : IsPullback g e w (c.π.app i)) :
    IsPullback (pullback.lift g (e ≫ c.π.app b) (by rw [H.w, Category.assoc, c.w]))
      e (pullback.snd w (D.map h)) (c.π.app b) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback w (D.map h))
  rw [pullback.lift_fst, c.w]
  exact H

/-- **Affine étale schemes over a limit descend to a stage.** Let `S = lim S_i` be the limit of
a cofiltered system of affine schemes with affine transition morphisms.  Every affine scheme `V`
étale over `S` is the base change `V = W ×_{S_i} S` of an affine scheme `W` étale over some
stage `S_i` (Stacks 01ZM and 07RP). -/
theorem exists_etale_isPullback_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]
    {V : Scheme.{u}} [IsAffine V] (e : V ⟶ c.pt) [Etale e] :
    ∃ (i : I) (W : Scheme.{u}) (w : W ⟶ D.obj i) (g : V ⟶ W),
      IsAffine W ∧ Etale w ∧ IsPullback g e w (c.π.app i) := by
  obtain ⟨i, X, f, g, hX, hf, hpb⟩ := exists_isPullback_of_isAffine_of_isLimit D c hc e
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨j, hj⟩ := exists_etale_overPullback_of_etale_pullback_snd D c hc f (by
    rw [← hpb.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (@Etale)]
    infer_instance)
  rw [etale_overPullback_map_homMk_iff] at hj
  exact ⟨j.left, _, _, _, inferInstance, hj, isPullback_pullback_lift_of_isPullback D c j.hom hpb⟩

/-- **Finitely many affine étale schemes over a limit descend to a common stage.** Let
`S = lim S_i` be the limit of a cofiltered system of affine schemes with affine transition
morphisms.  Finitely many affine schemes `V_k` étale over `S` are base changes
`V_k = W_k ×_{S_i} S` of affine schemes `W_k` étale over one stage `S_i`. -/
theorem exists_stage_forall_etale_isPullback_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]
    {ι : Type*} [Finite ι] (V : ι → Scheme.{u}) [∀ k, IsAffine (V k)] (e : ∀ k, V k ⟶ c.pt)
    [∀ k, Etale (e k)] :
    ∃ i : I, ∀ k, ∃ (W : Scheme.{u}) (w : W ⟶ D.obj i) (g : V k ⟶ W),
      IsAffine W ∧ Etale w ∧ IsPullback g (e k) w (c.π.app i) := by
  classical
  have := Fintype.ofFinite ι
  choose i W w g hW hw hg using fun k ↦ exists_etale_isPullback_of_isLimit D c hc (e k)
  obtain ⟨b, hb⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  refine ⟨b, fun k ↦ ?_⟩
  let h : b ⟶ i k := (hb (Finset.mem_image_of_mem i (Finset.mem_univ k))).some
  have := hw k
  have := hW k
  exact ⟨pullback (w k) (D.map h), pullback.snd _ _, _, inferInstance, inferInstance,
    isPullback_pullback_lift_of_isPullback D c h (hg k)⟩

end AlgebraicGeometry
