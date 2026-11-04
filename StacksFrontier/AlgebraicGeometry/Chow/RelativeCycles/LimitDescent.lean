module

public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.CompletelyDecomposed
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CompletelyDecomposed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending the data of a relative cycle to a finite stage of a limit

Let `S = lim_{i ∈ I} S_i` be the limit of a cofiltered system of quasi-compact and
quasi-separated schemes with affine transition morphisms. The proofs of
[Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D) and
[Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W) descend a completely decomposed proper
morphism `g : S' ⟶ S` of finite presentation, together with the members of `Hilb` representing
a family of cycles after base change along `g`, to a finite stage `S_i`, and then descend the
family of cycles itself along the descended morphism. This file collects that descent.

## Main results

* `AlgebraicGeometry.isCompletelyDecomposed_of_isIso` — an isomorphism is completely decomposed.
* `AlgebraicGeometry.IsCompletelyDecomposed.of_isPullback`,
  `AlgebraicGeometry.isCompletelyDecomposed_pullback_fst` — complete decomposition is stable
  under base change, read on a cartesian square and on the first projection.
* `AlgebraicGeometry.IsPullback.pullbackSnd_of_isLimit` — a cartesian square over a stage of the
  system stays cartesian over a later stage, with the base change of its right-hand column.
* `AlgebraicGeometry.exists_isProper_isCompletelyDecomposed_model_of_isLimit` — a completely
  decomposed proper morphism `g : S' ⟶ S` of finite presentation is the base change of a
  completely decomposed proper morphism of finite presentation over some stage later than a given
  one, by Limits, Lemmas 01ZM and 081F and More on Morphisms, Lemma 0GTM.

## Implementation notes

The limit lemmas used here are stated for a morphism `f₀ : X₀ ⟶ Y₀` of `CategoryTheory.Over`
objects over a stage, base changed along the projections of the system with
`CategoryTheory.Over.pullback`. A morphism `p : Y ⟶ S_i` is fed to them as the morphism
`Over.mk p ⟶ Over.mk (𝟙 S_i)` to the terminal object of the slice, whose base change along
`h : T ⟶ S_i` is the second projection `pullback.snd p h` followed by the isomorphism
`pullback (𝟙 S_i) h ≅ T`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0GTM](https://stacks.math.columbia.edu/tag/0GTM)
* [Stacks Project, Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
* [Stacks Project, Tag 0H6W](https://stacks.math.columbia.edu/tag/0H6W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes is completely decomposed: every point of the target is the image
of its inverse image, and an isomorphism induces isomorphisms on residue fields. -/
theorem isCompletelyDecomposed_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsCompletelyDecomposed f := by
  intro y
  refine ⟨inv f y, ?_, inferInstance⟩
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

/-- Complete decomposition is stable under base change, in the form of a cartesian square: if
`f` is completely decomposed then so is its base change `snd`. -/
theorem IsCompletelyDecomposed.of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hf : IsCompletelyDecomposed f) :
    IsCompletelyDecomposed snd := by
  rw [← h.isoPullback_hom_snd]
  exact isCompletelyDecomposed_comp _ _ (isCompletelyDecomposed_of_isIso _)
    (isCompletelyDecomposed_pullback f g hf)

/-- The first projection `pullback f g ⟶ X` is completely decomposed when `g` is. -/
theorem isCompletelyDecomposed_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hg : IsCompletelyDecomposed g) : IsCompletelyDecomposed (pullback.fst f g) :=
  IsCompletelyDecomposed.of_isPullback (IsPullback.of_hasPullback f g).flip hg

/-- The base change along `h : T ⟶ S₀` of the morphism `Over.mk p ⟶ Over.mk (𝟙 S₀)` to the
terminal object of the slice over `S₀`, followed by the isomorphism `pullback (𝟙 S₀) h ≅ T`, is
the second projection `pullback.snd p h`. -/
theorem overPullback_map_homMk_left_comp_snd {Y S₀ T : Scheme.{u}} (p : Y ⟶ S₀) (h : T ⟶ S₀) :
    ((Over.pullback h).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S₀))).left ≫
      pullback.snd (𝟙 S₀) h = pullback.snd p h :=
  Over.w ((Over.pullback h).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S₀)))

/-- A property of morphisms respecting isomorphisms holds for the base change of the morphism
`Over.mk p ⟶ Over.mk (𝟙 S₀)` along `h` exactly when it holds for `pullback.snd p h`. -/
theorem overPullback_map_homMk_left_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {Y S₀ T : Scheme.{u}} (p : Y ⟶ S₀) (h : T ⟶ S₀) :
    P ((Over.pullback h).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S₀))).left ↔
      P (pullback.snd p h) := by
  rw [← overPullback_map_homMk_left_comp_snd p h]
  exact (P.cancel_right_of_respectsIso _ _).symm

/-- Complete decomposition holds for the base change of the morphism
`Over.mk p ⟶ Over.mk (𝟙 S₀)` along `h` exactly when it holds for `pullback.snd p h`. -/
theorem overPullback_map_homMk_left_isCompletelyDecomposed_iff {Y S₀ T : Scheme.{u}}
    (p : Y ⟶ S₀) (h : T ⟶ S₀) :
    IsCompletelyDecomposed
        ((Over.pullback h).map (Over.homMk p (by simp) : Over.mk p ⟶ Over.mk (𝟙 S₀))).left ↔
      IsCompletelyDecomposed (pullback.snd p h) := by
  rw [← overPullback_map_homMk_left_comp_snd p h]
  refine ⟨fun hq => isCompletelyDecomposed_comp _ _ hq (isCompletelyDecomposed_of_isIso _),
    fun hq => ?_⟩
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    isCompletelyDecomposed_comp _ _ hq
      (isCompletelyDecomposed_of_isIso (inv (pullback.snd (𝟙 S₀) h)))

/-- A cartesian square over a stage of a system stays cartesian over a later stage: if `S'` is the
base change of `p : Y ⟶ D.obj i` along the projection `c.π.app i`, then it is the base change of
`pullback.snd p (D.map u)` along `c.π.app j` for every `u : j ⟶ i`. -/
theorem IsPullback.pullbackSnd_of_isLimit {I : Type*} [Category I] {D : I ⥤ Scheme.{u}}
    (c : Cone D) {i j : I} (u : j ⟶ i) {S' Y : Scheme.{u}} {a : S' ⟶ Y} {g : S' ⟶ c.pt}
    {p : Y ⟶ D.obj i} (hpb : IsPullback a g p (c.π.app i)) :
    IsPullback (pullback.lift a (g ≫ c.π.app j) (by rw [hpb.w, Category.assoc, c.w u]))
      g (pullback.snd p (D.map u)) (c.π.app j) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p (D.map u))
  rw [pullback.lift_fst, c.w u]
  exact hpb

/-- **Descending a completely decomposed proper morphism of finite presentation.** Let
`S = lim_{i ∈ I} S_i` be the limit of a cofiltered system of quasi-compact and quasi-separated
schemes with affine transition morphisms and let `g : S' ⟶ S` be proper, completely decomposed
and locally of finite presentation. For every stage `i₀` there are a later stage `i` and a
proper, completely decomposed morphism `gᵢ : T ⟶ S_i` locally of finite presentation whose base
change along `S ⟶ S_i` is `g`.

The morphism `g` is of finite presentation, being proper, so by Limits, Lemma 01ZM it is the
base change of a morphism of finite presentation over some stage; by Limits, Lemma 081F that
morphism becomes proper over a later stage and by More on Morphisms, Lemma 0GTM completely
decomposed over a still later one. -/
@[ega "IV 8.1.2" "partial"]
theorem exists_isProper_isCompletelyDecomposed_model_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)
    (hc : IsLimit c) {S' : Scheme.{u}} (g : S' ⟶ c.pt) [IsProper g]
    [LocallyOfFinitePresentation g] (hg : IsCompletelyDecomposed g) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀) (T : Scheme.{u}) (gᵢ : T ⟶ D.obj i)
      (e : S' ≅ pullback (c.π.app i) gᵢ),
      IsProper gᵢ ∧ LocallyOfFinitePresentation gᵢ ∧ IsCompletelyDecomposed gᵢ ∧
        e.hom ≫ pullback.fst (c.π.app i) gᵢ = g := by
  have hfp : FinitePresentation g := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i₁, Y, p, a, hp, hpb⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall D c hc g hfp
  have : LocallyOfFinitePresentation p := hp.1
  have : QuasiCompact p := hp.2.1
  have : QuasiSeparated p := hp.2.2
  have (k : I) : CompactSpace (Over.mk (𝟙 (D.obj k))).left :=
    inferInstanceAs (CompactSpace (D.obj k))
  have (k : I) : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj k))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj k))
  -- Move to a stage below both `i₀` and `i₁`.
  let k := IsCofiltered.min i₀ i₁
  let p₁ := pullback.snd p (D.map (IsCofiltered.minToRight i₀ i₁))
  have hpb₁ := IsPullback.pullbackSnd_of_isLimit c (IsCofiltered.minToRight i₀ i₁) hpb
  -- Properness at a later stage (Tag 081F).
  have : CompactSpace (Over.mk p₁).left :=
    QuasiCompact.compactSpace_of_compactSpace (X := pullback p _) p₁
  have : QuasiSeparatedSpace (Over.mk p₁).left :=
    quasiSeparatedSpace_of_quasiSeparated (X := pullback p _) p₁
  let f₁ : Over.mk p₁ ⟶ Over.mk (𝟙 (D.obj k)) := Over.homMk p₁ (by simp)
  have : LocallyOfFiniteType f₁.left := inferInstanceAs (LocallyOfFiniteType p₁)
  have : IsProper ((Over.pullback (c.π.app k)).map f₁).left := by
    refine (overPullback_map_homMk_left_iff @IsProper p₁ (c.π.app k)).mpr ?_
    rw [← hpb₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j₁, w₁, hprop⟩ := exists_isProper_baseChange_of_isLimit D c k hc _ _ f₁
  let p₂ := pullback.snd p₁ (D.map w₁)
  have : IsProper p₂ := (overPullback_map_homMk_left_iff @IsProper p₁ (D.map w₁)).mp hprop
  have hpb₂ := IsPullback.pullbackSnd_of_isLimit c w₁ hpb₁
  -- Complete decomposition at a later stage (Tag 0GTM).
  let f₂ : Over.mk p₂ ⟶ Over.mk (𝟙 (D.obj j₁)) := Over.homMk p₂ (by simp)
  have : LocallyOfFinitePresentation f₂.left := inferInstanceAs (LocallyOfFinitePresentation p₂)
  have hcd₂ : IsCompletelyDecomposed ((Over.pullback (c.π.app j₁)).map f₂).left := by
    refine (overPullback_map_homMk_left_isCompletelyDecomposed_iff p₂ (c.π.app j₁)).mpr ?_
    rw [← hpb₂.isoPullback_inv_snd]
    exact isCompletelyDecomposed_comp _ _ (isCompletelyDecomposed_of_isIso _) hg
  obtain ⟨j₂, w₂, hcd⟩ :=
    exists_isCompletelyDecomposed_baseChange_of_limitBaseChange D c hc j₁ _ _ f₂ hcd₂
  have hcd' : IsCompletelyDecomposed (pullback.snd p₂ (D.map w₂)) :=
    (overPullback_map_homMk_left_isCompletelyDecomposed_iff p₂ (D.map w₂)).mp hcd
  have hpb₃ := IsPullback.pullbackSnd_of_isLimit c w₂ hpb₂
  refine ⟨j₂, w₂ ≫ w₁ ≫ IsCofiltered.minToLeft i₀ i₁, _, pullback.snd p₂ (D.map w₂),
    hpb₃.flip.isoPullback, inferInstance, inferInstance, hcd', hpb₃.flip.isoPullback_hom_fst⟩

/-! ### The canonical identification `X_i ×_{S_i} S ≅ X` -/

section Comparison

variable {I : Type*} [Category I] (D : I ⥤ Scheme.{u}) (c : Cone D) {i i₀ : I} (u : i ⟶ i₀)
  {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ D.obj i₀)

/-- The canonical morphism `(X₀ ×_{S₀} S_i) ×_{S_i} S ⟶ X₀ ×_{S₀} S` for a stage `u : i ⟶ i₀` of
the system: it identifies the base change to the limit of `X_i = X₀ ×_{S₀} S_i` with
`X = X₀ ×_{S₀} S`, over `S`. -/
def limitComparison :
    pullback (pullback.snd f₀ (D.map u)) (c.π.app i) ⟶ pullback f₀ (c.π.app i₀) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, c.w u])

/-- The first projection of `limitComparison` to `X₀` is the composite of the two first
projections `(X₀ ×_{S₀} S_i) ×_{S_i} S ⟶ X₀ ×_{S₀} S_i ⟶ X₀`. -/
@[reassoc (attr := simp)]
theorem limitComparison_fst :
    limitComparison D c u f₀ ≫ pullback.fst f₀ (c.π.app i₀) =
      pullback.fst _ _ ≫ pullback.fst f₀ (D.map u) :=
  pullback.lift_fst _ _ _

/-- The second projection of `limitComparison` to `S` is the second projection
`(X₀ ×_{S₀} S_i) ×_{S_i} S ⟶ S`. -/
@[reassoc (attr := simp)]
theorem limitComparison_snd :
    limitComparison D c u f₀ ≫ pullback.snd f₀ (c.π.app i₀) =
      pullback.snd (pullback.snd f₀ (D.map u)) (c.π.app i) :=
  pullback.lift_snd _ _ _

/-- The canonical comparison morphism is an isomorphism: it is the composite of the pasting
isomorphism `(X₀ ×_{S₀} S_i) ×_{S_i} S ≅ X₀ ×_{S₀} S` with the identification of the two maps
`S ⟶ S₀`. -/
instance isIso_limitComparison : IsIso (limitComparison D c u f₀) := by
  have hpb : IsPullback (pullback.fst _ _ ≫ pullback.fst f₀ (D.map u))
      (pullback.snd (pullback.snd f₀ (D.map u)) (c.π.app i)) f₀ (c.π.app i₀) := by
    rw [← c.w u]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  have he : limitComparison D c u f₀ = hpb.isoPullback.hom :=
    pullback.hom_ext (by simp) (by simp)
  rw [he]
  infer_instance

end Comparison

end AlgebraicGeometry

end
