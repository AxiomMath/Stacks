module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factorizations through closed immersions over a limit descend to a stage

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact and quasi-separated schemes with affine
transition morphisms. For a closed immersion `ι : R₀ ⟶ P₀` of finite presentation and a morphism
`φ : X₀ ⟶ P₀` of schemes over a stage `X_{i₀}`, if the base change of `φ` to the limit factors
through the base change of `ι`, then the base change of `φ` to some later stage factors through
that of `ι`: the closed immersion `φ⁻¹(R₀) ⟶ X₀` becomes an isomorphism over the limit, hence
over a stage by Stacks 081E.

This is the form in which the proof of Stacks 0GI5 descends the axioms of an étale equivalence
relation `R ⊆ N ×_V N` (reflexivity, symmetry, transitivity) from the limit to a stage.

## Main results

* `CategoryTheory.IsPullback.isIso_fst_of_mono_of_factors`: in a pullback square whose right
  edge is a monomorphism through which the bottom edge factors, the left edge is an isomorphism.
* `AlgebraicGeometry.exists_factor_baseChange_of_isClosedImmersion`: the descent.

## References

* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z}

/-- In a pullback square whose right edge `g` is a monomorphism through which the bottom edge
`f` factors, the left edge `fst` is an isomorphism. -/
@[sga "3 IV 1.14" "more general", sga "3 VIB 2.11" "partial"]
theorem isIso_fst_of_mono_of_factors (h : IsPullback fst snd f g) [Mono g] {ψ : X ⟶ Y}
    (hψ : ψ ≫ g = f) : IsIso fst := by
  refine ⟨h.lift (𝟙 X) ψ (by rw [Category.id_comp, hψ]), ?_, h.lift_fst _ _ _⟩
  apply h.hom_ext
  · rw [Category.assoc, h.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, h.lift_snd, Category.id_comp, ← cancel_mono g, Category.assoc, hψ, h.w]

end CategoryTheory.IsPullback


namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasBinaryProducts C] [HasPullbacks C] {N R : C}
  (ι : R ⟶ N ⨯ N)

/-- The diagonal `N ⟶ N × N`, the map tested by reflexivity of a relation `R ⟶ N × N`. -/
noncomputable abbrev relRefl (N : C) : N ⟶ N ⨯ N := prod.lift (𝟙 N) (𝟙 N)

/-- The relation `R ⟶ N × N` followed by the swap, the map tested by symmetry. -/
noncomputable abbrev relSymm : R ⟶ N ⨯ N := ι ≫ prod.lift prod.snd prod.fst

/-- The map `R ×_{t, N, s} R ⟶ N × N` taking the outer coordinates, the map tested by
transitivity. -/
noncomputable abbrev relTrans : pullback (ι ≫ prod.snd) (ι ≫ prod.fst) ⟶ N ⨯ N :=
  prod.lift (pullback.fst _ _ ≫ ι ≫ prod.fst) (pullback.snd _ _ ≫ ι ≫ prod.snd)

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **A factorization through a closed immersion over the limit exists at a stage.** -/
theorem exists_factor_baseChange_of_isClosedImmersion (i₀ : I)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    {X₀ P₀ R₀ : Over (D.obj i₀)} (ι : R₀ ⟶ P₀) [IsClosedImmersion ι.left]
    [LocallyOfFinitePresentation ι.left] (φ : X₀ ⟶ P₀) [CompactSpace X₀.left]
    [QuasiSeparatedSpace X₀.left]
    (hlim : ∃ ψ, ψ ≫ (Over.pullback (c.π.app i₀)).map ι = (Over.pullback (c.π.app i₀)).map φ) :
    ∃ (i : I) (g : i ⟶ i₀) (ψ : (Over.pullback (D.map g)).obj X₀ ⟶
        (Over.pullback (D.map g)).obj R₀),
      ψ ≫ (Over.pullback (D.map g)).map ι = (Over.pullback (D.map g)).map φ := by
  have hmono : Mono ι := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ι.left))
  let Q₀ := pullback φ ι
  let π₁ : Q₀ ⟶ X₀ := pullback.fst φ ι
  let π₂ : Q₀ ⟶ R₀ := pullback.snd φ ι
  have hsq : IsPullback π₁ π₂ φ ι := IsPullback.of_hasPullback φ ι
  have hsqS : IsPullback π₁.left π₂.left φ.left ι.left := hsq.map (Over.forget _)
  have : IsClosedImmersion π₁.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsqS.flip inferInstance
  have : LocallyOfFinitePresentation π₁.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsqS.flip inferInstance
  have : CompactSpace Q₀.left := QuasiCompact.compactSpace_of_compactSpace π₁.left
  have : QuasiSeparatedSpace Q₀.left := quasiSeparatedSpace_of_quasiSeparated π₁.left
  obtain ⟨ψ, hψ⟩ := hlim
  have hF : IsIso ((Over.pullback (c.π.app i₀)).map π₁) := by
    have h := hsq.map (Over.pullback (c.π.app i₀))
    have : Mono ((Over.pullback (c.π.app i₀)).map ι) := inferInstance
    exact h.isIso_fst_of_mono_of_factors hψ
  have : IsIso ((Over.pullback (c.π.app i₀)).map π₁).left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback (c.π.app i₀)).map π₁)))
  obtain ⟨i, g, hg⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc i₀ Q₀ X₀ π₁
  have : IsIso ((Over.forget _).map ((Over.pullback (D.map g)).map π₁)) := hg
  have : IsIso ((Over.pullback (D.map g)).map π₁) :=
    isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨i, g, inv ((Over.pullback (D.map g)).map π₁) ≫ (Over.pullback (D.map g)).map π₂, ?_⟩
  rw [Category.assoc, ← Functor.map_comp, ← hsq.w, Functor.map_comp, IsIso.inv_hom_id_assoc]

include hc in
omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- **A limit isomorphism of `π₁ : φ⁻¹(R₀) ⟶ X₀`** from a factorization over the limit: the
pullback of a monomorphism along a map factoring through it is an isomorphism. -/
theorem isIso_pullback_fst_left_of_factor (i₀ : I) {X₀ P₀ R₀ : Over (D.obj i₀)} (ι : R₀ ⟶ P₀)
    [Mono ((Over.pullback (c.π.app i₀)).map ι)] (φ : X₀ ⟶ P₀)
    {ψ : (Over.pullback (c.π.app i₀)).obj X₀ ⟶ (Over.pullback (c.π.app i₀)).obj R₀}
    (hψ : ψ ≫ (Over.pullback (c.π.app i₀)).map ι =
      (Over.pullback (c.π.app i₀)).map φ) :
    IsIso ((Over.pullback (c.π.app i₀)).map (pullback.fst φ ι)).left := by
  have : IsIso ((Over.pullback (c.π.app i₀)).map (pullback.fst φ ι)) :=
    ((IsPullback.of_hasPullback φ ι).map (Over.pullback (c.π.app i₀))).isIso_fst_of_mono_of_factors
      hψ
  exact inferInstanceAs (IsIso ((Over.forget (c.pt)).map
    ((Over.pullback (c.π.app i₀)).map (pullback.fst φ ι))))

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- **From an isomorphism of `π₁ : φ⁻¹(R₀) ⟶ X₀` at a stage, a factorization at that stage.** -/
theorem exists_factor_of_isIso_pullback_fst_left {i₀ k : I} (g : k ⟶ i₀)
    {X₀ P₀ R₀ : Over (D.obj i₀)} (ι : R₀ ⟶ P₀) (φ : X₀ ⟶ P₀)
    (h : IsIso ((Over.pullback (D.map g)).map (pullback.fst φ ι)).left) :
    ∃ ψ : (Over.pullback (D.map g)).obj X₀ ⟶ (Over.pullback (D.map g)).obj R₀,
      ψ ≫ (Over.pullback (D.map g)).map ι = (Over.pullback (D.map g)).map φ := by
  have : IsIso ((Over.forget _).map ((Over.pullback (D.map g)).map (pullback.fst φ ι))) := h
  have : IsIso ((Over.pullback (D.map g)).map (pullback.fst φ ι)) :=
    isIso_of_reflects_iso _ (Over.forget _)
  refine ⟨inv ((Over.pullback (D.map g)).map (pullback.fst φ ι)) ≫
    (Over.pullback (D.map g)).map (pullback.snd φ ι), ?_⟩
  rw [Category.assoc, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
    IsIso.inv_hom_id_assoc]

include hc in
/-- **The isomorphism `φ⁻¹(R₀) ≅ X₀` of a factorization over the limit holds at a stage**, in the
form used by `AlgebraicGeometry.common_stage_of_finite`. -/
theorem exists_isIso_pullback_fst_left (i₀ : I)
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    {X₀ P₀ R₀ : Over (D.obj i₀)} (ι : R₀ ⟶ P₀) [QuasiCompact ι.left] [QuasiSeparated ι.left]
    [LocallyOfFinitePresentation ι.left] [Mono ((Over.pullback (c.π.app i₀)).map ι)]
    (φ : X₀ ⟶ P₀) [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    (hlim : ∃ ψ, ψ ≫ (Over.pullback (c.π.app i₀)).map ι = (Over.pullback (c.π.app i₀)).map φ) :
    ∃ a : Over i₀, IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst φ ι)).left := by
  have hsqS : IsPullback (pullback.fst φ ι).left (pullback.snd φ ι).left φ.left ι.left :=
    (IsPullback.of_hasPullback φ ι).map (Over.forget _)
  have : QuasiCompact (pullback.fst φ ι).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsqS.flip inferInstance
  have : LocallyOfFinitePresentation (pullback.fst φ ι).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hsqS.flip inferInstance
  have : CompactSpace (pullback φ ι).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst φ ι).left
  have : QuasiSeparated (pullback.fst φ ι).left :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hsqS.flip inferInstance
  have : QuasiSeparatedSpace (pullback φ ι).left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst φ ι).left
  obtain ⟨ψ, hψ⟩ := hlim
  have := isIso_pullback_fst_left_of_factor D c hc i₀ ι φ hψ
  obtain ⟨i, g, hg⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc i₀ _ X₀
    (pullback.fst φ ι)
  exact ⟨Over.mk g, hg⟩

section Relation

omit [IsCofiltered I] [EssentiallySmall.{u} I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- A property of morphisms stable under base change, holding for the base change to a stage
`b` over `i₀`, holds for the base change to any later stage `a ⟶ b`. -/
theorem prop_overPullback_map_of_hom {i₀ : I} (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y : Over (D.obj i₀)} (f : X ⟶ Y) {a b : Over i₀} (g : a ⟶ b)
    (h : P ((Over.pullback (D.map b.hom)).map f).left) :
    P ((Over.pullback (D.map a.hom)).map f).left := by
  have hc := overPullback_map_comp P (D.map b.hom) (D.map g.left) f h
  rwa [← D.map_comp, Over.w g] at hc

variable (i₀ : I) [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
  {N₀ R₀ : Over (D.obj i₀)} (ι₀ : R₀ ⟶ N₀ ⨯ N₀)

include hc in
/-- **The axioms of an étale equivalence relation with closed embedding descend to one stage.**
If the base change of `ι₀ : R₀ ⟶ N₀ × N₀` to the limit is a closed immersion with étale
projections, through which the diagonal, the swapped relation and the composite relation factor,
then at one stage `a` the base change of `ι₀` is a closed immersion with étale projections and the
three maps `relRefl`, `relSymm ι₀`, `relTrans ι₀` have isomorphic preimages, i.e. factor through
it. -/
theorem exists_stage_relation
    [CompactSpace N₀.left] [QuasiSeparatedSpace N₀.left] [CompactSpace R₀.left]
    [QuasiSeparatedSpace R₀.left] [CompactSpace (N₀ ⨯ N₀).left]
    [QuasiSeparatedSpace (N₀ ⨯ N₀).left]
    [CompactSpace (pullback (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)).left]
    [QuasiSeparatedSpace (pullback (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)).left]
    [LocallyOfFinitePresentation ι₀.left] [LocallyOfFinitePresentation (ι₀ ≫ prod.fst).left]
    [LocallyOfFinitePresentation (ι₀ ≫ prod.snd).left]
    (hci : IsClosedImmersion ((Over.pullback (c.π.app i₀)).map ι₀).left)
    (het₁ : Etale ((Over.pullback (c.π.app i₀)).map (ι₀ ≫ prod.fst)).left)
    (het₂ : Etale ((Over.pullback (c.π.app i₀)).map (ι₀ ≫ prod.snd)).left)
    (hrefl : ∃ ψ, ψ ≫ (Over.pullback (c.π.app i₀)).map ι₀ =
      (Over.pullback (c.π.app i₀)).map (relRefl N₀))
    (hsymm : ∃ ψ, ψ ≫ (Over.pullback (c.π.app i₀)).map ι₀ =
      (Over.pullback (c.π.app i₀)).map (relSymm ι₀))
    (htrans : ∃ ψ, ψ ≫ (Over.pullback (c.π.app i₀)).map ι₀ =
      (Over.pullback (c.π.app i₀)).map (relTrans ι₀)) :
    ∃ a : Over i₀,
      IsClosedImmersion ((Over.pullback (D.map a.hom)).map ι₀).left ∧
      Etale ((Over.pullback (D.map a.hom)).map (ι₀ ≫ prod.fst)).left ∧
      Etale ((Over.pullback (D.map a.hom)).map (ι₀ ≫ prod.snd)).left ∧
      IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relRefl N₀) ι₀)).left ∧
      IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relSymm ι₀) ι₀)).left ∧
      IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relTrans ι₀) ι₀)).left := by
  -- the closed immersion at a stage
  have : LocallyOfFiniteType ι₀.left := inferInstance
  obtain ⟨k₀, g₀, hg₀⟩ := exists_isClosedImmersion_baseChange_of_isLimit D c hc i₀ R₀ _ ι₀
  -- the étale projections at a stage
  obtain ⟨a₁, ha₁⟩ := exists_etale_pullback_of_isLimit D c hc i₀ R₀ N₀ (ι₀ ≫ prod.fst)
  obtain ⟨a₂, ha₂⟩ := exists_etale_pullback_of_isLimit D c hc i₀ R₀ N₀ (ι₀ ≫ prod.snd)
  -- the three factorizations at a stage
  have : Mono ((Over.pullback (c.π.app i₀)).map ι₀) :=
    (Over.forget _).mono_of_mono_map
      (inferInstanceAs (Mono ((Over.pullback (c.π.app i₀)).map ι₀).left))
  have : QuasiCompact ι₀.left := quasiCompact_of_compactSpace ι₀.left
  have : QuasiSeparated ι₀.left := QuasiSeparated.of_quasiSeparatedSpace ι₀.left
  obtain ⟨a₃, ha₃⟩ := exists_isIso_pullback_fst_left D c hc i₀ ι₀ (relRefl N₀) hrefl
  obtain ⟨a₄, ha₄⟩ := exists_isIso_pullback_fst_left D c hc i₀ ι₀ (relSymm ι₀) hsymm
  obtain ⟨a₅, ha₅⟩ := exists_isIso_pullback_fst_left D c hc i₀ ι₀ (relTrans ι₀) htrans
  -- a common stage
  let Q : Over i₀ → Fin 6 → Prop := fun a => ![
    IsClosedImmersion ((Over.pullback (D.map a.hom)).map ι₀).left,
    Etale ((Over.pullback (D.map a.hom)).map (ι₀ ≫ prod.fst)).left,
    Etale ((Over.pullback (D.map a.hom)).map (ι₀ ≫ prod.snd)).left,
    IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relRefl N₀) ι₀)).left,
    IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relSymm ι₀) ι₀)).left,
    IsIso ((Over.pullback (D.map a.hom)).map (pullback.fst (relTrans ι₀) ι₀)).left]
  obtain ⟨a, ha⟩ := common_stage_of_finite i₀ Q
    (fun {a b} g j hj => by
      fin_cases j
      · exact prop_overPullback_map_of_hom D (@IsClosedImmersion) ι₀ g hj
      · exact prop_overPullback_map_of_hom D (@Etale) _ g hj
      · exact prop_overPullback_map_of_hom D (@Etale) _ g hj
      · exact prop_overPullback_map_of_hom D (MorphismProperty.isomorphisms _) _ g hj
      · exact prop_overPullback_map_of_hom D (MorphismProperty.isomorphisms _) _ g hj
      · exact prop_overPullback_map_of_hom D (MorphismProperty.isomorphisms _) _ g hj)
    (fun j => by
      fin_cases j
      · exact ⟨Over.mk g₀, hg₀⟩
      · exact ⟨a₁, ha₁⟩
      · exact ⟨a₂, ha₂⟩
      · exact ⟨a₃, ha₃⟩
      · exact ⟨a₄, ha₄⟩
      · exact ⟨a₅, ha₅⟩)
  exact ⟨a, ha 0, ha 1, ha 2, ha 3, ha 4, ha 5⟩

/-- **The equivalence relation at a stage.** At a stage where the base change of `ι₀` is a
closed immersion with étale projections and the three test maps factor through it, the two
projections `s, t` of the base-changed relation are étale and jointly monic, and reflexivity,
symmetry and transitivity hold, with witnesses. -/
theorem exists_relationData {k : I} (g : k ⟶ i₀)
    (hci : IsClosedImmersion ((Over.pullback (D.map g)).map ι₀).left)
    (hrefl : IsIso ((Over.pullback (D.map g)).map (pullback.fst (relRefl N₀) ι₀)).left)
    (hsymm : IsIso ((Over.pullback (D.map g)).map (pullback.fst (relSymm ι₀) ι₀)).left)
    (htrans : IsIso ((Over.pullback (D.map g)).map (pullback.fst (relTrans ι₀) ι₀)).left) :
    let G := Over.pullback (D.map g)
    let sR := G.map (ι₀ ≫ prod.fst)
    let tR := G.map (ι₀ ≫ prod.snd)
    (∀ {W : Over (D.obj k)} (x y : W ⟶ G.obj R₀), x ≫ sR = y ≫ sR → x ≫ tR = y ≫ tR → x = y) ∧
    (∃ r : G.obj N₀ ⟶ G.obj R₀, r ≫ sR = 𝟙 _ ∧ r ≫ tR = 𝟙 _) ∧
    (∃ σ : G.obj R₀ ⟶ G.obj R₀, σ ≫ sR = tR ∧ σ ≫ tR = sR) ∧
    (∃ τ : pullback tR sR ⟶ G.obj R₀,
      τ ≫ sR = pullback.fst tR sR ≫ sR ∧ τ ≫ tR = pullback.snd tR sR ≫ tR) := by
  intro G sR tR
  have hmono : Mono (G.map ι₀) :=
    (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono (G.map ι₀).left))
  have hfst : G.map ι₀ ≫ G.map prod.fst = sR := (G.map_comp _ _).symm
  have hsnd : G.map ι₀ ≫ G.map prod.snd = tR := (G.map_comp _ _).symm
  -- `G.map prod.fst` and `G.map prod.snd` are jointly monic
  have hjm : ∀ {W : Over (D.obj k)} (x y : W ⟶ G.obj (N₀ ⨯ N₀)),
      x ≫ G.map prod.fst = y ≫ G.map prod.fst → x ≫ G.map prod.snd = y ≫ G.map prod.snd →
        x = y := by
    intro W x y h₁ h₂
    rw [← cancel_mono (PreservesLimitPair.iso G N₀ N₀).hom]
    apply prod.hom_ext
    · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst, h₁]
    · rw [Category.assoc, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd, h₂]
  refine ⟨fun x y h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · rw [← cancel_mono (G.map ι₀)]
    apply hjm
    · rw [Category.assoc, Category.assoc, hfst, h₁]
    · rw [Category.assoc, Category.assoc, hsnd, h₂]
  · obtain ⟨r, hr⟩ := exists_factor_of_isIso_pullback_fst_left D g ι₀ (relRefl N₀) hrefl
    refine ⟨r, ?_, ?_⟩
    · rw [← hfst, ← Category.assoc, hr, ← G.map_comp, prod.lift_fst, G.map_id]
    · rw [← hsnd, ← Category.assoc, hr, ← G.map_comp, prod.lift_snd, G.map_id]
  · obtain ⟨σ, hσ⟩ := exists_factor_of_isIso_pullback_fst_left D g ι₀ (relSymm ι₀) hsymm
    refine ⟨σ, ?_, ?_⟩
    · rw [← hfst, ← Category.assoc, hσ, ← G.map_comp, Category.assoc, prod.lift_fst]
    · rw [← hsnd, ← Category.assoc, hσ, ← G.map_comp, Category.assoc, prod.lift_snd]
  · obtain ⟨τ, hτ⟩ := exists_factor_of_isIso_pullback_fst_left D g ι₀ (relTrans ι₀) htrans
    let e := PreservesPullback.iso G (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)
    refine ⟨e.inv ≫ τ, ?_, ?_⟩
    · calc (e.inv ≫ τ) ≫ sR = e.inv ≫ ((τ ≫ G.map ι₀) ≫ G.map prod.fst) := by
            simp only [Category.assoc, hfst]
        _ = (e.inv ≫ G.map (pullback.fst _ _)) ≫ sR := by
            rw [hτ, ← G.map_comp, prod.lift_fst, Category.assoc,
              G.map_comp (pullback.fst (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)) (ι₀ ≫ prod.fst)]
        _ = pullback.fst tR sR ≫ sR := by rw [PreservesPullback.iso_inv_fst]
    · calc (e.inv ≫ τ) ≫ tR = e.inv ≫ ((τ ≫ G.map ι₀) ≫ G.map prod.snd) := by
            simp only [Category.assoc, hsnd]
        _ = (e.inv ≫ G.map (pullback.snd _ _)) ≫ tR := by
            rw [hτ, ← G.map_comp, prod.lift_snd, Category.assoc,
              G.map_comp (pullback.snd (ι₀ ≫ prod.snd) (ι₀ ≫ prod.fst)) (ι₀ ≫ prod.snd)]
        _ = pullback.snd tR sR ≫ tR := by rw [PreservesPullback.iso_inv_snd]

end Relation

end AlgebraicGeometry

end
