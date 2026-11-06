module

public import StacksFrontier.AlgebraicGeometry.Spaces.Bootstrap04S6Carriers
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice

/-!
# The quotient of a groupoid with flat stabilizer

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` whose source
map is flat and locally of finite presentation and whose stabilizer is flat and locally of
finite presentation over `U`, in the sense that for every point `a` of `U` over a scheme `T` the
arrows from `a` to `a` form a presheaf flat and locally of finite presentation over `T`. This is
the situation of the proof of **Stacks 06QJ**, (2) implies (1). From the bootstrap theorem
Stacks 04S6 part (3), this file proves that the quotient sheaf `U/R` is an algebraic space and that
the quotient stack `[U/R]` is a gerbe over it.

## The proof

Let `q : U ⟶ U/R` be the quotient map and `R' = U ×_{U/R} U` the equivalence relation of pairs with
the same image, that is (**Stacks 046O**) of pairs which are fppf-locally joined by an arrow. The
map `π = (s, t) : R ⟶ R'` is a surjection of sheaves (Stacks 046O). Its base change along a point
`(a, b)` of `R'` over `T` is the presheaf of arrows from `a` to `b`, which becomes, after one flat,
locally finitely presented, surjective `V ⟶ T` over which an arrow `r₀ : a ⟶ b` exists, isomorphic
to the presheaf of arrows from `a` to `a` by `r ↦ r₀⁻¹ ∘ r`. So that base change is surjective,
flat and locally of finite presentation after one fppf base change, and the bootstrap theorem makes
`R'` an algebraic space. Its source map is flat and locally of finite presentation by
**Stacks 06NR**, the source map `s = π ≫ s'` being so, so the quotient `U/R'` is an algebraic space,
again by the bootstrap theorem; and `U/R' = U/R`.

The quotient stack is a gerbe over `U/R` by the gerbe criterion for the structure arrow of
Stacks 044R: `q` is a surjection of sheaves, and two local points with the same image in `U/R` are
fppf-locally joined by an arrow (Stacks 046O).

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_iso_arrowsBetween_translate`: translation by
  an arrow identifies the arrows between two points with the stabilizer of one of them.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isAlgebraicSpace_relatedPairs`: `R'` is an
  algebraic space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isAlgebraicSpace_quotientSheaf_of_flatStabilizer`:
  `U/R` is an algebraic space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isGerbeOver_quotientStackToBase_quotientSheaf`:
  `[U/R]` is a gerbe over `U/R`.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046O](https://stacks.math.columbia.edu/tag/046O)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-! ### Translating arrows -/

/-- The presheaf of arrows from `b` to `a`, for two generalized points `a`, `b` of the object
space: the fibre product of the pair of endpoints `(t, s)` with `(a, b)`. -/
noncomputable abbrev arrowsBetween {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a b : T ⟶ G.objects.obj) : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback (prod.lift a b) (prod.lift G.target.hom G.source.hom)

set_option synthInstance.maxHeartbeats 400000 in
/-- Products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_FlatStabilizerQuotient
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

variable {G}

/-- The target of an arrow from `b` to `a` is `a`. -/
lemma arrowsBetween_target {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.objects.obj) :
    pullback.snd (prod.lift a b) (prod.lift G.target.hom G.source.hom) ≫ G.target.hom =
      pullback.fst (prod.lift a b) (prod.lift G.target.hom G.source.hom) ≫ a := by
  simpa only [Category.assoc, prod.lift_fst] using (congrArg (fun k => k ≫ prod.fst)
    (pullback.condition (f := prod.lift a b) (g := prod.lift G.target.hom G.source.hom))).symm

/-- The source of an arrow from `b` to `a` is `b`. -/
lemma arrowsBetween_source {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b : T ⟶ G.objects.obj) :
    pullback.snd (prod.lift a b) (prod.lift G.target.hom G.source.hom) ≫ G.source.hom =
      pullback.fst (prod.lift a b) (prod.lift G.target.hom G.source.hom) ≫ b := by
  simpa only [Category.assoc, prod.lift_snd] using (congrArg (fun k => k ≫ prod.snd)
    (pullback.condition (f := prod.lift a b) (g := prod.lift G.target.hom G.source.hom))).symm

/-- **Translation by an arrow.** If `r₀` is an arrow from `b` to `a`, then `r ↦ r₀⁻¹ ∘ r`
identifies the presheaf of arrows from `b` to `a` with the presheaf of arrows from `b` to `b`,
over the parameter space of the points. -/
theorem exists_iso_arrowsBetween_translate {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a b : T ⟶ G.objects.obj) (r₀ : T ⟶ G.arrows.obj) (ht : r₀ ≫ G.target.hom = a)
    (hs : r₀ ≫ G.source.hom = b) :
    ∃ e : arrowsBetween G a b ≅ arrowsBetween G b b,
      e.hom ≫ pullback.fst (prod.lift b b) (prod.lift G.target.hom G.source.hom) =
        pullback.fst (prod.lift a b) (prod.lift G.target.hom G.source.hom) := by
  set f₁ := pullback.fst (prod.lift a b) (prod.lift G.target.hom G.source.hom)
  set g₁ := pullback.snd (prod.lift a b) (prod.lift G.target.hom G.source.hom)
  set f₂ := pullback.fst (prod.lift b b) (prod.lift G.target.hom G.source.hom)
  set g₂ := pullback.snd (prod.lift b b) (prod.lift G.target.hom G.source.hom)
  have ht₁ : g₁ ≫ G.target.hom = f₁ ≫ a := arrowsBetween_target a b
  have hs₁ : g₁ ≫ G.source.hom = f₁ ≫ b := arrowsBetween_source a b
  have ht₂ : g₂ ≫ G.target.hom = f₂ ≫ b := arrowsBetween_target b b
  have hs₂ : g₂ ≫ G.source.hom = f₂ ≫ b := arrowsBetween_source b b
  have w₁ : (f₁ ≫ r₀ ≫ groupoidInverse G) ≫ G.source.hom = g₁ ≫ G.target.hom := by
    rw [Category.assoc, Category.assoc, groupoidInverse_source, ht, ht₁]
  have w₂ : (f₂ ≫ r₀) ≫ G.source.hom = g₂ ≫ G.target.hom := by
    rw [Category.assoc, hs, ht₂]
  let φ : arrowsBetween G a b ⟶ arrowsBetween G b b :=
    pullback.lift f₁ (groupoidCompose G (f₁ ≫ r₀ ≫ groupoidInverse G) g₁ w₁) (by
      apply prod.hom_ext
      · rw [Category.assoc, Category.assoc, prod.lift_fst, prod.lift_fst,
          groupoidCompose_target, Category.assoc, Category.assoc, groupoidInverse_target, hs]
      · rw [Category.assoc, Category.assoc, prod.lift_snd, prod.lift_snd,
          groupoidCompose_source, hs₁])
  let ψ : arrowsBetween G b b ⟶ arrowsBetween G a b :=
    pullback.lift f₂ (groupoidCompose G (f₂ ≫ r₀) g₂ w₂) (by
      apply prod.hom_ext
      · rw [Category.assoc, Category.assoc, prod.lift_fst, prod.lift_fst,
          groupoidCompose_target, Category.assoc, ht]
      · rw [Category.assoc, Category.assoc, prod.lift_snd, prod.lift_snd,
          groupoidCompose_source, hs₂])
  have hφf : φ ≫ f₂ = f₁ := pullback.lift_fst _ _ _
  have hφg : φ ≫ g₂ = groupoidCompose G (f₁ ≫ r₀ ≫ groupoidInverse G) g₁ w₁ :=
    pullback.lift_snd _ _ _
  have hψf : ψ ≫ f₁ = f₂ := pullback.lift_fst _ _ _
  have hψg : ψ ≫ g₁ = groupoidCompose G (f₂ ≫ r₀) g₂ w₂ := pullback.lift_snd _ _ _
  refine ⟨{ hom := φ, inv := ψ, hom_inv_id := ?_, inv_hom_id := ?_ }, hφf⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, hψf, hφf, Category.id_comp]
    · rw [Category.assoc, hψg, groupoidCompose_pre, Category.id_comp]
      have wa : (f₁ ≫ r₀) ≫ G.source.hom =
          groupoidCompose G (f₁ ≫ r₀ ≫ groupoidInverse G) g₁ w₁ ≫ G.target.hom := by
        rw [groupoidCompose_target, Category.assoc, Category.assoc, Category.assoc,
          groupoidInverse_target]
      rw [groupoidCompose_congr G _ wa (by rw [← Category.assoc, hφf]) hφg]
      have wab : (f₁ ≫ r₀) ≫ G.source.hom = (f₁ ≫ r₀ ≫ groupoidInverse G) ≫ G.target.hom := by
        rw [Category.assoc, Category.assoc, Category.assoc, groupoidInverse_target]
      have wL : groupoidCompose G (f₁ ≫ r₀) (f₁ ≫ r₀ ≫ groupoidInverse G) wab ≫
          G.source.hom = g₁ ≫ G.target.hom := by
        rw [groupoidCompose_source, w₁]
      rw [← groupoidCompose_assoc G (f₁ ≫ r₀) (f₁ ≫ r₀ ≫ groupoidInverse G) g₁ wab w₁ wL wa]
      have hid : identityAfterTarget G (f₁ ≫ r₀) = identityAfterTarget G g₁ := by
        simp only [identityAfterTarget]
        rw [Category.assoc, ← Category.assoc r₀, ht, ← Category.assoc, ← ht₁, Category.assoc]
      rw [groupoidCompose_congr G wL (identityAfterTarget_composable G g₁)
        ((groupoidCompose_congr G wab _ rfl (Category.assoc _ _ _).symm).trans
          ((groupoidCompose_inverseLeft G (f₁ ≫ r₀)).trans hid)) rfl]
      exact groupoidCompose_leftIdentity G g₁
  · apply pullback.hom_ext
    · rw [Category.assoc, hφf, hψf, Category.id_comp]
    · rw [Category.assoc, hφg, groupoidCompose_pre, Category.id_comp]
      have wa : (ψ ≫ f₁ ≫ r₀ ≫ groupoidInverse G) ≫ G.source.hom =
          (ψ ≫ g₁) ≫ G.target.hom := by
        rw [Category.assoc, w₁, Category.assoc]
      have wb : (f₂ ≫ r₀ ≫ groupoidInverse G) ≫ G.source.hom =
          groupoidCompose G (f₂ ≫ r₀) g₂ w₂ ≫ G.target.hom := by
        rw [groupoidCompose_target, Category.assoc, Category.assoc, Category.assoc,
          groupoidInverse_source]
      rw [groupoidCompose_congr G wa wb (by rw [← Category.assoc, hψf]) hψg]
      have wab : (f₂ ≫ r₀ ≫ groupoidInverse G) ≫ G.source.hom = (f₂ ≫ r₀) ≫ G.target.hom := by
        rw [Category.assoc, Category.assoc, Category.assoc, groupoidInverse_source]
      have wL : groupoidCompose G (f₂ ≫ r₀ ≫ groupoidInverse G) (f₂ ≫ r₀) wab ≫
          G.source.hom = g₂ ≫ G.target.hom := by
        rw [groupoidCompose_source, w₂]
      rw [← groupoidCompose_assoc G (f₂ ≫ r₀ ≫ groupoidInverse G) (f₂ ≫ r₀) g₂ wab w₂ wL wb]
      have hid : identityAfterSource G (f₂ ≫ r₀) = identityAfterTarget G g₂ := by
        simp only [identityAfterSource, identityAfterTarget]
        rw [Category.assoc, ← Category.assoc r₀, hs, ← Category.assoc, ← ht₂, Category.assoc]
      rw [groupoidCompose_congr G wL (identityAfterTarget_composable G g₂)
        ((groupoidCompose_congr G wab _ (Category.assoc _ _ _).symm rfl).trans
          ((groupoidCompose_inverseRight G (f₂ ≫ r₀)).trans hid)) rfl]
      exact groupoidCompose_leftIdentity G g₂

/-! ### The relation of pairs joined by an arrow, fppf-locally -/

section RelatedPairs

open Space

variable [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

variable (G) in
/-- The sheaf `R' = U ×_{U/R} U` of pairs of points of the object space with the same image in the
quotient sheaf `U/R`, that is (Stacks 046O) of pairs which are fppf-locally the source and the
target of an arrow. -/
noncomputable abbrev relatedPairs : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u :=
  pullback (toQuotientSheaf (Space.groupoidPreRelation G))
    (toQuotientSheaf (Space.groupoidPreRelation G))

variable (G) in
/-- The map `(s, t) : R ⟶ R'` sending an arrow to the pair of its source and its target. -/
noncomputable abbrev arrowsToRelatedPairs : G.arrows.obj ⟶ relatedPairs G :=
  pullback.lift (Space.groupoidPreRelation G).source.left (Space.groupoidPreRelation G).target.left
    (target_toQuotientSheaf_eq_source (Space.groupoidPreRelation G)).symm

omit [HasSheafify (BigFppfOver.topology C S hS) (Type u)] in
/-- The source of the pre-relation of a groupoid is its source map. -/
lemma groupoidPreRelation_source_left :
    (Space.groupoidPreRelation G).source.left = G.source.hom := by
  simp [PreRelation.source]

omit [HasSheafify (BigFppfOver.topology C S hS) (Type u)] in
/-- The target of the pre-relation of a groupoid is its target map. -/
lemma groupoidPreRelation_target_left :
    (Space.groupoidPreRelation G).target.left = G.target.hom := by
  simp [PreRelation.target]

/-- The first coordinate of `(s, t) : R ⟶ R'` is the source map. -/
lemma arrowsToRelatedPairs_fst :
    arrowsToRelatedPairs G ≫ pullback.fst _ _ = G.source.hom := by
  rw [pullback.lift_fst, groupoidPreRelation_source_left]

/-- The second coordinate of `(s, t) : R ⟶ R'` is the target map. -/
lemma arrowsToRelatedPairs_snd :
    arrowsToRelatedPairs G ≫ pullback.snd _ _ = G.target.hom := by
  rw [pullback.lift_snd, groupoidPreRelation_target_left]

/-- The presheaf `R' = U ×_{U/R} U` is a sheaf, as a fibre product of sheaves. -/
lemma isSheaf_relatedPairs :
    Presheaf.IsSheaf (BigFppfOver.topology C S hS) (relatedPairs G) :=
  Presheaf.isSheaf_pullback _ _ _ G.objects.property.isSheaf G.objects.property.isSheaf
    (quotientSheaf (Space.groupoidPreRelation G)).property

/-- The map `(s, t) : R ⟶ R'` is a surjection of sheaves (Stacks 046O). -/
private lemma isLocallySurjective_arrowsToRelatedPairs :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) (arrowsToRelatedPairs G) :=
  isLocallySurjective_relationToQuotientPullback (Space.groupoidPreRelation G)
    (Space.groupoidPreRelation_isPreEquivalenceRelation G)

/-- The base change of `(s, t) : R ⟶ R'` along a point `ξ` of `R'` is the presheaf of arrows
from the first to the second coordinate of `ξ`. -/
lemma isPullback_arrowsBetween_relatedPairs {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (ξ : T ⟶ relatedPairs G) {T' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T) :
    ∃ k : arrowsBetween G (f ≫ ξ ≫ pullback.snd _ _) (f ≫ ξ ≫ pullback.fst _ _) ⟶
        pullback ξ (arrowsToRelatedPairs G),
      IsPullback k (pullback.fst _ _) (pullback.fst ξ (arrowsToRelatedPairs G)) f := by
  let ι : relatedPairs G ⟶ G.objects.obj ⨯ G.objects.obj :=
    prod.lift (pullback.snd _ _) (pullback.fst _ _)
  have : Mono ι := ⟨fun i₁ i₂ h => pullback.hom_ext
    (by simpa [ι] using congrArg (fun k => k ≫ prod.snd) h)
    (by simpa [ι] using congrArg (fun k => k ≫ prod.fst) h)⟩
  have hπι : arrowsToRelatedPairs G ≫ ι = prod.lift G.target.hom G.source.hom := by
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, prod.lift_fst, arrowsToRelatedPairs_snd]
    · rw [Category.assoc, prod.lift_snd, prod.lift_snd, arrowsToRelatedPairs_fst]
  have hξι : f ≫ ξ ≫ ι = prod.lift (f ≫ ξ ≫ pullback.snd _ _) (f ≫ ξ ≫ pullback.fst _ _) := by
    apply prod.hom_ext <;> simp [ι]
  have ht : IsPullback (pullback.snd ξ (arrowsToRelatedPairs G))
      (pullback.fst ξ (arrowsToRelatedPairs G)) (prod.lift G.target.hom G.source.hom)
      (ξ ≫ ι) := by
    have h : IsPullback (pullback.snd ξ (arrowsToRelatedPairs G))
        (pullback.fst ξ (arrowsToRelatedPairs G)) (arrowsToRelatedPairs G ≫ ι) (ξ ≫ ι) :=
      (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono ξ (arrowsToRelatedPairs G) ι)).flip
    rwa [hπι] at h
  refine ⟨pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) ?_,
    IsPullback.of_right ?_ (pullback.lift_fst _ _ _) ht⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, arrowsToRelatedPairs_fst,
        arrowsBetween_source]
    · rw [Category.assoc, Category.assoc, Category.assoc, arrowsToRelatedPairs_snd,
        arrowsBetween_target]
  · rw [pullback.lift_snd, ← Category.assoc, hξι]
    exact (IsPullback.of_hasPullback _ _).flip

omit [HasSheafify (BigFppfOver.topology C S hS) (Type u)] in
/-- The identity arrows give a section of the presheaf of arrows from a point to itself. -/
lemma isSurjective_arrowsBetween_fst {T : BigFppfOver C S hS}
    (a : yoneda.obj T ⟶ G.objects.obj) :
    IsSurjective C S hS (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom)) := by
  let σ : yoneda.obj T ⟶ arrowsBetween G a a :=
    pullback.lift (𝟙 _) (a ≫ (identityArrow G).hom) (by
      apply prod.hom_ext
      · rw [Category.assoc, Category.assoc, prod.lift_fst, prod.lift_fst, Category.assoc,
          identityArrow_hom_comp_target, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, Category.assoc, prod.lift_snd, prod.lift_snd, Category.assoc,
          identityArrow_hom_comp_source, Category.comp_id, Category.id_comp])
  have hσ : σ ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  intro x
  refine ⟨pointsMap C S hS _ σ x, ?_⟩
  rw [← pointsMap_comp_apply, hσ, pointsMap_id]
  rfl

/-- **The sheaf `R'` of pairs of points joined fppf-locally by an arrow is an algebraic space**,
by the bootstrap theorem, as soon as the stabilizer is flat and locally of finite
presentation: for every point `b` of the object space over a scheme, the arrows from `b` to `b`
form a presheaf flat and locally of finite presentation over that scheme.

The map `(s, t) : R ⟶ R'` is a surjection of sheaves (Stacks 046O), and over a point `(a, b)` of
`R'` it becomes, after one fppf base change producing an arrow `r₀ : a ⟶ b`, the stabilizer of
`a`, by translation by `r₀`. -/
theorem isAlgebraicSpace_relatedPairs
    (hstabF : ∀ (T : BigFppfOver C S hS) (a : yoneda.obj T ⟶ G.objects.obj),
      Space.IsFlat C S hS (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom)))
    (hstabL : ∀ (T : BigFppfOver C S hS) (a : yoneda.obj T ⟶ G.objects.obj),
      Space.IsLocallyOfFinitePresentation C S hS
        (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom))) :
    IsAlgebraicSpace C S hS (relatedPairs G) := by
  refine isAlgebraicSpace_of_isBootstrap_of_fppfLocalChart C S hS
    (isBootstrapAlgebraicSpaceAlongFlatSurjection C S hS)
    (arrowsToRelatedPairs G) (isSheaf_relatedPairs (G := G)) G.arrows.property ?_
  intro T ξ
  obtain ⟨V, f, hfF, hfL, hfS, r, hr⟩ := exists_single_fppf_lift_of_isLocallySurjective C S hS
    G.arrows.property.isSheaf (isSheaf_relatedPairs (G := G)) (arrowsToRelatedPairs G)
    isLocallySurjective_arrowsToRelatedPairs T (yonedaEquiv ξ)
  let r₀ : yoneda.obj V ⟶ G.arrows.obj := yonedaEquiv.symm r
  have hr₀ : r₀ ≫ arrowsToRelatedPairs G = yoneda.map f ≫ ξ := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    simpa only [r₀, Equiv.apply_symm_apply] using hr
  let aV := yoneda.map f ≫ ξ ≫ pullback.fst _ _
  let bV := yoneda.map f ≫ ξ ≫ pullback.snd _ _
  have hs₀ : r₀ ≫ G.source.hom = aV := by
    rw [← arrowsToRelatedPairs_fst, ← Category.assoc, hr₀, Category.assoc]
  have ht₀ : r₀ ≫ G.target.hom = bV := by
    rw [← arrowsToRelatedPairs_snd, ← Category.assoc, hr₀, Category.assoc]
  obtain ⟨e, he⟩ := exists_iso_arrowsBetween_translate bV aV r₀ ht₀ hs₀
  obtain ⟨k, hsq⟩ := isPullback_arrowsBetween_relatedPairs (G := G) ξ (yoneda.map f)
  refine ⟨V, f, arrowsBetween G aV aV, pullback.fst _ _, e.inv ≫ k,
    isAlgebraicSpace_pullback C S hS _ _ (isAlgebraicSpace_yoneda C S hS V) G.arrows.property
      (isAlgebraicSpace_prod C S hS G.objects.property G.objects.property),
    hfF, hfL, hfS, ?_, isSurjective_arrowsBetween_fst aV, hstabF V aV, hstabL V aV⟩
  refine hsq.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rw [Iso.refl_hom, Category.comp_id, he]
  · simp
  · simp

/-! ### The quotient by the relation of related pairs -/

variable (G) in
/-- The equivalence relation `R' ⟶ U ×_B U` of pairs with the same image in `U/R`, over the base
`B` of the groupoid; its target is the second and its source the first coordinate, so that
`(s, t) : R ⟶ R'` is compatible with the two pre-relations. -/
noncomputable abbrev relatedPairsRelation :
    PreRelation (Over.mk (pullback.fst (toQuotientSheaf (Space.groupoidPreRelation G))
        (toQuotientSheaf (Space.groupoidPreRelation G)) ≫ G.objectsToBase.hom))
      (Over.mk G.objectsToBase.hom) :=
  prod.lift
    (Over.homMk (pullback.snd _ _) (by
      have h : toQuotientSheaf (Space.groupoidPreRelation G) ≫
          (quotientSheafToBase B.property.isSheaf (Space.groupoidPreRelation G)).hom =
            G.objectsToBase.hom :=
        toQuotientSheaf_quotientSheafToBase B.property.isSheaf (Space.groupoidPreRelation G)
      change _ ≫ G.objectsToBase.hom = _ ≫ G.objectsToBase.hom
      calc _ = pullback.snd _ _ ≫ toQuotientSheaf (Space.groupoidPreRelation G) ≫
              (quotientSheafToBase B.property.isSheaf (Space.groupoidPreRelation G)).hom := by
            rw [h]
        _ = pullback.fst _ _ ≫ toQuotientSheaf (Space.groupoidPreRelation G) ≫
              (quotientSheafToBase B.property.isSheaf (Space.groupoidPreRelation G)).hom := by
            rw [← Category.assoc, ← Category.assoc, pullback.condition]
        _ = _ := by rw [h]))
    (Over.homMk (pullback.fst _ _) rfl)

/-- The target of the relation `R' ⟶ U ×_B U` is the second coordinate. -/
lemma relatedPairsRelation_target_left :
    (relatedPairsRelation G).target.left = pullback.snd _ _ := by
  simp [PreRelation.target]

/-- The source of the relation `R' ⟶ U ×_B U` is the first coordinate. -/
lemma relatedPairsRelation_source_left :
    (relatedPairsRelation G).source.left = pullback.fst _ _ := by
  simp [PreRelation.source]

/-- The relation `R' = U ×_{U/R} U` of pairs with the same image in `U/R` is an equivalence
relation, being the kernel pair of the quotient map. -/
lemma isEquivalenceRelation_relatedPairsRelation :
    IsEquivalenceRelation (relatedPairsRelation G).target (relatedPairsRelation G).source := by
  have : IsEquivalenceRelation (relatedPairsRelation G).target.left
      (relatedPairsRelation G).source.left := by
    rw [relatedPairsRelation_target_left, relatedPairsRelation_source_left]
    exact (IsKernelPair.equivalenceRelation _ _ _ (pullbackIsPullback _ _)
      (IsPullback.of_hasPullback (toQuotientSheaf (Space.groupoidPreRelation G))
        (toQuotientSheaf (Space.groupoidPreRelation G))).flip).isEquivalenceRelation
  exact isEquivalenceRelation_of_left _ _

/-- **The quotient sheaf `U/R` of a groupoid with flat stabilizer is an algebraic space**, by
the bootstrap theorem: for a groupoid in algebraic spaces whose source map is flat and locally of
finite presentation and whose stabilizer is flat and locally of finite presentation.

The quotient `U/R` is the quotient `U/R'` by the equivalence relation `R' = U ×_{U/R} U`, which is
an algebraic space (`isAlgebraicSpace_relatedPairs`) whose source map is flat and locally of
finite presentation by Stacks 06NR, `(s, t) : R ⟶ R'` being a surjection of sheaves. The
bootstrap theorem in its quotient form then applies to `R'`. -/
theorem isAlgebraicSpace_quotientSheaf_of_flatStabilizer
    (hsF : Space.IsFlat C S hS G.source.hom)
    (hsL : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (hstabF : ∀ (T : BigFppfOver C S hS) (a : yoneda.obj T ⟶ G.objects.obj),
      Space.IsFlat C S hS (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom)))
    (hstabL : ∀ (T : BigFppfOver C S hS) (a : yoneda.obj T ⟶ G.objects.obj),
      Space.IsLocallyOfFinitePresentation C S hS
        (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom))) :
    IsAlgebraicSpace C S hS (quotientSheaf (Space.groupoidPreRelation G)).obj := by
  have hR' := isAlgebraicSpace_relatedPairs hstabF hstabL
  have hπ := isLocallySurjective_arrowsToRelatedPairs (G := G)
  have hF' : Space.IsFlat C S hS (relatedPairsRelation G).source.left := by
    rw [relatedPairsRelation_source_left]
    exact isFlat_of_comp_of_locallySurjective C S hS G.arrows.property hR'
      G.objects.property (arrowsToRelatedPairs G) _ (by rwa [arrowsToRelatedPairs_fst]) hπ
  have hL' : Space.IsLocallyOfFinitePresentation C S hS
      (relatedPairsRelation G).source.left := by
    rw [relatedPairsRelation_source_left]
    exact isLocallyOfFinitePresentation_of_comp_of_locallySurjective C S hS G.arrows.property
      hR' G.objects.property (arrowsToRelatedPairs G) _ (by rwa [arrowsToRelatedPairs_fst]) hπ
  have hX' := isAlgebraicSpace_quotientSheaf_of_isBootstrap
    (isBootstrapAlgebraicSpaceAlongFlatSurjection C S hS) (relatedPairsRelation G) hR'
    G.objects.property (isEquivalenceRelation_relatedPairsRelation (G := G)) hF' hL'
  -- The two quotients agree.
  let j := Space.groupoidPreRelation G
  let j' := relatedPairsRelation G
  have h₁ : j'.target.left ≫ toQuotientSheaf j = j'.source.left ≫ toQuotientSheaf j := by
    rw [relatedPairsRelation_target_left, relatedPairsRelation_source_left]
    exact pullback.condition.symm
  have h₂ : j.target.left ≫ toQuotientSheaf j' = j.source.left ≫ toQuotientSheaf j' := by
    have ht : j.target.left = arrowsToRelatedPairs G ≫ j'.target.left := by
      rw [relatedPairsRelation_target_left, pullback.lift_snd]
    have hs : j.source.left = arrowsToRelatedPairs G ≫ j'.source.left := by
      rw [relatedPairsRelation_source_left, pullback.lift_fst]
    rw [ht, hs, Category.assoc, Category.assoc, target_toQuotientSheaf_eq_source]
  let φ := quotientSheafDesc j' (quotientSheaf j) (toQuotientSheaf j) h₁
  let ψ := quotientSheafDesc j (quotientSheaf j') (toQuotientSheaf j') h₂
  have hφ := toQuotientSheaf_quotientSheafDesc j' (quotientSheaf j) (toQuotientSheaf j) h₁
  have hψ := toQuotientSheaf_quotientSheafDesc j (quotientSheaf j') (toQuotientSheaf j') h₂
  let e : quotientSheaf j' ≅ quotientSheaf j :=
    { hom := φ
      inv := ψ
      hom_inv_id := by
        rw [quotientSheafDesc_unique j' _ (toQuotientSheaf j')
            (target_toQuotientSheaf_eq_source j') (φ ≫ ψ) (by
              rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, hφ, hψ]),
          quotientSheafDesc_unique j' _ (toQuotientSheaf j')
            (target_toQuotientSheaf_eq_source j') (𝟙 _) (Category.comp_id _)]
      inv_hom_id := by
        rw [quotientSheafDesc_unique j _ (toQuotientSheaf j)
            (target_toQuotientSheaf_eq_source j) (ψ ≫ φ) (by
              rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, hψ, hφ]),
          quotientSheafDesc_unique j _ (toQuotientSheaf j)
            (target_toQuotientSheaf_eq_source j) (𝟙 _) (Category.comp_id _)] }
  exact isAlgebraicSpace_of_iso C S hS ((sheafToPresheaf _ _).mapIso e).symm hX'

end RelatedPairs

/-! ### The quotient stack as a gerbe over the quotient sheaf -/

section Gerbe

open Space

variable (G) in
/-- A groupoid in algebraic spaces read over another base `Z'`, along a morphism `q : U ⟶ Z'` from
its object space which identifies the source and the target of every arrow: the spaces, the source,
the target and the composition are unchanged, the object space lies over `Z'` through `q` and the
arrow space through `q ∘ t`. -/
noncomputable def overInvariantBase {Z' : AlgebraicSpaces C S hS} (q : G.objects ⟶ Z')
    (hq : G.source ≫ q = G.target ≫ q) : GroupoidInAlgebraicSpaces C S hS Z' where
  objects := G.objects
  arrows := G.arrows
  objectsToBase := q
  arrowsToBase := G.target ≫ q
  source := G.source
  target := G.target
  source_over := hq
  target_over := rfl
  comp := G.comp
  comp_over := by
    apply ObjectProperty.hom_ext
    change G.comp.hom ≫ G.target.hom ≫ q.hom = pullback.fst _ _ ≫ G.target.hom ≫ q.hom
    have h := groupoidCompose_target G (pullback.fst G.source.hom G.target.hom)
      (pullback.snd G.source.hom G.target.hom) pullback.condition
    rw [groupoidCompose_eq_comp, pullback.lift_fst_snd] at h
    have h' : G.comp.hom ≫ G.target.hom = pullback.fst _ _ ≫ G.target.hom :=
      (congrArg (· ≫ G.target.hom) (Category.id_comp G.comp.hom)).symm.trans h
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q.hom) h')).trans
      (Category.assoc _ _ _)
  pointwiseGroupoid := G.pointwiseGroupoid

/-- Reading a groupoid over another base leaves the underlying groupoid in presheaves, hence the
quotient stack, unchanged. -/
theorem toGroupoidInFunctors_overInvariantBase {Z' : AlgebraicSpaces C S hS}
    (q : G.objects ⟶ Z') (hq : G.source ≫ q = G.target ≫ q) :
    (overInvariantBase G q hq).toGroupoidInFunctors = G.toGroupoidInFunctors :=
  rfl

variable [HasSheafify (BigFppfOver.topology C S hS) (Type u)]

variable (G) in
/-- The quotient sheaf `U/R`, as an algebraic space when it is one. -/
noncomputable abbrev quotientSpace
    (hX : IsAlgebraicSpace C S hS (quotientSheaf (Space.groupoidPreRelation G)).obj) :
    AlgebraicSpaces C S hS :=
  ⟨(quotientSheaf (Space.groupoidPreRelation G)).obj, hX⟩

variable (G) in
/-- The quotient map `U ⟶ U/R`, as a morphism of algebraic spaces. -/
noncomputable abbrev toQuotientSpace
    (hX : IsAlgebraicSpace C S hS (quotientSheaf (Space.groupoidPreRelation G)).obj) :
    G.objects ⟶ quotientSpace G hX :=
  ObjectProperty.homMk (toQuotientSheaf (Space.groupoidPreRelation G))

/-- The quotient map `U ⟶ U/R`, as a morphism of algebraic spaces, identifies the source and the
target of every arrow. -/
lemma source_toQuotientSpace_eq_target
    (hX : IsAlgebraicSpace C S hS (quotientSheaf (Space.groupoidPreRelation G)).obj) :
    G.source ≫ toQuotientSpace G hX = G.target ≫ toQuotientSpace G hX := by
  apply ObjectProperty.hom_ext
  show G.source.hom ≫ _ = G.target.hom ≫ _
  rw [← groupoidPreRelation_source_left, ← groupoidPreRelation_target_left]
  exact (target_toQuotientSheaf_eq_source _).symm

/-- **The quotient stack `[U/R]` is a gerbe over the quotient sheaf `U/R`**, as soon as the latter
is an algebraic space: the quotient map `U ⟶ U/R` is a surjection of sheaves, and two local points
of `U` with the same image in `U/R` are fppf-locally the source and the target of an arrow
(Stacks 046O). This is the gerbe criterion for the structure arrow `[U/R] ⟶ U/R` of Stacks 044R,
for the groupoid read over `U/R`. -/
theorem isGerbeOver_quotientStackToBase_quotientSheaf
    (hX : IsAlgebraicSpace C S hS (quotientSheaf (Space.groupoidPreRelation G)).obj) :
    IsGerbeOver (BigFppfOver.topology C S hS)
      (Stack.fibredCategory C S hS (quotientSpace G hX).obj).val.p
      (Stack.quotientStackToBase (overInvariantBase G (toQuotientSpace G hX)
        (source_toQuotientSpace_eq_target hX))).toFunctor := by
  let j := Space.groupoidPreRelation G
  refine Stack.isGerbeOver_quotientStackToBase_of_locallyFull _ (fun T b => ?_)
    (fun T a b hab => ?_)
  · have hls := isLocallySurjective_toQuotientSheaf j
    exact ⟨Presheaf.imageSieve (toQuotientSheaf j) b, hls.imageSieve_mem b, fun V i hi => hi⟩
  · obtain ⟨E, hE, hrel⟩ := (toQuotientSheaf_eq_iff_locally_related j
      (Space.groupoidPreRelation_isPreEquivalenceRelation G) T a b).1 hab
    refine ⟨Sieve.generate E.presieve₀, fppf_hypercover_sieve_mem hS T E hE, ?_⟩
    rintro V i ⟨W, h, g, ⟨k⟩, rfl⟩
    obtain ⟨r, hra, hrb⟩ := hrel k
    rw [groupoidPreRelation_source_left] at hra
    rw [groupoidPreRelation_target_left] at hrb
    refine ⟨G.arrows.obj.map h.op r, ?_, ?_⟩
    · show G.source.hom.app _ (G.arrows.obj.map h.op r) = _
      rw [NatTrans.naturality_apply, ← hra, op_comp, Functor.map_comp_apply]
      rfl
    · show G.target.hom.app _ (G.arrows.obj.map h.op r) = _
      rw [NatTrans.naturality_apply, ← hrb, op_comp, Functor.map_comp_apply]
      rfl

end Gerbe

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
