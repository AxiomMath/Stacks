module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.TwoStepLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of a derived endomorphism along a short exact sequence

Let `P : 𝒞 ⥤ 𝒞`, `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ Mod_R` be additive functors, with `P` and `F₁`
preserving injective objects, and let `θ : P ⋙ F₁ ≅ F₁`.  A *twist* of a bounded below complex
`K` is a morphism of complexes `τ : K ⟶ P(K)`; it induces an endomorphism of `RF₂(RF₁(K))`,
namely `RF₂ ∘ RF₁` of `K ⟶ P(K) ⟶ RP(K)` followed by the comparison `RF₁ ∘ RP ≅ RF₁` attached to
`θ`.  For `P = π̄_*` the direct image along the base change `π̄ = π_X̄ × id` of the geometric
Frobenius, `F₁ = f_*` the direct image to `Spec k̄` and `F₂` global sections, this is exactly
the canonical action `π_X^*` on `RΓ_c(X_k̄, K)` of
`Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`.

This file proves that the trace of that endomorphism is additive along a short exact sequence
of complexes equipped with a twist, which is Step 1 of the proof of [Stacks, Tag 03UG] in its
abstract form.

## Main definitions

* `CategoryTheory.Functor.derivedTwistEndo` — the endomorphism of `RF₂(RF₁(K))` attached to a
  twist of `K`.
* `CategoryTheory.Functor.twistComparison` — the comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))`,
  invertible on bounded below complexes of injectives.
* `CategoryTheory.Functor.TwistResolution` — a degreewise split injective resolution of a short
  exact sequence together with a lift of a twist of it.
* `CategoryTheory.Functor.twistTriangle` and `CategoryTheory.Functor.twistTriangleEndo` — the
  triangle `RF₂RF₁(X₁) ⟶ RF₂RF₁(X₂) ⟶ RF₂RF₁(X₃) ⟶ RF₂RF₁(X₁)[1]` of a short exact sequence and
  the endomorphism of it induced by a twist.

## Main results

* `CategoryTheory.Functor.twistComparison_comp_derivedTwistEndo` — the chain model: on `F₂(F₁(K))`
  the endomorphism is the componentwise `F₂(F₁(τ) ≫ θ)`.
* `CategoryTheory.Functor.derivedTwistEndo_naturality` — naturality in the twisted complex.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_X₂_eq_add` — **additivity of the
  trace** along a short exact sequence with a twist.
* `CategoryTheory.Functor.isPerfect_twistDerivedObj_X₂` — perfectness of `RF₂(RF₁(-))` is two out
  of three along a short exact sequence.
* `CategoryTheory.Functor.TwistResolution.nonempty` — twisted injective resolutions exist.
* `CategoryTheory.Functor.twistTriangle_distinguished` — the triangle is distinguished, and the
  twist acts on it by a morphism of triangles, so its long exact sequence is equivariant.

## Implementation notes

The proof resolves the short exact sequence by a degreewise split short exact sequence of bounded
below complexes of injectives (`CochainComplex.resMap`), lifts the twist to it in the filtered
derived category of the two-step filtration (`CochainComplex.exists_twoStepComplexMap_comp_eq`),
reads the components back in the derived category, and applies
`CategoryTheory.FilteredDerived.perfectDerivedTrace_X₂_eq_add` ([Stacks, Tag 03TK]) to the image of
the resolution under `F₂ ∘ F₁`, which is again short exact because the resolution is degreewise
split. The source phrases the same argument as "filtered derived abstract nonsense".

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 1.
* [Stacks Project, Tag 03TK](https://stacks.math.columbia.edu/tag/03TK).
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁

/-! ### Degreewise split short exact sequences -/

namespace CochainComplex

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ]
  {T : ShortComplex (CochainComplex 𝒜 ℤ)}

/-- A degreewise split short complex of cochain complexes stays short exact under an additive
functor applied degreewise. -/
lemma shortExact_map_of_splitting
    (s : ∀ n, (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting)
    (F : 𝒜 ⥤ ℬ) [F.Additive] : (T.map (F.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ((s n).map F).shortExact

/-- The middle term of a degreewise split short complex is degreewise injective if the outer
ones are. -/
lemma injective_X₂_of_splitting
    (s : ∀ n, (T.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).Splitting) (n : ℤ)
    [Injective (T.X₁.X n)] [Injective (T.X₃.X n)] : Injective (T.X₂.X n) :=
  Injective.of_iso (s n).isoBinaryBiproduct.symm
    (inferInstanceAs (Injective (T.X₁.X n ⊞ T.X₃.X n)))

/-- The middle term of a short exact sequence of cochain complexes is bounded below if the outer
ones are. -/
lemma plus_X₂_of_shortExact (hT : T.ShortExact) (h₁ : CochainComplex.plus 𝒜 T.X₁)
    (h₃ : CochainComplex.plus 𝒜 T.X₃) : CochainComplex.plus 𝒜 T.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨min a b, (isStrictlyGE_iff _ _).2 fun i hi => ?_⟩
  have hi' := hT.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) i)
  exact hi'.exact.isZero_X₂ ((isZero_of_isStrictlyGE T.X₁ a i (by omega)).eq_of_src _ _)
    ((isZero_of_isStrictlyGE T.X₃ b i (by omega)).eq_of_tgt _ _)

/-- **The two-step filtered complex of a short exact sequence of bounded below complexes of
injectives is a bounded below complex of filtered injectives.** -/
lemma filteredInjectivePlusC_twoStepComplex_of_shortExact (hT : T.ShortExact)
    [∀ n, Mono (T.f.f n)] (h₁ : CochainComplex.plus 𝒜 T.X₁) (h₃ : CochainComplex.plus 𝒜 T.X₃)
    [∀ n, Injective (T.X₁.X n)] [∀ n, Injective (T.X₃.X n)] :
    FilteredDerivedCategory.filteredInjectivePlusC 𝒜 (twoStepComplex T) := by
  obtain ⟨a, ha⟩ := plus_X₂_of_shortExact hT h₁ h₃
  refine ⟨⟨a, (isStrictlyGE_iff _ _).2 fun i hi => ?_⟩, fun n p => ?_⟩
  · rw [IsZero.iff_id_eq_zero]
    ext1
    exact FilteredObject.hom_ext (IsZero.eq_of_src (isZero_of_isStrictlyGE T.X₂ a i hi) _ _)
  by_cases hp1 : p = 1
  · subst hp1
    exact Injective.of_iso (FilteredObject.twoStepGrOneIso _).symm
      (inferInstanceAs (Injective (T.X₁.X n)))
  by_cases hp0 : p = 0
  · subst hp0
    exact Injective.of_iso (FilteredObject.twoStepGrZeroIso _
      (degreeShortComplex_shortExact _ hT n)).symm (inferInstanceAs (Injective (T.X₃.X n)))
  · refine IsZero.injective ?_
    rcases lt_or_gt_of_ne hp0 with h | h
    · exact FilteredObject.isZero_gr_twoStep_of_neg _ h
    · exact FilteredObject.isZero_gr_twoStep_of_two_le _ (by omega)

end CochainComplex

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ChainModel

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [Abelian E] [EnoughInjectives C] [EnoughInjectives D]

omit [EnoughInjectives C] [EnoughInjectives D] in
/-- The isomorphism of induced functors on `K⁺` attached to `F ⋙ G ≅ H`, at the image of a
bounded below complex, is the image of the componentwise isomorphism. -/
lemma mapHomotopyCategoryPlusIsoOfCompIso_hom_app_quotient (F : C ⥤ D) (G : D ⥤ E)
    (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (K : CochainComplex.Plus C) :
    (Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e).hom.app
        ((HomotopyCategory.Plus.quotient C).obj K) =
      (HomotopyCategory.Plus.quotient E).map
        (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom _).app K.obj) :
          (F ⋙ G).mapCochainComplexPlus.obj K ⟶ H.mapCochainComplexPlus.obj K) := by
  ext : 1
  change (HomotopyCategory.quotient E _).map
      ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _).inv.app K.obj) ≫
    (HomotopyCategory.quotient E _).map
      ((mapHomologicalComplexCompIso e _).hom.app K.obj) = _
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [mapHomologicalComplexCompIso]

/-- Pasting three commutative squares. -/
lemma comp_eq_of_three_squares {A : Type*} [Category* A]
    {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ : A} (i : X₀ ⟶ X₁) (u : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (c : X₃ ⟶ X₄)
    (c' : X₂ ⟶ Y₂) (m' : Y₂ ⟶ X₄) (τ : X₁ ⟶ Y₁) (u' : Y₁ ⟶ Y₂) (q : X₀ ⟶ Y₀) (i' : Y₀ ⟶ Y₁)
    (hn : m ≫ c = c' ≫ m') (hfac : u ≫ c' = τ ≫ u') (hq : q ≫ i' = i ≫ τ) :
    (i ≫ u ≫ m) ≫ c = q ≫ i' ≫ u' ≫ m' := by
  rw [Category.assoc, Category.assoc, hn, reassoc_of% hfac, reassoc_of% hq]

omit [EnoughInjectives D] in
/-- **The derived-functor unit of a composite, transported along `F ⋙ G ≅ H`.**  The unit of
`R(F ⋙ G)` at a bounded below complex `K`, followed by the induced isomorphism
`R(F ⋙ G) ≅ RH`, is the image of the componentwise isomorphism `(F ⋙ G)(K) ≅ H(K)` followed
by the unit of `RH` at `K`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) (K : CochainComplex.Plus C) :
    (mapCochainComplexPlusDerivedUnit (F ⋙ G)).app K ≫
        (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom _).app K.obj) :
            (F ⋙ G).mapCochainComplexPlus.obj K ⟶ H.mapCochainComplexPlus.obj K) ≫
        (mapCochainComplexPlusDerivedUnit H).app K := by
  have hn := (Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso F G H e).hom.naturality
    ((DerivedCategory.Plus.quotientCompQhIso C).hom.app K)
  have hq := (DerivedCategory.Plus.quotientCompQhIso E).inv.naturality
    (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex e.hom _).app K.obj) :
      (F ⋙ G).mapCochainComplexPlus.obj K ⟶ H.mapCochainComplexPlus.obj K)
  have hfac := rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctorPlus H.rightDerivedFunctorPlus
    (F ⋙ G).rightDerivedFunctorPlusUnith H.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso C)
    (isoWhiskerRight (Stacks.EtaleCohomology.mapHomotopyCategoryPlusIsoOfCompIso F G H e)
      DerivedCategory.Plus.Qh).hom ((HomotopyCategory.Plus.quotient C).obj K)
  dsimp only [Functor.comp_map, Functor.comp_obj, isoWhiskerRight_hom, whiskerRight_app]
    at hn hq hfac
  rw [mapHomotopyCategoryPlusIsoOfCompIso_hom_app_quotient] at hfac
  rw [mapCochainComplexPlusDerivedUnit_app, mapCochainComplexPlusDerivedUnit_app]
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ hn hfac hq

end ChainModel

/-! ### The endomorphism of `RF₂(RF₁(K))` attached to a twist `K ⟶ P(K)` -/

section Twist

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D]
  [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- The componentwise isomorphism `F₁(P(K)) ≅ F₁(K)` induced by `θ`, as a morphism of bounded
below complexes. -/
abbrev twistCompMap (K : CochainComplex.Plus C) :
    F₁.mapCochainComplexPlus.obj (P.mapCochainComplexPlus.obj K) ⟶
      F₁.mapCochainComplexPlus.obj K :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex θ.hom _).app K.obj)

/-- **The derived endomorphism attached to a twist.**  For a bounded below complex `K` and a
morphism of complexes `τ : K ⟶ P(K)`, the endomorphism of `RF₂(RF₁(K))` obtained by applying
`RF₂ ∘ RF₁` to `K ⟶ P(K) ⟶ RP(K)` and composing with the comparison `RF₁ ∘ RP ≅ RF₁` attached
to `θ : P ⋙ F₁ ≅ F₁`. -/
def derivedTwistEndo (K : CochainComplex.Plus C) (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    F₂.rightDerivedFunctorPlus.obj (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ⟶
      F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) :=
  F₂.rightDerivedFunctorPlus.map
    (F₁.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map τ ≫ (mapCochainComplexPlusDerivedUnit P).app K) ≫
      (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).inv.app
        (DerivedCategory.Plus.Q.obj K))

private lemma eq_of_comp_iso {A : Type*} [Category* A] {X₀ X₁ X₂ X₃ Y : A}
    (a : X₀ ⟶ X₁) (t : X₁ ⟶ Y) (ih : X₁ ⟶ X₂) (ii : X₂ ⟶ X₁) (q : X₀ ⟶ X₃) (uK : X₃ ⟶ X₂)
    (lhs : X₀ ⟶ Y) (chom : X₂ ⟶ Y) (hc : chom = ii ≫ t) (h1 : a ≫ t = lhs)
    (h2 : a ≫ ih = q ≫ uK) (hii : ih ≫ ii = 𝟙 _) : lhs = q ≫ uK ≫ chom := by
  rw [hc, ← reassoc_of% h2, reassoc_of% hii, h1]

omit [EnoughInjectives D] in
/-- **The unit of `RF₁` at `P(K)` against the unit of `RP`.**  The unit of `RF₁` at `P(K)`
followed by `RF₁` of the unit of `RP` at `K` is `θ` followed by the unit of `RF₁` at `K` and the
comparison `RF₁ ≅ RF₁ ∘ RP` attached to `θ`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_map_unit (K : CochainComplex.Plus C) :
    (mapCochainComplexPlusDerivedUnit F₁).app (P.mapCochainComplexPlus.obj K) ≫
        F₁.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit P).app K) =
      DerivedCategory.Plus.Q.map (twistCompMap P F₁ θ K) ≫
        (mapCochainComplexPlusDerivedUnit F₁).app K ≫
          (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).hom.app
            (DerivedCategory.Plus.Q.obj K) := by
  have h1 := mapCochainComplexPlusDerivedUnit_comp P F₁ (rightDerivedFunctorPlusComp P F₁)
    (rightDerivedFunctorPlusComp_fac P F₁) K
  have h2 := mapCochainComplexPlusDerivedUnit_app_comp_rightDerivedFunctorPlusIsoOfCompIso_hom
    P F₁ F₁ θ K
  exact eq_of_comp_iso _ _ _ _ _ _ _ _ rfl h1 h2
    ((Stacks.EtaleCohomology.rightDerivedFunctorPlusIsoOfCompIso P F₁ F₁ θ).hom_inv_id_app _)

omit [EnoughInjectives D] in
/-- **Chain model of the twisted endomorphism at the level of `RF₁`.**  The unit of `RF₁` at `K`
intertwines the componentwise endomorphism `F₁(τ) ≫ θ` of `F₁(K)` with the endomorphism of
`RF₁(K)` induced by `τ`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_twist (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    (mapCochainComplexPlusDerivedUnit F₁).app K ≫
        (F₁.rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map τ ≫ (mapCochainComplexPlusDerivedUnit P).app K) ≫
          (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).inv.app
            (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map (F₁.mapCochainComplexPlus.map τ ≫ twistCompMap P F₁ θ K) ≫
        (mapCochainComplexPlusDerivedUnit F₁).app K := by
  have hn := (mapCochainComplexPlusDerivedUnit F₁).naturality τ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Functor.map_comp, Category.assoc, ← Category.assoc _ (F₁.rightDerivedFunctorPlus.map _),
    ← hn, Category.assoc, reassoc_of% (mapCochainComplexPlusDerivedUnit_app_comp_map_unit P F₁ θ K),
    Iso.hom_inv_id_app, Category.comp_id, Functor.map_comp, Category.assoc]

/-- The componentwise endomorphism `F₂(F₁(τ) ≫ θ)` of `F₂(F₁(K))`: the chain model of
`CategoryTheory.Functor.derivedTwistEndo`. -/
abbrev twistChainEndo (K : CochainComplex.Plus C) (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K) ⟶
      F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K) :=
  F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map τ ≫ twistCompMap P F₁ θ K)

/-- The comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` assembled from the two derived-functor units. -/
def twistComparison (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K)) ⟶
      F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) :=
  (mapCochainComplexPlusDerivedUnit F₂).app (F₁.mapCochainComplexPlus.obj K) ≫
    F₂.rightDerivedFunctorPlus.map ((mapCochainComplexPlusDerivedUnit F₁).app K)

/-- **Chain model of the twisted endomorphism.**  The comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))`
intertwines the componentwise endomorphism `F₂(F₁(τ) ≫ θ)` with
`CategoryTheory.Functor.derivedTwistEndo`. -/
lemma twistComparison_comp_derivedTwistEndo (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    twistComparison F₁ F₂ K ≫ derivedTwistEndo P F₁ F₂ θ K τ =
      DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ K τ) ≫ twistComparison F₁ F₂ K := by
  have hn := (mapCochainComplexPlusDerivedUnit F₂).naturality
    (F₁.mapCochainComplexPlus.map τ ≫ twistCompMap P F₁ θ K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [twistComparison, derivedTwistEndo, Category.assoc, ← Functor.map_comp,
    mapCochainComplexPlusDerivedUnit_app_comp_twist, Functor.map_comp, ← Category.assoc, ← hn,
    Category.assoc]

/-- The comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` is invertible on a bounded below complex of
injective objects, when `F₁` preserves injective objects. -/
lemma isIso_twistComparison [F₁.PreservesInjectiveObjects] (K : CochainComplex.Plus C)
    (hK : ∀ n, Injective (K.obj.X n)) : IsIso (twistComparison F₁ F₂ K) := by
  have h₁ : IsIso ((mapCochainComplexPlusDerivedUnit F₁).app K) :=
    Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app F₁ K
      fun n => have := hK n; rightAcyclic_of_injective F₁ _
  have h₂ : IsIso ((mapCochainComplexPlusDerivedUnit F₂).app (F₁.mapCochainComplexPlus.obj K)) :=
    Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app F₂ _
      fun n => have := hK n; have : Injective (F₁.obj (K.obj.X n)) := inferInstance
        rightAcyclic_of_injective F₂ (F₁.obj (K.obj.X n))
  rw [twistComparison]
  infer_instance

/-- **Naturality of the twisted endomorphism.**  A morphism `ψ : K ⟶ L` compatible with twists
`τ_K` and `τ_L` up to quasi-isomorphism intertwines the two derived endomorphisms. -/
lemma derivedTwistEndo_naturality {K L : CochainComplex.Plus C} (ψ : K ⟶ L)
    (τK : K ⟶ P.mapCochainComplexPlus.obj K) (τL : L ⟶ P.mapCochainComplexPlus.obj L)
    (h : DerivedCategory.Plus.Q.map (τK ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ τL)) :
    derivedTwistEndo P F₁ F₂ θ K τK ≫
        F₂.rightDerivedFunctorPlus.map
          (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) =
      F₂.rightDerivedFunctorPlus.map
          (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        derivedTwistEndo P F₁ F₂ θ L τL := by
  have hc := (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).inv.naturality
    (DerivedCategory.Plus.Q.map ψ)
  have hu := (mapCochainComplexPlusDerivedUnit P).naturality ψ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc hu
  rw [Functor.map_comp, Functor.map_comp] at h
  simp only [derivedTwistEndo, ← Functor.map_comp, Category.assoc]
  congr 1
  rw [← hc, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    Category.assoc, ← hu, reassoc_of% h, Functor.map_comp, Functor.map_comp, Category.assoc]


/-- The comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` is natural in `K`. -/
lemma twistComparison_naturality {K L : CochainComplex.Plus C} (φ : K ⟶ L) :
    DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map φ)) ≫
        twistComparison F₁ F₂ L =
      twistComparison F₁ F₂ K ≫ F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) := by
  have h₁ := (mapCochainComplexPlusDerivedUnit F₁).naturality φ
  have h₂ := (mapCochainComplexPlusDerivedUnit F₂).naturality (F₁.mapCochainComplexPlus.map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [twistComparison, twistComparison, reassoc_of% h₂, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← h₁]

/-- The comparison `RF₂(RF₁(K)) ≅ F₂(F₁(T))` attached to a quasi-isomorphism `K ⟶ T` into a
bounded below complex of injectives, in the unbounded derived category of `E`. -/
def twistResolutionIso [F₁.PreservesInjectiveObjects] {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n)) :
    DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) ≅
      DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj :=
  haveI : IsIso (DerivedCategory.Plus.Q.map ψ) :=
    haveI : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  haveI := isIso_twistComparison F₁ F₂ T hT
  DerivedCategory.Plus.ι.mapIso
    (F₂.rightDerivedFunctorPlus.mapIso
        (F₁.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ψ))) ≪≫
      (asIso (twistComparison F₁ F₂ T)).symm)

/-- **The resolution comparison intertwines the twisted endomorphism with its chain model.** -/
lemma twistResolutionIso_hom_comp [F₁.PreservesInjectiveObjects] {K T : CochainComplex.Plus C}
    (ψ : K ⟶ T) [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n))
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g)) :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ) ≫
        (twistResolutionIso F₁ F₂ ψ hT).hom =
      (twistResolutionIso F₁ F₂ ψ hT).hom ≫
        DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom := by
  have := isIso_twistComparison F₁ F₂ T hT
  have hn := derivedTwistEndo_naturality P F₁ F₂ θ ψ τ g h
  have hc := twistComparison_comp_derivedTwistEndo P F₁ F₂ θ T g
  have hc' : derivedTwistEndo P F₁ F₂ θ T g ≫ CategoryTheory.inv (twistComparison F₁ F₂ T) =
      CategoryTheory.inv (twistComparison F₁ F₂ T) ≫
        DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  change DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change derivedTwistEndo P F₁ F₂ θ K τ ≫ (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) ≫
      DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g)
  rw [reassoc_of% hn, hc', Category.assoc]

/-- **Naturality of the resolution comparison.** -/
lemma twistResolutionIso_naturality [F₁.PreservesInjectiveObjects]
    {K T K' T' : CochainComplex.Plus C} (ψ : K ⟶ T) [QuasiIso ψ.hom]
    (hT : ∀ n, Injective (T.obj.X n)) (ψ' : K' ⟶ T') [QuasiIso ψ'.hom]
    (hT' : ∀ n, Injective (T'.obj.X n)) (φ : K ⟶ K') (φ' : T ⟶ T') (h : φ ≫ ψ' = ψ ≫ φ') :
    DerivedCategory.Plus.ι.map (F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ))) ≫
        (twistResolutionIso F₁ F₂ ψ' hT').hom =
      (twistResolutionIso F₁ F₂ ψ hT).hom ≫
        DerivedCategory.Q.map
          (F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map φ')).hom := by
  have := isIso_twistComparison F₁ F₂ T hT
  have := isIso_twistComparison F₁ F₂ T' hT'
  have hn := twistComparison_naturality F₁ F₂ φ'
  have hn' : CategoryTheory.inv (twistComparison F₁ F₂ T) ≫
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map φ')) =
      F₂.rightDerivedFunctorPlus.map
          (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ')) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T') := by
    rw [IsIso.inv_comp_eq, ← reassoc_of% hn, IsIso.hom_inv_id, Category.comp_id]
  change DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map φ')))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map φ)) ≫
      (F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ')) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T')) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) ≫
      DerivedCategory.Plus.Q.map (F₂.mapCochainComplexPlus.map (F₁.mapCochainComplexPlus.map φ'))
  rw [Category.assoc, hn', ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, h]

end Twist

/-! ### Traces of twisted endomorphisms -/

section Trace

open CategoryTheory.FilteredDerived

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- **The trace of a twisted endomorphism is computed on an injective resolution.**  For a
quasi-isomorphism `ψ : K ⟶ T` into a bounded below complex of injectives and twists `τ` of `K`
and `g` of `T` compatible along `ψ` in the derived category, the trace of the derived
endomorphism of `RF₂(RF₁(K))` attached to `τ` is the trace of the componentwise endomorphism
`F₂(F₁(g) ≫ θ)` of `F₂(F₁(T))`. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n)) (τ : K ⟶ P.mapCochainComplexPlus.obj K)
    (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hT' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj)) :
    perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedTrace R ⟨_, hT'⟩
        (DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom) :=
  perfectDerivedTrace_congr R _ _ (twistResolutionIso F₁ F₂ ψ hT) _ _
    (twistResolutionIso_hom_comp P F₁ F₂ θ ψ hT τ g h)

/-- A twist of a bounded below complex, as a morphism of bounded below complexes. -/
abbrev plusTwist {K : CochainComplex C ℤ} (hK : CochainComplex.plus C K)
    (τ : K ⟶ (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :
    (⟨K, hK⟩ : CochainComplex.Plus C) ⟶ P.mapCochainComplexPlus.obj ⟨K, hK⟩ :=
  ObjectProperty.homMk τ

/-- `RF₂(RF₁(K))` for a bounded below complex `K`, in the unbounded derived category. -/
abbrev twistDerivedObj {K : CochainComplex C ℤ} (hK : CochainComplex.plus C K) :
    DerivedCategory (ModuleCat.{max u v} R) :=
  DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
    (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, hK⟩)))

end Trace

/-! ### Additivity along a short exact sequence -/

section Additivity

open CategoryTheory.FilteredDerived CochainComplex

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] [F₁.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- **A twisted injective resolution** of a short exact sequence `S` of bounded below complexes
with a twist `τ : S ⟶ P(S)`: a degreewise split short exact sequence `T` of bounded below
complexes of injectives, a componentwise quasi-isomorphism `ψ : S ⟶ T`, and a twist `g` of `T`
compatible with `τ` along `ψ` in the derived category. -/
structure TwistResolution {S : ShortComplex (CochainComplex C ℤ)}
    (τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))) where
  /-- The resolving short exact sequence. -/
  T : ShortComplex (CochainComplex C ℤ)
  /-- A degreewise splitting of `T`. -/
  split : ∀ n, (T.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting
  shortExact : T.ShortExact
  plus₁ : CochainComplex.plus C T.X₁
  plus₂ : CochainComplex.plus C T.X₂
  plus₃ : CochainComplex.plus C T.X₃
  injective₁ (n : ℤ) : Injective (T.X₁.X n)
  injective₂ (n : ℤ) : Injective (T.X₂.X n)
  injective₃ (n : ℤ) : Injective (T.X₃.X n)
  /-- The resolution map. -/
  ψ : S ⟶ T
  quasiIso₁ : QuasiIso ψ.τ₁
  quasiIso₂ : QuasiIso ψ.τ₂
  quasiIso₃ : QuasiIso ψ.τ₃
  /-- The lifted twist. -/
  g : T ⟶ T.map (P.mapHomologicalComplex (ComplexShape.up ℤ))
  comm₁ : DerivedCategory.Q.map (ψ.τ₁ ≫ g.τ₁) =
    DerivedCategory.Q.map (τ.τ₁ ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.τ₁)
  comm₂ : DerivedCategory.Q.map (ψ.τ₂ ≫ g.τ₂) =
    DerivedCategory.Q.map (τ.τ₂ ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.τ₂)
  comm₃ : DerivedCategory.Q.map (ψ.τ₃ ≫ g.τ₃) =
    DerivedCategory.Q.map (τ.τ₃ ≫ (P.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.τ₃)

omit [F₁.PreservesInjectiveObjects] in
/-- **Twisted injective resolutions exist**: the cone resolution of `S`, with `τ` lifted in the
filtered derived category of the two-step filtration. -/
theorem TwistResolution.nonempty {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (h₁ : CochainComplex.plus C S.X₁) (h₃ : CochainComplex.plus C S.X₃)
    (τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))) :
    Nonempty (TwistResolution P τ) := by
  have : ∀ n, Mono (S.f.f n) := mono_f_f_of_shortExact hS
  obtain ⟨a, ha⟩ := id h₁
  obtain ⟨b, hb⟩ := id h₃
  obtain ⟨R₁, -, -⟩ := exists_injectiveResolution_isStrictlyGE a S.X₁
  obtain ⟨R₃, -, -⟩ := exists_injectiveResolution_isStrictlyGE b S.X₃
  let φ := resφ hS R₁.ι R₁.boundedBelow R₃.ι
  let T := resShortComplex hS R₁.ι R₁.boundedBelow R₃.ι
  let ψ : S ⟶ T := resMap hS R₁.ι R₁.boundedBelow R₃.ι
  have hT : T.ShortExact := resShortComplex_shortExact hS R₁.ι R₁.boundedBelow R₃.ι
  let sp : ∀ n, (T.map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting :=
    fun n => mappingCone.triangleRotateShortComplexSplitting φ n
  let P' := P.mapHomologicalComplex (ComplexShape.up ℤ)
  have hT' : (T.map P').ShortExact := shortExact_map_of_splitting sp P
  have : ∀ n, Mono ((T.map P').f.f n) := mono_f_f_of_shortExact hT'
  have i₁ : ∀ n, Injective (T.X₁.X n) := fun n => inferInstanceAs (Injective (R₁.cocomplex.X n))
  have i₃ : ∀ n, Injective (T.X₃.X n) := fun n =>
    inferInstanceAs (Injective (R₃.cocomplex.X (n + 1 + -1)))
  have i₂ : ∀ n, Injective (T.X₂.X n) := fun n => injective_X₂_of_splitting sp n
  have : ∀ n, Injective ((T.map P').X₁.X n) := fun n =>
    inferInstanceAs (Injective (P.obj (T.X₁.X n)))
  have : ∀ n, Injective ((T.map P').X₃.X n) := fun n =>
    inferInstanceAs (Injective (P.obj (T.X₃.X n)))
  have hT₁ : CochainComplex.plus C T.X₁ := R₁.boundedBelow
  have hT₃ : CochainComplex.plus C T.X₃ := (CochainComplex.plus C).prop_of_iso
    ((shiftFunctorCompIsoId (CochainComplex C ℤ) (-1 : ℤ) 1 (by omega)).app R₃.cocomplex).symm
    R₃.boundedBelow
  have hTinj : FilteredDerivedCategory.filteredInjectivePlusC C (twoStepComplex (T.map P')) :=
    filteredInjectivePlusC_twoStepComplex_of_shortExact hT'
      (P.mapCochainComplexPlus.obj ⟨_, hT₁⟩).property
      (P.mapCochainComplexPlus.obj ⟨_, hT₃⟩).property
  obtain ⟨g, hg⟩ := exists_twoStepComplexMap_comp_eq hT ψ
    (filteredQuasiIsoC_twoStepComplexMap_resMap hS R₁.ι R₁.boundedBelow R₃.ι) hTinj
    (τ ≫ P'.mapShortComplex.map ψ)
  obtain ⟨e₁, e₂, e₃⟩ := Q_map_τ_eq_of_Qh_map_twoStepComplexMap_eq hS hT' hTinj _ _ hg
  have q₁ : QuasiIso ψ.τ₁ := inferInstanceAs (QuasiIso R₁.ι)
  have q₃ : QuasiIso ψ.τ₃ := by
    change QuasiIso (resτ₃ R₃.ι)
    unfold resτ₃
    infer_instance
  exact ⟨⟨T, sp, hT, hT₁, plus_X₂_of_shortExact hT hT₁ hT₃, hT₃, i₁, i₂, i₃, ψ, q₁,
    StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ ψ hS hT, q₃, g, e₁, e₂, e₃⟩⟩

namespace TwistResolution

variable {P} {S : ShortComplex (CochainComplex C ℤ)}
  {τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))} (Rs : TwistResolution P τ)

/-- The image of the resolving sequence under `F₂ ∘ F₁`, again short exact. -/
abbrev image : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  (Rs.T.map (F₁.mapHomologicalComplex (ComplexShape.up ℤ))).map
    (F₂.mapHomologicalComplex (ComplexShape.up ℤ))

omit [EnoughInjectives C] [EnoughInjectives D] [P.PreservesInjectiveObjects]
  [F₁.PreservesInjectiveObjects] in
/-- The image of the resolving sequence under `F₂ ∘ F₁` is short exact. -/
lemma image_shortExact : (Rs.image F₁ F₂).ShortExact :=
  shortExact_map_of_splitting (fun n => (Rs.split n).map F₁) F₂

/-- The componentwise endomorphism `F₂(F₁(g) ≫ θ)` of the image of the resolving sequence. -/
def imageEndo : Rs.image F₁ F₂ ⟶ Rs.image F₁ F₂ where
  τ₁ := (F₂.mapHomologicalComplex _).map ((F₁.mapHomologicalComplex _).map Rs.g.τ₁ ≫
    (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app Rs.T.X₁)
  τ₂ := (F₂.mapHomologicalComplex _).map ((F₁.mapHomologicalComplex _).map Rs.g.τ₂ ≫
    (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app Rs.T.X₂)
  τ₃ := (F₂.mapHomologicalComplex _).map ((F₁.mapHomologicalComplex _).map Rs.g.τ₃ ≫
    (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app Rs.T.X₃)
  comm₁₂ := by
    ext n : 1
    have h := congrArg (fun z => z.f n) Rs.g.comm₁₂
    simp only [HomologicalComplex.comp_f] at h
    change Rs.g.τ₁.f n ≫ P.map (Rs.T.f.f n) = Rs.T.f.f n ≫ Rs.g.τ₂.f n at h
    dsimp
    rw [← F₂.map_comp, ← F₂.map_comp]
    simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
    rw [← θ.hom.naturality (Rs.T.f.f n), Functor.comp_map, ← F₁.map_comp_assoc, h,
      F₁.map_comp, Category.assoc]
  comm₂₃ := by
    ext n : 1
    have h := congrArg (fun z => z.f n) Rs.g.comm₂₃
    simp only [HomologicalComplex.comp_f] at h
    change Rs.g.τ₂.f n ≫ P.map (Rs.T.g.f n) = Rs.T.g.f n ≫ Rs.g.τ₃.f n at h
    dsimp
    rw [← F₂.map_comp, ← F₂.map_comp]
    simp only [NatTrans.mapHomologicalComplex_app_f, Category.assoc]
    rw [← θ.hom.naturality (Rs.T.g.f n), Functor.comp_map, ← F₁.map_comp_assoc, h,
      F₁.map_comp, Category.assoc]

variable (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
  (h₃ : CochainComplex.plus C S.X₃)

/-- The comparison `RF₂(RF₁(X₁)) ≅ F₂(F₁(T₁))`. -/
def iso₁ : twistDerivedObj F₁ F₂ h₁ ≅ DerivedCategory.Q.obj (Rs.image F₁ F₂).X₁ :=
  haveI : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₁ :
      (⟨S.X₁, h₁⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₁, Rs.plus₁⟩).hom := Rs.quasiIso₁
  twistResolutionIso F₁ F₂ (K := ⟨S.X₁, h₁⟩) (T := ⟨Rs.T.X₁, Rs.plus₁⟩)
    (ObjectProperty.homMk Rs.ψ.τ₁) Rs.injective₁

/-- The comparison `RF₂(RF₁(X₂)) ≅ F₂(F₁(T₂))`. -/
def iso₂ : twistDerivedObj F₁ F₂ h₂ ≅ DerivedCategory.Q.obj (Rs.image F₁ F₂).X₂ :=
  haveI : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₂ :
      (⟨S.X₂, h₂⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₂, Rs.plus₂⟩).hom := Rs.quasiIso₂
  twistResolutionIso F₁ F₂ (K := ⟨S.X₂, h₂⟩) (T := ⟨Rs.T.X₂, Rs.plus₂⟩)
    (ObjectProperty.homMk Rs.ψ.τ₂) Rs.injective₂

/-- The comparison `RF₂(RF₁(X₃)) ≅ F₂(F₁(T₃))`. -/
def iso₃ : twistDerivedObj F₁ F₂ h₃ ≅ DerivedCategory.Q.obj (Rs.image F₁ F₂).X₃ :=
  haveI : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₃ :
      (⟨S.X₃, h₃⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₃, Rs.plus₃⟩).hom := Rs.quasiIso₃
  twistResolutionIso F₁ F₂ (K := ⟨S.X₃, h₃⟩) (T := ⟨Rs.T.X₃, Rs.plus₃⟩)
    (ObjectProperty.homMk Rs.ψ.τ₃) Rs.injective₃

/-- `Rs.iso₁` intertwines the twisted endomorphism of `RF₂(RF₁(X₁))` with the component
`(Rs.imageEndo F₁ F₂ θ).τ₁` of the chain model. -/
lemma iso₁_hom_comp :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁)) ≫
        (Rs.iso₁ F₁ F₂ h₁).hom =
      (Rs.iso₁ F₁ F₂ h₁).hom ≫ DerivedCategory.Q.map (Rs.imageEndo F₁ F₂ θ).τ₁ :=
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₁ :
      (⟨S.X₁, h₁⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₁, Rs.plus₁⟩).hom := Rs.quasiIso₁
  twistResolutionIso_hom_comp P F₁ F₂ θ (K := ⟨S.X₁, h₁⟩) (T := ⟨Rs.T.X₁, Rs.plus₁⟩)
    (ObjectProperty.homMk Rs.ψ.τ₁) Rs.injective₁ (plusTwist P h₁ τ.τ₁)
    (plusTwist P Rs.plus₁ Rs.g.τ₁)
    (DerivedCategory.Plus.ι.map_injective Rs.comm₁.symm)

/-- `Rs.iso₂` intertwines the twisted endomorphism of `RF₂(RF₁(X₂))` with the component
`(Rs.imageEndo F₁ F₂ θ).τ₂` of the chain model. -/
lemma iso₂_hom_comp :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂)) ≫
        (Rs.iso₂ F₁ F₂ h₂).hom =
      (Rs.iso₂ F₁ F₂ h₂).hom ≫ DerivedCategory.Q.map (Rs.imageEndo F₁ F₂ θ).τ₂ :=
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₂ :
      (⟨S.X₂, h₂⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₂, Rs.plus₂⟩).hom := Rs.quasiIso₂
  twistResolutionIso_hom_comp P F₁ F₂ θ (K := ⟨S.X₂, h₂⟩) (T := ⟨Rs.T.X₂, Rs.plus₂⟩)
    (ObjectProperty.homMk Rs.ψ.τ₂) Rs.injective₂ (plusTwist P h₂ τ.τ₂)
    (plusTwist P Rs.plus₂ Rs.g.τ₂)
    (DerivedCategory.Plus.ι.map_injective Rs.comm₂.symm)

/-- `Rs.iso₃` intertwines the twisted endomorphism of `RF₂(RF₁(X₃))` with the component
`(Rs.imageEndo F₁ F₂ θ).τ₃` of the chain model. -/
lemma iso₃_hom_comp :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃)) ≫
        (Rs.iso₃ F₁ F₂ h₃).hom =
      (Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.Q.map (Rs.imageEndo F₁ F₂ θ).τ₃ :=
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₃ :
      (⟨S.X₃, h₃⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₃, Rs.plus₃⟩).hom := Rs.quasiIso₃
  twistResolutionIso_hom_comp P F₁ F₂ θ (K := ⟨S.X₃, h₃⟩) (T := ⟨Rs.T.X₃, Rs.plus₃⟩)
    (ObjectProperty.homMk Rs.ψ.τ₃) Rs.injective₃ (plusTwist P h₃ τ.τ₃)
    (plusTwist P Rs.plus₃ Rs.g.τ₃)
    (DerivedCategory.Plus.ι.map_injective Rs.comm₃.symm)

end TwistResolution

/-- **Additivity of the trace of a twisted derived endomorphism along a short exact sequence**
(Step 1 of the proof of [Stacks, Tag 03UG]).  Let `0 → X₁ → X₂ → X₃ → 0` be a short exact
sequence of bounded below complexes and `τ` a twist of it, i.e. a morphism of short complexes
into its image under `P`.  If `RF₂(RF₁(Xᵢ))` is perfect for each `i` then the traces of the
derived endomorphisms attached to `τ` satisfy `Tr(X₂) = Tr(X₁) + Tr(X₃)`.  The proof realises
`τ` on an injective resolution of the sequence compatibly with the two-step filtration and
applies [Stacks, Tag 03TK] in the form of
`CategoryTheory.FilteredDerived.perfectDerivedTrace_X₂_eq_add` to the chain model. -/
@[sga "5 IIIB 5.6" "special case"]
theorem perfectDerivedTrace_derivedTwistEndo_X₂_eq_add {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
    (h₃ : CochainComplex.plus C S.X₃)
    (τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ)))
    (hp₁ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₁))
    (hp₂ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₂))
    (hp₃ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₃)) :
    perfectDerivedTrace R ⟨_, hp₂⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂))) =
      perfectDerivedTrace R ⟨_, hp₁⟩
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁))) +
        perfectDerivedTrace R ⟨_, hp₃⟩
          (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃))) := by
  obtain ⟨Rs⟩ := TwistResolution.nonempty P hS h₁ h₃ τ
  have hq₁ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₁ F₁ F₂ h₁).symm hp₁
  have hq₂ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₂ F₁ F₂ h₂).symm hp₂
  have hq₃ := StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₃ F₁ F₂ h₃).symm hp₃
  rw [perfectDerivedTrace_congr R ⟨_, hp₁⟩ ⟨_, hq₁⟩ _ _ _ (Rs.iso₁_hom_comp F₁ F₂ θ h₁),
    perfectDerivedTrace_congr R ⟨_, hp₂⟩ ⟨_, hq₂⟩ _ _ _ (Rs.iso₂_hom_comp F₁ F₂ θ h₂),
    perfectDerivedTrace_congr R ⟨_, hp₃⟩ ⟨_, hq₃⟩ _ _ _ (Rs.iso₃_hom_comp F₁ F₂ θ h₃)]
  exact perfectDerivedTrace_X₂_eq_add (Rs.image_shortExact F₁ F₂) (Rs.imageEndo F₁ F₂ θ) hq₁ hq₂ hq₃

/-- **Perfectness of `RF₂(RF₁(-))` is two out of three along a short exact sequence**: if
`RF₂(RF₁(X₁))` and `RF₂(RF₁(X₃))` are perfect, so is `RF₂(RF₁(X₂))`. -/
theorem isPerfect_twistDerivedObj_X₂ {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
    (h₃ : CochainComplex.plus C S.X₃)
    (hp₁ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₁))
    (hp₃ : StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₃)) :
    StacksDraft.Perfect.IsPerfect (twistDerivedObj F₁ F₂ h₂) := by
  obtain ⟨Rs⟩ := TwistResolution.nonempty (𝟭 C) hS h₁ h₃ 0
  exact StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₂ F₁ F₂ h₂)
    (isPerfect_X₂_of_shortExact (Rs.image_shortExact F₁ F₂)
      (StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₁ F₁ F₂ h₁).symm hp₁)
      (StacksDraft.Perfect.isPerfect_of_iso (Rs.iso₃ F₁ F₂ h₃).symm hp₃))

/-! ### The equivariant triangle of a short exact sequence -/

section Triangle

open Pretriangulated

variable {P} {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂)
  (h₃ : CochainComplex.plus C S.X₃)
  {τ : S ⟶ S.map (P.mapHomologicalComplex (ComplexShape.up ℤ))} (Rs : TwistResolution P τ)

/-- The image under `RF₂ ∘ RF₁` of a morphism of bounded below complexes, in the unbounded
derived category. -/
abbrev twistDerivedMap {K L : CochainComplex C ℤ} (hK : CochainComplex.plus C K)
    (hL : CochainComplex.plus C L) (φ : K ⟶ L) :
    twistDerivedObj F₁ F₂ hK ⟶ twistDerivedObj F₁ F₂ hL :=
  DerivedCategory.Plus.ι.map (F₂.rightDerivedFunctorPlus.map (F₁.rightDerivedFunctorPlus.map
    (DerivedCategory.Plus.Q.map (ObjectProperty.homMk φ :
      (⟨K, hK⟩ : CochainComplex.Plus C) ⟶ ⟨L, hL⟩))))

/-- **The triangle `RF₂RF₁(X₁) ⟶ RF₂RF₁(X₂) ⟶ RF₂RF₁(X₃) ⟶ RF₂RF₁(X₁)[1]`** of a short exact
sequence; the first two maps are induced by the sequence and the connecting map is read off a
twisted injective resolution. -/
def twistTriangle : Triangle (DerivedCategory (ModuleCat.{max u v} R)) :=
  Triangle.mk (twistDerivedMap F₁ F₂ h₁ h₂ S.f) (twistDerivedMap F₁ F₂ h₂ h₃ S.g)
    ((Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.triangleOfSESδ (Rs.image_shortExact F₁ F₂) ≫
      (Rs.iso₁ F₁ F₂ h₁).inv⟦(1 : ℤ)⟧')

omit [P.PreservesInjectiveObjects] in
/-- `Rs.iso₁` and `Rs.iso₂` carry the first map of `twistTriangle` to that of the image of the
resolving sequence. -/
lemma twistTriangle_comm₁ : twistDerivedMap F₁ F₂ h₁ h₂ S.f ≫ (Rs.iso₂ F₁ F₂ h₂).hom =
    (Rs.iso₁ F₁ F₂ h₁).hom ≫ DerivedCategory.Q.map (Rs.image F₁ F₂).f :=
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₁ :
      (⟨S.X₁, h₁⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₁, Rs.plus₁⟩).hom := Rs.quasiIso₁
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₂ :
      (⟨S.X₂, h₂⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₂, Rs.plus₂⟩).hom := Rs.quasiIso₂
  twistResolutionIso_naturality F₁ F₂ (K := ⟨S.X₁, h₁⟩) (T := ⟨Rs.T.X₁, Rs.plus₁⟩)
    (K' := ⟨S.X₂, h₂⟩) (T' := ⟨Rs.T.X₂, Rs.plus₂⟩) (ObjectProperty.homMk Rs.ψ.τ₁) Rs.injective₁
    (ObjectProperty.homMk Rs.ψ.τ₂) Rs.injective₂ (ObjectProperty.homMk S.f)
    (ObjectProperty.homMk Rs.T.f) (by ext : 1; exact Rs.ψ.comm₁₂.symm)

omit [P.PreservesInjectiveObjects] in
/-- `Rs.iso₂` and `Rs.iso₃` carry the second map of `twistTriangle` to that of the image of the
resolving sequence. -/
lemma twistTriangle_comm₂ : twistDerivedMap F₁ F₂ h₂ h₃ S.g ≫ (Rs.iso₃ F₁ F₂ h₃).hom =
    (Rs.iso₂ F₁ F₂ h₂).hom ≫ DerivedCategory.Q.map (Rs.image F₁ F₂).g :=
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₂ :
      (⟨S.X₂, h₂⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₂, Rs.plus₂⟩).hom := Rs.quasiIso₂
  have : QuasiIso (ObjectProperty.homMk Rs.ψ.τ₃ :
      (⟨S.X₃, h₃⟩ : CochainComplex.Plus C) ⟶ ⟨Rs.T.X₃, Rs.plus₃⟩).hom := Rs.quasiIso₃
  twistResolutionIso_naturality F₁ F₂ (K := ⟨S.X₂, h₂⟩) (T := ⟨Rs.T.X₂, Rs.plus₂⟩)
    (K' := ⟨S.X₃, h₃⟩) (T' := ⟨Rs.T.X₃, Rs.plus₃⟩) (ObjectProperty.homMk Rs.ψ.τ₂) Rs.injective₂
    (ObjectProperty.homMk Rs.ψ.τ₃) Rs.injective₃ (ObjectProperty.homMk S.g)
    (ObjectProperty.homMk Rs.T.g) (by ext : 1; exact Rs.ψ.comm₂₃.symm)

/-- The triangle of a short exact sequence is isomorphic to the triangle of the image of its
twisted injective resolution. -/
def twistTriangleIso :
    twistTriangle F₁ F₂ h₁ h₂ h₃ Rs ≅ DerivedCategory.triangleOfSES (Rs.image_shortExact F₁ F₂) :=
  Triangle.isoMk _ _ (Rs.iso₁ F₁ F₂ h₁) (Rs.iso₂ F₁ F₂ h₂) (Rs.iso₃ F₁ F₂ h₃)
    (twistTriangle_comm₁ F₁ F₂ h₁ h₂ Rs) (twistTriangle_comm₂ F₁ F₂ h₂ h₃ Rs) (by
      change ((Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.triangleOfSESδ (Rs.image_shortExact F₁ F₂) ≫
        (Rs.iso₁ F₁ F₂ h₁).inv⟦(1 : ℤ)⟧') ≫ (Rs.iso₁ F₁ F₂ h₁).hom⟦(1 : ℤ)⟧' =
          (Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.triangleOfSESδ (Rs.image_shortExact F₁ F₂)
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
        Category.comp_id])

omit [P.PreservesInjectiveObjects] in
/-- **The triangle of a short exact sequence is distinguished.** -/
lemma twistTriangle_distinguished :
    twistTriangle F₁ F₂ h₁ h₂ h₃ Rs ∈ distTriang (DerivedCategory (ModuleCat.{max u v} R)) :=
  isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished _) _
    (twistTriangleIso F₁ F₂ h₁ h₂ h₃ Rs)

/-- **The twisted endomorphism of the triangle**: its components are the derived endomorphisms
attached to the twist on the three terms, so the long exact cohomology sequence of the triangle
is equivariant, connecting maps included. -/
def twistTriangleEndo : twistTriangle F₁ F₂ h₁ h₂ h₃ Rs ⟶ twistTriangle F₁ F₂ h₁ h₂ h₃ Rs where
  hom₁ := DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁))
  hom₂ := DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂))
  hom₃ := DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃))
  comm₁ := by
    change twistDerivedMap F₁ F₂ h₁ h₂ S.f ≫
        DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂)) =
      DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁)) ≫
        twistDerivedMap F₁ F₂ h₁ h₂ S.f
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine (derivedTwistEndo_naturality P F₁ F₂ θ (K := ⟨S.X₁, h₁⟩) (L := ⟨S.X₂, h₂⟩)
      (ObjectProperty.homMk S.f) _ _ ?_).symm
    congr 1
    ext : 1
    exact τ.comm₁₂
  comm₂ := by
    change twistDerivedMap F₁ F₂ h₂ h₃ S.g ≫
        DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃)) =
      DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₂ τ.τ₂)) ≫
        twistDerivedMap F₁ F₂ h₂ h₃ S.g
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    refine (derivedTwistEndo_naturality P F₁ F₂ θ (K := ⟨S.X₂, h₂⟩) (L := ⟨S.X₃, h₃⟩)
      (ObjectProperty.homMk S.g) _ _ ?_).symm
    congr 1
    ext : 1
    exact τ.comm₂₃
  comm₃ := by
    have e₁ : (Rs.iso₁ F₁ F₂ h₁).inv ≫
        DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁)) =
        DerivedCategory.Q.map (Rs.imageEndo F₁ F₂ θ).τ₁ ≫ (Rs.iso₁ F₁ F₂ h₁).inv := by
      rw [Iso.inv_comp_eq, ← reassoc_of% (Rs.iso₁_hom_comp F₁ F₂ θ h₁), Iso.hom_inv_id,
        Category.comp_id]
    have hδ := DerivedCategory.triangleOfSESδ_naturality (Rs.image_shortExact F₁ F₂)
      (Rs.image_shortExact F₁ F₂) (Rs.imageEndo F₁ F₂ θ)
    change ((Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.triangleOfSESδ (Rs.image_shortExact F₁ F₂) ≫
        (Rs.iso₁ F₁ F₂ h₁).inv⟦(1 : ℤ)⟧') ≫
        (DerivedCategory.Plus.ι.map
          (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₁ τ.τ₁)))⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ _ (plusTwist P h₃ τ.τ₃)) ≫
        ((Rs.iso₃ F₁ F₂ h₃).hom ≫ DerivedCategory.triangleOfSESδ (Rs.image_shortExact F₁ F₂) ≫
          (Rs.iso₁ F₁ F₂ h₁).inv⟦(1 : ℤ)⟧')
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, e₁, Functor.map_comp,
      reassoc_of% hδ, ← reassoc_of% (Rs.iso₃_hom_comp F₁ F₂ θ h₃)]

end Triangle

end Additivity

end CategoryTheory.Functor
