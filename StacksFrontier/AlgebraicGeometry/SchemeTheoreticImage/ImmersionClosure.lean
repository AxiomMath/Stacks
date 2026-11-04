module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The scheme-theoretic closure of an immersion over an open where it is closed

Let `i : U ⟶ T` be a quasi-compact immersion and let `Z = i.image` be its scheme-theoretic
closure, with closed immersion `Z ⟶ T` and open immersion `U ⟶ Z`. If `W ⊆ T` is an open
subscheme containing the image of `i` in which that image is closed, then the inverse image of
`W` in `Z` is exactly `U`: closing up `U` adds no point over `W`.

This is the step of the domination argument for compactifications (the proof of
[Stacks, Tag 0ATT] (a)) that identifies the dominating compactification with the given ones over
the scheme being compactified.

## Main results

* `AlgebraicGeometry.Scheme.Hom.range_imageι`: the scheme-theoretic closure of a quasi-compact
  morphism has the closure of its range as underlying set.
* `AlgebraicGeometry.Scheme.Hom.preimage_imageι_eq_opensRange_toImage`: the inverse image of `W`
  in the scheme-theoretic closure is the open subscheme `U`.
* `AlgebraicGeometry.GraphClosure.preimage_closureFst` and
  `AlgebraicGeometry.GraphClosure.preimage_closureSnd`: for separated `Xb, P` over `V`, an open
  `U ⊆ Xb`, an open `A ⊆ P` and a closed immersion `i : U ⟶ A` over `V`, the scheme-theoretic
  closure `Z` of the graph `U ⟶ Xb ×_V P` satisfies `pr₁⁻¹(U) = U` and `pr₂⁻¹(A) = U` in `Z`.

## References

* [Stacks Project, Tag 0ATT](https://stacks.math.columbia.edu/tag/0ATT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {U T : Scheme.{u}} (i : U ⟶ T)

/-- The scheme-theoretic closure of a quasi-compact morphism has, as underlying set, the closure
of the range of the morphism. -/
@[ega "I 9.5.10" "more general", ega "I 9.5.4" "partial"]
theorem range_imageι [QuasiCompact i] :
    Set.range i.imageι = closure (Set.range i) := by
  rw [IdealSheafData.range_subschemeι, Hom.support_ker]

/-- **Closing up an immersion adds no point over an open where it is already closed.** Let
`i : U ⟶ T` be a quasi-compact immersion and `W ⊆ T` an open containing the range of `i`, in
which that range is closed. Then the inverse image of `W` in the scheme-theoretic closure of `i`
is the open subscheme `U`. -/
@[ega "I 3.7.2" "partial"]
theorem preimage_imageι_eq_opensRange_toImage [IsImmersion i] [QuasiCompact i] (W : T.Opens)
    (hW : Set.range i ⊆ W)
    (hcl : IsClosed (((↑) : W → T) ⁻¹' Set.range i)) :
    i.imageι ⁻¹ᵁ W = i.toImage.opensRange := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Hom.coe_opensRange,
    Set.mem_range]
  constructor
  · intro hz
    -- `i.imageι z` lies in the closure of the range of `i` and in `W`.
    have hcl' : i.imageι z ∈ closure (Set.range i) := by
      rw [← range_imageι]; exact ⟨z, rfl⟩
    have hmem : (⟨i.imageι z, hz⟩ : W) ∈
        closure (((↑) : W → T) ⁻¹' Set.range i) := by
      rw [W.isOpen.isOpenEmbedding_subtypeVal.closure_eq_preimage_closure_image]
      refine closure_mono ?_ hcl'
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨i x, hW ⟨x, rfl⟩⟩, ⟨x, rfl⟩, rfl⟩
    rw [hcl.closure_eq] at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨x, i.imageι.isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Hom.toImage_imageι]
    exact hx
  · rintro ⟨x, rfl⟩
    rw [← Scheme.Hom.comp_apply, Hom.toImage_imageι]
    exact hW ⟨x, rfl⟩

/-- `Scheme.Hom.preimage_imageι_eq_opensRange_toImage` with the closedness hypothesis supplied by
a factorization of `i` through `W` as a closed immersion. -/
@[ega "I 3.7.2" "partial"]
theorem preimage_imageι_eq_opensRange_toImage_of_isClosedImmersion [IsImmersion i]
    [QuasiCompact i] (W : T.Opens) (c : U ⟶ W.toScheme) [IsClosedImmersion c]
    (hc : c ≫ W.ι = i) :
    i.imageι ⁻¹ᵁ W = i.toImage.opensRange := by
  refine preimage_imageι_eq_opensRange_toImage i W ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [← hc, Scheme.Hom.comp_apply]
    exact (c x).2
  · have : ((↑) : W → T) ⁻¹' Set.range i = Set.range c := by
      ext y
      simp only [Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, Subtype.ext ?_⟩
        rw [← hx, ← hc, Scheme.Hom.comp_apply]
        rfl
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [← hc, Scheme.Hom.comp_apply]; rfl⟩
    rw [this]
    exact c.isClosedEmbedding.isClosed_range

end AlgebraicGeometry.Scheme.Hom

/-! ### The closure of a graph in a product of two schemes over a base -/

namespace AlgebraicGeometry.GraphClosure

open Limits

variable {V Xb P U A : Scheme.{u}} (π₁ : Xb ⟶ V) (π₂ : P ⟶ V) (u : U ⟶ Xb) (a : A ⟶ P)
  (i : U ⟶ A) (h : u ≫ π₁ = i ≫ a ≫ π₂)

/-- The graph `U ⟶ Xb ×_V P` of the morphism `U ⟶ A ⟶ P`, paired with `u : U ⟶ Xb`. -/
noncomputable abbrev graph : U ⟶ pullback π₁ π₂ := pullback.lift u (i ≫ a) h

/-- The graph followed by the first projection is `u`. -/
@[reassoc (attr := simp)]
theorem graph_fst : graph π₁ π₂ u a i h ≫ pullback.fst π₁ π₂ = u := pullback.lift_fst _ _ _

/-- The graph followed by the second projection is `i ≫ a`. -/
@[reassoc (attr := simp)]
theorem graph_snd : graph π₁ π₂ u a i h ≫ pullback.snd π₁ π₂ = i ≫ a := pullback.lift_snd _ _ _

/-- The graph factors through the open `pr₁⁻¹(U)` of the product. -/
noncomputable def graphToFst [IsOpenImmersion u] :
    U ⟶ (pullback.fst π₁ π₂ ⁻¹ᵁ u.opensRange).toScheme :=
  IsOpenImmersion.lift (pullback.fst π₁ π₂ ⁻¹ᵁ u.opensRange).ι (graph π₁ π₂ u a i h) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (graph π₁ π₂ u a i h ≫ pullback.fst π₁ π₂) x ∈ u.opensRange
    rw [graph_fst]
    exact ⟨x, rfl⟩)

/-- The factorization `graphToFst` followed by the inclusion of `pr₁⁻¹(U)` is the graph. -/
@[reassoc (attr := simp)]
theorem graphToFst_ι [IsOpenImmersion u] :
    graphToFst π₁ π₂ u a i h ≫ (pullback.fst π₁ π₂ ⁻¹ᵁ u.opensRange).ι = graph π₁ π₂ u a i h :=
  IsOpenImmersion.lift_fac _ _ _

/-- The graph factors through the open `pr₂⁻¹(A)` of the product. -/
noncomputable def graphToSnd [IsOpenImmersion a] :
    U ⟶ (pullback.snd π₁ π₂ ⁻¹ᵁ a.opensRange).toScheme :=
  IsOpenImmersion.lift (pullback.snd π₁ π₂ ⁻¹ᵁ a.opensRange).ι (graph π₁ π₂ u a i h) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (graph π₁ π₂ u a i h ≫ pullback.snd π₁ π₂) x ∈ a.opensRange
    rw [graph_snd, Scheme.Hom.comp_apply]
    exact ⟨i x, rfl⟩)

/-- The factorization `graphToSnd` followed by the inclusion of `pr₂⁻¹(A)` is the graph. -/
@[reassoc (attr := simp)]
theorem graphToSnd_ι [IsOpenImmersion a] :
    graphToSnd π₁ π₂ u a i h ≫ (pullback.snd π₁ π₂ ⁻¹ᵁ a.opensRange).ι = graph π₁ π₂ u a i h :=
  IsOpenImmersion.lift_fac _ _ _

/-- If `f ≫ s = k ≫ o` with `k` a closed immersion, `o` an open immersion and `s` separated
with range inside that of `o`, then `f` is a closed immersion. -/
private theorem isClosedImmersion_of_comp_eq_of_isSeparated {X Y B C : Scheme.{u}} (f : X ⟶ Y)
    (k : X ⟶ B) (o : B ⟶ C) (s : Y ⟶ C) [IsOpenImmersion o] [IsSeparated s] [IsClosedImmersion k]
    (hs : Set.range s ⊆ Set.range o) (w : f ≫ s = k ≫ o) : IsClosedImmersion f := by
  let q : Y ⟶ B := IsOpenImmersion.lift o s hs
  have hqo : q ≫ o = s := IsOpenImmersion.lift_fac _ _ _
  have hq : f ≫ q = k := by rw [← cancel_mono o, Category.assoc, hqo, w]
  have : IsSeparated (q ≫ o) := by rw [hqo]; infer_instance
  have : IsSeparated q := IsSeparated.of_comp q o
  have : IsClosedImmersion (f ≫ q) := by rw [hq]; infer_instance
  exact IsClosedImmersion.of_comp f q

/-- Over `pr₁⁻¹(U)` the graph is a closed immersion: composed with the separated morphism
`pr₁⁻¹(U) ⟶ U` it is the identity. -/
@[ega "I 5.4.3" "more general"]
theorem isClosedImmersion_graphToFst [IsOpenImmersion u] [IsSeparated π₂] :
    IsClosedImmersion (graphToFst π₁ π₂ u a i h) :=
  isClosedImmersion_of_comp_eq_of_isSeparated _ (𝟙 U) u
    ((pullback.fst π₁ π₂ ⁻¹ᵁ u.opensRange).ι ≫ pullback.fst π₁ π₂)
    (by rintro _ ⟨w, rfl⟩; exact w.2)
    (by rw [graphToFst_ι_assoc, graph_fst, Category.id_comp])

/-- Over `pr₂⁻¹(A)` the graph is a closed immersion: composed with the separated morphism
`pr₂⁻¹(A) ⟶ A` it is the closed immersion `i`. -/
@[ega "I 5.4.3" "more general"]
theorem isClosedImmersion_graphToSnd [IsOpenImmersion a] [IsSeparated π₁]
    [IsClosedImmersion i] : IsClosedImmersion (graphToSnd π₁ π₂ u a i h) :=
  isClosedImmersion_of_comp_eq_of_isSeparated _ i a
    ((pullback.snd π₁ π₂ ⁻¹ᵁ a.opensRange).ι ≫ pullback.snd π₁ π₂)
    (by rintro _ ⟨w, rfl⟩; exact w.2)
    (by rw [graphToSnd_ι_assoc, graph_snd])

/-- The graph is an immersion: a closed immersion into the open `pr₁⁻¹(U)`. -/
instance isImmersion_graph [IsOpenImmersion u] [IsSeparated π₂] :
    IsImmersion (graph π₁ π₂ u a i h) := by
  have := isClosedImmersion_graphToFst π₁ π₂ u a i h
  rw [← graphToFst_ι π₁ π₂ u a i h]
  infer_instance

/-- The scheme-theoretic closure of the graph, mapped to the first factor. -/
noncomputable abbrev closureFst : (graph π₁ π₂ u a i h).image ⟶ Xb :=
  (graph π₁ π₂ u a i h).imageι ≫ pullback.fst π₁ π₂

/-- The scheme-theoretic closure of the graph, mapped to the second factor. -/
@[sga "7 XVIII 3.1" "partial"]
noncomputable abbrev closureSnd : (graph π₁ π₂ u a i h).image ⟶ P :=
  (graph π₁ π₂ u a i h).imageι ≫ pullback.snd π₁ π₂

/-- On `U`, the first projection of the closure of the graph is `u`. -/
@[reassoc (attr := simp)]
theorem toImage_closureFst : (graph π₁ π₂ u a i h).toImage ≫ closureFst π₁ π₂ u a i h = u := by
  simp [closureFst]

/-- On `U`, the second projection of the closure of the graph is `i ≫ a`. -/
@[reassoc (attr := simp)]
theorem toImage_closureSnd :
    (graph π₁ π₂ u a i h).toImage ≫ closureSnd π₁ π₂ u a i h = i ≫ a := by
  simp [closureSnd]

/-- **Over `U` the closure of the graph is `U`**: the inverse image of `U ⊆ Xb` in the closure
of the graph is the open subscheme `U`. -/
theorem preimage_closureFst [IsOpenImmersion u] [IsSeparated π₂]
    [QuasiCompact (graph π₁ π₂ u a i h)] :
    closureFst π₁ π₂ u a i h ⁻¹ᵁ u.opensRange = (graph π₁ π₂ u a i h).toImage.opensRange := by
  have := isClosedImmersion_graphToFst π₁ π₂ u a i h
  rw [closureFst, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_imageι_eq_opensRange_toImage_of_isClosedImmersion _ _
    (graphToFst π₁ π₂ u a i h) (graphToFst_ι π₁ π₂ u a i h)

/-- **Over `A` the closure of the graph is `U`**: the inverse image of `A ⊆ P` in the closure of
the graph is the open subscheme `U`, on which the second projection is the closed immersion
`i : U ⟶ A`. -/
theorem preimage_closureSnd [IsOpenImmersion u] [IsOpenImmersion a] [IsSeparated π₁]
    [IsSeparated π₂] [IsClosedImmersion i] [QuasiCompact (graph π₁ π₂ u a i h)] :
    closureSnd π₁ π₂ u a i h ⁻¹ᵁ a.opensRange = (graph π₁ π₂ u a i h).toImage.opensRange := by
  have := isClosedImmersion_graphToSnd π₁ π₂ u a i h
  rw [closureSnd, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_imageι_eq_opensRange_toImage_of_isClosedImmersion _ _
    (graphToSnd π₁ π₂ u a i h) (graphToSnd_ι π₁ π₂ u a i h)

/-- A commutative square `t ≫ g = ι ≫ a` with `t : U ⟶ Z` and `a : A ⟶ P` open immersions and
`g⁻¹(a(A)) = t(U)` is cartesian: `U` is the inverse image of `A` under `g`. -/
theorem _root_.AlgebraicGeometry.isPullback_of_preimage_opensRange_eq {U Z A P : Scheme.{u}}
    (t : U ⟶ Z) (ι : U ⟶ A) (g : Z ⟶ P) (a : A ⟶ P) [IsOpenImmersion t] [IsOpenImmersion a]
    (w : t ≫ g = ι ≫ a) (hpre : g ⁻¹ᵁ a.opensRange = t.opensRange) :
    IsPullback t ι g a := by
  have H : ∀ s : PullbackCone g a, Set.range s.fst ⊆ Set.range t := by
    intro s z hz
    obtain ⟨x, rfl⟩ := hz
    have : g (s.fst x) ∈ a.opensRange := by
      rw [← Scheme.Hom.comp_apply, s.condition, Scheme.Hom.comp_apply]
      exact ⟨s.snd x, rfl⟩
    have h' : s.fst x ∈ g ⁻¹ᵁ a.opensRange := this
    rw [hpre] at h'
    exact h'
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift t s.fst (H s))
    (fun s => IsOpenImmersion.lift_fac _ _ _) (fun s => ?_) (fun s m h₁ _ => ?_)⟩⟩
  · have hl := IsOpenImmersion.lift_fac t s.fst (H s)
    apply (cancel_mono a).1
    calc IsOpenImmersion.lift t s.fst (H s) ≫ ι ≫ a
        = IsOpenImmersion.lift t s.fst (H s) ≫ t ≫ g := by rw [w]
      _ = s.fst ≫ g := by rw [← Category.assoc, hl]
      _ = s.snd ≫ a := s.condition
  · have hl := IsOpenImmersion.lift_fac t s.fst (H s)
    rw [← cancel_mono t, hl]
    exact h₁

/-- A commutative square of an open immersion `u' : U ⟶ Z` over an open immersion `u : U ⟶ X`
along `g : Z ⟶ X`, with `g⁻¹(u(U)) = u'(U)`, is cartesian with the identity of `U` on the left:
`g` is an isomorphism over `u`. -/
theorem _root_.AlgebraicGeometry.isPullback_id_of_preimage_opensRange_eq {U Z X : Scheme.{u}}
    (u' : U ⟶ Z) (g : Z ⟶ X) (u : U ⟶ X) [IsOpenImmersion u'] [IsOpenImmersion u]
    (w : u' ≫ g = u) (hpre : g ⁻¹ᵁ u.opensRange = u'.opensRange) :
    IsPullback u' (𝟙 U) g u :=
  isPullback_of_preimage_opensRange_eq u' (𝟙 U) g u (by rw [w, Category.id_comp]) hpre

end AlgebraicGeometry.GraphClosure
