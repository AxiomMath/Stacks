module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenImmersionSquare

/-!
# The closure of a graph in a compactification times a proper scheme

Let `c : X ⟶ X̄` be a compactification of `φ : X ⟶ S` and `ψ : X ⟶ P` a morphism over `S` to a
scheme `P` proper over `S`. The scheme-theoretic image `W` of `(c, ψ) : X ⟶ X̄ ×_S P` is again a
compactification of `X`; its projection `W ⟶ X̄` is proper and `X` is its inverse image of `X`,
and its projection `ḡ : W ⟶ P` is proper and extends `ψ`.

When `ψ` is itself a compactification this is `AlgebraicGeometry.CompactificationOf.dominating`.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.graph`, with projections `graphFst` and `graphSnd`.

## Main results

* `AlgebraicGeometry.CompactificationOf.isPullback_graphFst`: `X = q₁⁻¹(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {S X P : Scheme.{u}} {φ : X ⟶ S} [QuasiCompact φ] (c : CompactificationOf (Over.mk φ))
  (πP : P ⟶ S) [IsProper πP] (ψ : X ⟶ P) (hψ : ψ ≫ πP = φ)

include hψ in
/-- The morphism `(c, ψ) : X ⟶ X̄ ×_S P`. -/
def graphImmersion : X ⟶ pullback c.toBase πP :=
  pullback.lift c.immersion ψ (by rw [CompactificationOf.immersion_toBase, hψ])

omit [QuasiCompact φ] [IsProper πP] in
/-- The first component of `(c, ψ)` is `c`. -/
@[reassoc (attr := simp)]
lemma graphImmersion_fst : graphImmersion c πP ψ hψ ≫ pullback.fst _ _ = c.immersion :=
  pullback.lift_fst _ _ _

omit [QuasiCompact φ] [IsProper πP] in
/-- The second component of `(c, ψ)` is `ψ`. -/
@[reassoc (attr := simp)]
lemma graphImmersion_snd : graphImmersion c πP ψ hψ ≫ pullback.snd _ _ = ψ :=
  pullback.lift_snd _ _ _

/-- The morphism `(c, ψ) : X ⟶ X̄ ×_S P` is an immersion. -/
instance : IsImmersion (graphImmersion c πP ψ hψ) := by
  have : IsImmersion (graphImmersion c πP ψ hψ ≫ pullback.fst c.toBase πP) := by
    rw [graphImmersion_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst c.toBase πP)

/-- The morphism `(c, ψ) : X ⟶ X̄ ×_S P` is quasi-compact. -/
instance : QuasiCompact (graphImmersion c πP ψ hψ) := by
  have : QuasiCompact (graphImmersion c πP ψ hψ ≫ pullback.fst c.toBase πP) := by
    rw [graphImmersion_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst c.toBase πP)

/-- The morphism from `X` to the scheme-theoretic image of `(c, ψ)` is an open immersion. -/
instance : IsOpenImmersion (graphImmersion c πP ψ hψ).toImage :=
  isOpenImmersion_toImage _ (Or.inl inferInstance)

/-- **The closure of the graph of `ψ`**: the open immersion of `X` into the scheme-theoretic image
`W` of `(c, ψ) : X ⟶ X̄ ×_S P`, which is proper over `S`. -/
def graph : CompactificationOf (Over.mk φ) :=
  ⟨StructuredArrow.mk
      (Y := Over.mk ((graphImmersion c πP ψ hψ).imageι ≫ pullback.fst _ _ ≫ c.toBase))
      (Over.homMk (U := Over.mk φ) (graphImmersion c πP ψ hψ).toImage (by
        change (graphImmersion c πP ψ hψ).toImage ≫ (graphImmersion c πP ψ hψ).imageι ≫
          pullback.fst _ _ ≫ c.toBase = φ
        rw [← Category.assoc, Scheme.Hom.toImage_imageι, graphImmersion_fst_assoc,
          CompactificationOf.immersion_toBase])),
    ⟨(inferInstance : IsOpenImmersion (graphImmersion c πP ψ hψ).toImage),
      (inferInstance : IsProper ((graphImmersion c πP ψ hψ).imageι ≫ pullback.fst _ _ ≫
        c.toBase))⟩⟩

/-- The open immersion of `X` into `W` is the corestriction of `(c, ψ)` to its image. -/
lemma graph_immersion : (graph c πP ψ hψ).immersion = (graphImmersion c πP ψ hψ).toImage := rfl

/-- The projection `W ⟶ X̄`. -/
def graphFst : (graph c πP ψ hψ).space ⟶ c.space :=
  (graphImmersion c πP ψ hψ).imageι ≫ pullback.fst _ _

/-- The projection `ḡ : W ⟶ P`. -/
def graphSnd : (graph c πP ψ hψ).space ⟶ P :=
  (graphImmersion c πP ψ hψ).imageι ≫ pullback.snd _ _

/-- The composite `X ⟶ W ⟶ X̄` is `c`. -/
@[reassoc (attr := simp)]
lemma immersion_graphFst : (graph c πP ψ hψ).immersion ≫ graphFst c πP ψ hψ = c.immersion := by
  show (graphImmersion c πP ψ hψ).toImage ≫ (graphImmersion c πP ψ hψ).imageι ≫
    pullback.fst _ _ = c.immersion
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, graphImmersion_fst]

/-- The composite `X ⟶ W ⟶ P` is `ψ`. -/
@[reassoc (attr := simp)]
lemma immersion_graphSnd : (graph c πP ψ hψ).immersion ≫ graphSnd c πP ψ hψ = ψ := by
  show (graphImmersion c πP ψ hψ).toImage ≫ (graphImmersion c πP ψ hψ).imageι ≫
    pullback.snd _ _ = ψ
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, graphImmersion_snd]

/-- The projection `W ⟶ X̄` is a morphism over `S`. -/
lemma graphFst_toBase : graphFst c πP ψ hψ ≫ c.toBase = (graph c πP ψ hψ).toBase := by
  simp [graphFst]; rfl

/-- The projection `ḡ : W ⟶ P` is a morphism over `S`. -/
lemma graphSnd_toBase : graphSnd c πP ψ hψ ≫ πP = (graph c πP ψ hψ).toBase := by
  show ((graphImmersion c πP ψ hψ).imageι ≫ pullback.snd _ _) ≫ πP =
    (graphImmersion c πP ψ hψ).imageι ≫ pullback.fst _ _ ≫ c.toBase
  rw [Category.assoc, pullback.condition]

/-- The projection `W ⟶ X̄` is proper. -/
instance : IsProper (graphFst c πP ψ hψ) := by
  have : IsProper (graphImmersion c πP ψ hψ).imageι := inferInstance
  exact inferInstanceAs (IsProper ((graphImmersion c πP ψ hψ).imageι ≫ pullback.fst _ _))

/-- The projection `ḡ : W ⟶ P` is proper. -/
instance : IsProper (graphSnd c πP ψ hψ) := by
  have : IsProper (graphImmersion c πP ψ hψ).imageι := inferInstance
  exact inferInstanceAs (IsProper ((graphImmersion c πP ψ hψ).imageι ≫ pullback.snd _ _))

/-- **A point of `W` over the image of `X` in `X̄` lies on the image of `X` in `W`.** -/
theorem preimage_range_graphFst_subset :
    (graphFst c πP ψ hψ).base ⁻¹' Set.range c.immersion.base ⊆
      Set.range (graph c πP ψ hψ).immersion.base := by
  let W := graph c πP ψ hψ
  let q := graphFst c πP ψ hψ
  let m := W.immersion
  let V : W.space.Opens := q ⁻¹ᵁ c.immersion.opensRange
  have hsub : ∀ {A B C : Scheme.{u}} (f : A ⟶ B) (m : C ⟶ B) [IsOpenImmersion m],
      Set.range ((f ⁻¹ᵁ m.opensRange).ι ≫ f).base ⊆ Set.range m.base := by
    rintro A B C f m _ _ ⟨v, rfl⟩
    exact v.2
  let r : V.toScheme ⟶ X := IsOpenImmersion.lift c.immersion (V.ι ≫ q) (hsub q _)
  let O : V.toScheme.Opens := V.ι ⁻¹ᵁ m.opensRange
  have hO : IsSchemeTheoreticallyDominant O.ι :=
    isSchemeTheoreticallyDense_toImage (graphImmersion c πP ψ hψ) (Or.inl inferInstance) V
  let s : O.toScheme ⟶ X := IsOpenImmersion.lift m (O.ι ≫ V.ι) (hsub V.ι _)
  have hs : s ≫ m = O.ι ≫ V.ι := IsOpenImmersion.lift_fac _ _ _
  have hOs : O.ι ≫ r = s := by
    rw [← cancel_mono c.immersion, Category.assoc, IsOpenImmersion.lift_fac,
      ← immersion_graphFst c πP ψ hψ, ← Category.assoc s, hs, Category.assoc]
  have : IsSeparated (Over.mk W.toBase).hom := (W.property.2).toIsSeparated
  have heq := eq_of_isSchemeTheoreticallyDominant_ι (S := S)
    (X := Over.mk (V.ι ≫ W.toBase)) (Y := Over.mk W.toBase)
    (Over.homMk V.ι rfl) (Over.homMk (r ≫ m) (by
      show (r ≫ W.immersion) ≫ W.toBase = V.ι ≫ W.toBase
      have h1 : W.immersion ≫ W.toBase = φ := CompactificationOf.immersion_toBase W
      have h2 : c.immersion ≫ c.toBase = φ := CompactificationOf.immersion_toBase c
      have h3 : r ≫ c.immersion = V.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
      calc (r ≫ W.immersion) ≫ W.toBase = r ≫ φ := by rw [Category.assoc, h1]
        _ = (r ≫ c.immersion) ≫ c.toBase := by rw [Category.assoc, h2]
        _ = V.ι ≫ W.toBase := by rw [h3, Category.assoc, graphFst_toBase]))
    O (by simp [← Category.assoc, hOs, hs])
  intro p hp
  have hpV : p ∈ (V : Set W.space) := hp
  have h1 := congrArg (fun f => f.left.base ⟨p, hpV⟩) heq
  simp only [Over.homMk_left] at h1
  exact ⟨r.base ⟨p, hpV⟩, h1.symm⟩

/-- **The closure of the graph is cartesian over `c`**: `X = q₁⁻¹(X)`. -/
theorem isPullback_graphFst :
    IsPullback (𝟙 X) (graph c πP ψ hψ).immersion c.immersion (graphFst c πP ψ hψ) :=
  isPullback_id_of_preimage_range_subset _ _ _ (immersion_graphFst c πP ψ hψ)
    (preimage_range_graphFst_subset c πP ψ hψ)

/-- The image of `X` is dense in the closure of the graph. -/
theorem denseRange_graph_immersion : DenseRange (graph c πP ψ hψ).immersion.base :=
  (isDominant_toImage (graphImmersion c πP ψ hψ) (Or.inl inferInstance)).denseRange

end AlgebraicGeometry.CompactificationOf

end
