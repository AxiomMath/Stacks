module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Derived colimits in a pre-triangulated category

Let `D` be a pre-triangulated category and let `(Kₙ, fₙ)` be a system of objects of `D`, that is,
a sequence of objects `Kₙ` together with morphisms `fₙ : Kₙ ⟶ Kₙ₊₁`; equivalently a functor
`F : ℕ ⥤ D`. Assume the direct sum `⊕ Kₙ` exists. An object `K` of `D` is a *derived colimit*, or
a *homotopy colimit*, of the system when there is a distinguished triangle
$$ \bigoplus K_n \xrightarrow{1 - f_n} \bigoplus K_n \to K \to \bigoplus K_n[1] $$
whose first map is, on the `n`-th summand, the difference of the coprojection at `n` and the
coprojection at `n + 1` composed after `fₙ`. One writes `K = hocolim Kₙ`. Such a `K` exists as
soon as `⊕ Kₙ` does, by completing the difference map to a distinguished triangle (TR1), and any
two derived colimits of one system are isomorphic (TR3), though not by a unique isomorphism —
which is why this is a property of an object rather than a construction.

## Main definitions

* `CategoryTheory.Pretriangulated.IsHomotopyColimit`: the object `K` is a derived colimit of the
  system `F : ℕ ⥤ D`. That a derived colimit exists is `∃ K, IsHomotopyColimit F K`.

## Main results

* `CategoryTheory.Pretriangulated.IsHomotopyColimit.map`: a triangulated functor that preserves
  the direct sum of the system carries a derived colimit to a derived colimit.
* `CategoryTheory.Pretriangulated.IsHomotopyColimitCocone`: maps `cₙ : Kₙ ⟶ K` exhibit `K` as a
  derived colimit, the second map of the triangle being `Σ cₙ`; with its behaviour under
  triangulated functors, isomorphisms of the target and isomorphisms of systems. This is what
  "`K = hocolim Kₙ` functorially" means for a family of such data depending on a parameter.

## Implementation notes

A system of objects `(Kₙ, fₙ)` is a functor `F : ℕ ⥤ D` on the poset `ℕ`, with `fₙ` the map
`F.map (homOfLE (Nat.le_succ n))`; `CategoryTheory.Functor.ofSequence` turns the source's data
into such a functor. The direct sum is the coproduct `∐ F.obj` of the family `F.obj`, taken in
`D` itself.

The source folds "the direct sum `⊕ Kₙ` exists" into the condition; here it is the instance
hypothesis `[HasCoproduct F.obj]`, because the triangle cannot be written down without the
coproduct object. Nothing is lost: the source's "`K` is a derived colimit of `(Kₙ, fₙ)`" is
`HasCoproduct F.obj → IsHomotopyColimit F K`, and no `K` satisfies the source's condition when
the direct sum fails to exist.

The source assumes `D` triangulated, but the definition mentions only the class `distTriang D`
and the subtraction of morphisms, never the octahedron axiom, so `Pretriangulated D` suffices.

The first map of the triangle is pinned, with the source's sign `1 - fₙ` rather than `fₙ - 1`;
the two remaining maps are existentially quantified, as in the source. Quantifying over the
first map as well would say only that `K` is the cofibre of *some* endomorphism of `∐ F.obj`,
which is strictly weaker. Dually, a derived limit is
`CategoryTheory.Pretriangulated.IsDerivedLimit`.

Since a derived colimit is unique only up to a non-unique isomorphism, no map out of it is
canonical and no `hocolim` notation is introduced. The refinement that records the coprojections
`iₙ : Kₙ ⟶ K` with `iₙ₊₁ ∘ fₙ = iₙ` and the morphism `c : K ⟶ (⊕ Kₙ)⟦1⟧`, together with its
uniqueness statement, is [Stacks, Tag 0CRH].

## References

* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z) (Definition 13.33.1);
  the remarks on existence and on uniqueness up to non-unique isomorphism follow the definition
  there.
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory.Pretriangulated

open Limits

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An object `K` of a pre-triangulated category `D` is a **derived colimit**, or **homotopy
colimit**, of a system of objects `F : ℕ ⥤ D` whose direct sum `∐ F.obj` exists — written
`K = hocolim Kₙ` — if there is a distinguished triangle
`∐ F.obj ⟶ ∐ F.obj ⟶ K ⟶ (∐ F.obj)⟦1⟧` whose first map is `1 - fₙ` on the `n`-th summand, i.e.
`Sigma.ι F.obj n - fₙ ≫ Sigma.ι F.obj (n + 1)`, where `Kₙ = F.obj n` and
`fₙ = F.map (homOfLE (Nat.le_succ n))` is the transition map `Kₙ ⟶ Kₙ₊₁`. Such a `K` is unique
only up to non-unique isomorphism, which is why this is a predicate and not a construction. -/
@[stacks 090Z]
public def IsHomotopyColimit (F : ℕ ⥤ D) [HasCoproduct F.obj] (K : D) : Prop :=
  ∃ (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) p q ∈ distTriang D

/-- An object `K` of a pre-triangulated category `D` is a **derived colimit with the
coprojections `c`** of a system of objects `F : ℕ ⥤ D` whose direct sum `∐ F.obj` exists if it is
a derived colimit, `CategoryTheory.Pretriangulated.IsHomotopyColimit`, by a defining triangle
whose second map `p : ∐ F.obj ⟶ K` restricts on the `n`-th summand to the prescribed morphism
`c n : Kₙ ⟶ K`. This is the recording half of [Stacks, Tag 0CRH]: the coprojections of a derived
colimit are not determined by the object `K`, so a statement that mentions them must carry
them. Only that half is formalized here, so this carries no tag. -/
public def IsHomotopyColimitWith (F : ℕ ⥤ D) [HasCoproduct F.obj] (K : D)
    (c : ∀ n, F.obj n ⟶ K) : Prop :=
  ∃ (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧),
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) p q ∈ distTriang D ∧
    ∀ n, Sigma.ι F.obj n ≫ p = c n

/-- Forgetting the coprojections of a derived colimit leaves a derived colimit. -/
theorem IsHomotopyColimitWith.isHomotopyColimit {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) : IsHomotopyColimit F K :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1⟩

/-- The recorded coprojections may be replaced by a pointwise equal family. -/
theorem IsHomotopyColimitWith.congr_coprojections {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c c' : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (hc : ∀ n, c n = c' n) :
    IsHomotopyColimitWith F K c' :=
  have ⟨p, q, hT, hp⟩ := h
  ⟨p, q, hT, fun n ↦ (hp n).trans (hc n)⟩

/-- Conversely, the coprojections of a derived colimit can always be read off a defining
triangle: they are the restrictions of its second map to the summands. -/
theorem IsHomotopyColimit.exists_isHomotopyColimitWith {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    (h : IsHomotopyColimit F K) : ∃ c, IsHomotopyColimitWith F K c := by
  obtain ⟨p, q, hT⟩ := h
  exact ⟨fun n ↦ Sigma.ι F.obj n ≫ p, p, q, hT, fun _ ↦ rfl⟩

/-- **A derived colimit is one up to isomorphism.** The defining triangle of `K` is carried to
the defining triangle of an isomorphic `K'` by the isomorphism of triangles which is the identity
on the direct sum and the given isomorphism on the third vertex; the coprojections of `K'` are
those of `K` composed with the isomorphism. -/
theorem IsHomotopyColimitWith.of_iso {F : ℕ ⥤ D} [HasCoproduct F.obj] {K K' : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (e : K ≅ K') :
    IsHomotopyColimitWith F K' (fun n ↦ c n ≫ e.hom) := by
  obtain ⟨p, q, hT, hc⟩ := h
  exact ⟨p ≫ e.hom, e.inv ≫ q, isomorphic_distinguished _ hT _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp)),
    fun n ↦ by rw [← Category.assoc, hc]⟩

/-! ### The image of a derived colimit under a triangulated functor -/

section Map

variable {E : Type u'} [Category.{v'} E] [Preadditive E]

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- The endomorphism `1 - G fₙ` of the direct sum of the image system `n ↦ G Kₙ` is carried, by
composition with the comparison map `⊕ G Kₙ ⟶ G (⊕ Kₙ)`, to the image under `G` of the
endomorphism `1 - fₙ` of `⊕ Kₙ`. The map of the image system is spelled out as a `Sigma.desc`
over the family `fun n ↦ G (Kₙ)` rather than over `(F ⋙ G).obj`, so that one `HasCoproduct`
instance serves both it and the comparison map: instance search does not see through
`Functor.comp`. -/
private lemma desc_oneSub_comp_sigmaComparison (F : ℕ ⥤ D) [HasCoproduct F.obj] (G : D ⥤ E)
    [G.Additive] [HasCoproduct fun n ↦ G.obj (F.obj n)] :
    (Sigma.desc fun n ↦ Sigma.ι (fun m ↦ G.obj (F.obj m)) n -
          G.map (F.map (homOfLE (Nat.le_succ n))) ≫
            Sigma.ι (fun m ↦ G.obj (F.obj m)) (n + 1)) ≫ sigmaComparison G F.obj =
      sigmaComparison G F.obj ≫ G.map (Sigma.desc fun n ↦ Sigma.ι F.obj n -
        F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) := by
  rw [sigmaComparison_map_desc]
  refine Sigma.hom_ext _ _ fun n ↦ ?_
  simp [Preadditive.sub_comp, ι_comp_sigmaComparison]

variable [HasZeroObject E] [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E]

/-- A triangulated functor `G` carries a derived colimit to a derived colimit, as soon as it
preserves the direct sum of the system: if `K = hocolim Kₙ` in `D` and `G` preserves `⊕ Kₙ`, then
`G K = hocolim G Kₙ` in `E`. The defining triangle of `K` is carried to a distinguished triangle
by `G`, and the comparison `⊕ G Kₙ ≅ G (⊕ Kₙ)` turns its first map into the map `1 - G fₙ` that
the derived colimit of the image system requires, because `G` is additive. The coprojections of
the image are the images of the coprojections: the comparison map takes the `n`-th coprojection
of `⊕ G Kₙ` to `G (σₙ)`. -/
theorem IsHomotopyColimitWith.map {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitWith F K c) (G : D ⥤ E) [G.CommShift ℤ]
    [G.IsTriangulated] [HasCoproduct (F ⋙ G).obj]
    [PreservesColimit (Discrete.functor F.obj) G] :
    IsHomotopyColimitWith (F ⋙ G) (G.obj K) (fun n ↦ G.map (c n)) := by
  have : HasCoproduct fun n ↦ G.obj (F.obj n) := ‹HasCoproduct (F ⋙ G).obj›
  obtain ⟨p, q, hT, hc⟩ := h
  set e := asIso (sigmaComparison G F.obj)
  have hδ : ((G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
        (shiftFunctor E (1 : ℤ)).map e.inv) ≫ (shiftFunctor E (1 : ℤ)).map e.hom =
      𝟙 (G.obj K) ≫ G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj) := by
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    simp
  refine ⟨e.hom ≫ G.map p,
    (G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
      (shiftFunctor E (1 : ℤ)).map e.inv, ?_, fun n ↦ ?_⟩
  · exact isomorphic_distinguished _ (G.map_distinguished _ hT) _
      (Triangle.isoMk _ _ e e (Iso.refl _) (desc_oneSub_comp_sigmaComparison F G)
        (Category.comp_id _) hδ)
  · have hι : Sigma.ι (F ⋙ G).obj n ≫ sigmaComparison G F.obj = G.map (Sigma.ι F.obj n) :=
      ι_comp_sigmaComparison G F.obj n
    rw [← Category.assoc, show e.hom = sigmaComparison G F.obj from rfl, hι, ← G.map_comp, hc]

/-- A triangulated functor `G` carries a derived colimit to a derived colimit, as soon as it
preserves the direct sum of the system: if `K = hocolim Kₙ` in `D` and `G` preserves `⊕ Kₙ`, then
`G K = hocolim G Kₙ` in `E`. The defining triangle of `K` is carried to a distinguished triangle
by `G`, and the comparison `⊕ G Kₙ ≅ G (⊕ Kₙ)` turns its first map into the map `1 - G fₙ` that
the derived colimit of the image system requires, because `G` is additive. -/
theorem IsHomotopyColimit.map {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    (h : IsHomotopyColimit F K) (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]
    [HasCoproduct (F ⋙ G).obj] [PreservesColimit (Discrete.functor F.obj) G] :
    IsHomotopyColimit (F ⋙ G) (G.obj K) := by
  have : HasCoproduct fun n ↦ G.obj (F.obj n) := ‹HasCoproduct (F ⋙ G).obj›
  obtain ⟨p, q, hT⟩ := h
  set e := asIso (sigmaComparison G F.obj)
  have hδ : ((G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
        (shiftFunctor E (1 : ℤ)).map e.inv) ≫ (shiftFunctor E (1 : ℤ)).map e.hom =
      𝟙 (G.obj K) ≫ G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj) := by
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    simp
  refine ⟨e.hom ≫ G.map p,
    (G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
      (shiftFunctor E (1 : ℤ)).map e.inv, ?_⟩
  exact isomorphic_distinguished _ (G.map_distinguished _ hT) _
    (Triangle.isoMk _ _ e e (Iso.refl _) (desc_oneSub_comp_sigmaComparison F G)
      (Category.comp_id _) hδ)

/-! ### Derived colimits with prescribed coprojections -/

/-- The maps `cₙ : Kₙ ⟶ K` **exhibit `K` as a derived colimit** of the system `F`: the triangle
`⊕ Kₙ ⟶ ⊕ Kₙ ⟶ K ⟶ (⊕ Kₙ)[1]` with first map `1 - fₙ` and second map `Σ cₙ` is distinguished
for some third map. -/
def IsHomotopyColimitCocone (F : ℕ ⥤ D) [HasCoproduct F.obj] {K : D} (c : ∀ n, F.obj n ⟶ K) :
    Prop :=
  ∃ q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧,
    Triangle.mk (Sigma.desc fun n ↦ Sigma.ι F.obj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)) (Sigma.desc c) q ∈ distTriang D

/-- Coprojections exhibiting `K` as a derived colimit make `K` a derived colimit. -/
theorem IsHomotopyColimitCocone.isHomotopyColimit {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitCocone F c) : IsHomotopyColimit F K :=
  let ⟨q, hq⟩ := h
  ⟨_, q, hq⟩

/-- A derived colimit is exhibited by the coprojections `Sigma.ι Kₙ ≫ p` of its triangle. -/
theorem IsHomotopyColimit.exists_isHomotopyColimitCocone {F : ℕ ⥤ D} [HasCoproduct F.obj]
    {K : D} (h : IsHomotopyColimit F K) :
    ∃ c : ∀ n, F.obj n ⟶ K, IsHomotopyColimitCocone F c := by
  obtain ⟨p, q, hT⟩ := h
  refine ⟨fun n ↦ Sigma.ι F.obj n ≫ p, q, ?_⟩
  have hp : (Sigma.desc fun n ↦ Sigma.ι F.obj n ≫ p) = p :=
    Sigma.hom_ext _ _ fun n ↦ by simp
  rw [hp]
  exact hT

/-- Coprojections exhibiting a derived colimit, followed by an isomorphism `K ≅ K'`, exhibit `K'`
as a derived colimit. -/
theorem IsHomotopyColimitCocone.comp_iso {F : ℕ ⥤ D} [HasCoproduct F.obj] {K K' : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitCocone F c) (e : K ≅ K') :
    IsHomotopyColimitCocone F fun n ↦ c n ≫ e.hom := by
  obtain ⟨q, hT⟩ := h
  refine ⟨e.inv ≫ q, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) ?_ (by simp))⟩
  refine Sigma.hom_ext _ _ fun n ↦ ?_
  simp

/-- Coprojections exhibiting a derived colimit of `F` exhibit, through an isomorphism of systems
`F' ≅ F`, a derived colimit of `F'`. -/
theorem IsHomotopyColimitCocone.of_iso {F F' : ℕ ⥤ D} [HasCoproduct F.obj] [HasCoproduct F'.obj]
    {K : D} {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitCocone F c) (e : F' ≅ F) :
    IsHomotopyColimitCocone F' fun n ↦ e.hom.app n ≫ c n := by
  obtain ⟨q, hT⟩ := h
  let s : ∐ F'.obj ≅ ∐ F.obj :=
    { hom := Sigma.desc fun n ↦ e.hom.app n ≫ Sigma.ι F.obj n
      inv := Sigma.desc fun n ↦ e.inv.app n ≫ Sigma.ι F'.obj n
      hom_inv_id := Sigma.hom_ext _ _ fun n ↦ by simp
      inv_hom_id := Sigma.hom_ext _ _ fun n ↦ by simp }
  refine ⟨q ≫ (shiftFunctor D (1 : ℤ)).map s.inv, isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ s s (Iso.refl _) ?_ ?_ ?_)⟩
  · refine Sigma.hom_ext _ _ fun n ↦ ?_
    have hn := e.hom.naturality (homOfLE (Nat.le_succ n))
    simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, s, Sigma.ι_desc_assoc,
      Sigma.ι_desc, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub]
    rw [reassoc_of% hn]
  · refine Sigma.hom_ext _ _ fun n ↦ ?_
    simp [s]
  · simp only [Triangle.mk_obj₃, Triangle.mk_obj₁, Triangle.mk_mor₃, Iso.refl_hom,
      Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- A triangulated functor `G` preserving the direct sum of the system carries coprojections
exhibiting a derived colimit to coprojections exhibiting a derived colimit. -/
theorem IsHomotopyColimitCocone.map {F : ℕ ⥤ D} [HasCoproduct F.obj] {K : D}
    {c : ∀ n, F.obj n ⟶ K} (h : IsHomotopyColimitCocone F c) (G : D ⥤ E) [G.CommShift ℤ]
    [G.IsTriangulated] [HasCoproduct (F ⋙ G).obj] [PreservesColimit (Discrete.functor F.obj) G] :
    IsHomotopyColimitCocone (F ⋙ G) fun n ↦ G.map (c n) := by
  have : HasCoproduct fun n ↦ G.obj (F.obj n) := ‹HasCoproduct (F ⋙ G).obj›
  obtain ⟨q, hT⟩ := h
  set e := asIso (sigmaComparison G F.obj)
  have hδ : ((G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
        (shiftFunctor E (1 : ℤ)).map e.inv) ≫ (shiftFunctor E (1 : ℤ)).map e.hom =
      𝟙 (G.obj K) ≫ G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj) := by
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    simp
  have hc : (Sigma.desc fun n ↦ G.map (c n)) ≫ 𝟙 (G.obj K) = e.hom ≫ G.map (Sigma.desc c) := by
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    simp [e]
  refine ⟨(G.map q ≫ (G.commShiftIso (1 : ℤ)).hom.app (∐ F.obj)) ≫
      (shiftFunctor E (1 : ℤ)).map e.inv, ?_⟩
  exact isomorphic_distinguished _ (G.map_distinguished _ hT) _
    (Triangle.isoMk _ _ e e (Iso.refl _) (desc_oneSub_comp_sigmaComparison F G) hc hδ)

end Map

end CategoryTheory.Pretriangulated

end
