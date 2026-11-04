module

public import StacksFrontier.CategoryTheory.Limits.ProObject.Stages

/-!
# A ladder is a pro-isomorphism

`Stacks.ProObject.hasProLadder` extracts from an isomorphism of the pro-objects presented by two
`ℕᵒᵖ`-indexed inverse diagrams its *ladder*: two families of maps between the stages, compatible
with the transition maps and composing to transition maps, all after passing far enough along the
index. This file proves the converse, so that a ladder and an isomorphism of pro-objects are the
same thing, and collects the formal properties of ladders that follow.

## Main results

* `Stacks.ProObject.nonempty_colimitYonedaIso_of_hasProLadder` — **a ladder gives an isomorphism
  of the pro-objects**, presented as colimits of representables; with
  `Stacks.ProObject.hasProLadder` this makes the two notions equivalent
  (`Stacks.ProObject.hasProLadder_iff`).
* `Stacks.ProObject.HasProLadder.map` — a functor carries a ladder to a ladder.
* `Stacks.ProObject.HasProLadder.symm`, `Stacks.ProObject.HasProLadder.trans` — ladders are
  symmetric and compose.

## Implementation notes

The pro-object of `A : ℕᵒᵖ ⥤ C` is presented by `colimit (A.op ⋙ yoneda)` in the presheaf category
on `Cᵒᵖ`; its value at `op (op X)` is `colim_n (X ⟶ A_n)`. A family `f n : A_{p n} ⟶ B_n` gives the
morphism of presheaves whose component at the stage `n` of `B` is `yoneda.map (f n).op` followed by
the colimit injection at the stage `p n` of `A`; the ladder identities are exactly what makes these
components a cocone and the two morphisms mutually inverse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace Stacks.ProObject

variable {C : Type u} [Category.{v} C]

/-! ### Formal properties of ladders -/

/-- **A ladder is symmetric**: the two families of maps exchange their roles. -/
public theorem HasProLadder.symm {A B : ℕᵒᵖ ⥤ C} (h : HasProLadder A B) : HasProLadder B A := by
  obtain ⟨p, f, q, g, cf, cg, fg, gf⟩ := h
  exact ⟨q, g, p, f, cg, cf, gf, fg⟩

/-- **A functor carries a ladder to a ladder**: every identity of the ladder is an identity between
composites of maps of the diagrams, which the functor preserves. -/
public theorem HasProLadder.map {D : Type u'} [Category.{v'} D] (K : C ⥤ D) {A B : ℕᵒᵖ ⥤ C}
    (h : HasProLadder A B) : HasProLadder (A ⋙ K) (B ⋙ K) := by
  obtain ⟨p, f, q, g, cf, cg, fg, gf⟩ := h
  have lift {a b : ℕ} {X : ℕ → C} {Y : C} {u v : ∀ k, a ≤ k → b ≤ k → (X k ⟶ Y)}
      (H : ∃ k h₁ h₂, u k h₁ h₂ = v k h₁ h₂) :
      ∃ k h₁ h₂, K.map (u k h₁ h₂) = K.map (v k h₁ h₂) :=
    H.imp fun _ => .imp fun _ => .imp fun _ => congrArg K.map
  exact ⟨p, fun n => K.map (f n), q, fun n => K.map (g n),
    fun n m hnm => by simpa using lift (cf n m hnm),
    fun n m hnm => by simpa using lift (cg n m hnm),
    fun n => by simpa using lift (fg n), fun n => by simpa using lift (gf n)⟩

/-! ### From a ladder to an isomorphism of pro-objects -/

section ColimitYoneda

/-- The colimit injection at a later stage, precomposed with the transition map, is the colimit
injection at the earlier stage. -/
private theorem yoneda_map_invTransition_ι (A : ℕᵒᵖ ⥤ C) {j k : ℕ} (h : j ≤ k) :
    yoneda.map (invTransition A h).op ≫ colimit.ι (A.op ⋙ yoneda) (op (op k)) =
      colimit.ι (A.op ⋙ yoneda) (op (op j)) :=
  colimit.w (A.op ⋙ yoneda) (homOfLE h).op.op

/-- The cocone on the representables of the stages of `B` with vertex the pro-object of `A`,
whose component at the stage `n` is induced by `f n : A_{p n} ⟶ B_n`. -/
private def ladderCocone {A B : ℕᵒᵖ ⥤ C} (p : ℕ → ℕ) (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n))
    (cf : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm) :
    Cocone (B.op ⋙ yoneda) where
  pt := colimit (A.op ⋙ yoneda)
  ι :=
    { app := fun n => yoneda.map (f n.unop.unop).op ≫
        colimit.ι (A.op ⋙ yoneda) (op (op (p n.unop.unop)))
      naturality := fun i j φ => by
        have hij : i.unop.unop ≤ j.unop.unop := leOfHom φ.unop.unop
        have hφ : φ = (homOfLE hij).op.op := Subsingleton.elim _ _
        subst hφ
        obtain ⟨k, h₁, h₂, hk⟩ := cf i.unop.unop j.unop.unop hij
        change yoneda.map (invTransition B hij).op ≫ yoneda.map (f j.unop.unop).op ≫
            colimit.ι (A.op ⋙ yoneda) (op (op (p j.unop.unop))) =
          (yoneda.map (f i.unop.unop).op ≫
            colimit.ι (A.op ⋙ yoneda) (op (op (p i.unop.unop)))) ≫ 𝟙 _
        rw [Category.comp_id, ← yoneda_map_invTransition_ι A h₂,
          ← yoneda_map_invTransition_ι A h₁]
        have hk' := congrArg (fun t => yoneda.map t.op ≫ colimit.ι (A.op ⋙ yoneda) (op (op k))) hk
        simp only [op_comp, Functor.map_comp, Category.assoc] at hk' ⊢
        exact hk'.symm }

/-- The morphism of pro-objects induced by a family `f n : A_{p n} ⟶ B_n` compatible with the
transition maps. -/
private def ladderHom {A B : ℕᵒᵖ ⥤ C} (p : ℕ → ℕ) (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n))
    (cf : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm) :
    colimit (B.op ⋙ yoneda) ⟶ colimit (A.op ⋙ yoneda) :=
  colimit.desc _ (ladderCocone p f cf)

private theorem ι_ladderHom {A B : ℕᵒᵖ ⥤ C} (p : ℕ → ℕ)
    (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n))
    (cf : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm) (n : ℕ) :
    colimit.ι (B.op ⋙ yoneda) (op (op n)) ≫ ladderHom p f cf =
      yoneda.map (f n).op ≫ colimit.ι (A.op ⋙ yoneda) (op (op (p n))) :=
  colimit.ι_desc (ladderCocone p f cf) (op (op n))

/-- The two morphisms of pro-objects induced by the two halves of a ladder compose to the
identity, by the identity of the ladder saying that the composite is a transition map. -/
private theorem ladderHom_comp_ladderHom {A B : ℕᵒᵖ ⥤ C} (p : ℕ → ℕ)
    (f : ∀ n, A.obj (op (p n)) ⟶ B.obj (op n)) (q : ℕ → ℕ)
    (g : ∀ n, B.obj (op (q n)) ⟶ A.obj (op n))
    (cf : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : p n ≤ k) (h₂ : p m ≤ k),
      invTransition A h₁ ≫ f n = invTransition A h₂ ≫ f m ≫ invTransition B hnm)
    (cg : ∀ n m : ℕ, ∀ hnm : n ≤ m, ∃ (k : ℕ) (h₁ : q n ≤ k) (h₂ : q m ≤ k),
      invTransition B h₁ ≫ g n = invTransition B h₂ ≫ g m ≫ invTransition A hnm)
    (gf : ∀ n : ℕ, ∃ (k : ℕ) (h₁ : q (p n) ≤ k) (h₂ : n ≤ k),
      invTransition B h₁ ≫ g (p n) ≫ f n = invTransition B h₂) :
    ladderHom p f cf ≫ ladderHom q g cg = 𝟙 _ := by
  refine colimit.hom_ext fun j => ?_
  obtain ⟨k, h₁, h₂, hk⟩ := gf j.unop.unop
  show colimit.ι (B.op ⋙ yoneda) (op (op j.unop.unop)) ≫ _ = _ ≫ 𝟙 _
  rw [← Category.assoc, ι_ladderHom, Category.assoc, ι_ladderHom, Category.comp_id,
    ← yoneda_map_invTransition_ι B h₁, ← yoneda_map_invTransition_ι B h₂, ← Category.assoc,
    ← yoneda.map_comp, ← Category.assoc, ← yoneda.map_comp, ← op_comp, ← op_comp, ← hk]

/-- **A ladder gives an isomorphism of pro-objects.** The two families of maps of a ladder induce
mutually inverse morphisms between the pro-objects presented by the two diagrams. This is the
converse of `Stacks.ProObject.hasProLadder`. -/
public theorem nonempty_colimitYonedaIso_of_hasProLadder {A B : ℕᵒᵖ ⥤ C}
    (h : HasProLadder A B) :
    Nonempty (colimit (A.op ⋙ yoneda) ≅ colimit (B.op ⋙ yoneda)) := by
  obtain ⟨p, f, q, g, cf, cg, fg, gf⟩ := h
  exact ⟨⟨ladderHom q g cg, ladderHom p f cf, ladderHom_comp_ladderHom q g p f cg cf fg,
    ladderHom_comp_ladderHom p f q g cf cg gf⟩⟩

/-- **A ladder is the same as an isomorphism of pro-objects**, for `ℕᵒᵖ`-indexed diagrams. -/
public theorem hasProLadder_iff (A B : ℕᵒᵖ ⥤ C) :
    HasProLadder A B ↔ Nonempty (colimit (A.op ⋙ yoneda) ≅ colimit (B.op ⋙ yoneda)) :=
  ⟨nonempty_colimitYonedaIso_of_hasProLadder, fun ⟨e⟩ => hasProLadder A B e⟩

/-- **Ladders compose**: the isomorphisms of pro-objects they give compose. -/
public theorem HasProLadder.trans {A B D : ℕᵒᵖ ⥤ C} (h₁ : HasProLadder A B)
    (h₂ : HasProLadder B D) : HasProLadder A D := by
  obtain ⟨e₁⟩ := nonempty_colimitYonedaIso_of_hasProLadder h₁
  obtain ⟨e₂⟩ := nonempty_colimitYonedaIso_of_hasProLadder h₂
  exact hasProLadder A D (e₁ ≪≫ e₂)

end ColimitYoneda

end Stacks.ProObject

end
