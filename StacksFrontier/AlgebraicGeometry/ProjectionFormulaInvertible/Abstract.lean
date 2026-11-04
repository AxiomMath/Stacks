module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaMap.Basic

/-!
# The abstract projection formula: invertibility from an invertible tensor factor

`CategoryTheory.adjunctionTensorMap` is the abstract form of the morphism of
[Stacks, Tag 0FZE]: for an adjunction `L ⊣ R`, bifunctors `A` on `C` and `B` on `D` and an
oplax comparison `α : A ⋙ L ⟶ L.prod L ⋙ B`, it is the map

`A (R G, H) ⟶ R (B (G, L H))`.

This file proves it is an isomorphism as soon as three conditions hold, none of which mentions
`G`: the comparison `α` is invertible in its first argument at `H`, tensoring on the right by
`H` is an equivalence of `C`, and tensoring on the right by `L H` is an equivalence of `D`.

## Main definitions

* `Stacks.ProjectionFormula.tensorRightOf`: tensoring on the right by a fixed object in a
  bifunctor, `M ↦ A (M, H)`.

## Main results

* `Stacks.ProjectionFormula.isIso_adjunctionTensorMap`: **the abstract projection formula.**

## The route

No monoidal coherence is used, and no inverse object is constructed: the whole proof is the
single identity `Stacks.ProjectionFormula.adjunctionTensorMap_homEquiv`, which is already
available, read as a statement about hom-sets.

Write `E` for `tensorRightOf A H` and `E'` for `tensorRightOf B (L H)`, and `θ` for the map in
question. That identity says exactly that for `s : T ⟶ R G`,

`E s ≫ θ = adj.homEquiv (α_{(T, H)} ≫ E' (adj.homEquiv.symm s))`,

so `s ↦ E s ≫ θ` is a composite of four bijections: the adjunction bijection, the action of
`E'` on a hom-set (`E'` is fully faithful), composition with the invertible `α_{(T, H)}`, and
the adjunction bijection again. Since `E` is fully faithful, `s ↦ E s` is itself a bijection
onto `Hom (E T, E (R G))`, so composition with `θ` is a bijection

`Hom (E T, E (R G)) ≅ Hom (E T, R (E' G))`

for every `T`. Taking `T = R G` gives injectivity of composition with `θ` where it is needed,
and `E` essentially surjective turns `R (E' G)` into some `E T₀`, which gives a section. The
two halves assemble into the inverse.

This is the mate of `α` under `CategoryTheory.Adjunction.mateEquiv`, and Mathlib's docstring
there warns that the mate of an isomorphism need not be one. What rescues the argument is
precisely that the two *vertical* functors `E` and `E'` are equivalences; the Yoneda form above
uses that directly and never needs the mates correspondence.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

universe u₁ v₁ u₂ v₂

section TensorRight

variable {C : Type u₁} [Category.{v₁} C]

/-- **Tensoring on the right by a fixed object** in a bifunctor `A : C × C ⥤ C`: the
endofunctor `M ↦ A (M, H)`, acting on morphisms by `g ↦ A (g ⊗ 𝟙_H)`. -/
def tensorRightOf (A : C × C ⥤ C) (H : C) : C ⥤ C where
  obj M := A.obj (M, H)
  map g := A.map (g ×ₘ 𝟙 H)
  map_id M := by simp
  map_comp g g' := by
    rw [← A.map_comp]
    congr 1
    exact Prod.ext rfl (by simp)

/-- The functor `tensorRightOf A H` sends an object `M` to `A.obj (M, H)`. -/
@[simp]
lemma tensorRightOf_obj (A : C × C ⥤ C) (H M : C) :
    (tensorRightOf A H).obj M = A.obj (M, H) := rfl

/-- The functor `tensorRightOf A H` sends a morphism `g` to `A.map (g ×ₘ 𝟙 H)`. -/
@[simp]
lemma tensorRightOf_map (A : C × C ⥤ C) (H : C) {M N : C} (g : M ⟶ N) :
    (tensorRightOf A H).map g = A.map (g ×ₘ 𝟙 H) := rfl

end TensorRight

section Main

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Composition with an isomorphism on the left is a bijection of hom-sets. -/
lemma bijective_comp_isIso {X Y Z : C} (g : X ⟶ Y) [IsIso g] :
    Function.Bijective (fun w : Y ⟶ Z => g ≫ w) :=
  ⟨fun _ _ h => (cancel_epi g).1 h, fun w => ⟨inv g ≫ w, by simp⟩⟩

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **Composition with the abstract projection formula map is a bijection on hom-sets out of
the image of `tensorRightOf A H`.** This is
`Stacks.ProjectionFormula.adjunctionTensorMap_homEquiv` read as a factorisation of
`s ↦ (tensorRightOf A H).map s ≫ adjunctionTensorMap …` into four bijections: the adjunction
bijection, the action of `tensorRightOf B (L H)` on a hom-set, composition with the invertible
comparison, and the adjunction bijection again. -/
lemma bijective_comp_adjunctionTensorMap (G : D) (H T : C)
    [(tensorRightOf B (L.obj H)).Full] [(tensorRightOf B (L.obj H)).Faithful]
    [IsIso (α.app (T, H))] :
    Function.Bijective (fun s : T ⟶ R.obj G =>
      (tensorRightOf A H).map s ≫ adjunctionTensorMap adj A B α G H) := by
  have hrw : (fun s : T ⟶ R.obj G =>
        (tensorRightOf A H).map s ≫ adjunctionTensorMap adj A B α G H) =
      (adj.homEquiv ((tensorRightOf A H).obj T) ((tensorRightOf B (L.obj H)).obj G)) ∘
        (fun w : (tensorRightOf B (L.obj H)).obj (L.obj T) ⟶
            (tensorRightOf B (L.obj H)).obj G => α.app (T, H) ≫ w) ∘
        (fun v : L.obj T ⟶ G => (tensorRightOf B (L.obj H)).map v) ∘
        (adj.homEquiv T G).symm := by
    funext s
    have h := adjunctionTensorMap_homEquiv adj A B α T H G ((adj.homEquiv T G).symm s)
    rw [Equiv.apply_symm_apply] at h
    exact h
  rw [hrw]
  refine (adj.homEquiv _ _).bijective.comp (Function.Bijective.comp ?_ ?_)
  · exact bijective_comp_isIso (α.app (T, H))
  · exact (Function.Bijective.comp
      ⟨(tensorRightOf B (L.obj H)).map_injective, (tensorRightOf B (L.obj H)).map_surjective⟩
      (adj.homEquiv T G).symm.bijective)

/-- **The abstract projection formula.** If the oplax comparison `α` is invertible in its first
argument at `H`, and tensoring on the right by `H`, respectively by `L H`, is an equivalence,
then the abstract projection formula map `A (R G, H) ⟶ R (B (G, L H))` is an isomorphism, for
every `G`.

In the intended application `A` and `B` are the tensor products of sheaves of modules on two
ringed spaces, `L ⊣ R` is `f^* ⊣ f_*`, invertibility of `α` is [Stacks, Tag 01CD], and the two
equivalence hypotheses say that `H` and `f^* H` are invertible modules. -/
theorem isIso_adjunctionTensorMap (G : D) (H : C)
    [(tensorRightOf A H).IsEquivalence] [(tensorRightOf B (L.obj H)).IsEquivalence]
    (hα : ∀ M : C, IsIso (α.app (M, H))) :
    IsIso (adjunctionTensorMap adj A B α G H) := by
  have key : ∀ T : C, Function.Bijective (fun s : T ⟶ R.obj G =>
      A.map (s ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α G H) := fun T =>
    @bijective_comp_adjunctionTensorMap _ _ _ _ _ _ adj A B α G H T _ _ (hα T)
  -- Composition with the map is injective on endomorphisms of its source: every one of those
  -- is the image of an endomorphism of `R G`, because tensoring by `H` is full.
  have inj : ∀ t₁ t₂ : A.obj (R.obj G, H) ⟶ A.obj (R.obj G, H),
      t₁ ≫ adjunctionTensorMap adj A B α G H =
        t₂ ≫ adjunctionTensorMap adj A B α G H → t₁ = t₂ := by
    intro t₁ t₂ h
    obtain ⟨u₁, rfl⟩ := (tensorRightOf A H).map_surjective t₁
    obtain ⟨u₂, rfl⟩ := (tensorRightOf A H).map_surjective t₂
    exact congrArg (tensorRightOf A H).map ((key (R.obj G)).injective h)
  -- Tensoring by `H` is essentially surjective, so the target is one of its values; and
  -- surjectivity of composition with the map there produces a section.
  obtain ⟨P, i, s, hs⟩ : ∃ (P : C) (i : A.obj (P, H) ≅ R.obj (B.obj (G, L.obj H)))
      (s : P ⟶ R.obj G),
      A.map (s ×ₘ 𝟙 H) ≫ adjunctionTensorMap adj A B α G H = i.hom := by
    refine ⟨(tensorRightOf A H).objPreimage (R.obj (B.obj (G, L.obj H))),
      (tensorRightOf A H).objObjPreimageIso (R.obj (B.obj (G, L.obj H))), ?_⟩
    exact (key ((tensorRightOf A H).objPreimage
      (R.obj (B.obj (G, L.obj H))))).surjective
      ((tensorRightOf A H).objObjPreimageIso (R.obj (B.obj (G, L.obj H)))).hom
  have hsect : (i.inv ≫ A.map (s ×ₘ 𝟙 H)) ≫ adjunctionTensorMap adj A B α G H = 𝟙 _ := by
    rw [Category.assoc, hs, Iso.inv_hom_id]
  refine ⟨i.inv ≫ A.map (s ×ₘ 𝟙 H), inj _ _ ?_, hsect⟩
  rw [Category.assoc, hsect, Category.comp_id, Category.id_comp]

end Main

end Stacks.ProjectionFormula

end
