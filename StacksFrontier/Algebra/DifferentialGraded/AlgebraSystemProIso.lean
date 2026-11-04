module

public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory

/-!
# Pro-isomorphisms of inverse systems of differential graded algebras

Let `ι` be a preordered type, viewed as a category, and let `(A_i)` and `(B_i)` be inverse systems
of differential graded `R`-algebras indexed by `ι`, that is functors `ιᵒᵖ ⥤ DGA(R)`. A morphism of
pro-objects `(A_i) → (B_i)` is represented by a monotone reindexing `m : ι → ι` together with
homomorphisms `A_{m(i)} → B_i` compatible with the transition maps, which is a functor
`F : ι ⥤ ι` together with a natural transformation `F.op ⋙ A ⟶ B`. Section 24.35 of the Stacks
Project uses such representatives throughout, and calls `(A_i)` and `(B_i)` *pro-isomorphic*
when there are representatives in both directions whose two composites are transition maps, as
in Remark 0GZ5, Lemma 0GZH and the proof of Proposition 0GZK.

## Main definitions

* `DifferentialGradedAlgebra.SystemProIso`: two inverse systems of differential graded algebras
  with mutually inverse representatives of morphisms of pro-objects between them.
* `DifferentialGradedAlgebra.SystemProIso.symm`: the same read in the other direction.
* `DifferentialGradedAlgebra.SystemProIso.trans`: the composite of two pro-isomorphisms.

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type w} [Preorder ι]

/-- **A pro-isomorphism of inverse systems of differential graded algebras.** Monotone
reindexings `F₁` and `F₂`, representatives `hom : A_{F₁ i} → B_i` and `inv : B_{F₂ i} → A_i` of
morphisms of pro-objects in the two directions, and the two composites
`A_{F₁ F₂ i} → B_{F₂ i} → A_i` and `B_{F₂ F₁ i} → A_{F₁ i} → B_i` equal to transition maps. -/
structure SystemProIso (A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R) where
  /-- The reindexing of the morphism `(A_i) → (B_i)`. -/
  F₁ : ι ⥤ ι
  /-- The reindexing of the morphism `(B_i) → (A_i)`. -/
  F₂ : ι ⥤ ι
  /-- The representative `A_{F₁ i} → B_i` of the morphism `(A_i) → (B_i)`. -/
  hom : F₁.op ⋙ A ⟶ B
  /-- The representative `B_{F₂ i} → A_i` of the morphism `(B_i) → (A_i)`. -/
  inv : F₂.op ⋙ B ⟶ A
  /-- The reindexing of the round trip of `(A_i)` is cofinal. -/
  le₁ : ∀ i : ι, i ≤ F₁.obj (F₂.obj i)
  /-- The reindexing of the round trip of `(B_i)` is cofinal. -/
  le₂ : ∀ i : ι, i ≤ F₂.obj (F₁.obj i)
  /-- The round trip of `(A_i)` is the transition map `A_{F₁ F₂ i} → A_i`. -/
  hom_inv : ∀ i : ι, hom.app (op (F₂.obj i)) ≫ inv.app (op i) = A.map (homOfLE (le₁ i)).op
  /-- The round trip of `(B_i)` is the transition map `B_{F₂ F₁ i} → B_i`. -/
  inv_hom : ∀ i : ι, inv.app (op (F₁.obj i)) ≫ hom.app (op i) = B.map (homOfLE (le₂ i)).op

namespace SystemProIso

variable {A B C : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- A pro-isomorphism read in the other direction. -/
@[simps]
def symm (e : SystemProIso A B) : SystemProIso B A where
  F₁ := e.F₂
  F₂ := e.F₁
  hom := e.inv
  inv := e.hom
  le₁ := e.le₂
  le₂ := e.le₁
  hom_inv := e.inv_hom
  inv_hom := e.hom_inv

/-- The composite of two pro-isomorphisms: the reindexings compose, and the representatives are
`A_{F₁ F₁' i} → B_{F₁' i} → C_i` and `C_{F₂' F₂ i} → B_{F₂ i} → A_i`. -/
def trans (e : SystemProIso A B) (e' : SystemProIso B C) : SystemProIso A C where
  F₁ := e'.F₁ ⋙ e.F₁
  F₂ := e.F₂ ⋙ e'.F₂
  hom := Functor.whiskerLeft e'.F₁.op e.hom ≫ e'.hom
  inv := Functor.whiskerLeft e.F₂.op e'.inv ≫ e.inv
  le₁ := fun i => (e.le₁ i).trans (leOfHom (e.F₁.map (homOfLE (e'.le₁ (e.F₂.obj i)))))
  le₂ := fun i => (e'.le₂ i).trans (leOfHom (e'.F₂.map (homOfLE (e.le₂ (e'.F₁.obj i)))))
  hom_inv := fun i => by
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc, Functor.comp_obj,
      Functor.op_obj]
    rw [← Category.assoc (e'.hom.app _), e'.hom_inv]
    have hnat := e.hom.naturality (homOfLE (e'.le₁ (e.F₂.obj i))).op
    simp only [Functor.comp_map, Functor.op_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, e.hom_inv, ← Functor.map_comp]
    rfl
  inv_hom := fun i => by
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc, Functor.comp_obj,
      Functor.op_obj]
    rw [← Category.assoc (e.inv.app _), e.inv_hom]
    have hnat := e'.inv.naturality (homOfLE (e.le₂ (e'.F₁.obj i))).op
    simp only [Functor.comp_map, Functor.op_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, e'.inv_hom, ← Functor.map_comp]
    rfl

end SystemProIso

end DifferentialGradedAlgebra
