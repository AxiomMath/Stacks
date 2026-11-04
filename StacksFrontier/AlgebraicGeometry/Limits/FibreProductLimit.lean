module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of schemes commute with fibre products

Let `α : A ⟶ C` and `β : B ⟶ C` be natural transformations between diagrams of schemes indexed
by the same category, and let `A`, `B`, `C` have limits with vertices `A'`, `B'`, `C'` and
morphisms `α' : A' ⟶ C'`, `β' : B' ⟶ C'` compatible with the legs. Then the diagram of fibre
products `i ↦ A i ×_{C i} B i` has limit `A' ×_{C'} B'`.

This is the interchange of two limits, written out for the shape of a fibre product so that the
cone is the evident one: the leg at `i` is `CategoryTheory.Limits.pullback.map` of the three
legs. Nothing is assumed of the index category — no cofilteredness, no smallness.

## Main definitions

* `AlgebraicGeometry.FibreProductLimit.diagram`: the diagram `i ↦ A i ×_{C i} B i`.
* `AlgebraicGeometry.FibreProductLimit.cone`: the cone on it with vertex `A' ×_{C'} B'`.

## Main results

* `AlgebraicGeometry.FibreProductLimit.isLimit`: **that cone is a limit.**
* `AlgebraicGeometry.FibreProductLimit.isAffine_diagram_obj`: when every stage of the three
  diagrams is affine, so is every stage of the diagram of fibre products.

## Implementation notes

The two morphisms `α'` and `β'` are taken as data together with the two compatibility families,
rather than being produced from the limit property of the cone on `C`, so that no comparison
with a given pair of such morphisms is needed.

The functor `AlgebraicGeometry.FibreProductLimit.diagram` is marked `implicit_reducible`: its
value at `i` is a `pullback`, whose own unfolding stops at the unexposed
`CategoryTheory.Limits.getLimitCone`, so a goal composing a leg of a cone on this diagram with
`pullback.fst` is not type-correct at `implicit` transparency unless the functor itself unfolds
there.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace FibreProductLimit

variable {I : Type v} [Category.{w} I] {A B C : I ⥤ Scheme.{u}} (α : A ⟶ C) (β : B ⟶ C)

section Diagram

/-- **The diagram of fibre products** of two natural transformations with common target. -/
@[simps obj, implicit_reducible]
def diagram : I ⥤ Scheme.{u} where
  obj i := pullback (α.app i) (β.app i)
  map {i j} e :=
    pullback.map _ _ _ _ (A.map e) (B.map e) (C.map e) (α.naturality e).symm (β.naturality e).symm
  map_id i := by
    simp only [CategoryTheory.Functor.map_id]
    exact pullback.map_id
  map_comp {i j k} e e' := by
    simp only [CategoryTheory.Functor.map_comp]
    exact (pullback.map_comp _ _ _ _ _ _ _ _ _ _).symm

/-- The transition map of the diagram of fibre products, followed by the first projection, is
the first projection followed by the transition map of `A`. -/
@[reassoc (attr := simp)]
lemma diagram_map_fst {i j : I} (e : i ⟶ j) :
    (diagram α β).map e ≫ pullback.fst (α.app j) (β.app j) =
      pullback.fst (α.app i) (β.app i) ≫ A.map e :=
  pullback.lift_fst _ _ _

/-- The transition map of the diagram of fibre products, followed by the second projection, is
the second projection followed by the transition map of `B`. -/
@[reassoc (attr := simp)]
lemma diagram_map_snd {i j : I} (e : i ⟶ j) :
    (diagram α β).map e ≫ pullback.snd (α.app j) (β.app j) =
      pullback.snd (α.app i) (β.app i) ≫ B.map e :=
  pullback.lift_snd _ _ _

/-- The fibre product of two affine schemes over an affine scheme is affine. -/
instance isAffine_diagram_obj [∀ i, IsAffine (A.obj i)] [∀ i, IsAffine (B.obj i)]
    [∀ i, IsAffine (C.obj i)] (i : I) : IsAffine ((diagram α β).obj i) :=
  inferInstanceAs (IsAffine (pullback (α.app i) (β.app i)))

end Diagram

section Cone

variable {cA : Cone A} {cB : Cone B} {cC : Cone C}
  (α' : cA.pt ⟶ cC.pt) (β' : cB.pt ⟶ cC.pt)
  (hα : ∀ i, cA.π.app i ≫ α.app i = α' ≫ cC.π.app i)
  (hβ : ∀ i, cB.π.app i ≫ β.app i = β' ≫ cC.π.app i)

include hα hβ

/-- **The cone on the diagram of fibre products with vertex the fibre product of the limits.** -/
@[simps pt, implicit_reducible]
def cone : Cone (diagram α β) where
  pt := pullback α' β'
  π :=
    { app := fun i ↦
        pullback.map α' β' (α.app i) (β.app i) (cA.π.app i) (cB.π.app i) (cC.π.app i)
          (hα i).symm (hβ i).symm
      naturality := fun i j e ↦ by
        have hf : ∀ k : I, pullback.map α' β' (α.app k) (β.app k) (cA.π.app k) (cB.π.app k)
            (cC.π.app k) (hα k).symm (hβ k).symm ≫ pullback.fst (α.app k) (β.app k) =
            pullback.fst α' β' ≫ cA.π.app k := fun _ ↦ pullback.lift_fst _ _ _
        have hs : ∀ k : I, pullback.map α' β' (α.app k) (β.app k) (cA.π.app k) (cB.π.app k)
            (cC.π.app k) (hα k).symm (hβ k).symm ≫ pullback.snd (α.app k) (β.app k) =
            pullback.snd α' β' ≫ cB.π.app k := fun _ ↦ pullback.lift_snd _ _ _
        refine pullback.hom_ext ?_ ?_
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, diagram_map_fst, hf j, reassoc_of% hf i, cA.w e]
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, diagram_map_snd, hs j, reassoc_of% hs i, cB.w e] }

/-- The leg of `cone` at `i`, followed by the first projection, is the first projection of
`pullback α' β'` followed by the leg of `cA` at `i`. -/
@[reassoc (attr := simp)]
lemma cone_π_app_fst (i : I) :
    (cone α β α' β' hα hβ).π.app i ≫ pullback.fst (α.app i) (β.app i) =
      pullback.fst α' β' ≫ cA.π.app i :=
  pullback.lift_fst _ _ _

/-- The leg of `cone` at `i`, followed by the second projection, is the second projection of
`pullback α' β'` followed by the leg of `cB` at `i`. -/
@[reassoc (attr := simp)]
lemma cone_π_app_snd (i : I) :
    (cone α β α' β' hα hβ).π.app i ≫ pullback.snd (α.app i) (β.app i) =
      pullback.snd α' β' ≫ cB.π.app i :=
  pullback.lift_snd _ _ _

omit hα hβ

/-- The first components of the legs of a cone on the diagram of fibre products form a cone
on `A`. -/
@[simps, implicit_reducible]
def fstCone (s : Cone (diagram α β)) : Cone A where
  pt := s.pt
  π :=
    { app := fun i ↦ s.π.app i ≫ pullback.fst (α.app i) (β.app i)
      naturality := fun i j e ↦ by
        have h := s.π.naturality e
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h ⊢
        rw [Category.assoc, ← diagram_map_fst α β e, ← Category.assoc, ← h] }

/-- The second components of the legs of a cone on the diagram of fibre products form a cone
on `B`. -/
@[simps, implicit_reducible]
def sndCone (s : Cone (diagram α β)) : Cone B where
  pt := s.pt
  π :=
    { app := fun i ↦ s.π.app i ≫ pullback.snd (α.app i) (β.app i)
      naturality := fun i j e ↦ by
        have h := s.π.naturality e
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h ⊢
        rw [Category.assoc, ← diagram_map_snd α β e, ← Category.assoc, ← h] }

include hα hβ

/-- **A limit of schemes commutes with fibre products.** -/
def isLimit (hA : IsLimit cA) (hB : IsLimit cB) (hC : IsLimit cC) :
    IsLimit (cone α β α' β' hα hβ) where
  lift s := by
    refine pullback.lift (hA.lift (fstCone α β s)) (hB.lift (sndCone α β s)) (hC.hom_ext ?_)
    intro i
    rw [Category.assoc, Category.assoc, ← hα i, ← hβ i, ← Category.assoc, ← Category.assoc,
      hA.fac, hB.fac]
    simp only [fstCone_π_app, sndCone_π_app, Category.assoc, pullback.condition]
  fac s i := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, cone_π_app_fst, ← Category.assoc, pullback.lift_fst, hA.fac]
      rfl
    · rw [Category.assoc, cone_π_app_snd, ← Category.assoc, pullback.lift_snd, hB.fac]
      rfl
  uniq s m hm := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      refine hA.hom_ext fun i ↦ ?_
      rw [hA.fac, Category.assoc, ← cone_π_app_fst α β α' β' hα hβ i, ← Category.assoc, hm i]
      rfl
    · rw [pullback.lift_snd]
      refine hB.hom_ext fun i ↦ ?_
      rw [hB.fac, Category.assoc, ← cone_π_app_snd α β α' β' hα hβ i, ← Category.assoc, hm i]
      rfl

end Cone

end FibreProductLimit

end AlgebraicGeometry

end
