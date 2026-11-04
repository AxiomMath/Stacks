module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative Čech complex of an abelian presheaf

Let `p : X ⥤ C` be a structure functor and `f : U ⥤ X` a functor over it. The degree `n`
piece of the relative Čech nerve of `f` is the category of `n + 1` objects of `U` sitting
over a common object of `X`, each equipped with a comparison isomorphism lying over an
identity of `C`. For a morphism of categories fibred in groupoids over the fppf site this
reproduces the usual relative Čech nerve. Reindexing along maps of finite linear orders
makes these categories into a simplicial diagram, strictly, and pushing an abelian presheaf
on `X` forward along the resulting projections produces a cosimplicial abelian presheaf
whose degree `n` term is the pushforward of the pullback of the given presheaf. Its
alternating-coface complex is the relative Čech complex.

## Main definitions

* `Stacks.RelativeCech.Tuple`: the category of tuples indexing the relative Čech nerve.
* `Stacks.RelativeCech.term`: the degree `n` term of the cosimplicial abelian presheaf.
* `Stacks.RelativeCech.cosimplicial`: the cosimplicial abelian presheaf itself.
* `Stacks.RelativeCech.complex`: the relative Čech complex.

## Main results

* `Stacks.RelativeCech.complex_X`: the degrees of the complex are the terms above.
* `Stacks.RelativeCech.complex_d`: its differential is the alternating sum of the coface
  pullback maps.

## Implementation notes

The tuple model remembers the common target object together with the comparison isomorphisms,
the latter required to lie over identity morphisms of `C`; the structure functor on the source
is taken to be `f ⋙ p`. Reindexing is then strict, so no coherence data is needed to build
the cosimplicial object. Pushforward of presheaves is realised as a right Kan extension, and
the coface and codegeneracy maps are obtained from its counit, equivalently from the
adjunction-unit pullback maps.

The universe `w` of coefficients is independent of the universes of the two fibred categories;
it is only required to be large enough for the right Kan extensions to exist, which is why the
abelian groups live in `max uU uX vX w`.

## References

* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
-/

@[expose] public section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace Stacks.RelativeCech

universe vU vX vC uU uX uC w

variable {U : Type uU} {X : Type uX} {C : Type uC}
    [Category.{vU} U] [Category.{vX} X] [Category.{vC} C]
    (p : X ⥤ C) (f : U ⥤ X)

/-- An indexed tuple of objects of `U` lying over a common object of `X`, with comparison
isomorphisms whose images in `C` are identities. These tuples index the degree `n` piece of
the relative Čech nerve of `f` over `p`. -/
public structure Tuple (n : ℕ) where
  /-- The common object of `X` the tuple lies over. -/
  target : X
  /-- The `n + 1` objects of `U` making up the tuple. -/
  source : Fin (n + 1) → U
  /-- The comparison isomorphism identifying the image of each entry with the target. -/
  comparison : ∀ i, f.obj (source i) ≅ target
  /-- Each comparison isomorphism lies over an identity of `C`. -/
  comparison_lift : ∀ i, p.IsHomLift (𝟙 (p.obj target)) (comparison i).hom

namespace Tuple

/-- A morphism of tuples: a morphism of targets and a morphism of each entry, compatible with
the comparison isomorphisms. -/
public structure Hom {n : ℕ} (a b : Tuple p f n) where
  /-- The morphism of common targets. -/
  target : a.target ⟶ b.target
  /-- The morphism of entries. -/
  source : ∀ i, a.source i ⟶ b.source i
  /-- Compatibility of the entrywise morphisms with the comparison isomorphisms. -/
  comparison_naturality : ∀ i,
    f.map (source i) ≫ (b.comparison i).hom =
      (a.comparison i).hom ≫ target

/-- The identity morphism of a tuple. -/
public def homId {n : ℕ} (a : Tuple p f n) : Hom p f a a where
  target := 𝟙 _
  source := fun _ => 𝟙 _
  comparison_naturality := by simp

/-- Composition of morphisms of tuples, formed targetwise and entrywise. -/
public def homComp {n : ℕ} {a b c : Tuple p f n}
    (g : Hom p f a b) (h : Hom p f b c) : Hom p f a c where
  target := g.target ≫ h.target
  source := fun i => g.source i ≫ h.source i
  comparison_naturality := by
    intro i
    rw [Functor.map_comp, Category.assoc, h.comparison_naturality,
      ← Category.assoc, g.comparison_naturality, Category.assoc]

/-- Tuples of a fixed length form a category under targetwise and entrywise composition. -/
public instance instCategory (n : ℕ) : Category (Tuple p f n) where
  Hom := Hom p f
  id := homId p f
  comp := homComp p f
  id_comp := by intro _ _ g; cases g; simp [homId, homComp]
  comp_id := by intro _ _ g; cases g; simp [homId, homComp]
  assoc := by intro _ _ _ _ g h k; cases g; cases h; cases k; simp [homComp, Category.assoc]

/-- The functor sending a tuple to the object of `X` it lies over. -/
@[implicit_reducible] public def projection (n : ℕ) : Tuple p f n ⥤ X where
  obj a := a.target
  map g := g.target
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Reindexing of tuples along a map of finite index sets. It is strict: it changes neither
the common target nor the comparison data. -/
@[implicit_reducible] public def reindex {m n : ℕ} (φ : Fin (m + 1) → Fin (n + 1)) :
    Tuple p f n ⥤ Tuple p f m where
  obj a := ⟨a.target, fun i => a.source (φ i), fun i => a.comparison (φ i),
    fun i => a.comparison_lift (φ i)⟩
  map g := ⟨g.target, fun i => g.source (φ i), fun i => g.comparison_naturality (φ i)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Tuple

/-- Reindexing commutes strictly with the projection to `X`. -/
public theorem projection_reindex {m n : ℕ} (φ : Fin (m + 1) → Fin (n + 1)) :
    Tuple.reindex p f φ ⋙ Tuple.projection p f m = Tuple.projection p f n := rfl

/-- Degree `n` of the cosimplicial abelian presheaf underlying the relative Čech complex: the
pushforward along the projection of the pullback of `F`, realised as a right Kan extension. -/
@[implicit_reducible] public noncomputable def term
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) (n : ℕ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w} :=
  ((Tuple.projection p f n).op).ran.obj ((Tuple.projection p f n).op ⋙ F)

/-- Pullback along a simplicial reindexing map, obtained from the counit of the right Kan
extension. -/
@[implicit_reducible] public noncomputable def reindexMap
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    term p f F m ⟶ term p f F n :=
  let pm := Tuple.projection p f m
  let pn := Tuple.projection p f n
  let h := Tuple.reindex p f φ.toOrderHom
  ((pn.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv _ _)
    (by
      let c := pm.op.ranCounit.app (pm.op ⋙ F)
      change (h.op ⋙ pm.op) ⋙ term p f F m ⟶ (h.op ⋙ pm.op) ⋙ F
      simpa [term, pm, Functor.assoc] using (Functor.whiskerLeft h.op c))

/-- The defining factorisation of `reindexMap` through the Kan-extension counit. -/
public theorem reindexMap_fac (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w})
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    Functor.whiskerLeft (Tuple.projection p f n).op (reindexMap p f F φ) ≫
      ((Tuple.projection p f n).op.ranCounit.app ((Tuple.projection p f n).op ⋙ F)) =
    Functor.whiskerLeft (Tuple.reindex p f φ.toOrderHom).op
      ((Tuple.projection p f m).op.ranCounit.app ((Tuple.projection p f m).op ⋙ F)) := by
  let q := Tuple.projection p f n
  let β : q.op ⋙ term p f F m ⟶ q.op ⋙ F := Functor.whiskerLeft
    (Tuple.reindex p f φ.toOrderHom).op
    ((Tuple.projection p f m).op.ranCounit.app ((Tuple.projection p f m).op ⋙ F))
  show (((q.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv _ _).symm
    (((q.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv _ _) β)) = β
  simp

/-- The cosimplicial abelian presheaf of the relative Čech construction. -/
@[implicit_reducible] public noncomputable def cosimplicial
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) :
    CosimplicialObject (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) where
  obj n := term p f F n.len
  map φ := reindexMap p f F φ
  map_id := by
    intro n
    let q := Tuple.projection p f n.len
    let A := term p f F n.len
    let G := q.op ⋙ F
    change ((q.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv A G)
      (Functor.whiskerLeft
        (Tuple.reindex p f (OrderHom.id : Fin (n.len + 1) →o Fin (n.len + 1))).op
        (q.op.ranCounit.app G)) = 𝟙 A
    have hh : Functor.whiskerLeft
        (Tuple.reindex p f (OrderHom.id : Fin (n.len + 1) →o Fin (n.len + 1))).op
        (q.op.ranCounit.app G) = q.op.ranCounit.app G := by
      ext x
      rfl
    rw [hh]
    apply (Equiv.eq_symm_apply
      ((q.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv A G)).mp
    simpa [A, G, term, Functor.ranAdjunction_counit] using
      ((q.op.ranAdjunction AddCommGrpCat.{max uU uX vX w}).homEquiv_symm_id G).symm
  map_comp := by
    intro n m k φ ψ
    let q := Tuple.projection p f k.len
    let G := q.op ⋙ F
    apply (q.op.ran.obj G).hom_ext_of_isRightKanExtension (q.op.ranCounit.app G)
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    rw [reindexMap_fac p f F (φ ≫ ψ)]
    rw [reindexMap_fac p f F ψ]
    apply NatTrans.ext
    funext x
    have hf := congr_app (reindexMap_fac p f F φ)
      ((Tuple.reindex p f ψ.toOrderHom).op.obj x)
    simpa [Functor.whiskerLeft_app, NatTrans.comp_app,
      SimplexCategory.comp_toOrderHom, q, Tuple.reindex,
      Tuple.projection, Functor.comp_obj, OrderHom.comp] using hf.symm

/-- **Stacks 06X8.** The relative Čech complex of an abelian presheaf for a functor over a
base category: the alternating-coface complex of the relative Čech cosimplicial presheaf. -/
@[implicit_reducible, stacks 06X8 "presheaf_relative_cech_complex"]
public noncomputable def complex (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) :
    CochainComplex (Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) ℕ :=
  (alternatingCofaceMapComplex _).obj (cosimplicial p f F)

/-- The degree `n` term of the relative Čech complex is the `n`-th relative Čech term. -/
@[simp] public theorem complex_X (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) (n : ℕ) :
    (complex p f F).X n = term p f F n := rfl

/-- The differential of the relative Čech complex is the alternating sum of the coface
pullback maps. -/
public theorem complex_d (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX w}) (n : ℕ) :
    (complex p f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • reindexMap p f F (SimplexCategory.δ i) := by
  simp [complex, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
    AlternatingCofaceMapComplex.objD, CosimplicialObject.δ, cosimplicial]

end Stacks.RelativeCech

end
