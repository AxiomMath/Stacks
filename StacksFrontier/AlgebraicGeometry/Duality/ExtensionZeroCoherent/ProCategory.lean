module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DiagonalRepresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of pro-objects with countable index

Stacks 05PX gives the morphisms `lim_j colim_i Mor(F_i, G_j)` of two pro-systems of a category
`𝒟` but declines to construct the category `Pro-𝒟`. This file constructs it for the systems that
occur in the duality chapter, those indexed by the natural numbers. A pro-object is used through
its functor of points `A(L) = colim_n Mor(M_n, L)`, which is `CategoryTheory.Pro.coyonedaColim`,
and `Pro-𝒟` is the opposite of the full subcategory of `𝒟 ⥤ Type v` spanned by the functors of
that shape. Stacks 0G2X identifies the morphisms of this category with the morphisms of
pro-systems above, so what is built is the pro-category itself.

An object `L` of `𝒟` is a pro-object through the constant inverse sequence at `L`, whose functor
of points is `Mor(L, -)`; morphisms of pro-objects into such a constant pro-object are, by the
co-Yoneda lemma, the elements of the functor of points at `L`.

## Main definitions

* `CategoryTheory.IsSequentialProObject`: the functors of points of the pro-objects with
  countable index.
* `CategoryTheory.ProSeq`: the category `Pro-𝒟`.
* `CategoryTheory.ProSeq.points`: the functor of points of a pro-object.
* `CategoryTheory.ProSeq.of`: the pro-object of an inverse sequence.
* `CategoryTheory.ProSeq.const`: an object of `𝒟` viewed as a constant pro-object.

## Main results

* `CategoryTheory.ProSeq.ofHomEquiv`: the morphisms of `Pro-𝒟` between the pro-objects of two
  inverse sequences are the morphisms of pro-systems of Stacks 05PX, through Stacks 0G2X.
* `CategoryTheory.ProSeq.homConstEquiv`: morphisms into the constant pro-object at `L` are the
  elements of the functor of points at `L`.

## Implementation notes

`CategoryTheory.Pro.coyonedaColim` needs an index category living in the morphism universe of
`𝒟`, so an inverse sequence is used through `CategoryTheory.Pro.liftedInverseSequence`, which
lifts `ℕᵒᵖ` to that universe. The opposite of the lifted index category is connected, being
equivalent to `ℕ`, and that is what identifies the functor of points of a constant inverse
sequence with a corepresentable functor.

## References

* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory

variable (𝒟 : Type u) [Category.{v} 𝒟]

/-- The functors of points of the pro-objects of `𝒟` with countable index: those `A : 𝒟 ⥤ Type v`
isomorphic to `colim_n Mor(M_n, -)` for an inverse sequence `M : ℕᵒᵖ ⥤ 𝒟`. -/
public def IsSequentialProObject : ObjectProperty (𝒟 ⥤ Type v) :=
  fun A => ∃ M : ℕᵒᵖ ⥤ 𝒟, Nonempty (A ≅ Pro.coyonedaColim (Pro.liftedInverseSequence M))

/-- The category `Pro-𝒟` of pro-objects of `𝒟` with countable index: the opposite of the full
subcategory of `𝒟 ⥤ Type v` spanned by the functors of points of inverse sequences. -/
@[sga "4 I 8.10" "special case"]
public abbrev ProSeq : Type (max u (v + 1)) := (IsSequentialProObject 𝒟).FullSubcategoryᵒᵖ

/-- The index category of a lifted inverse sequence has connected opposite: it is equivalent to
the filtered category `ℕ`. -/
public instance isConnected_liftedSequenceIndexOp :
    IsConnected ((ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ) :=
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have : IsConnected (ℕᵒᵖ) := isConnected_op
  have : IsConnected (ULiftHom.{v} (ULift.{v} ℕᵒᵖ)) :=
    isConnected_of_equivalent (ULiftHomULiftCategory.equiv ℕᵒᵖ)
  isConnected_op

variable {𝒟}

/-- A corepresentable functor `Mor(L, -)` is the functor of points of a pro-object, namely of the
constant inverse sequence at `L`. -/
public lemma isSequentialProObject_coyoneda (L : 𝒟) :
    IsSequentialProObject 𝒟 (coyoneda.obj (op L)) := by
  refine ⟨(Functor.const ℕᵒᵖ).obj L, ⟨?_⟩⟩
  have e : (Pro.liftedInverseSequence ((Functor.const ℕᵒᵖ).obj L)).op ⋙ coyoneda ≅
      (Functor.const _).obj (coyoneda.obj (op L)) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact coyoneda.map_id _)
  exact ((HasColimit.isoOfNatIso e).trans
    (colimit.isoColimitCocone ⟨constCocone _ _, isColimitConstCocone _ _⟩)).symm

namespace ProSeq

/-- The functor of points `L ↦ Mor_{Pro-𝒟}(P, L)` of a pro-object `P`. -/
public abbrev points (P : ProSeq 𝒟) : 𝒟 ⥤ Type v := P.unop.obj

/-- The pro-object of an inverse sequence `M : ℕᵒᵖ ⥤ 𝒟`, that is, its formal limit. -/
public def of (M : ℕᵒᵖ ⥤ 𝒟) : ProSeq 𝒟 :=
  op ⟨Pro.coyonedaColim (Pro.liftedInverseSequence M), M, ⟨Iso.refl _⟩⟩

/-- The functor of points of `ProSeq.of M` is `L ↦ colim_n Mor(M_n, L)`. -/
public lemma points_of (M : ℕᵒᵖ ⥤ 𝒟) :
    (of M).points = Pro.coyonedaColim (Pro.liftedInverseSequence M) :=
  rfl

/-- An object of `𝒟`, viewed as a constant pro-object; its functor of points is `Mor(L, -)`. -/
public def const : 𝒟 ⥤ ProSeq 𝒟 :=
  (ObjectProperty.lift (IsSequentialProObject 𝒟) coyoneda
    (fun L => isSequentialProObject_coyoneda L.unop)).rightOp

/-- The functor of points of the constant pro-object at `L` is `Mor(L, -)`. -/
public lemma points_const (L : 𝒟) : (const.obj L).points = coyoneda.obj (op L) := rfl

/-- **Stacks 0G2X** for the category of pro-objects: a morphism `ProSeq.of M ⟶ ProSeq.of N` is a
morphism of pro-systems from `M` to `N`, that is, an element of
`lim_m colim_n Mor(M_n, N_m)`. -/
public def ofHomEquiv (M N : ℕᵒᵖ ⥤ 𝒟) :
    (of M ⟶ of N) ≃
      Pro.Hom (Pro.liftedInverseSequence M) (Pro.liftedInverseSequence N) :=
  (opEquiv _ _).trans (InducedCategory.homEquiv.trans (Pro.homEquiv _ _))

/-- Morphisms of pro-objects from `P` into the constant pro-object at `L` are the elements of the
functor of points of `P` at `L`. This is the co-Yoneda lemma. -/
public def homConstEquiv (P : ProSeq 𝒟) (L : 𝒟) : (P ⟶ const.obj L) ≃ P.points.obj L :=
  (opEquiv _ _).trans (InducedCategory.homEquiv.trans coyonedaEquiv)

/-- The bijection `ProSeq.homConstEquiv` sends `f` to the element attached by the co-Yoneda lemma
to the transformation of functors of points underlying `f`. -/
public lemma homConstEquiv_apply (P : ProSeq 𝒟) (L : 𝒟) (f : P ⟶ const.obj L) :
    homConstEquiv P L f = coyonedaEquiv f.unop.hom :=
  rfl

end ProSeq

end CategoryTheory

end
