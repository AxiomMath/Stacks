module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech complex is a functor of the covering

Stacks 03F4 attaches to a morphism of families of morphisms with fixed target a morphism of the
associated Čech complexes, in the opposite direction. This file proves that the assignment is
functorial: the identity morphism of families induces the identity of Čech complexes, and a
composite of morphisms of families induces the composite of the induced maps, in the opposite
order.

## Main definitions

* `Stacks.CechSite.cechProductMapSlice`: the map of iterated fibre products attached to a
  morphism of families, as a morphism of the slice category over the target of the refined
  family.

## Main results

* `Stacks.CechSite.cechProductMap_id` and `Stacks.CechSite.cechProductMap_comp`: the maps of
  iterated fibre products are functorial.
* `Stacks.CechSite.cechComplexMap_id` and `Stacks.CechSite.cechComplexMap_comp`: the induced
  maps of Čech complexes are functorial. Together they make the Čech complex a functor on the
  opposite of a category of families of morphisms with fixed target.

## Implementation notes

Over a general site these statements are computations, not formalities. A morphism of families
carries a *choice* of comparison morphisms `h₀ i : E.X i ⟶ G.X (s₀ i)`, and the induced map of
Čech complexes restricts along the map of iterated fibre products that those choices determine;
the Čech complex is functorial only because those maps of fibre products are, which has to be
checked against the product projections. Over a topological space it is free, since `Opens X` is
a partial order and all its parallel morphisms agree; that is the shortcut taken in
`Stacks.Cohomology.CechRefinement.refinementCochainMap_comp`, and it does not transfer to a
site.

The underlying morphism of `C` of a map of iterated fibre products is pinned down by
`Stacks.CechSite.hom_ext_of_pi_left`: the product projections of a slice category are jointly
monic on underlying morphisms *together with* the structure morphism of the product, since a
morphism of `C` with a prescribed composite to the base lifts to the slice. Phrasing the
extensionality this way avoids comparing the sources of the two maps, which for a composite of
morphisms of families lie in three different slice categories and would otherwise force a
transport along associativity.

## References

* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

universe t w w' w'' v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C]

section Slice

/-- Two morphisms of `C` into the underlying object of a product of a slice category over `T`
agree as soon as they agree after each projection and after the structure morphism of the
product. -/
theorem hom_ext_of_pi_left {T : C} {α : Type t} (Y : α → Over T) [HasProduct Y] {Z : C}
    {u v : Z ⟶ (∏ᶜ Y).left} (hhom : u ≫ (∏ᶜ Y).hom = v ≫ (∏ᶜ Y).hom)
    (hπ : ∀ a, u ≫ (Pi.π Y a).left = v ≫ (Pi.π Y a).left) : u = v :=
  congrArg Over.Hom.left
    (Pi.hom_ext (Over.homMk u rfl : Over.mk (u ≫ (∏ᶜ Y).hom) ⟶ ∏ᶜ Y)
      (Over.homMk v hhom.symm) fun a ↦ Over.OverMorphism.ext (hπ a))

variable {U V W : C}

/-- The map of iterated fibre products induced by a morphism of families, as a morphism of the
slice category over the target of the refined family. Its underlying morphism of `C` is
`Stacks.CechSite.cechProductMap`. -/
noncomputable def cechProductMapSlice (E : PreZeroHypercover.{w} U)
    (G : PreZeroHypercover.{w'} V) {f : U ⟶ V} (φ : E.HomOver G f) (n : ℕ)
    (i : Fin (n + 1) → E.I₀)
    [∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))] :
    Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f) ⟶
      ∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) :=
  Pi.lift (fun a ↦ (Over.homMk
    ((Pi.π (fun b ↦ Over.mk (E.f (i b))) a).left ≫ φ.h₀ (i a)) (by
      simp only [Over.mk_hom]
      rw [Category.assoc, φ.w₀, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w (Pi.π (fun b ↦ Over.mk (E.f (i b))) a))) :
      Over.mk ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).hom ≫ f) ⟶ Over.mk (G.f (φ.s₀ (i a)))))

variable (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V)
  (H : PreZeroHypercover.{w''} W)

/-- The underlying morphism of `cechProductMapSlice` is `cechProductMap`. -/
theorem cechProductMapSlice_left {f : U ⟶ V} (φ : E.HomOver G f) (n : ℕ)
    (i : Fin (n + 1) → E.I₀)
    [∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))] :
    (cechProductMapSlice E G φ n i).left = cechProductMap E G φ n i :=
  rfl

/-- The map of iterated fibre products induced by a morphism of families, composed with the
underlying morphism of a product projection, is the corresponding projection of the source
followed by the comparison morphism of the family. The two families may live in different
universes; `Stacks.CechSite.cechProductMap_comp_π_left` is the form for families in a single
universe. -/
theorem cechProductMap_comp_π_left_heterogeneous {f : U ⟶ V} (φ : E.HomOver G f) (n : ℕ)
    (i : Fin (n + 1) → E.I₀)
    [∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))]
    (b : Fin (n + 1)) :
    cechProductMap E G φ n i ≫ (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b) := by
  rw [← cechProductMapSlice_left, ← Over.comp_left]
  simp only [cechProductMapSlice, Pi.lift_comp_π, Over.homMk_left]

/-- The map of iterated fibre products induced by the identity morphism of a family is the
identity. -/
theorem cechProductMap_id (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))] :
    cechProductMap E E (PreZeroHypercover.HomOver.id E) n i = 𝟙 _ := by
  refine hom_ext_of_pi_left
    (fun a ↦ Over.mk (E.f ((PreZeroHypercover.HomOver.id E).s₀ (i a)))) ?_ fun a ↦ ?_
  · exact ((cechProductMap_comp_hom E E (PreZeroHypercover.HomOver.id E) n i).trans
      (Category.comp_id _)).trans (Category.id_comp _).symm
  · exact ((cechProductMap_comp_π_left_heterogeneous E E (PreZeroHypercover.HomOver.id E) n i
      a).trans (Category.comp_id _)).trans (Category.id_comp _).symm

/-- Two squares `a ≫ q = r ≫ s` and `b ≫ p = q ≫ t` paste to `(a ≫ b) ≫ p = r ≫ s ≫ t`. -/
private theorem comp_comp_eq {X Y Z P Q R : C} (a : X ⟶ Y) (b : Y ⟶ Z) (p : Z ⟶ P) (q : Y ⟶ Q)
    (r : X ⟶ R) (s : R ⟶ Q) (t : Q ⟶ P) (hb : b ≫ p = q ≫ t) (ha : a ≫ q = r ≫ s) :
    (a ≫ b) ≫ p = r ≫ s ≫ t := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]

/-- The maps of iterated fibre products induced by two composable morphisms of families compose
to the one induced by their composite. -/
theorem cechProductMap_comp {g : U ⟶ V} {h : V ⟶ W} {k : U ⟶ W} (φ : E.HomOver G g)
    (ψ : G.HomOver H h) (hk : g ≫ h = k) (n : ℕ) (i : Fin (n + 1) → E.I₀)
    [∀ j : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (j a)))]
    [∀ j : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (j a)))]
    [∀ j : Fin (n + 1) → H.I₀, HasProduct (fun a ↦ Over.mk (H.f (j a)))] :
    cechProductMap E G φ n i ≫ cechProductMap G H ψ n (φ.s₀ ∘ i) =
      cechProductMap E H (φ.comp ψ hk) n i := by
  subst hk
  refine hom_ext_of_pi_left
    (fun a ↦ Over.mk (H.f ((φ.comp ψ rfl).s₀ (i a)))) ?_ fun a ↦ ?_
  · exact (comp_comp_eq _ _ _ _ _ _ _ (cechProductMap_comp_hom G H ψ n (φ.s₀ ∘ i))
      (cechProductMap_comp_hom E G φ n i)).trans
      (cechProductMap_comp_hom E H (φ.comp ψ rfl) n i).symm
  · exact (comp_comp_eq _ _ _ _ _ _ _
      (cechProductMap_comp_π_left_heterogeneous G H ψ n (φ.s₀ ∘ i) a)
      (cechProductMap_comp_π_left_heterogeneous E G φ n i a)).trans
      (cechProductMap_comp_π_left_heterogeneous E H (φ.comp ψ rfl) n i a).symm

end Slice

section ComplexMap

variable {U V W : C} {A : Type u'} [Category.{v'} A] [Preadditive A]

-- The identity morphism of families sends an index to itself, and the Čech complex of the
-- source is therefore the Čech complex of the target only up to that unfolding; without it at
-- `implicit` transparency the identity of the degree-`n` iterated fibre product is not seen to
-- be a morphism between the two products the two sides name.
attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.HomOver.id
  cechFormalCoproduct
  CategoryTheory.Limits.FormalCoproduct.evalOp
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj in
/-- **Stacks 03F4**, functoriality: the identity morphism of a family of morphisms with fixed
target induces the identity of its Čech complex. -/
theorem cechComplexMap_id (E : PreZeroHypercover.{w} U) [HasProducts.{w} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (F : Cᵒᵖ ⥤ A) :
    cechComplexMap E E (PreZeroHypercover.HomOver.id E) F = 𝟙 (cechComplex E F) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply Pi.hom_ext
  intro i
  have hmap : F.map (cechProductMap E E (PreZeroHypercover.HomOver.id E) n i).op =
      𝟙 (F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) :=
    (congrArg F.map (congrArg Quiver.Hom.op (cechProductMap_id E n i))).trans
      (F.map_id (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)))
  refine (cechComplexMap_f_Pi_π E E (PreZeroHypercover.HomOver.id E) F n i).trans ?_
  rw [hmap]
  exact (Category.comp_id (Pi.π (fun j : Fin (n + 1) → E.I₀ ↦
      F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)))
      ((PreZeroHypercover.HomOver.id E).s₀ ∘ i))).trans
    (Category.id_comp (Pi.π (fun j : Fin (n + 1) → E.I₀ ↦
      F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (j a)))).left)))
      ((PreZeroHypercover.HomOver.id E).s₀ ∘ i))).symm

attribute [local implicit_reducible] cechFormalCoproduct
  CategoryTheory.Limits.FormalCoproduct.evalOp
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj in
/-- **Stacks 03F4**, functoriality: two composable morphisms of families of morphisms with fixed
target induce, in the opposite order, the map of Čech complexes of their composite. -/
theorem cechComplexMap_comp (E : PreZeroHypercover.{w} U) (G : PreZeroHypercover.{w'} V)
    (H : PreZeroHypercover.{w''} W) {g : U ⟶ V} {h : V ⟶ W} {k : U ⟶ W} (φ : E.HomOver G g)
    (ψ : G.HomOver H h) (hk : g ≫ h = k)
    [HasProducts.{w} A] [HasProducts.{w'} A] [HasProducts.{w''} A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → H.I₀), HasProduct (fun a ↦ Over.mk (H.f (i a)))]
    (F : Cᵒᵖ ⥤ A) :
    cechComplexMap G H ψ F ≫ cechComplexMap E G φ F = cechComplexMap E H (φ.comp ψ hk) F := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  apply Pi.hom_ext
  intro i
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z ↦ (cechComplexMap G H ψ F).f n ≫ z)
    (cechComplexMap_f_Pi_π E G φ F n i)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z ↦ z ≫ F.map (cechProductMap E G φ n i).op)
    (cechComplexMap_f_Pi_π G H ψ F n (φ.s₀ ∘ i))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  rw [← F.map_comp, ← op_comp, cechProductMap_comp E G H φ ψ hk n i]
  exact (cechComplexMap_f_Pi_π E H (φ.comp ψ hk) F n i).symm

end ComplexMap

end Stacks.CechSite
