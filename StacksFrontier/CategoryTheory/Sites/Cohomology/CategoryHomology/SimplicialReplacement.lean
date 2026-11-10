module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import StacksCore.Tactic.StacksAttribute

/-!
# The simplicial replacement of a presheaf on a category

Let `C` be a small category and `F` an abelian-group-valued presheaf on `C`. The *simplicial
replacement* of `F` is the simplicial abelian group whose group in degree `n` is
`⨁_{Uₙ → ⋯ → U₀} F(U₀)`,
the sum being over the strings of `n` composable arrows of `C`, and whose simplicial
operators act by reindexing the string and restricting the coefficient along the canonical
arrow from the new right endpoint to the old one. Its alternating face map complex is the
complex `K_•(F)` of Stacks 08PG, which computes the homology of `C` with coefficients in `F`.

## Main definitions

* `Stacks.CategoryHomology.simplexIndexMap`: the functor `Fin (A.len + 1) ⥤ Fin (B.len + 1)`
  attached to a morphism `A ⟶ B` of `Δ`.
* `Stacks.CategoryHomology.replacementGroup`: the degree-`n` group `⨁_x F(x.right)`.
* `Stacks.CategoryHomology.replacementMap`: the map induced by a morphism of simplices.
* `Stacks.CategoryHomology.simplicialReplacement`: the simplicial abelian group assembled
  from these.
* `Stacks.CategoryHomology.simplicialReplacementComplex`: its alternating face map chain
  complex, the complex `K_•(F)`.

## Main results

* `Stacks.CategoryHomology.replacementMap_on_generator`: the value of `replacementMap` on a
  generator of the direct sum. This is the computation rule everything else goes through.
* `Stacks.CategoryHomology.replacementMap_laws`: the maps `replacementMap` respect identities
  and composition, which is what makes `simplicialReplacement` a simplicial object.

## Implementation notes

Strings `Uₙ → ⋯ → U₀` are represented as `ComposableArrows`, ordered from left to right, so
that the right endpoint `x.right` is the object `U₀` carrying the coefficient. Under a
simplicial operator the coefficient is restricted along the canonical arrow from the new
right endpoint to the old one; consequently the last face is precisely the restriction face
appearing in the source.

Both simplicial identities are proved by evaluating on a generator. The point that makes this
painless is that the reindexing is *definitionally* functorial: `simplexIndexMap (𝟙 A)` is the
identity functor and `simplexIndexMap (a ≫ b)` is the composite, each by `rfl`, and
`whiskerLeft` of an identity or of a composite is likewise `rfl`. So the two generators being
compared always carry the *same* index, and only the coefficients have to be identified. For
the identity law that identification is `x.map_id` after `Subsingleton.elim` in the preorder
category `Fin (n + 1)`; for the composition law it is `x.map_comp` together with
`Functor.map_comp` for `F`, again after `Subsingleton.elim`. No transport of a summand along
an equality of indices is needed.

Tag 08PG is split over four modules of this section, this one carrying the clause
`simplicial_replacement_complex`. The others are `SimplicialReplacementDeltaFunctor.lean`
(that `F ↦ H_n(K_•(F))` is a δ-functor), `RepresentableReplacementAsANerve.lean` (that
`K_•(j_{U!}ℤ_U)` is the free chain complex on the nerve of `C/U`) and
`RepresentableAcyclicity.lean` (that it is consequently acyclic in negative degrees, so `K_•`
computes the left derived functors of `colim`).

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped DirectSum Simplicial

universe u v

namespace Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C]

/-- The functor on index categories attached to a morphism of simplices: a morphism
`f : A ⟶ B` of `Δ` is a monotone map `{0, …, A.len} → {0, …, B.len}`, hence a functor of the
associated preorder categories. -/
abbrev simplexIndexMap {A B : SimplexCategory} (f : A ⟶ B) :
    Fin (A.len + 1) ⥤ Fin (B.len + 1) :=
  (SimplexCategory.toCat.map f).toFunctor

/-- The direct sum attached to the strings of `n` composable arrows in `C`. -/
abbrev replacementGroup (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ) :=
  AddCommGrpCat.of (⨁ x : ComposableArrows C n, F.obj (op x.right))

/-- The map on replacement groups associated to a morphism of simplices: the summand indexed
by a string `x` is sent to the summand indexed by the reindexed string, after restricting the
coefficient along the arrow of `x` from the new right endpoint to the old one. -/
noncomputable def replacementMap (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ) :
    replacementGroup F Δ.unop.len ⟶ replacementGroup F Γ.unop.len := by
  classical
  exact AddCommGrpCat.ofHom <| DirectSum.toAddMonoid fun x =>
      (DirectSum.of
        (fun y : ComposableArrows C Γ.unop.len => F.obj (op y.right))
        (x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor)).comp
      (F.map (op (x.map (homOfLE (Fin.le_last _))))).hom

/-- The value of `replacementMap` on the generator of the summand indexed by `x`. -/
lemma replacementMap_on_generator (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ)
    (x : ComposableArrows C Δ.unop.len) (s : F.obj (op x.right)) :
    replacementMap F f ((@DirectSum.of (ComposableArrows C Δ.unop.len)
      (fun z => F.obj (op z.right)) _ (Classical.decEq _) x) s) =
      (@DirectSum.of (ComposableArrows C Γ.unop.len)
        (fun z => F.obj (op z.right)) _ (Classical.decEq _))
        (x.whiskerLeft (simplexIndexMap f.unop))
        ((F.map (op (x.map (homOfLE (Fin.le_last _))))) s) := by
  simp [replacementMap, DirectSum.toAddMonoid_of, simplexIndexMap]
  rfl

/-- Functoriality of a presheaf, in the elementwise form used below: restricting along a
composite is restricting twice. This is `CategoryTheory.op_comp` followed by
`CategoryTheory.Functor.map_comp`; it is stated separately only because the morphisms below
are written with `Opposite.op` rather than `Quiver.Hom.op`, so neither lemma applies to them
by `rw` without this `change`. -/
private lemma map_op_comp_apply (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (s : F.obj (op Z)) :
    (F.map (op (a ≫ b))) s = (F.map (op a)) ((F.map (op b)) s) := by
  change (F.map ((a ≫ b).op)) s = (F.map a.op) ((F.map b.op) s)
  rw [CategoryTheory.op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Two homomorphisms out of a replacement group agree if they agree on all generators. -/
private lemma replacementGroup_hom_ext {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {n : ℕ}
    {G : AddCommGrpCat.{max u v}} {a b : replacementGroup F n ⟶ G}
    (h : ∀ (x : ComposableArrows C n) (s : F.obj (op x.right)),
      a ((@DirectSum.of (ComposableArrows C n) (fun z => F.obj (op z.right)) _
        (Classical.decEq _) x) s) =
      b ((@DirectSum.of (ComposableArrows C n) (fun z => F.obj (op z.right)) _
        (Classical.decEq _) x) s)) : a = b := by
  classical
  exact AddCommGrpCat.hom_ext (DirectSum.addHom_ext' fun x => AddMonoidHom.ext fun s => h x s)

/-- The maps defining the simplicial replacement respect identities and composition. -/
theorem replacementMap_laws (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (∀ Δ : SimplexCategoryᵒᵖ,
      replacementMap F (𝟙 Δ) = 𝟙 (replacementGroup F Δ.unop.len)) ∧
    (∀ {Δ Γ Θ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ) (g : Γ ⟶ Θ),
      replacementMap F (f ≫ g) = replacementMap F f ≫ replacementMap F g) := by
  classical
  constructor
  · intro Δ
    refine replacementGroup_hom_ext fun x s => ?_
    rw [replacementMap_on_generator]
    have hmap : F.map (op (x.map (homOfLE (Fin.le_last (Fin.last Δ.unop.len))))) =
        𝟙 (F.obj (op x.right)) := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 (Fin.last Δ.unop.len)), x.map_id]
      exact F.map_id _
    exact congrArg (DirectSum.of _ x) (congrArg (fun φ => φ s) hmap)
  · intro Δ Γ Θ f g
    refine replacementGroup_hom_ext fun x s => ?_
    simp only [ConcreteCategory.comp_apply]
    rw [replacementMap_on_generator F (f ≫ g) x s, replacementMap_on_generator F f x s]
    refine (congrArg _ ?_).trans
      (replacementMap_on_generator F g (x.whiskerLeft (simplexIndexMap f.unop)) _).symm
    refine Eq.trans ?_ (map_op_comp_apply F (x.map _) (x.map _) s)
    exact congrArg (fun φ => F.map (op φ) s) (x.map_comp _ _)

/-- The simplicial abelian group underlying the simplicial replacement. -/
@[implicit_reducible]
noncomputable def simplicialReplacement (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    SimplicialObject AddCommGrpCat.{max u v} where
  obj Δ := replacementGroup F Δ.unop.len
  map f := replacementMap F f
  map_id := (replacementMap_laws F).1
  map_comp := (replacementMap_laws F).2

/-- **Stacks 08PG, the simplicial replacement complex.** The chain complex whose degree-`n`
term is `⊕_(Uₙ → ⋯ → U₀) F(U₀)` and whose differential is the alternating sum of the face
maps. -/
@[stacks 08PG "simplicial_replacement_complex"]
noncomputable abbrev simplicialReplacementComplex
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : ChainComplex AddCommGrpCat.{max u v} ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (simplicialReplacement F)

end Stacks.CategoryHomology
