module

public import StacksFrontier.AlgebraicGeometry.InternalHomCokernel.Basic

/-!
# Internal Hom in the first variable is contravariant and additive, and splits a biproduct

Let `O` be a presheaf of commutative rings on a category `C`.  Precomposition in the first
variable of the internal Hom of [Stacks, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM),
`Stacks.PresheafOfModules.InternalHom.internalHomMapLeft`, is a contravariant additive functor
in that variable.  Consequently it carries a finite biproduct to a finite biproduct:

`Hom_O(⨁ i, M i, G) ≅ ⨁ i, Hom_O(M i, G)`.

Together with `Hom_O(O, G) ≅ G` of
`StacksFrontier/AlgebraicGeometry/InternalHomCokernel/Unit.lean` this computes the dual of a
finite free module, which is the identification that lets a dualized finite presentation
`𝒪_U^{⊕ m} ⟶ 𝒪_U^{⊕ n} ⟶ F|_U ⟶ 0` be read as the kernel of a map between finite free modules,
as assertion (1) of [Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ) states it.

## Main definitions

* `internalHomBiproductIso`: the splitting above.

## Main results

* `internalHomMapLeft_id`: precomposition with an identity is the identity.
* `internalHomMapLeft_zero`, `internalHomMapLeft_add`, `internalHomMapLeft_sum`: additivity.

## Implementation notes

`Stacks.PresheafOfModules.InternalHom.internalHomFunctor` already packages precomposition as a
functor into the opposite category, which is the shape in which Tag 03EN's first-variable
statement is proved.  The lemmas here are the same functoriality written for
`internalHomMapLeft` itself, without the passage to the opposite category, because that is the
form the biproduct computation and the kernel comparison of
`StacksFrontier/AlgebraicGeometry/InternalHomCokernel/Basic.lean` use.  No opposite-category
cocone translation is needed anywhere.

The sections of `internalHom O F G` over `V` are the morphisms `F|_V ⟶ G|_V` definitionally, but
a variable of the section type is not *syntactically* of that morphism type, so each
section-level computation is isolated as a lemma whose morphism argument carries the morphism
type (`restrFun_map_id_comp` and the three beside it) and then applied.  That is what keeps
`rw` inside closed patterns; no transparency option is used.

Biproducts are taken over an index type in `Type` with a `Fintype` instance, matching
`CategoryTheory.Limits.HasFiniteBiproducts`, and existence of the biproducts is an instance
argument: presheaves of modules have finite products, and
`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` turns that into finite
biproducts, but it is a theorem rather than an instance in Mathlib, so it is supplied at the
use site.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.PresheafOfModules.InternalHom

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat)
variable {F F' F'' G : PresheafOfModules.{max u v} (Oforget O)}

/-! ### Restriction to a slice is additive -/

/-- Restriction to a slice is additive on morphisms. -/
public theorem restrFun_map_add (V : C) (f f' : F ⟶ F') :
    (restrFun O V).map (f + f') = (restrFun O V).map f + (restrFun O V).map f' := by
  ext W
  rfl

/-! ### The section-level computations

Each of these is the computation that a section of the internal Hom undergoes, stated for an
argument that carries the morphism type rather than the section type. -/

/-- Precomposing with the restriction of an identity changes nothing. -/
public theorem restrFun_map_id_comp (V : C)
    (g : (restrFun O V).obj F ⟶ (restrFun O V).obj G) :
    (restrFun O V).map (𝟙 F) ≫ g = g := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Precomposing with the restriction of a composite is precomposing twice. -/
public theorem restrFun_map_comp_comp (f : F ⟶ F') (f' : F' ⟶ F'') (V : C)
    (g : (restrFun O V).obj F'' ⟶ (restrFun O V).obj G) :
    (restrFun O V).map (f ≫ f') ≫ g
      = (restrFun O V).map f ≫ ((restrFun O V).map f' ≫ g) := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Precomposition with the restriction of a sum of two morphisms is additive. -/
public theorem restrFun_map_add_comp (f f' : F ⟶ F') (V : C)
    (g : (restrFun O V).obj F' ⟶ (restrFun O V).obj G) :
    (restrFun O V).map (f + f') ≫ g
      = (restrFun O V).map f ≫ g + (restrFun O V).map f' ≫ g := by
  rw [restrFun_map_add, Preadditive.add_comp]

/-- Precomposition with the restriction of the zero morphism is zero. -/
public theorem restrFun_map_zero_comp (V : C)
    (g : (restrFun O V).obj F' ⟶ (restrFun O V).obj G) :
    (restrFun O V).map (0 : F ⟶ F') ≫ g = 0 := by
  rw [restrFun_map_zero, Limits.zero_comp]

/-! ### Contravariant functoriality and additivity -/

/-- Precomposition with an identity is the identity. -/
@[simp] public theorem internalHomMapLeft_id :
    internalHomMapLeft O (G := G) (𝟙 F) = 𝟙 (internalHom O F G) := by
  ext V g
  exact restrFun_map_id_comp O V.unop g

/-- Precomposition is additive in the morphism. -/
public theorem internalHomMapLeft_add (f f' : F ⟶ F') :
    internalHomMapLeft O (G := G) (f + f')
      = internalHomMapLeft O f + internalHomMapLeft O f' := by
  ext V g
  exact restrFun_map_add_comp O f f' V.unop g

/-- Precomposition with the zero morphism is zero. -/
@[simp] public theorem internalHomMapLeft_zero :
    internalHomMapLeft O (G := G) (0 : F ⟶ F') = 0 := by
  ext V g
  exact restrFun_map_zero_comp O V.unop g

/-- Precomposition takes a finite sum of morphisms to the sum of the precompositions. -/
public theorem internalHomMapLeft_sum {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ F')) :
    internalHomMapLeft O (G := G) (∑ i ∈ s, f i)
      = ∑ i ∈ s, internalHomMapLeft O (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, internalHomMapLeft_add, ih]

/-! ### Internal Hom splits a finite biproduct in the first variable -/

variable [HasFiniteBiproducts (PresheafOfModules.{max u v} (Oforget O))]
variable {I : Type} [DecidableEq I] [Fintype I]

/-- **Internal Hom carries a finite biproduct in the first variable to a finite biproduct**:
`Hom_O(⨁ i, M i, G) ≅ ⨁ i, Hom_O(M i, G)`.  The two morphisms are assembled from
precomposition with the injections and with the projections of the biproduct, and that they are
mutually inverse is the two biproduct identities together with additivity and contravariant
functoriality of precomposition. -/
public noncomputable def internalHomBiproductIso (M : I → PresheafOfModules.{max u v} (Oforget O))
    (G : PresheafOfModules.{max u v} (Oforget O)) :
    internalHom O (⨁ M) G ≅ ⨁ (fun i => internalHom O (M i) G) where
  hom := biproduct.lift (fun i => internalHomMapLeft O (G := G) (biproduct.ι M i))
  inv := biproduct.desc (fun i => internalHomMapLeft O (G := G) (biproduct.π M i))
  hom_inv_id := by
    have h := biproduct.total (f := fun i => internalHom O (M i) G)
    have hstep : ∑ i : I, internalHomMapLeft O (G := G) (biproduct.ι M i)
          ≫ internalHomMapLeft O (G := G) (biproduct.π M i)
        = internalHomMapLeft O (G := G) (∑ i : I, biproduct.π M i ≫ biproduct.ι M i) := by
      rw [internalHomMapLeft_sum]
      exact Finset.sum_congr rfl (fun i _ => internalHomMapLeft_comp O _ _)
    calc biproduct.lift (fun i => internalHomMapLeft O (G := G) (biproduct.ι M i))
          ≫ biproduct.desc (fun i => internalHomMapLeft O (G := G) (biproduct.π M i))
        = biproduct.lift (fun i => internalHomMapLeft O (G := G) (biproduct.ι M i))
          ≫ (∑ i : I, biproduct.π (fun i => internalHom O (M i) G) i
              ≫ biproduct.ι (fun i => internalHom O (M i) G) i)
          ≫ biproduct.desc (fun i => internalHomMapLeft O (G := G) (biproduct.π M i)) := by
          rw [h, Category.id_comp]
      _ = ∑ i : I, internalHomMapLeft O (G := G) (biproduct.ι M i)
              ≫ internalHomMapLeft O (G := G) (biproduct.π M i) := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Category.assoc, ← Category.assoc, biproduct.lift_π, biproduct.ι_desc]
      _ = 𝟙 _ := by rw [hstep, biproduct.total, internalHomMapLeft_id]
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ (fun j => ?_)
    refine biproduct.hom_ext _ _ (fun k => ?_)
    simp only [Category.assoc, biproduct.ι_desc_assoc, biproduct.lift_π, Category.comp_id]
    rw [internalHomMapLeft_comp]
    by_cases hjk : j = k
    · subst hjk
      rw [biproduct.ι_π_self, biproduct.ι_π_self, internalHomMapLeft_id]
    · rw [biproduct.ι_π_ne _ (Ne.symm hjk), biproduct.ι_π_ne _ hjk, internalHomMapLeft_zero]

end Stacks.PresheafOfModules.InternalHom

end
