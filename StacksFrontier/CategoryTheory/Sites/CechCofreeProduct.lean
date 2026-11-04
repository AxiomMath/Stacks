module

public import StacksFrontier.CategoryTheory.Sites.CechCofree

/-!
# The cofree presheaf on a family is the product of the cofree presheaves on its members

`Stacks.CategoryTheory.CechComplex.cofree obj val` is defined objectwise as a product of the
single-object cofree presheaves `cofreeOne (obj k) (val k)`; this file identifies it with the
categorical product of those presheaves in the presheaf category, and deduces the form of the
positive-degree Čech vanishing which is consumed in [Stacks, Tag 01EP]: a presheaf which splits
off a *product* of presheaves, each only *isomorphic* to a single-object cofree presheaf, has
vanishing positive-degree Čech cohomology.

That is the shape in which the vanishing is applied when the splitting is manufactured in
another category and transported, since a transported cofree presheaf is only isomorphic to a
cofree one, and since some of the factors of the transported product may be zero rather than
cofree.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.cofreeOuterProj obj val k` is the projection of
  `cofree obj val` onto `cofreeOne (obj k) (val k)`, as a morphism of presheaves, and
  `cofreeToPi obj val` is the induced morphism to the categorical product.
* `Stacks.CategoryTheory.CechComplex.piCofreeOneIso obj val` is the resulting isomorphism from
  the product of the single-object cofree presheaves to `cofree obj val`.

## Main results

* `Stacks.CategoryTheory.CechComplex.isZero_cofreeOne`: a single-object cofree presheaf with a
  zero value is zero.
* `Stacks.CategoryTheory.CechComplex.isIso_cofreeToPi`: `cofree obj val` *is* the product of the
  presheaves `cofreeOne (obj k) (val k)`.
* `Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract_of_pi`:
  **positive-degree Čech cohomology of a retract of a product of presheaves isomorphic to
  single-object cofree presheaves vanishes.**

## Implementation notes

That `cofreeToPi obj val` is an isomorphism is checked one object at a time, through the
observation that composing it with `CategoryTheory.Limits.piComparison` for the evaluation
functor gives the identity: the value of `cofree obj val` at an object is *definitionally* the
product of the values of the `cofreeOne (obj k) (val k)` with projections `cofreeOuterπ`, so
that composite is a product lift of the projections. No limit cone has to be exhibited and no
pointwise limit comparison has to be built by hand.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v v' u u'

namespace Stacks.CategoryTheory.CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {κ : Type t}

/-! ### Cofree presheaves with a zero value -/

/-- **A single-object cofree presheaf with a zero value is zero.** Its value at any object is a
product of copies of a zero object. -/
theorem isZero_cofreeOne [HasZeroMorphisms A] [HasProducts.{v} A] (V : C) (J : A)
    (hJ : IsZero J) : IsZero (cofreeOne V J) :=
  Functor.isZero _ fun T ↦ (IsZero.iff_id_eq_zero _).2
    (cofreeOne_obj_hom_ext (W := T.unop) V J fun _ ↦ hJ.eq_of_tgt _ _)

/-! ### The cofree presheaf on a family as a product -/

section Product

variable [HasProducts.{t} A] [HasProducts.{v} A] (obj : κ → C) (val : κ → A)

/-- The projection of `cofree obj val` onto the cofree presheaf on the single object `obj k`,
as a morphism of presheaves. -/
@[simps]
noncomputable def cofreeOuterProj (k : κ) : cofree obj val ⟶ cofreeOne (obj k) (val k) where
  app W := cofreeOuterπ obj val W k
  naturality _ _ f := cofree_map_comp_cofreeOuterπ obj val f k

/-- The canonical morphism from `cofree obj val` to the categorical product of the cofree
presheaves on the single objects `obj k`. It is an isomorphism, see `isIso_cofreeToPi`. -/
noncomputable def cofreeToPi : cofree obj val ⟶ ∏ᶜ fun k ↦ cofreeOne (obj k) (val k) :=
  Pi.lift (cofreeOuterProj obj val)

/-- Evaluating `cofreeToPi` at an object and composing with the product comparison of the
evaluation functor gives the identity: the value of `cofree obj val` at an object *is* the
product of the values of the single-object cofree presheaves. -/
theorem cofreeToPi_app_comp_piComparison (W : Cᵒᵖ) :
    ((CategoryTheory.evaluation Cᵒᵖ A).obj W).map (cofreeToPi obj val) ≫
        piComparison ((CategoryTheory.evaluation Cᵒᵖ A).obj W)
          (fun k ↦ cofreeOne (obj k) (val k)) =
      𝟙 _ :=
  Pi.hom_ext _ _ fun k ↦ by
    rw [Category.assoc, piComparison_comp_π, ← CategoryTheory.Functor.map_comp, cofreeToPi,
      Pi.lift_π]
    exact (Category.id_comp (cofreeOuterπ obj val W k)).symm

/-- **`cofree obj val` is the product of the cofree presheaves on the single objects `obj k`.** -/
instance isIso_cofreeToPi : IsIso (cofreeToPi obj val) := by
  have : ∀ W, IsIso ((cofreeToPi obj val).app W) := fun W ↦ by
    have : IsIso (((CategoryTheory.evaluation Cᵒᵖ A).obj W).map (cofreeToPi obj val) ≫
        piComparison ((CategoryTheory.evaluation Cᵒᵖ A).obj W)
          (fun k ↦ cofreeOne (obj k) (val k))) := by
      rw [cofreeToPi_app_comp_piComparison]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right
      (((CategoryTheory.evaluation Cᵒᵖ A).obj W).map (cofreeToPi obj val))
      (piComparison ((CategoryTheory.evaluation Cᵒᵖ A).obj W)
        fun k ↦ cofreeOne (obj k) (val k))
  exact NatIso.isIso_of_isIso_app _

/-- **The product of the cofree presheaves on the single objects `obj k` is
`cofree obj val`.** -/
noncomputable def piCofreeOneIso :
    (∏ᶜ fun k ↦ cofreeOne (obj k) (val k)) ≅ cofree obj val :=
  (asIso (cofreeToPi obj val)).symm

end Product

/-! ### Vanishing for a retract of a product -/

section Vanishing

variable [Abelian A] [HasProducts.{w} A] [HasFiniteProducts C] [HasProducts.{t} A]
  [HasProducts.{v} A] {ι : Type w} (U : ι → C) (obj : κ → C) (val : κ → A) (P : Cᵒᵖ ⥤ A)

/-- A product of presheaves each isomorphic to a cofree presheaf on a single object is
isomorphic to the cofree presheaf on the corresponding family. -/
noncomputable def piIsoCofree (Q : κ → (Cᵒᵖ ⥤ A)) (e : ∀ k, Q k ≅ cofreeOne (obj k) (val k)) :
    (∏ᶜ Q) ≅ cofree obj val :=
  Pi.mapIso e ≪≫ piCofreeOneIso obj val

/-- **Positive-degree Čech cohomology of a retract of a product of presheaves isomorphic to
single-object cofree presheaves vanishes.** The factors are only required to be *isomorphic* to
cofree presheaves, so that this applies to a product transported from another category, in which
some factors may have turned out to be zero rather than cofree; a zero presheaf is the cofree
presheaf on any object with a zero value, see `isZero_cofreeOne`. -/
theorem isZero_homology_cechComplex_of_retract_of_pi (Q : κ → (Cᵒᵖ ⥤ A))
    (e : ∀ k, Q k ≅ cofreeOne (obj k) (val k)) (s : P ⟶ ∏ᶜ Q) (r : (∏ᶜ Q) ⟶ P)
    (hsr : s ≫ r = 𝟙 P) (n : ℕ) (hn : 0 < n) :
    IsZero (((cechComplexFunctor U).obj P).homology n) :=
  isZero_homology_cechComplex_of_retract U obj P (s ≫ (piIsoCofree obj val Q e).hom)
    ((piIsoCofree obj val Q e).inv ≫ r)
    (by rw [Category.assoc, Iso.hom_inv_id_assoc, hsr]) n hn

end Vanishing

end Stacks.CategoryTheory.CechComplex

end
