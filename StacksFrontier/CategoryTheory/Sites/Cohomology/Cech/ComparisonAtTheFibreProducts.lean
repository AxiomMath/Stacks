module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice

/-!
# A coefficient comparison invertible at the fibre products of a covering family

The Čech complex of a family `E = {U_i → X}` with coefficients in a presheaf `G` on the slice
at `X` reads `G` only at the iterated fibre products `U_{i_0} ×_X ⋯ ×_X U_{i_p}`: in degree `p`
it is the product of the values of `G` there, over all `(p + 1)`-tuples of indices.  So a
morphism of coefficient presheaves which is invertible *at those objects alone* already induces
an isomorphism of Čech complexes, and hence of Čech cohomology, with nothing required of it
anywhere else on the slice.

This is the comparison the geometry supplies.  A quasi-coherent module is identified with a
base change of its sections only over the *affine* objects of a site, and a general object of
the slice at an affine chart is not affine; but the iterated fibre products of a covering
family of an affine chart by affine charts are affine again.  Asking for the identification on
the whole slice would be asking for something false, while asking for it at the fibre products
is exactly what cartesianness gives.

## Main results

* `Stacks.CechSite.isIso_sliceCechComplexFunctor_map`: a coefficient morphism invertible at the
  iterated fibre products of the family induces an isomorphism of slice Čech complexes.
* `Stacks.CechSite.sliceCechComplexIsoOfIsoAtFibreProducts` and
  `Stacks.CechSite.sliceCechCohomologyIsoOfIsoAtFibreProducts`: the same as an isomorphism of
  complexes and of cohomology objects.
* `Stacks.CechSite.isZero_sliceCechCohomology_of_isoAtFibreProducts` and
  `Stacks.CechSite.isZero_cechCohomology_of_isoAtFibreProducts`: **the vanishing transport**, on
  the slice and on the ambient category.

## Implementation notes

The degreewise component of `(Stacks.CechSite.sliceCechComplexFunctor E).map α` is literally a
`CategoryTheory.Limits.Pi.map` of the components of `α` at the fibre products, so the proof is a
`change` onto that spelling followed by instance search: a `Pi.map` all of whose components are
isomorphisms is an isomorphism.  The `change` is needed because the Čech complex is assembled
through `CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor`, which does not display
the product in that form.

The comparison is stated for a morphism `α : G ⟶ G'` of presheaves on the slice and not for
bare degreewise isomorphisms.  That is not a weakening: the naturality of `α` in the slice is
what makes the squares of the Čech differentials commute, and without it the degreewise maps
need not assemble into a morphism of complexes at all.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

section Complex

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]

/-- **A coefficient morphism invertible at the iterated fibre products of the family induces an
isomorphism of slice Čech complexes.**  In degree `p` the induced map is the product, over the
`(p + 1)`-tuples of indices, of the components of `α` at the iterated fibre products, so
invertibility there is all that is needed. -/
theorem isIso_sliceCechComplexFunctor_map {G G' : (Over X)ᵒᵖ ⥤ A} (α : G ⟶ G')
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a))))))) :
    IsIso ((sliceCechComplexFunctor E).map α) := by
  have hdeg : ∀ n : ℕ, IsIso (((sliceCechComplexFunctor E).map α).f n) := by
    intro n
    have : ∀ i : Fin (n + 1) → E.I₀,
        IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))) := hα n
    change IsIso (CategoryTheory.Limits.Pi.map
      (f := fun i : Fin (n + 1) → E.I₀ ↦ G.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a))))))
      (g := fun i : Fin (n + 1) → E.I₀ ↦ G'.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a))))))
      (fun i ↦ α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))))
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The isomorphism of slice Čech complexes induced by a coefficient morphism invertible at
the iterated fibre products of the family.** -/
noncomputable def sliceCechComplexIsoOfIsoAtFibreProducts {G G' : (Over X)ᵒᵖ ⥤ A} (α : G ⟶ G')
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a))))))) :
    sliceCechComplex E G ≅ sliceCechComplex E G' :=
  have := isIso_sliceCechComplexFunctor_map E α hα
  asIso ((sliceCechComplexFunctor E).map α)

end Complex

section Cohomology

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]

/-- The isomorphism on slice Čech cohomology induced by a coefficient morphism invertible at the
iterated fibre products of the family. -/
noncomputable def sliceCechCohomologyIsoOfIsoAtFibreProducts {G G' : (Over X)ᵒᵖ ⥤ A}
    (α : G ⟶ G')
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))))
    (p : ℕ) :
    sliceCechCohomology E G p ≅ sliceCechCohomology E G' p :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (sliceCechComplexIsoOfIsoAtFibreProducts E α hα)

/-- **Vanishing of slice Čech cohomology transfers along a coefficient morphism invertible at
the iterated fibre products of the family.** -/
theorem isZero_sliceCechCohomology_of_isoAtFibreProducts {G G' : (Over X)ᵒᵖ ⥤ A} (α : G ⟶ G')
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))))
    (p : ℕ) (h : IsZero (sliceCechCohomology E G p)) :
    IsZero (sliceCechCohomology E G' p) :=
  h.of_iso (sliceCechCohomologyIsoOfIsoAtFibreProducts E α hα p).symm

/-- **Vanishing of Čech cohomology on the ambient category, from a coefficient morphism on the
slice invertible at the iterated fibre products of the family.**  This is the form the geometry
consumes: the coefficient presheaf `F` lives on the whole site, its restriction to the slice is
compared with an auxiliary presheaf `G` whose Čech cohomology is known to vanish, and the
comparison is asked only at the fibre products. -/
theorem isZero_cechCohomology_of_isoAtFibreProducts {G : (Over X)ᵒᵖ ⥤ A} {F : Cᵒᵖ ⥤ A}
    (α : G ⟶ (Over.forget X).op ⋙ F)
    (hα : ∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
      IsIso (α.app (op (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))))))
    (p : ℕ) (h : IsZero (sliceCechCohomology E G p)) :
    IsZero (cechCohomology E F p) :=
  isZero_sliceCechCohomology_of_isoAtFibreProducts E α hα p h

end Cohomology

end Stacks.CechSite

end
