module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily

/-!
# The Čech complex of a presheaf given only on the slice at the target

The Čech complex of a family `{U_i → X}` only ever evaluates the coefficient presheaf on the
iterated fibre products `U_{i_0} ×_X ⋯ ×_X U_{i_p}`, all of which are objects *over* `X`.  This
is visible in the construction: `Stacks.CechSite.cechComplexFunctor` is restriction along
`(CategoryTheory.Over.forget X).op` followed by
`CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor`.  So the complex is really a
functor of a presheaf on `(Over X)ᵒᵖ`, and this file names that functor and records the
identification.

The point is not economy but availability.  A presheaf may carry extra structure on the slice
at `X` that it cannot carry on the whole category — the associated module `Fᵃ` of
[Stacks, Tag 03DU] is a presheaf of modules over the *varying* coordinate rings, so on
`(Over X)ᵒᵖ` with `X` affine it is a presheaf of `Γ(X, 𝒪)`-modules, and nowhere else.  Every
comparison theorem about the Čech complex with module coefficients, [Stacks, Tag 03FJ] in
particular, is therefore applicable on the slice and not on the ambient category, and this file
is what carries the conclusion back.

## Main definitions

* `Stacks.CechSite.sliceCechCosimplicialObjectFunctor` and
  `Stacks.CechSite.sliceCechComplexFunctor`: the Čech cosimplicial object and the Čech complex
  of a family, as functors of a presheaf on the slice at the target.
* `Stacks.CechSite.sliceCechCosimplicialObject`, `Stacks.CechSite.sliceCechComplex` and
  `Stacks.CechSite.sliceCechCohomology`: the same, applied to one presheaf.
* `Stacks.CechSite.sliceCechComplexIsoOfCosimplicialIso`: a comparison of slice Čech complexes
  from a comparison of cosimplicial objects.

## Main results

* `Stacks.CechSite.cechComplexFunctor_eq_comp`,
  `Stacks.CechSite.cechComplex_eq_sliceCechComplex` and
  `Stacks.CechSite.cechCohomology_eq_sliceCechCohomology`: the Čech complex of a presheaf on
  the ambient category is the slice Čech complex of its restriction.  All three hold by
  definition.
* `Stacks.CechSite.cechComplexIsoSlice`: transport of the Čech complex along an identification
  of that restriction with a presheaf on the slice.
* `Stacks.CechSite.isZero_cechCohomology_of_isZero_slice`: **the slice-to-ambient transport for
  Čech vanishing.**

## Implementation notes

The identifications are `rfl`, so nothing here is a construction; what the file supplies is the
*vocabulary* in which a slice-only coefficient presheaf can be spoken about, together with the
functoriality that `cechComplexFunctor` hides inside a composite.  `sliceCechComplexFunctor` is
`CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor` at the Čech simplicial object of
the family, and is given a name of its own because the composite is what the ambient
`cechComplexFunctor` unfolds to and is otherwise invisible.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe w v v' u u'

namespace Stacks.CechSite

section Preadditive

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]

/-- The Čech cosimplicial object of a family, as a functor of a presheaf on the slice. -/
public abbrev sliceCechCosimplicialObjectFunctor :
    ((Over X)ᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  FormalCoproduct.cosimplicialObjectFunctor (cechSimplicialObject E)

/-- The Čech complex of a family, as a functor of a presheaf on the slice. -/
public abbrev sliceCechComplexFunctor : ((Over X)ᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  FormalCoproduct.cochainComplexFunctor (cechSimplicialObject E)

/-- The Čech cosimplicial object of a presheaf defined only on the slice at the target. -/
public abbrev sliceCechCosimplicialObject (G : (Over X)ᵒᵖ ⥤ A) : CosimplicialObject A :=
  (sliceCechCosimplicialObjectFunctor E).obj G

/-- The Čech complex of a presheaf defined only on the slice at the target. -/
public abbrev sliceCechComplex (G : (Over X)ᵒᵖ ⥤ A) : CochainComplex A ℕ :=
  (sliceCechComplexFunctor E).obj G

/-- The slice Čech complex is the alternating coface map complex of the slice Čech
cosimplicial object, by definition. -/
public theorem sliceCechComplex_eq_alternatingCofaceMapComplex (G : (Over X)ᵒᵖ ⥤ A) :
    sliceCechComplex E G =
      (alternatingCofaceMapComplex A).obj (sliceCechCosimplicialObject E G) :=
  rfl

/-- **A comparison of slice Čech complexes from a comparison of cosimplicial objects.** -/
public def sliceCechComplexIsoOfCosimplicialIso {G : (Over X)ᵒᵖ ⥤ A} {D : CosimplicialObject A}
    (η : sliceCechCosimplicialObject E G ≅ D) :
    sliceCechComplex E G ≅ (alternatingCofaceMapComplex A).obj D :=
  (alternatingCofaceMapComplex A).mapIso η

/-- The Čech complex functor is restriction to the slice followed by the slice Čech complex
functor. -/
public theorem cechComplexFunctor_eq_comp :
    cechComplexFunctor (A := A) E =
      (Functor.whiskeringLeft (Over X)ᵒᵖ Cᵒᵖ A).obj (Over.forget X).op ⋙
        sliceCechComplexFunctor E :=
  rfl

/-- The Čech complex of a presheaf is the slice Čech complex of its restriction to the slice. -/
public theorem cechComplex_eq_sliceCechComplex (F : Cᵒᵖ ⥤ A) :
    cechComplex E F = sliceCechComplex E ((Over.forget X).op ⋙ F) :=
  rfl

/-- Transport of the Čech complex along an identification of the restriction to the slice. -/
public def cechComplexIsoSlice {F : Cᵒᵖ ⥤ A} {G : (Over X)ᵒᵖ ⥤ A}
    (e : (Over.forget X).op ⋙ F ≅ G) : cechComplex E F ≅ sliceCechComplex E G :=
  (sliceCechComplexFunctor E).mapIso e

end Preadditive

section Abelian

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]

/-- The Čech cohomology of a presheaf defined only on the slice at the target. -/
public abbrev sliceCechCohomology (G : (Over X)ᵒᵖ ⥤ A) (n : ℕ) : A :=
  (sliceCechComplex E G).homology n

/-- The Čech cohomology of a presheaf is the slice Čech cohomology of its restriction to the
slice. -/
public theorem cechCohomology_eq_sliceCechCohomology (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechCohomology E F n = sliceCechCohomology E ((Over.forget X).op ⋙ F) n :=
  rfl

/-- **The slice-to-ambient transport for Čech vanishing.** -/
public theorem isZero_cechCohomology_of_isZero_slice {F : Cᵒᵖ ⥤ A} {G : (Over X)ᵒᵖ ⥤ A}
    (e : (Over.forget X).op ⋙ F ≅ G) (n : ℕ) (h : IsZero (sliceCechCohomology E G n)) :
    IsZero (cechCohomology E F n) :=
  h.of_iso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).mapIso
    (cechComplexIsoSlice E e))

end Abelian

end Stacks.CechSite

end
