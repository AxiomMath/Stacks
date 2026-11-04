module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryProducts

/-!
# Property-(P) resolutions of differential graded bimodules

Let `A` and `B` be differential graded algebras over a commutative ring `R`. A differential
graded `(A, B)`-bimodule *has property (P)* when it carries a filtration
`0 = F_{-1}P ⊆ F_0P ⊆ F_1P ⊆ ⋯ ⊆ P` by differential graded sub-bimodules which is exhaustive,
whose inclusions are split as maps of graded bimodules, and whose successive quotients are
direct sums of shifts of `Aᵒᵖ ⊗_R B`. This file proves that every differential graded
`(A, B)`-bimodule receives a quasi-isomorphism from one having property (P).

## Main results

* `DifferentialGraded.Bimodule.exists_propertyP_resolution`: every differential graded
  `(A, B)`-bimodule `M` admits a homomorphism `P ⟶ M` of differential graded bimodules which is
  a quasi-isomorphism and whose source has property (P).

## Implementation notes

Property (P) for a bimodule is read on the right differential graded module over
`Aᵒᵖ ⊗_R B` that the bimodule is, by the equivalence of Tag 0FQJ: the conclusion asks for a
`DifferentialGradedModule.PropertyPFiltration` of `DifferentialGraded.Bimodule.toTensorModule`.
That equivalence carries sub-bimodules to submodules, graded bimodule maps to graded module maps
and `Aᵒᵖ ⊗_R B` to its own regular module, so the two readings of property (P) say the same
thing; stating it through the equivalence is what makes Tag 09KP applicable verbatim.

The construction of Tag 0FQJ is used in its concrete form,
`DifferentialGraded.Bimodule.toTensorModule` and
`DifferentialGraded.Bimodule.ofTensorModule`, rather than through the abstract equivalence
`DifferentialGraded.Bimodule.tensorEquivalence`. The concrete functor leaves the underlying
module, its grading and its differential unchanged *definitionally*, so being a
quasi-isomorphism over `Aᵒᵖ ⊗_R B` and over `B` are literally the same condition and no
comparison of complexes is needed; `tensorMapPreimage` (full faithfulness) turns the resolution
of the tensor module into a homomorphism of bimodules.

Quasi-isomorphy is transported in the cycle-and-boundary form
`DifferentialGradedModule.IsQuasiIsomorphism`, which mentions only the underlying module, its
grading and its differential; it is converted to Mathlib's `QuasiIso` at the two ends by
`DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso` and
`DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism`.

## References

* [Stacks Project, Tag 0FQK](https://stacks.math.columbia.edu/tag/0FQK)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R]

/-- The inverse of an isomorphism of differential graded modules undoes it on elements. -/
private theorem inv_toFun_hom_toFun {C : DifferentialGradedAlgebra.{u, u} R}
    {Q P : DifferentialGradedModule.{u, u, u} C} (e : Q ≅ P) (x) :
    e.inv.toFun (e.hom.toFun x) = x :=
  congrArg (fun f : DifferentialGradedModule.Hom Q Q => f.toFun x) e.hom_inv_id

/-- A property-(P) filtration is transported along an isomorphism of differential graded
modules: the stages and all their data are unchanged, only the embeddings into the filtered
module are composed with the isomorphism. -/
private def propertyPFiltrationOfIso {C : DifferentialGradedAlgebra.{u, u} R}
    {Q P : DifferentialGradedModule.{u, u, u} C} (e : Q ≅ P)
    (F : DifferentialGradedModule.PropertyPFiltration Q) :
    DifferentialGradedModule.PropertyPFiltration P := by
  have he : Function.Injective e.hom.toFun := fun x y h =>
    (inv_toFun_hom_toFun e x).symm.trans
      ((congrArg e.inv.toFun h).trans (inv_toFun_hom_toFun e y))
  exact
    { F := F.F
      ι := fun i => F.ι i ≫ e.hom
      injective := fun i => he.comp (F.injective i)
      incl := F.incl
      incl_comp := fun i x => congrArg e.hom.toFun (F.incl_comp i x)
      admissible := F.admissible
      exhaustive := fun x => by
        obtain ⟨i, y, hy⟩ := F.exhaustive (e.inv.toFun x)
        exact ⟨i, y, (congrArg e.hom.toFun hy).trans (inv_toFun_hom_toFun e.symm x)⟩
      bottomIndex := F.bottomIndex
      bottomDecidableEq := F.bottomDecidableEq
      bottomShift := F.bottomShift
      bottomMap := F.bottomMap
      bottom_bijective := F.bottom_bijective
      quotientIndex := F.quotientIndex
      quotientDecidableEq := F.quotientDecidableEq
      quotientShift := F.quotientShift
      quotientMap := F.quotientMap
      quotient_surjective := F.quotient_surjective
      quotient_ker := F.quotient_ker }

/-- **Stacks 0FQK.** *"Let `R` be a ring. Let `(A, d)` and `(B, d)` be differential graded
`R`-algebras. Let `M` be a differential graded `(A, B)`-bimodule. There exists a homomorphism
`P → M` of differential graded `(A, B)`-bimodules which is a quasi-isomorphism such that `P`
has property (P)."*

Property (P) of the resolving bimodule is recorded as a property-(P) filtration of the right
differential graded `Aᵒᵖ ⊗_R B`-module it is by Tag 0FQJ, and being a quasi-isomorphism is
Mathlib's `QuasiIso` on the cochain complex underlying the homomorphism of right `B`-modules. -/
@[stacks 0FQK]
theorem exists_propertyP_resolution (A B : DifferentialGradedAlgebra.{u, u} R)
    (M : Bimodule A B) :
    ∃ (P : Bimodule A B) (f : P ⟶ M),
      QuasiIso ((DifferentialGradedModule.forgetToCochainComplex B).map f.rightHom) ∧
        Nonempty (DifferentialGradedModule.PropertyPFiltration (toTensorModule A B P)) := by
  obtain ⟨Q, g, hg, ⟨F⟩⟩ := DifferentialGradedModule.exists_propertyP_resolution
    (tensorAlgebra A B) (toTensorModule A B M)
  set e := toTensorModuleOfTensorModuleIso A B Q
  refine ⟨ofTensorModule A B Q, tensorMapPreimage A B (e.hom ≫ g), ?_,
    ⟨propertyPFiltrationOfIso e.symm F⟩⟩
  have hcomp : QuasiIso ((DifferentialGradedModule.forgetToCochainComplex
      (tensorAlgebra A B)).map (e.hom ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  exact DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism _
    (DifferentialGradedModule.isQuasiIsomorphism_of_quasiIso _ hcomp)

end DifferentialGraded.Bimodule

end
