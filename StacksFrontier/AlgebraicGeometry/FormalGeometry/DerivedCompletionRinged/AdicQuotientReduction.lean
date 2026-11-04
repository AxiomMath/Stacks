module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.NilpotentIdeal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence

/-!
# Derived reduction modulo the powers of a sheaf of ideals, and derived completion

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `K ∈ D(𝒪)`. For every `n` the
projection `𝒪 ⟶ 𝒪/ℐⁿ` induces the *derived reduction*

`K ≅ K ⊗^𝐋_𝒪 𝒪[0] ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`,

and these maps are compatible with the transition maps `𝒪/ℐⁿ ⟶ 𝒪/ℐᵐ` of the tower.
These are the canonical maps of [Stacks, Tag 0CQH].

## Main definitions

* `AlgebraicGeometry.RingedSite.adicQuotientObj`: `𝒪/ℐⁿ` as an object of `D(𝒪)`, in degree
  zero.
* `AlgebraicGeometry.RingedSite.adicQuotientReduction`: the derived reduction
  `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCompletion_hom_ext`: two maps out of `K^∧` into a
  derived-complete object agree as soon as their composites with `K ⟶ K^∧` agree.
* `AlgebraicGeometry.RingedSite.adicQuotientReduction_comp_map`: the reductions are compatible
  with the transition maps of the tower.

## Implementation notes

`𝒪/ℐⁿ` is `Stacks.Sites.adicQuotientModule`, the cokernel in sheaves of `𝒪`-modules of the
inclusion of `ℐⁿ` into the free rank-one sheaf of modules, with transition maps
`Stacks.Sites.adicQuotientModuleMap` ([Stacks, Tag 0942]). The derived tensor product is the
canonical one of [Stacks, Tag 06YU], and `K ≅ K ⊗^𝐋_𝒪 𝒪[0]` is its unit law. The derived category
is the standard model `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

section Reflector

variable [(ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).IsRightAdjoint]

/-- Two maps out of a derived completion into a derived-complete object agree as soon as their
composites with `K ⟶ K^∧` agree. -/
theorem derivedCompletion_hom_ext
    {K T : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))}
    (hT : IsDerivedComplete.{u, u, u, u} X I T)
    {g g' : (derivedCompletion X I).obj K ⟶ T}
    (e : (derivedCompletionUnit X I).app K ≫ g =
      (derivedCompletionUnit X I).app K ≫ g') :
    g = g' := by
  have h : (ObjectProperty.homMk g :
        (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).leftAdjoint.obj K ⟶
          (⟨T, hT⟩ : ObjectProperty.FullSubcategory
            (IsDerivedComplete.{u, u, u, u} X I))) =
      ObjectProperty.homMk g' :=
    ((derivedCompletionAdjunction X I).homEquiv K
      (⟨T, hT⟩ : ObjectProperty.FullSubcategory
        (IsDerivedComplete.{u, u, u, u} X I))).injective (by
      rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit])
  exact congrArg (ObjectProperty.ι (IsDerivedComplete.{u, u, u, u} X I)).map h

end Reflector

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- `𝒪/ℐⁿ` as an object of `D(𝒪)`, placed in degree zero. -/
abbrev adicQuotientObj (n : ℕ) :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
    (Stacks.Sites.adicQuotientModule (X := X) I n)

/-- The derived reduction `K ⟶ K ⊗^𝐋_𝒪 𝒪/ℐⁿ` of [Stacks, Tag 0CQH]: the unit law
`K ≅ K ⊗^𝐋_𝒪 𝒪[0]` of the derived tensor product, followed by tensoring with the projection
`𝒪 ⟶ 𝒪/ℐⁿ`. -/
def adicQuotientReduction
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    K ⟶ ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
      (adicQuotientObj X I n) :=
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).unitIso K).inv ≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
        (Stacks.Sites.adicQuotientModuleπ (X := X) I n))

/-- The derived reductions are compatible for varying `n`: the reduction modulo `ℐⁿ` followed by
the transition map `𝒪/ℐⁿ ⟶ 𝒪/ℐᵐ` of the tower is the reduction modulo `ℐᵐ`. -/
theorem adicQuotientReduction_comp_map
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    {m n : ℕ} (h : m ≤ n) :
    adicQuotientReduction X I K n ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).map
            (Stacks.Sites.adicQuotientModuleMap (X := X) I h)) =
      adicQuotientReduction X I K m := by
  rw [adicQuotientReduction, adicQuotientReduction, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap]

end Tensor

end AlgebraicGeometry.RingedSite

end
