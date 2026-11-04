module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechAmitsurComparison
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The Amitsur coefficient functor preserves finite products

`Stacks.Descent.amitsurCoefficients R M` sends a commutative algebra `A` over the lifted base
ring to the `R`-module `A ⊗_R M`.  This file proves that **it preserves finite products**: a
finite product of algebras is carried to the product of the base changes.

That is the one property the finite-family reduction of [Stacks, Tag 03FI] part (3) asks of a
coefficient presheaf, in the form
`Stacks.CechSite.isIso_cechComplexMap_of_preservesFiniteProducts`.  For the pullback-sections
presheaf `ℱᵃ` of a quasi-coherent module the tree gets it from the *sheaf* condition, through
`CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts`; but the presheaf
`V ↦ Γ(V, 𝒪) ⊗_R M` of a module `M` in an arbitrary universe is **not** a Zariski sheaf — it
agrees with `ℱᵃ` only over the affine objects — so that route is unavailable and the property
has to be proved where it actually lives, namely in the algebra.

## The route

Tensoring is additive, and an additive functor between preadditive categories with finite
biproducts preserves finite products; so the content is entirely in getting from `CommAlgCat` to
`ModuleCat`, a passage between two categories neither of whose product structures is given by a
`forget`-creation lemma in the library.  Three steps:

* `Stacks.Descent.moduleTensorFunctor` is `- ⊗_R M` on `ModuleCat`, with the coefficient module
  in a universe of its own; it is additive, hence preserves finite products.
* `CategoryTheory.forget₂ (CommAlgCat R) CommRingCat` preserves finite products, because
  `Mathlib.Algebra.Category.CommAlgCat.Basic`'s equivalence `CommAlgCat R ≌ Under R` carries it
  to `CategoryTheory.Under.forget`, which does.  This is also where the algebra universe is
  forced to equal the ring universe: that equivalence exists only there.
* `CategoryTheory.forget₂ (CommAlgCat R) (ModuleCat R)` then preserves finite products by
  reflection: its composite with `CategoryTheory.forget (ModuleCat R)` is
  `CategoryTheory.forget (CommAlgCat R)`, which preserves them, and the forgetful functor of
  `ModuleCat` reflects limits because it reflects isomorphisms.

## Main results

* `Stacks.Descent.moduleTensorFunctor`: `- ⊗_R M` with the coefficient universe free, and its
  additivity.
* `Stacks.Descent.preservesFiniteProducts_forget₂_commAlgCat_moduleCat`.
* `Stacks.Descent.tensorModuleFunctor_eq_comp`: `AlgebraicTopology.tensorModuleFunctor` is the
  forgetful functor to modules followed by `Stacks.Descent.moduleTensorFunctor`.
* `Stacks.Descent.preservesFiniteProducts_amitsurCoefficients`: **the Amitsur coefficient
  functor preserves finite products.**

## Implementation notes

`Stacks.Descent.moduleTensorFunctor` is written with the same formulas as
`AlgebraicTopology.tensorModuleFunctor`, so that
`Stacks.Descent.tensorModuleFunctor_eq_comp` holds by `rfl` and the transport of product
preservation costs nothing.  It is not obtained from Mathlib's monoidal structure on
`ModuleCat`, which keeps the two factors in one universe, whereas the coefficient module here
sits above the algebras.

The instances are declared as named theorems rather than `instance`s where instance search would
otherwise have to guess the coefficient module, which it cannot: `M` does not appear in the type
of the functor's source or target in a way that determines it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v m

namespace Stacks.Descent

/-! ### Tensoring a module with a coefficient module in another universe -/

section ModuleTensor

variable (R : Type u) [CommRing R] (M : Type m) [AddCommGroup M] [Module R M]

/-- **Tensoring with a coefficient module, on `ModuleCat`, with the coefficient module in a
universe of its own.**  This is `AlgebraicTopology.tensorModuleFunctor` with its source taken to
be the modules rather than the algebras over `R`, which is where additivity is available. -/
def moduleTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{max v m} R where
  obj N := ModuleCat.of R (TensorProduct R N M)
  map f := ModuleCat.ofHom (LinearMap.rTensor M f.hom)
  map_id N := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext n x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext n x
    rfl

/-- `Stacks.Descent.moduleTensorFunctor` is additive: the tensor product of a sum of linear maps
with the identity of the coefficient module is the sum of the tensor products. -/
instance moduleTensorFunctor_additive : (moduleTensorFunctor.{u, v, m} R M).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    change LinearMap.rTensor M (f + g).hom = _
    rw [ModuleCat.hom_add, LinearMap.rTensor_add]
    rfl

end ModuleTensor

/-! ### From commutative algebras to modules -/

section Forget

variable (R : Type u) [CommRing R]

/-- The forgetful functor from commutative `R`-algebras to commutative rings is, up to a natural
isomorphism which is the identity on carriers, the composite of the equivalence with the rings
under `R` and `CategoryTheory.Under.forget`. -/
def forget₂CommAlgCatCommRingCatIso :
    forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ≅
      (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
        Under.forget (CommRingCat.of R) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; rfl)

/-- **The forgetful functor from commutative `R`-algebras to commutative rings preserves finite
products.** -/
theorem preservesFiniteProducts_forget₂_commAlgCat_commRingCat :
    PreservesFiniteProducts (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) where
  preserves _n :=
    preservesLimitsOfShape_of_natIso (forget₂CommAlgCatCommRingCatIso R).symm

/-- **The forgetful functor from commutative `R`-algebras to types preserves finite
products.** -/
theorem preservesFiniteProducts_forget_commAlgCat :
    PreservesFiniteProducts (forget (CommAlgCat.{u} R)) := by
  have h := preservesFiniteProducts_forget₂_commAlgCat_commRingCat R
  rw [← HasForget₂.forget_comp (C := CommAlgCat.{u} R) (D := CommRingCat.{u})]
  infer_instance

/-- The forgetful functor from commutative `R`-algebras to `R`-modules, through the algebras. -/
abbrev forget₂CommAlgCatModuleCat : CommAlgCat.{u} R ⥤ ModuleCat.{u} R :=
  forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)

/-- The forgetful functor to `R`-modules followed by the forgetful functor to types is the
forgetful functor to types. -/
theorem forget₂CommAlgCatModuleCat_comp_forget :
    forget₂CommAlgCatModuleCat.{u} R ⋙ forget (ModuleCat.{u} R) = forget (CommAlgCat.{u} R) := by
  rw [Functor.assoc, HasForget₂.forget_comp, HasForget₂.forget_comp]

/-- **The forgetful functor from commutative `R`-algebras to `R`-modules preserves finite
products.**  Its composite with the forgetful functor of `ModuleCat` preserves them, and that
forgetful functor reflects limits, since it reflects isomorphisms. -/
theorem preservesFiniteProducts_forget₂_commAlgCat_moduleCat :
    PreservesFiniteProducts (forget₂CommAlgCatModuleCat.{u} R) where
  preserves n := by
    have h := preservesFiniteProducts_forget_commAlgCat R
    refine ⟨fun {K} ↦ ?_⟩
    have hpres :
        PreservesLimit K (forget₂CommAlgCatModuleCat.{u} R ⋙ forget (ModuleCat.{u} R)) := by
      rw [forget₂CommAlgCatModuleCat_comp_forget]
      infer_instance
    exact preservesLimit_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

end Forget

/-! ### The Amitsur coefficient functor -/

section Amitsur

variable (R : Type u) [CommRing R] (M : Type m) [AddCommGroup M] [Module R M]

/-- `AlgebraicTopology.tensorModuleFunctor` factors through the forgetful functor to modules.
Both sides send an algebra `A` to `A ⊗_R M` and an algebra map to its tensor with the identity,
so the equality is definitional. -/
theorem tensorModuleFunctor_eq_comp :
    AlgebraicTopology.tensorModuleFunctor.{u, u, m} R M =
      forget₂CommAlgCatModuleCat.{u} R ⋙ moduleTensorFunctor.{u, u, m} R M := rfl

/-- **`AlgebraicTopology.tensorModuleFunctor` preserves finite products.** -/
theorem preservesFiniteProducts_tensorModuleFunctor :
    PreservesFiniteProducts (AlgebraicTopology.tensorModuleFunctor.{u, u, m} R M) := by
  have h₁ := preservesFiniteProducts_forget₂_commAlgCat_moduleCat.{u} R
  rw [tensorModuleFunctor_eq_comp]
  infer_instance

/-- **The Amitsur coefficient functor preserves finite products.**  It is the tensor functor
followed by a restriction of scalars, and restriction of scalars preserves all limits. -/
theorem preservesFiniteProducts_amitsurCoefficients :
    PreservesFiniteProducts (amitsurCoefficients.{u, u, m} R M) where
  preserves n := by
    have h := preservesFiniteProducts_tensorModuleFunctor (ULift.{u} R) M
    have h₁ : PreservesLimitsOfShape (Discrete (Fin n))
        (AlgebraicTopology.tensorModuleFunctor.{u, u, m} (ULift.{u} R) M) := h.preserves n
    have h₂ : PreservesLimitsOfShape (Discrete (Fin n))
        (ModuleCat.restrictScalars.{max u m} (algebraMap R (ULift.{u} R))) := inferInstance
    exact inferInstanceAs (PreservesLimitsOfShape (Discrete (Fin n))
      (AlgebraicTopology.tensorModuleFunctor.{u, u, m} (ULift.{u} R) M ⋙
        ModuleCat.restrictScalars.{max u m} (algebraMap R (ULift.{u} R))))

end Amitsur

end Stacks.Descent

end
