module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear

/-!
# Derived global sections and base scalars, in any model of the derived categories

`AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id` is stated with the derived categories
resolved to `HasDerivedCategory.standard`. This file states it with the two `HasDerivedCategory`
instances taken as binders, so that it also holds in the locally small model.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id_of_hasDerivedCategory`: `A`-linear
  derived global sections carries multiplication by a base scalar to multiplication by that
  scalar, in any model of the two derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w₁ w₂

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (X : Over (Spec (CommRingCat.of A)))

/-- **`A`-linear derived global sections carries multiplication by a base scalar to
multiplication by that scalar, in any model of the two derived categories.** The underived
functor does, by `globalSectionsOver_linear`, and
`Stacks.SemilinearFunctor.map_smul_id_rightDerived` transfers that to the right derived functor.

This is `derivedGlobalSectionsOver_map_smul_id` with the two `HasDerivedCategory` instances taken
as binders rather than resolved to the `HasDerivedCategory.standard` instance that
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLinear.lean` raises to a high
priority, so that it also holds in the locally small model;
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/BaseScalarTriangle.lean` works in
that model and uses this form. -/
theorem derivedGlobalSectionsOver_map_smul_id_of_hasDerivedCategory
    [HasDerivedCategory.{w₁} X.left.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)] (a : A)
    (E : DerivedCategory X.left.Modules) :
    letI : Linear A X.left.Modules := modulesLinear A X
    (derivedGlobalSectionsOver X.hom).map (a • 𝟙 E) =
      a • 𝟙 ((derivedGlobalSectionsOver X.hom).obj E) := by
  let : Linear A X.left.Modules := modulesLinear A X
  let := globalSectionsOver_linear X
  have hunder : ∀ N : X.left.Modules, (globalSectionsOver X.hom).map (a • 𝟙 N) =
      a • 𝟙 ((globalSectionsOver X.hom).obj N) := fun N => by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  exact Stacks.SemilinearFunctor.map_smul_id_rightDerived (R := A) (S := A)
    (H₁ := HomotopyCategory X.left.Modules (ComplexShape.up ℤ))
    (D₁ := DerivedCategory X.left.Modules) (D₂ := DerivedCategory (ModuleCat.{u} A))
    (G := homotopyGlobalSectionsOver X.hom) (L := DerivedCategory.Qh)
    (derivedGlobalSectionsOver X.hom) (derivedGlobalSectionsOverUnit X.hom)
    (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ)) a a
    (fun M => Stacks.SemilinearFunctor.map_smul_id_comp (R := A) (S := A)
      ((globalSectionsOver X.hom).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh a a
      (fun N => Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory (R := A) (S := A)
        (globalSectionsOver X.hom) a a hunder (ComplexShape.up ℤ) N) M) E

end AlgebraicGeometry

end
