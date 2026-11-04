module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorProduct

/-!
# The monoidal category of sheaves of modules over a ring

Let `(C, J)` be a site and `Λ` a commutative ring. The sheaves of `Λ`-modules on `C` form a
symmetric monoidal category, `CategoryTheory.Sheaf.monoidalCategory`, whose tensor product
`F ⊗ G` is the sheafification of `U ↦ F(U) ⊗_Λ G(U)`. This file records the facts about it that
the construction of the derived tensor product needs: the monoidal structure is closed, so
tensoring with a fixed sheaf commutes with all colimits and is additive, and sequential colimits
of sheaves of modules are exact.

## Main definitions

* `Stacks.ModuleSheaf.monoidalClosed`: the closed structure.
* `Stacks.ModuleSheaf.tensorRightSheafifyIso`: tensoring a sheaf with the sheafification of a
  presheaf `P` is sheafifying the objectwise tensor product with `P`.

## Main results

* `Stacks.ModuleSheaf.preservesColimitsOfSize_tensorLeft`,
  `Stacks.ModuleSheaf.preservesColimitsOfSize_tensorRight`: tensoring with a fixed sheaf, on
  either side, commutes with colimits.
* `Stacks.ModuleSheaf.hasExactColimitsOfShape_nat`: sequential colimits are exact.

## Implementation notes

Mathlib does not make `CategoryTheory.Sheaf.monoidalCategory` an instance, since on some value
categories it clashes with the cartesian structure, and it is activated as a local instance
wherever it is used, together with `CategoryTheory.Sheaf.symmetricCategory`. The closed structure
is Day's reflection theorem, `CategoryTheory.Monoidal.Reflective.monoidalClosed`, applied to the
reflection of presheaves onto sheaves, whose left adjoint, sheafification, is monoidal.

The coefficient ring lives in the universe `w` of the module sections, which is assumed to
contain the universes `u` and `v` of the site (`UnivLE.{max u v, w}`): `ModuleCat.{s} Λ` is
monoidal only for `Λ : Type s`, and under the universe inequality every sheafification
hypothesis is automatic, by `Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-- Sheafification of presheaves of `Λ`-modules. This is
`Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE`, given high priority so that instance
search does not first try the instances stated at a module universe of the form `max u v x`,
whose universe cannot be determined from `ModuleCat.{w} Λ`. -/
instance (priority := 10000) hasSheafify : HasSheafify J (ModuleCat.{w} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE J Λ

/-- The morphisms of presheaves of `Λ`-modules which become isomorphisms after sheafification
are stable under the tensor product. Recorded as a high-priority instance for this category, the
input of `CategoryTheory.Sheaf.monoidalCategory`, because in the presence of all of Mathlib's
instances the general search does not finish in time. -/
instance (priority := 10000) isMonoidal_W : (J.W (A := ModuleCat.{w} Λ)).IsMonoidal :=
  inferInstance

/-- Sheaves of `Λ`-modules have colimits indexed by small categories. Recorded as an instance
for this category because instance search does not find the general one in time. -/
instance hasColimitsOfSize_zero : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.instHasColimitsOfSize

/-- Sheaves of `Λ`-modules have colimits of every shape in `Type 0`. This is the instance through
which the colimits occurring in total complexes and sequential colimits are found; it is given
high priority because the general instances for sheaf categories pass through essential
smallness of the site, where the universe of the module sections cannot be determined. -/
instance (priority := 10000) hasColimitsOfShape_of_small (K : Type) [Category.{0} K] :
    HasColimitsOfShape K (Sheaf J (ModuleCat.{w} Λ)) :=
  (hasColimitsOfSize_zero J Λ).has_colimits_of_shape K

/-- Sheaves of `Λ`-modules have colimits indexed by categories in the universe of the module
sections. -/
instance hasColimitsOfSize :
    HasColimitsOfSize.{w, w} (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.instHasColimitsOfSize

open MonoidalClosed.FunctorCategory in
/-- **The monoidal category of sheaves of `Λ`-modules is closed.** This is Day's reflection
theorem for the reflection of presheaves onto sheaves: the presheaves form a closed symmetric
monoidal category and sheafification is monoidal. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed (Sheaf J (ModuleCat.{w} Λ)) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J (ModuleCat.{w} Λ))

attribute [local instance] monoidalClosed

/-- Tensoring on the left with a fixed sheaf commutes with colimits, being a left adjoint. -/
instance preservesColimitsOfSize_tensorLeft (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesColimitsOfSize.{w, w} (tensorLeft F) :=
  (ihom.adjunction F).leftAdjoint_preservesColimits

/-- Tensoring on the left with a fixed sheaf commutes with small colimits. -/
instance preservesColimitsOfSize_zero_tensorLeft (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
  preservesColimitsOfSize_shrink _

/-- Tensoring on the right with a fixed sheaf commutes with colimits: it is isomorphic to
tensoring on the left, by the braiding. -/
instance preservesColimitsOfSize_tensorRight (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesColimitsOfSize.{w, w} (tensorRight F) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

/-- Tensoring on the right with a fixed sheaf commutes with small colimits. -/
instance preservesColimitsOfSize_zero_tensorRight (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
  preservesColimitsOfSize_shrink _

/-- Tensoring on the right with a fixed sheaf is right exact. -/
instance preservesFiniteColimits_tensorRight (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesFiniteColimits (tensorRight F) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the left with a fixed sheaf is right exact. -/
instance preservesFiniteColimits_tensorLeft (F : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesFiniteColimits (tensorLeft F) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the left with a fixed sheaf is additive: it preserves binary coproducts, which
are biproducts, and zero morphisms, being a left adjoint. -/
instance tensorLeft_additive (F : Sheaf J (ModuleCat.{w} Λ)) :
    (tensorLeft F).Additive := by
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (tensorLeft F)
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft F)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Tensoring on the right with a fixed sheaf is additive. -/
instance tensorRight_additive (F : Sheaf J (ModuleCat.{w} Λ)) :
    (tensorRight F).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight F)

/-- The tensor product of sheaves of modules is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (Sheaf J (ModuleCat.{w} Λ)) where
  whiskerLeft_zero {F _ _} := (tensorLeft F).map_zero _ _
  zero_whiskerRight := by intros; exact (tensorRight _).map_zero _ _
  whiskerLeft_add {F _ _} f g := (tensorLeft F).map_add (f := f) (g := g)
  add_whiskerRight f g := (tensorRight _).map_add (f := f) (g := g)

/-- Sequential colimits of sheaves of `Λ`-modules are exact. -/
instance hasExactColimitsOfShape_nat :
    HasExactColimitsOfShape ℕ (Sheaf J (ModuleCat.{w} Λ)) := by
  have : HasExactColimitsOfShape ℕ (ModuleCat.{w} Λ) := by
    have : AB5OfSize.{0, 0} (ModuleCat.{w} Λ) := AB5OfSize_shrink _
    exact AB5OfSize.ofShape ℕ
  infer_instance

/-- The total tensor complex of two complexes of sheaves of modules exists: in each degree it
is a coproduct indexed by a type in `Type 0`. -/
instance hasMapBifunctor_curriedTensor {ι₁ ι₂ ι : Type} {c₁ : ComplexShape ι₁}
    {c₂ : ComplexShape ι₂} (K₁ : HomologicalComplex (Sheaf J (ModuleCat.{w} Λ)) c₁)
    (K₂ : HomologicalComplex (Sheaf J (ModuleCat.{w} Λ)) c₂) (c : ComplexShape ι)
    [TotalComplexShape c₁ c₂ c] [DecidableEq ι] :
    K₁.HasMapBifunctor K₂ (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) c := fun _ =>
  have := (hasColimitsOfSize_zero J Λ).has_colimits_of_shape
  inferInstance

/-- The total complex of a double complex of sheaves of modules exists. -/
instance hasTotal {ι₁ ι₂ ι : Type} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
    (K : HomologicalComplex₂ (Sheaf J (ModuleCat.{w} Λ)) c₁ c₂) (c : ComplexShape ι)
    [TotalComplexShape c₁ c₂ c] [DecidableEq ι] : K.HasTotal c := fun _ =>
  have := (hasColimitsOfSize_zero J Λ).has_colimits_of_shape
  inferInstance

end Stacks.ModuleSheaf
