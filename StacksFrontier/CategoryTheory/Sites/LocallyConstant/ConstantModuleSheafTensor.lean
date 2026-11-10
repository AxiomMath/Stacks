module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorCoproductRight
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalSections
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility

/-!
# The tensor product of constant sheaves of modules over a constant sheaf of rings

Let `(C, J)` be a site, `Λ` a commutative ring, `R` a sheaf of commutative rings and
`α : Λ̲ ⟶ R` a locally bijective morphism out of the constant presheaf of rings on `Λ`, so that
`Stacks.ConstantRingModules.toModuleSheaf` identifies sheaves of modules over `R` with sheaves of
`Λ`-modules and `Stacks.ConstantRingModules.constSheafOfModules` is the constant sheaf of modules
functor into the first of the two.

This file computes the tensor product over `R` of a constant sheaf of modules on a **finite free**
`Λ`-module with an arbitrary sheaf of `R`-modules — it is a finite coproduct of copies of the
second factor — and deduces that, when the second factor is locally constant of finite type, so is
the tensor product. At the level of complexes: every term of the total tensor complex of two
bounded above complexes of constant sheaves of modules, the first on finite free modules and the
second on modules of finite type, is locally constant of finite type.

## Main definitions

* `Stacks.ConstantRingModules.constSheafOfModulesPiIso`: the constant sheaf of modules on the
  standard finite free module `I → Λ` is the free sheaf of modules on `I`.
* `Stacks.ConstantRingModules.constSheafOfModulesPiTensorIso`: **tensoring with it is a finite
  coproduct**, `Φ(I → Λ) ⊗_R B ≅ ∐_{i : I} B`.
* `Stacks.ConstantRingModules.isFiniteTypeLocallyConstantModules`: the property of Tag 093U read
  on sheaves of modules over `R` through the identification.

## Main results

* `Stacks.ConstantRingModules.isFiniteTypeLocallyConstantModules_sheafTensor_constSheafOfModules`:
  the tensor product over `R` of the constant sheaf of modules on a finite free `Λ`-module with
  the constant sheaf of modules on a `Λ`-module of finite type is locally constant of finite type.
* `Stacks.ConstantRingModules.isFiniteTypeLocallyConstantModules_mapBifunctor`: **the termwise
  statement at the level of complexes.**
* The exactness of `constSheafOfModules`: `additive_constSheafOfModules` and
  `preservesFiniteColimits_constSheafOfModules`.

## Implementation notes

**This is not the monoidality already in the library.** The tensor product here is the tensor
product of sheaves of modules over `R`,
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the bifunctor the derived tensor product of
Stacks 06YU is built from. `Stacks.ConstantSheaf.constantSheafTensorIso` of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.TensorFiniteType`, and the finite type
statement `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_tensor` beside it, are
about a *different* bifunctor: the sheafified tensor product of `ModuleCat Λ`-valued sheaves given
by `CategoryTheory.Sheaf.monoidalCategory`. That the two agree under the identification of the two
readings of a sheaf of `Λ`-modules is not in the library and is not proved here; the route taken
instead is the finite free one, which needs no comparison of the two tensor products.

**Why finite free and not finite type on the left.** The left factor is decomposed: a finite free
`Λ`-module is `I → Λ` for a finite `I`, the constant sheaf of modules on it is the free sheaf of
modules on `I` by `Stacks.SheafOfModules.freeIsoMapFinitePi`, which is by definition the coproduct
of `I` copies of the unit object, and tensoring a coproduct of units with `B` is the coproduct of
copies of `B` by `Stacks.SheafOfModules.Strict.coproductUnitTensorIso`. Nothing is asked of the
right factor, so finite type local constancy of the product follows from that of the right factor
alone, through closure of the property of Tag 093U under finite coproducts.

**The unit comparison is not new.** `Φ(Λ)` is the sheafification along `α` of the unit presheaf of
modules over the constant presheaf of rings — that is an equality, not an isomorphism — so the
comparison `Φ(Λ) ≅ unit R` that `freeIsoMapFinitePi` asks for is
`PresheafOfModules.sheafificationObjUnitIso α` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Unit`,
already stated for an arbitrary locally bijective `α`. No analogue
of `Stacks.SheafOfModules.Constant.unitIsoConstantModuleSheaf`, which is the same comparison
hard-wired to the constant sheaf of rings, is restated here.

**Universes.** The exactness instances are universe-general. The tensor statements are at a small
site with every universe equal, which is the configuration in which the tensor product of sheaves
of modules over a ringed site and the derived tensor product of Stacks 06YU are available; see the
implementation notes of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensor`.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.ConstantSheaf Stacks.SheafOfModules

universe u v a

section Exactness

variable {C : Type u} [Category.{v} C] (Λ : Type a) [Ring Λ] (J : GrothendieckTopology C)
  {R : Sheaf J RingCat.{a}} (α : constRing (C := C) Λ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  [HasWeakSheafify J (ModuleCat.{a} Λ)] [J.WEqualsLocallyBijective (ModuleCat.{a} Λ)]

/-- The functor `ofFunctor` from sheaves of `Λ`-modules is an equivalence. -/
instance isEquivalence_ofFunctor : (ofFunctor.{a} (C := C) Λ).IsEquivalence :=
  (presheafEquivalence.{a} (C := C) Λ).isEquivalence_inverse

/-- The functor `ofFunctor` preserves finite colimits. -/
instance preservesFiniteColimits_ofFunctor :
    PreservesFiniteColimits (ofFunctor.{a} (C := C) Λ) :=
  letI : PreservesColimitsOfSize.{0, 0} (ofFunctor.{a} (C := C) Λ) :=
    Adjunction.isEquivalence_preservesColimits _
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The constant sheaf of modules functor `constSheafOfModules Λ J α` preserves finite colimits. -/
instance preservesFiniteColimits_constSheafOfModules :
    PreservesFiniteColimits (constSheafOfModules.{a} Λ J α) :=
  inferInstanceAs (PreservesFiniteColimits
    (constPresheafOfModules.{a} Λ ⋙ _root_.PresheafOfModules.sheafification α))

/-- The constant sheaf of modules functor `constSheafOfModules Λ J α` is additive. -/
instance additive_constSheafOfModules : (constSheafOfModules.{a} Λ J α).Additive :=
  letI _h := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (constSheafOfModules.{a} Λ J α)
  Functor.additive_of_preservesBinaryBiproducts _

end Exactness

section FiniteFree

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- The constant sheaf of modules on the finite free `Λ`-module `I → Λ` is isomorphic to the free
sheaf of modules on `I`. -/
def constSheafOfModulesPiIso (I : Type u) [Fintype I] [DecidableEq I] :
    (constSheafOfModules.{u} Λ J α).obj (ModuleCat.of Λ (I → Λ)) ≅
      _root_.SheafOfModules.free (R := Tensor.ringSheaf.{u, u, u} R) I :=
  (freeIsoMapFinitePi (constSheafOfModules.{u} Λ J α)
    (_root_.PresheafOfModules.sheafificationObjUnitIso α) I).symm

/-- The tensor product over `R` of the constant sheaf of modules on `I → Λ` with a sheaf of
modules `B` is isomorphic to the coproduct `∐_{i : I} B`. -/
def constSheafOfModulesPiTensorIso (I : Type u) [Fintype I] [DecidableEq I]
    (B : _root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} R)) :
    ((Tensor.sheafTensor.{u, u, u} R).obj
        ((constSheafOfModules.{u} Λ J α).obj (ModuleCat.of Λ (I → Λ)))).obj B ≅
      ∐ (fun _ : I => B) :=
  ((Tensor.sheafTensor.{u, u, u} R).flip.obj B).mapIso
      (constSheafOfModulesPiIso Λ R α I) ≪≫
    Strict.coproductUnitTensorIso R B I

end FiniteFree

/-! ### Finite type local constancy -/

section LocallyConstant

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ] (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

/-- The property of being locally constant of finite type, read on sheaves of modules over `R`
through the identification with sheaves of `Λ`-modules. -/
abbrev isFiniteTypeLocallyConstantModules :
    ObjectProperty (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} R)) :=
  ObjectProperty.inverseImage
    (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ :
      ObjectProperty (Sheaf J (ModuleCat.{u} Λ)))
    (toModuleSheaf.{u} Λ J α)

/-- The property `isFiniteTypeLocallyConstantModules Λ R α` is closed under finite coproducts. -/
instance isClosedUnderFiniteCoproducts_isFiniteTypeLocallyConstantModules :
    (isFiniteTypeLocallyConstantModules Λ R α).IsClosedUnderFiniteCoproducts :=
  ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape.{u}
    (fun _ _ => inferInstance)


omit [IsNoetherianRing Λ] in
/-- The constant sheaf of modules on a `Λ`-module of finite type is locally constant of finite
type. -/
theorem isFiniteTypeLocallyConstantModules_constSheafOfModules (N : ModuleCat.{u} Λ)
    (hN : ModuleCat.isFG Λ N) :
    isFiniteTypeLocallyConstantModules Λ R α ((constSheafOfModules.{u} Λ J α).obj N) :=
  ObjectProperty.prop_of_iso (IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ)
    ((constantSheafModuleSheafIso.{u} Λ J α).app N)
    (finiteTypeLocallyConstant_constantSheaf J N hN)

/-- If `B` is locally constant of finite type, then so is the tensor product over `R` of the
constant sheaf of modules on `I → Λ` with `B`, for a finite type `I`. -/
theorem isFiniteTypeLocallyConstantModules_sheafTensor_pi (I : Type u) [Finite I]
    (B : _root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} R))
    (hB : isFiniteTypeLocallyConstantModules Λ R α B) :
    isFiniteTypeLocallyConstantModules Λ R α
      (((Tensor.sheafTensor.{u, u, u} R).obj
        ((constSheafOfModules.{u} Λ J α).obj (ModuleCat.of Λ (I → Λ)))).obj B) := by
  classical
  have := Fintype.ofFinite I
  exact ObjectProperty.prop_of_iso (isFiniteTypeLocallyConstantModules Λ R α)
    (constSheafOfModulesPiTensorIso Λ R α I B).symm
    (ObjectProperty.prop_coproduct (isFiniteTypeLocallyConstantModules Λ R α)
      (fun _ : I => hB))

/-- The tensor product over `R` of the constant sheaf of modules on a finite free `Λ`-module `M`
with the constant sheaf of modules on a `Λ`-module `N` of finite type is locally constant of
finite type. -/
theorem isFiniteTypeLocallyConstantModules_sheafTensor_constSheafOfModules
    (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] [Module.Free Λ M] (hN : ModuleCat.isFG Λ N) :
    isFiniteTypeLocallyConstantModules Λ R α
      (((Tensor.sheafTensor.{u, u, u} R).obj ((constSheafOfModules.{u} Λ J α).obj M)).obj
        ((constSheafOfModules.{u} Λ J α).obj N)) := by
  classical
  let ι := Module.Free.ChooseBasisIndex Λ M
  let eM : M ≅ ModuleCat.of Λ (ULift.{u} (Fin (Fintype.card ι)) → Λ) :=
    LinearEquiv.toModuleIso
      (((Module.Free.chooseBasis Λ M).reindex (Fintype.equivFin ι)).equivFun.trans
        (LinearEquiv.funCongrLeft Λ Λ (Equiv.ulift.{u} (α := Fin (Fintype.card ι)))))
  refine ObjectProperty.prop_of_iso (isFiniteTypeLocallyConstantModules Λ R α)
    (((Tensor.sheafTensor.{u, u, u} R).flip.obj
        ((constSheafOfModules.{u} Λ J α).obj N)).mapIso
      ((constSheafOfModules.{u} Λ J α).mapIso eM)).symm ?_
  exact isFiniteTypeLocallyConstantModules_sheafTensor_pi Λ R α (ULift.{u} (Fin (Fintype.card ι))) _
    (isFiniteTypeLocallyConstantModules_constSheafOfModules Λ R α N hN)


omit [IsNoetherianRing Λ] in
/-- Applying `constSheafOfModules Λ J α` termwise to a cochain complex that is strictly `≤ a`
gives a cochain complex that is strictly `≤ a`. -/
theorem isStrictlyLE_mapHomologicalComplex_constSheafOfModules
    (P : CochainComplex (ModuleCat.{u} Λ) ℤ) (a : ℤ) [P.IsStrictlyLE a] :
    CochainComplex.IsStrictlyLE
      (((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a :=
  (CochainComplex.isStrictlyLE_iff _ a).2 fun i hi =>
    (constSheafOfModules.{u} Λ J α).map_isZero (P.isZero_of_isStrictlyLE a i hi)

/-- Let `P` and `Q` be bounded above cochain complexes of `Λ`-modules, with the terms of `P`
finite free and the terms of `Q` of finite type. Then every term of the total tensor complex over
`R` of their termwise constant sheaves of modules is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModules_mapBifunctor
    (P Q : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b]
    (hPfin : ∀ i : ℤ, Module.Finite Λ (P.X i)) (hPfree : ∀ i : ℤ, Module.Free Λ (P.X i))
    (hQ : ∀ i : ℤ, ModuleCat.isFG Λ (Q.X i)) (n : ℤ) :
    isFiniteTypeLocallyConstantModules Λ R α
      ((HomologicalComplex.mapBifunctor
        (((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((constSheafOfModules.{u} Λ J α).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
        (Tensor.sheafTensor.{u, u, u} R) (ComplexShape.up ℤ)).X n) := by
  have := isStrictlyLE_mapHomologicalComplex_constSheafOfModules Λ R α P a
  have := isStrictlyLE_mapHomologicalComplex_constSheafOfModules Λ R α Q b
  refine Stacks.ConstantSheaf.prop_mapBifunctor_of_isStrictlyLE
    (Tensor.sheafTensor.{u, u, u} R) _ _ a b _ (fun p q => ?_) n
  have := hPfin p
  have := hPfree p
  exact isFiniteTypeLocallyConstantModules_sheafTensor_constSheafOfModules Λ R α
    (P.X p) (Q.X q) (hQ q)

end LocallyConstant

end Stacks.ConstantRingModules

end
