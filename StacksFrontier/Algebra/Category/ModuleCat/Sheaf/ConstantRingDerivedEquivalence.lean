module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The derived categories of sheaves of modules over a constant sheaf of rings

`Stacks.ConstantSheaf.constantRingModuleEquivalence` is an equivalence of abelian categories
`Sheaf J (ModuleCat R) ≌ SheafOfModules Osharp` for a sheaf of rings `Osharp` presented by the
constant presheaf of rings with value `R`. An equivalence of abelian categories is exact, so it
induces an equivalence of the unbounded derived categories

`D(Sheaf J (ModuleCat R)) ≌ D(SheafOfModules Osharp)`,

commuting with the shift and carrying distinguished triangles to distinguished triangles. This
is what lets a construction made on `D(SheafOfModules Osharp)` — such as the derived tensor
product of a ringed site — be read on `D(Sheaf J (ModuleCat R))`, where the locally constant
coefficients of Stacks 094G, 094H and 094I live.

## Main definitions

* `Stacks.ConstantSheaf.constantRingModuleDerivedFunctor` and
  `Stacks.ConstantSheaf.moduleSheafOfConstantRingDerivedFunctor`: the two induced functors on
  derived categories.
* `Stacks.ConstantSheaf.constantRingModuleDerivedEquivalence`: **the equivalence of derived
  categories**.

## Implementation notes

`CategoryTheory.Functor.mapDerivedCategory` already carries `CommShift ℤ` and `IsTriangulated`
instances in Mathlib, so nothing of that kind has to be proved here; what is proved is that the
induced functor is an equivalence, by
`Stacks.DerivedCategory.mapDerivedCategory_isEquivalence`, which reads the functor on
homological complexes as a localizer morphism between two localized equivalences.

`CategoryTheory.HasDerivedCategory.standard` is made a local instance; the two sides may sit in
different universes, which `CategoryTheory.Functor.mapDerivedCategory` permits.

## References

* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.DerivedCategory

/-- **An equivalence of abelian categories induces an equivalence of derived categories.** The
functor it induces on homological complexes is an equivalence which inverts exactly the
quasi-isomorphisms, hence a localized equivalence, and the derived categories are the
localizations. -/
theorem mapDerivedCategory_isEquivalence {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (e : A ≌ B) [e.functor.Additive] : e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let _ : Φ.functor.IsEquivalence :=
    (e.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let _ : Φ.IsInduced := ⟨by
    ext X Y f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f e.functor⟩
  let _ : Φ.IsLocalizedEquivalence := Φ.isLocalizedEquivalence_of_isInduced
  let _ : CatCommSq Φ.functor _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      e.functor.mapDerivedCategory := ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    e.functor.mapDerivedCategory

end Stacks.DerivedCategory

namespace Stacks.ConstantSheaf

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

variable {C : Type u} [Category.{v} C] {R : Type w} [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}}
  (a : ringPresheaf (constantRingPresheaf C R) ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
  [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
  [HasSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

attribute [local instance] HasDerivedCategory.standard

/-- Reading a presheaf of `R`-modules as a presheaf of modules over the constant presheaf of
rings is additive: it is the identity on the components of a morphism. -/
instance constantRingPresheafOfModules_additive :
    (constantRingPresheafOfModules C R).Additive where
  map_add := by intros; ext U x; rfl

/-- The functor of `Stacks.ConstantSheaf.constantRingModuleEquivalence`, from sheaves of
`R`-modules to sheaves of modules over `Osharp`, is additive. -/
instance constantRingModuleEquivalence_functor_additive :
    (constantRingModuleEquivalence J a).functor.Additive := by
  have : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp) a).Additive :=
    Functor.additive_of_preserves_binary_products _
  change (sheafOfModulesOfConstantRingFunctor J a).Additive
  unfold sheafOfModulesOfConstantRingFunctor
  infer_instance

/-- The inverse of `Stacks.ConstantSheaf.constantRingModuleEquivalence`, from sheaves of modules
over `Osharp` to sheaves of `R`-modules, is additive. -/
instance constantRingModuleEquivalence_inverse_additive :
    (constantRingModuleEquivalence J a).inverse.Additive :=
  Equivalence.inverse_additive _

/-- **Reading a sheaf of `R`-modules as a sheaf of modules over `Osharp`, on derived
categories.** -/
def constantRingModuleDerivedFunctor :
    DerivedCategory (Sheaf J (ModuleCat.{w} R)) ⥤
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
  (constantRingModuleEquivalence J a).functor.mapDerivedCategory

/-- **Restricting the scalars back to the constant ring `R`, on derived categories.** -/
def moduleSheafOfConstantRingDerivedFunctor :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} R)) :=
  (constantRingModuleEquivalence J a).inverse.mapDerivedCategory

/-- The functor `Stacks.ConstantSheaf.constantRingModuleDerivedFunctor` on derived categories is
an equivalence. -/
instance constantRingModuleDerivedFunctor_isEquivalence :
    (constantRingModuleDerivedFunctor J a).IsEquivalence :=
  Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (constantRingModuleEquivalence J a)

/-- **The derived category of sheaves of `R`-modules is the derived category of sheaves of
modules over a sheaf of rings presented by the constant presheaf of rings with value `R`.** An
equivalence of abelian categories is exact, so it induces an equivalence of derived categories;
Mathlib's `CategoryTheory.Functor.mapDerivedCategory` equips it with a shift commutation and
makes it triangulated. -/
def constantRingModuleDerivedEquivalence :
    DerivedCategory (Sheaf J (ModuleCat.{w} R)) ≌
      DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
  (constantRingModuleDerivedFunctor J a).asEquivalence

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The functor of `Stacks.ConstantSheaf.constantRingModuleDerivedEquivalence` is
`Stacks.ConstantSheaf.constantRingModuleDerivedFunctor`. -/
@[simp]
theorem constantRingModuleDerivedEquivalence_functor :
    (constantRingModuleDerivedEquivalence J a).functor =
      constantRingModuleDerivedFunctor J a :=
  rfl

section ConstantRingSheaf

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **The derived category of sheaves of `R`-modules is the derived category of sheaves of
modules over the constant sheaf of rings with value `R`.** -/
def constantSheafModuleDerivedEquivalence :
    DerivedCategory (Sheaf J (ModuleCat.{w} R)) ≌
      DerivedCategory
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingSheaf J R))) :=
  constantRingModuleDerivedEquivalence J (constantRingSheafMap J R)

end ConstantRingSheaf

end Stacks.ConstantSheaf

end
