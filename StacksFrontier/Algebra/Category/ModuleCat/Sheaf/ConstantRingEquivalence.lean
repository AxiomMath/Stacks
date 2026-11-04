module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules over a constant sheaf of rings are sheaves of modules

Let `(C, J)` be a site and `R` a commutative ring, and let `Osharp` be a sheaf of commutative
rings presented by the constant presheaf of rings with value `R`, that is, equipped with a
locally bijective comparison `a` from it. The bridge
`Stacks.ConstantSheaf.sheafOfModulesOfConstantRingFunctor` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingBridge`, which reads a sheaf of
`R`-modules as a sheaf of modules over `Osharp`, is **an equivalence of categories**

`Sheaf J (ModuleCat R) ≌ SheafOfModules Osharp`.

Its inverse is the restriction of scalars along `a`, which is the right adjoint already built
there.

## Main results

* `Stacks.ConstantSheaf.isIso_sheafOfModulesOfConstantRingAdjunction_counit_app`: the counit of
  the bridge adjunction is an isomorphism, because restricting the scalars back along a locally
  bijective comparison is fully faithful.
* `Stacks.ConstantSheaf.isIso_sheafOfModulesOfConstantRingAdjunction_unit_app`: the unit is an
  isomorphism, because the presheaf of abelian groups underlying a sheaf of `R`-modules is
  already a sheaf, so the sheafification that the bridge performs changes nothing.
* `Stacks.ConstantSheaf.constantRingModuleEquivalence`: **the equivalence**
  `Sheaf J (ModuleCat R) ≌ SheafOfModules Osharp`.
* `Stacks.ConstantSheaf.constantSheafModuleEquivalence`: the same for `Osharp` the constant
  sheaf of rings itself, which is the equivalence `Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲`.

## Implementation notes

Full faithfulness of the right adjoint is read off Mathlib's
`PresheafOfModules.sheafificationAdjunction`, whose right adjoint
`SheafOfModules.forget ⋙ PresheafOfModules.restrictScalars` is full and faithful because its
counit is an isomorphism; `Stacks.ConstantSheaf.moduleSheafOfConstantRing` is that functor read
through the on-the-nose reading
`Stacks.ConstantSheaf.constantRingPresheafOfModulesInverse` of a presheaf of modules over the
constant presheaf of rings as a presheaf of `R`-modules, and `sheafToPresheaf` is faithful, so
`CategoryTheory.Functor.FullyFaithful.ofCompFaithful` transfers it.

For the unit, the explicit isomorphism
`F ≅ moduleSheafOfConstantRing (sheafOfModulesOfConstantRing F)` is built from the sheafification
unit of `PresheafOfModules` at `ofConstantRingPresheaf F`: that unit is `CategoryTheory.toSheafify`
on underlying presheaves of abelian groups, and the presheaf of abelian groups underlying `F` is a
sheaf, so it is invertible, and `PresheafOfModules.toPresheaf` reflects isomorphisms.

Being an equivalence, the bridge is automatically additive and exact in both directions; no
separate exactness statement is needed.

## References

* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.ConstantSheaf

open AlgebraicGeometry.SheafOfModules (ringPresheaf)

variable {C : Type u} [Category.{v} C] {R : Type w} [CommRing R] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}}
  (a : ringPresheaf (constantRingPresheaf C R) ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
  [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]

/-- Restricting the scalars of a sheaf of modules over `Osharp` back to the constant ring `R` is
**fully faithful**: after composing with the faithful `sheafToPresheaf` it is Mathlib's right
adjoint `SheafOfModules.forget ⋙ PresheafOfModules.restrictScalars a` followed by the inverse of
the on-the-nose reading of a presheaf of `R`-modules as a presheaf of modules over the constant
presheaf of rings. -/
def moduleSheafOfConstantRingFullyFaithful :
    (moduleSheafOfConstantRing J a).FullyFaithful := by
  have h : moduleSheafOfConstantRing J a ⋙ sheafToPresheaf J (ModuleCat.{w} R) =
      SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⋙
        PresheafOfModules.restrictScalars a ⋙ constantRingPresheafOfModulesInverse C R :=
    rfl
  refine Functor.FullyFaithful.ofCompFaithful (G := sheafToPresheaf J (ModuleCat.{w} R)) ?_
  rw [h]
  exact (Functor.FullyFaithful.ofFullyFaithful
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) ⋙
        PresheafOfModules.restrictScalars a)).comp
    (constantRingPresheafEquivalence C R).fullyFaithfulInverse

/-- Restriction of scalars from `Osharp` to `R` is a full functor. -/
instance moduleSheafOfConstantRing_full : (moduleSheafOfConstantRing J a).Full :=
  (moduleSheafOfConstantRingFullyFaithful J a).full

/-- Restriction of scalars from `Osharp` to `R` is a faithful functor. -/
instance moduleSheafOfConstantRing_faithful : (moduleSheafOfConstantRing J a).Faithful :=
  (moduleSheafOfConstantRingFullyFaithful J a).faithful

variable [HasWeakSheafify J (ModuleCat.{w} R)]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- **The counit of the bridge adjunction is an isomorphism**, since its right adjoint
`Stacks.ConstantSheaf.moduleSheafOfConstantRing` is fully faithful. -/
instance isIso_sheafOfModulesOfConstantRingAdjunction_counit_app
    (S : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :
    IsIso ((sheafOfModulesOfConstantRingAdjunction J a).counit.app S) :=
  inferInstance

/-- The sheafification unit of presheaves of modules at a sheaf of `R`-modules, read over the
constant presheaf of rings, **is an isomorphism**: on underlying presheaves of abelian groups it
is `CategoryTheory.toSheafify`, and the presheaf of abelian groups underlying a sheaf of
`R`-modules is a sheaf. -/
instance isIso_presheafOfModules_sheafificationAdjunction_unit_app_ofConstantRingPresheaf
    (F : Sheaf J (ModuleCat.{w} R)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction a).unit.app
      (ofConstantRingPresheaf F.obj)) := by
  have hP : Presheaf.IsSheaf J (ofConstantRingPresheaf F.obj).presheaf :=
    GrothendieckTopology.HasSheafCompose.isSheaf
      (F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) F.obj F.property
  have h : IsIso ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction a).unit.app
        (ofConstantRingPresheaf F.obj))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.isIso_toSheafify J hP
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf
    (ringPresheaf (constantRingPresheaf C R)))

/-- A sheaf of `R`-modules **is recovered** from its reading as a sheaf of modules over
`Osharp`: the sheafification the bridge performs does not change the sections, so restricting
the scalars back gives the sheaf one started with. -/
def selfIsoModuleSheafOfConstantRing (F : Sheaf J (ModuleCat.{w} R)) :
    F ≅ (moduleSheafOfConstantRing J a).obj
      ((sheafOfModulesOfConstantRingFunctor J a).obj F) :=
  (sheafToPresheaf J (ModuleCat.{w} R)).preimageIso
    ((constantRingPresheafOfModulesInverse C R).mapIso
      (asIso ((PresheafOfModules.sheafificationAdjunction a).unit.app
        (ofConstantRingPresheaf F.obj))))

/-- **The unit of the bridge adjunction is an isomorphism**, by
`Stacks.ConstantSheaf.selfIsoModuleSheafOfConstantRing`. -/
instance isIso_sheafOfModulesOfConstantRingAdjunction_unit_app
    (F : Sheaf J (ModuleCat.{w} R)) :
    IsIso ((sheafOfModulesOfConstantRingAdjunction J a).unit.app F) :=
  Adjunction.isIso_unit_app_of_iso _ (selfIsoModuleSheafOfConstantRing J a F)

/-- **Sheaves of `R`-modules are the same thing as sheaves of modules over a sheaf of rings
presented by the constant presheaf of rings with value `R`.** The equivalence is the bridge
`Stacks.ConstantSheaf.sheafOfModulesOfConstantRingFunctor`, with restriction of scalars
`Stacks.ConstantSheaf.moduleSheafOfConstantRing` as its inverse; both unit and counit of the
adjunction between them are isomorphisms. -/
def constantRingModuleEquivalence :
    Sheaf J (ModuleCat.{w} R) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  (sheafOfModulesOfConstantRingAdjunction J a).toEquivalence

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J (ModuleCat.{w} R)] in
/-- The functor of `constantRingModuleEquivalence` is `sheafOfModulesOfConstantRingFunctor`. -/
@[simp]
theorem constantRingModuleEquivalence_functor :
    (constantRingModuleEquivalence J a).functor = sheafOfModulesOfConstantRingFunctor J a :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J (ModuleCat.{w} R)] in
/-- The inverse of `constantRingModuleEquivalence` is `moduleSheafOfConstantRing`. -/
@[simp]
theorem constantRingModuleEquivalence_inverse :
    (constantRingModuleEquivalence J a).inverse = moduleSheafOfConstantRing J a :=
  rfl

section ConstantRingSheaf

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **Sheaves of `R`-modules are the same thing as sheaves of modules over the constant sheaf of
rings with value `R`.** This is
`Stacks.ConstantSheaf.constantRingModuleEquivalence` at the constant sheaf of rings itself,
which the constant presheaf of rings presents by
`Stacks.ConstantSheaf.isLocallyInjective_constantRingSheafMap` and
`Stacks.ConstantSheaf.isLocallySurjective_constantRingSheafMap`. -/
def constantSheafModuleEquivalence :
    Sheaf J (ModuleCat.{w} R) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingSheaf J R)) :=
  constantRingModuleEquivalence J (constantRingSheafMap J R)

end ConstantRingSheaf

end Stacks.ConstantSheaf

end
