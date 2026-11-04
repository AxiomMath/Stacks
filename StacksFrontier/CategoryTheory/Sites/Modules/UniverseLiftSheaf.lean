module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLift

/-!
# Sheaves of modules along an equivalence of sites, with a change of ring universe

Let `e : C ≌ D` be an equivalence of categories carrying Grothendieck topologies `J` and `K`
for which both `e.functor` and `e.inverse` are continuous (for instance
`K = e.inverse.inducedTopology J`). Let `R` be a sheaf of rings on `(C, J)` and `R'` a sheaf of
rings on `(D, K)`, with section rings in possibly different universes, and let
`T : RingTransport e R.obj R'.obj` be a natural family of ring isomorphisms
`R'(Y) ≃+* R(e⁻¹ Y)`. The equivalence of presheaves of modules
`Stacks.UniverseLift.RingTransport.equivalence` preserves the sheaf condition in both
directions, so it restricts to an equivalence

  `SheafOfModules.{m} R ≌ SheafOfModules.{m} R'`.

## Main definitions

* `Stacks.UniverseLift.RingTransport.sheafFunctor`: the transport of sheaves of modules.
* `Stacks.UniverseLift.RingTransport.sheafEquivalence`: the induced equivalence of categories of
  sheaves of modules.

## Main results

* `Stacks.UniverseLift.RingTransport.sheafFunctorCompForget`: the transport commutes with the
  forgetful functors to presheaves of modules, on the nose.
* `Stacks.UniverseLift.RingTransport.sheafFunctorCompEvaluation`: evaluating the transport at
  `Y` is evaluating at `e⁻¹ Y` and restricting scalars along the ring isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite

universe m v₁ v₂ u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift.RingTransport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {e : C ≌ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{r₁}} {R' : Sheaf K RingCat.{r₂}} (T : RingTransport e R.obj R'.obj)

section

variable [e.inverse.IsContinuous K J]

/-- The transport of a presheaf of modules whose underlying abelian presheaf is a `J`-sheaf is
a `K`-sheaf: its underlying abelian presheaf is the precomposition with `e⁻¹`. -/
lemma isSheaf_functor_obj (M : PresheafOfModules.{m} R.obj)
    (hM : Presheaf.IsSheaf J M.presheaf) :
    Presheaf.IsSheaf K (T.functor.obj M).presheaf :=
  e.inverse.op_comp_isSheaf K J ⟨M.presheaf, hM⟩

/-- **The transport of sheaves of modules along a ring transport.** -/
@[simps obj_val map_val]
noncomputable def sheafFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{m} R' where
  obj M := ⟨T.functor.obj M.val, T.isSheaf_functor_obj M.val M.isSheaf⟩
  map φ := ⟨T.functor.map φ.val⟩

/-- The transport of sheaves of modules commutes with the forgetful functors to presheaves of
modules. -/
noncomputable def sheafFunctorCompForget :
    T.sheafFunctor ⋙ SheafOfModules.forget.{m} R' ≅ SheafOfModules.forget.{m} R ⋙ T.functor :=
  Iso.refl _

/-- Evaluating the transport of a sheaf of modules at `Y` is evaluating it at `e⁻¹ Y` and
restricting scalars along `R'(Y) ≃+* R(e⁻¹ Y)`. -/
noncomputable def sheafFunctorCompEvaluation (Y : Dᵒᵖ) :
    T.sheafFunctor ⋙ SheafOfModules.evaluation.{m} R' Y ≅
      SheafOfModules.evaluation.{m} R (e.inverse.op.obj Y) ⋙
        ModuleCat.restrictScalars (T.iso Y).toRingHom :=
  Iso.refl _

/-- The transport of sheaves of modules is additive. -/
instance sheafFunctor_additive :
    (T.sheafFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').Additive where

end

variable [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]

/-- **The equivalence of categories of sheaves of modules induced by a ring transport** along an
equivalence of sites. Its functor is `RingTransport.sheafFunctor` and its inverse is the
transport along the opposite ring transport `RingTransport.symm`. -/
noncomputable def sheafEquivalence : SheafOfModules.{m} R ≌ SheafOfModules.{m} R' :=
  letI : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  CategoryTheory.Equivalence.mk T.sheafFunctor T.symm.sheafFunctor
    (NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso (T.unitIso.app M.val))
      (fun φ ↦ SheafOfModules.hom_ext (T.unitIso.hom.naturality φ.val)))
    (NatIso.ofComponents
      (fun M ↦ (SheafOfModules.fullyFaithfulForget R').preimageIso (T.counitIso.app M.val))
      (fun φ ↦ SheafOfModules.hom_ext (T.counitIso.hom.naturality φ.val)))

/-- The functor of the equivalence of sheaves of modules is the transport. -/
@[simp]
lemma sheafEquivalence_functor :
    (T.sheafEquivalence : SheafOfModules.{m} R ≌ SheafOfModules.{m} R').functor =
      T.sheafFunctor :=
  rfl

/-- The inverse of the equivalence of sheaves of modules is the transport along the
opposite ring transport. -/
lemma sheafEquivalence_inverse :
    (T.sheafEquivalence : SheafOfModules.{m} R ≌ SheafOfModules.{m} R').inverse =
      letI : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
      T.symm.sheafFunctor :=
  rfl

/-- The functor of the equivalence of sheaves of modules is additive. -/
instance sheafEquivalence_functor_additive :
    (T.sheafEquivalence : SheafOfModules.{m} R ≌ SheafOfModules.{m} R').functor.Additive :=
  inferInstanceAs (T.sheafFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').Additive

/-- The transport of sheaves of modules is an equivalence of categories. -/
instance sheafFunctor_isEquivalence :
    (T.sheafFunctor : SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').IsEquivalence :=
  T.sheafEquivalence.isEquivalence_functor

end Stacks.UniverseLift.RingTransport
