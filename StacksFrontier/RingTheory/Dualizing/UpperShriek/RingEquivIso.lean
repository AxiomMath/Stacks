module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Transporting derived Hom and derived extension of scalars along ring isomorphisms

A ring isomorphism induces an equivalence of module categories, hence of derived categories, and
the functors attached to a ring homomorphism `f : B → C` are carried along it: for ring
isomorphisms `B' ≃ B` and `C' ≃ C` and the transported homomorphism
`f' = e_C⁻¹ ∘ f ∘ e_B : B' → C'`, both `RHom` and derived extension of scalars for `f'` are the
ones for `f` conjugated by the induced equivalences. A composite of derived extensions of scalars
is likewise the derived extension along the composite.

## Main definitions

* `StacksDraft.DerivedRingEquivIso.derivedRestrictionRingEquivIso` — restriction of scalars along
  `f`, read on derived categories, commutes with restriction along ring isomorphisms of the source
  and the target.
* `StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso` — `RHom` for `f'` is `RHom` for `f`
  followed by the equivalence induced by `e_C`.
* `StacksDraft.DerivedRingEquivIso.derivedExtensionCompIso` — a composite of derived extensions of
  scalars is the derived extension along the composite.
* `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso` and
  `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight` — derived extension of
  scalars transported along ring isomorphisms of the source and the target, and along one of the
  target alone.

## Implementation notes

The source and the target of `f` live in a ring universe `u`, while the rings isomorphic to them
live in `Type (max v u)` and all modules are taken in the module universe `max v u`; at `v = 0`
this is the single-universe statement, and the rings may be transported along `ULift.ringEquiv`.

Derived extension of scalars is not a single functor here but any model of it, presented as a
functor together with a comparison exhibiting it as a left derived functor of extension of
scalars.

The isomorphisms for `RHom` and for derived extension of scalars are obtained by uniqueness of
adjoints from `StacksDraft.DerivedRingEquivIso.derivedRestrictionRingEquivIso`.
-/

@[expose] public section

open CategoryTheory
open Dualizing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace StacksDraft.DerivedRingEquivIso

/-- Restriction of scalars along `f : B → C`, read on derived categories, commutes with
restriction along ring isomorphisms `B' ≃ B` and `C' ≃ C` of the source and the target. -/
noncomputable def derivedRestrictionRingEquivIso
    {B C : Type u} [CommRing B] [CommRing C]
    {B' C' : Type (max v u)} [CommRing B'] [CommRing C']
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C) :
    let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
    (ModuleCat.restrictScalars.{max v u, max v u, max v u} f').mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v u, u, max v u}
          eB.symm.toRingHom).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max v u, u, max v u}
          eC.symm.toRingHom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v u, u, u} f).mapDerivedCategory := by
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let rF := ModuleCat.restrictScalars.{max v u, u, u} f
  let rG := ModuleCat.restrictScalars.{max v u, max v u, max v u} f'
  let rB := ModuleCat.restrictScalars.{max v u, u, max v u} eB.symm.toRingHom
  let rC := ModuleCat.restrictScalars.{max v u, u, max v u} eC.symm.toRingHom
  have hcomp : f'.comp eB.symm.toRingHom = eC.symm.toRingHom.comp f := by
    ext x
    simp [f', RingHom.comp_apply]
  let e₁ : ModuleCat.restrictScalars.{max v u, u, max v u}
      (f'.comp eB.symm.toRingHom) ≅ rG ⋙ rB :=
    ModuleCat.restrictScalarsComp eB.symm.toRingHom f'
  let e₂ : ModuleCat.restrictScalars.{max v u, u, max v u}
      (eC.symm.toRingHom.comp f) ≅ rC ⋙ rF :=
    ModuleCat.restrictScalarsComp f eC.symm.toRingHom
  exact (mapDerivedCategoryComp rG rB).symm ≪≫
    mapDerivedCategoryNatIso (rG ⋙ rB)
      (ModuleCat.restrictScalars.{max v u, u, max v u}
        (f'.comp eB.symm.toRingHom)) e₁.symm ≪≫
    mapDerivedCategoryNatIso
      (ModuleCat.restrictScalars.{max v u, u, max v u}
        (f'.comp eB.symm.toRingHom))
      (ModuleCat.restrictScalars.{max v u, u, max v u}
        (eC.symm.toRingHom.comp f))
      (eqToIso (congrArg
        (ModuleCat.restrictScalars.{max v u, u, max v u}) hcomp)) ≪≫
    mapDerivedCategoryNatIso
      (ModuleCat.restrictScalars.{max v u, u, max v u}
        (eC.symm.toRingHom.comp f)) (rC ⋙ rF) e₂.symm ≪≫
    mapDerivedCategoryComp rC rF

/-- Derived Hom transported along ring isomorphisms of the source and the target: `RHom` for the
transported homomorphism is `RHom` for the original one followed by the induced equivalence of
derived categories. -/
noncomputable def derivedHomRingEquivIso
    {B C : Type u} [CommRing B] [CommRing C]
    {B' C' : Type (max v u)} [CommRing B'] [CommRing C']
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C) :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
    EB.functor ⋙ derivedHom.{max v u, 0} f' ≅
      derivedHom.{u, v} f ⋙ EC.functor := by
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let adjF := Classical.choice
    (restrictScalarsDerived_adj_derivedHom.{u, v} f)
  let adjF' := Classical.choice
    (restrictScalarsDerived_adj_derivedHom.{max v u, 0} f')
  let adjB := EB.symm.toAdjunction
  let adjC := EC.symm.toAdjunction
  let adj₁ := adjF'.comp adjB
  let adj₂ := adjC.comp adjF
  exact adj₁.rightAdjointUniq
    (adj₂.ofNatIsoLeft (derivedRestrictionRingEquivIso.{u, v} eB eC f).symm)

/-- A composite of derived extensions of scalars is the derived extension along the composite. -/
noncomputable def derivedExtensionCompIso
    {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* C) (g : C →+* D)
    (F : DerivedCategory (ModuleCat.{max v u} B) ⥤
      DerivedCategory (ModuleCat.{max v u} C))
    (alpha : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))]
    (G : DerivedCategory (ModuleCat.{max v u} C) ⥤
      DerivedCategory (ModuleCat.{max v u} D))
    (beta : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, max v u} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor beta
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} C) (ComplexShape.up ℤ))]
    (H : DerivedCategory (ModuleCat.{max v u} B) ⥤
      DerivedCategory (ModuleCat.{max v u} D))
    (gamma : DerivedCategory.Q ⋙ H ⟶
      (ModuleCat.extendScalars.{u, u, max v u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [H.IsLeftDerivedFunctor gamma
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))] :
    F ⋙ G ≅ H := by
  let adjF := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    f F alpha
  let adjG := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    g G beta
  let adjH := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    (g.comp f) H gamma
  let rF := ModuleCat.restrictScalars.{max v u} f
  let rG := ModuleCat.restrictScalars.{max v u} g
  let rComp := ModuleCat.restrictScalars.{max v u} (g.comp f)
  let eR : rComp.mapDerivedCategory ≅ rG.mapDerivedCategory ⋙ rF.mapDerivedCategory :=
    mapDerivedCategoryNatIso rComp (rG ⋙ rF) (ModuleCat.restrictScalarsComp f g) ≪≫
      mapDerivedCategoryComp rG rF
  exact (adjF.comp adjG).ofNatIsoRight eR.symm |>.leftAdjointUniq adjH

/-- Derived extension of scalars transported along ring isomorphisms of the source and the
target. -/
noncomputable def derivedExtensionRingEquivIso
    {B C : Type u} [CommRing B] [CommRing C]
    {B' C' : Type (max v u)} [CommRing B'] [CommRing C']
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C)
    (F : DerivedCategory (ModuleCat.{max v u} B) ⥤
      DerivedCategory (ModuleCat.{max v u} C))
    (alpha : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))]
    (G : DerivedCategory (ModuleCat.{max v u} B') ⥤
      DerivedCategory (ModuleCat.{max v u} C'))
    (beta : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{max v u, max v u, max v u}
        (eC.symm.toRingHom.comp (f.comp eB.toRingHom))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor beta
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B') (ComplexShape.up ℤ))] :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
    EB.functor ⋙ G ≅ F ⋙ EC.functor := by
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eB)
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max v u, u, max v u} eC)
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let adjF := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    f F alpha
  let adjG :=
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
      max v u, max v u, 0} f' G beta
  let adjEB := EB.toAdjunction
  let adjEC := EC.toAdjunction
  let adj₁ := adjEB.comp adjG
  let adj₂ := adjF.comp adjEC
  exact adj₁.ofNatIsoRight (derivedRestrictionRingEquivIso.{u, v} eB eC f)
    |>.leftAdjointUniq adj₂

/-- Derived extension of scalars transported along a ring isomorphism of the target. -/
noncomputable def derivedExtensionRingEquivIsoRight
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']
    (eC : C' ≃+* C) (f : B →+* C)
    (F : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} C))
    (alpha : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))]
    (G : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} C'))
    (beta : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, u}
        (eC.symm.toRingHom.comp (f.comp (RingEquiv.refl B).toRingHom))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor beta
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))] :
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} eC)
    G ≅ F ⋙ EC.functor := by
  let h := derivedExtensionRingEquivIso.{u, 0}
    (RingEquiv.refl B) eC f F alpha G beta
  exact (Functor.leftUnitor G).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryIdIso (B := B)).symm G ≪≫ h

end StacksDraft.DerivedRingEquivIso

end
