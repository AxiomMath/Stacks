module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso

/-!
# Transport along ring isomorphisms within one ring universe, at a larger module universe

For commutative rings `B`, `C`, `B'`, `C'` in one universe `u`, ring isomorphisms `B' ≃ B`,
`C' ≃ C` and a ring homomorphism `f : B → C`, restriction of scalars, derived Hom and derived
extension of scalars on derived categories of modules in the universe `max v u` are transported
along the induced equivalences of derived categories.

## Main definitions

* `StacksDraft.DerivedRingEquivIso.mapDerivedCategoryIdIsoLarge`: restriction of scalars along
  the identity induces the identity on derived categories.
* `StacksDraft.DerivedRingEquivIso.derivedRestrictionRingEquivIsoLarge`: restriction of scalars
  on derived categories commutes with restriction along ring isomorphisms.
* `StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIsoLarge`: `RHom` transported along ring
  isomorphisms.
* `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoLarge` and
  `StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRightLarge`: derived extension of
  scalars transported along ring isomorphisms.
-/

@[expose] public section

open CategoryTheory
open Dualizing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace StacksDraft.DerivedRingEquivIso

/-- Restriction of scalars along the identity of `B` induces the identity of `D(B)`, at the
module universe `max v u`. -/
noncomputable def mapDerivedCategoryIdIsoLarge {B : Type u} [CommRing B] :
    (ModuleCat.restrictScalars.{max v u} (RingHom.id B)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{max v u} B)) :=
  let F := 𝟭 (ModuleCat.{max v u} B)
  let η : DerivedCategory.Q ⋙ F.mapDerivedCategory ≅ DerivedCategory.Q :=
    F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q
  let e := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory) DerivedCategory.Q
    F.mapDerivedCategory (𝟭 (DerivedCategory (ModuleCat.{max v u} B))) η
  mapDerivedCategoryNatIso (ModuleCat.restrictScalars.{max v u} (RingHom.id B)) F
    (ModuleCat.restrictScalarsId B) ≪≫ e

/-- Restriction of scalars along `f : B → C`, read on derived categories, commutes with
restriction along ring isomorphisms `B' ≃ B` and `C' ≃ C` of the source and the target, all four
rings in one universe. -/
noncomputable def derivedRestrictionRingEquivIsoLarge
    {B C B' C' : Type u} [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C) :
    let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
    (ModuleCat.restrictScalars.{max v u, u, u} f').mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v u, u, u} eB.symm.toRingHom).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max v u, u, u} eC.symm.toRingHom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v u, u, u} f).mapDerivedCategory := by
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let rF := ModuleCat.restrictScalars.{max v u, u, u} f
  let rG := ModuleCat.restrictScalars.{max v u, u, u} f'
  let rB := ModuleCat.restrictScalars.{max v u, u, u} eB.symm.toRingHom
  let rC := ModuleCat.restrictScalars.{max v u, u, u} eC.symm.toRingHom
  have hcomp : f'.comp eB.symm.toRingHom = eC.symm.toRingHom.comp f := by
    ext x
    simp [f', RingHom.comp_apply]
  let e₁ : ModuleCat.restrictScalars.{max v u, u, u}
      (f'.comp eB.symm.toRingHom) ≅ rG ⋙ rB :=
    ModuleCat.restrictScalarsComp eB.symm.toRingHom f'
  let e₂ : ModuleCat.restrictScalars.{max v u, u, u}
      (eC.symm.toRingHom.comp f) ≅ rC ⋙ rF :=
    ModuleCat.restrictScalarsComp f eC.symm.toRingHom
  exact (mapDerivedCategoryComp rG rB).symm ≪≫
    mapDerivedCategoryNatIso (rG ⋙ rB)
      (ModuleCat.restrictScalars.{max v u, u, u}
        (f'.comp eB.symm.toRingHom)) e₁.symm ≪≫
    mapDerivedCategoryNatIso
      (ModuleCat.restrictScalars.{max v u, u, u}
        (f'.comp eB.symm.toRingHom))
      (ModuleCat.restrictScalars.{max v u, u, u}
        (eC.symm.toRingHom.comp f))
      (eqToIso (congrArg
        (ModuleCat.restrictScalars.{max v u, u, u}) hcomp)) ≪≫
    mapDerivedCategoryNatIso
      (ModuleCat.restrictScalars.{max v u, u, u}
        (eC.symm.toRingHom.comp f)) (rC ⋙ rF) e₂.symm ≪≫
    mapDerivedCategoryComp rC rF

/-- Derived Hom transported along ring isomorphisms of the source and the target, all four rings
in one universe: `RHom` for the transported homomorphism is `RHom` for the original one followed
by the induced equivalence of derived categories. -/
noncomputable def derivedHomRingEquivIsoLarge
    {B C B' C' : Type u} [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    (eB : B' ≃+* B) (eC : C' ≃+* C) (f : B →+* C) :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
    let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
    EB.functor ⋙ derivedHom.{u, v} f' ≅ derivedHom.{u, v} f ⋙ EC.functor := by
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eB)
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let adjF := Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v} f)
  let adjF' := Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v} f')
  let adjB := EB.symm.toAdjunction
  let adjC := EC.symm.toAdjunction
  let adj₁ := adjF'.comp adjB
  let adj₂ := adjC.comp adjF
  exact adj₁.rightAdjointUniq
    (adj₂.ofNatIsoLeft (derivedRestrictionRingEquivIsoLarge.{u, v} eB eC f).symm)

/-- Derived extension of scalars transported along ring isomorphisms of the source and the
target, all four rings in one universe. -/
noncomputable def derivedExtensionRingEquivIsoLarge
    {B C B' C' : Type u} [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
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
      (ModuleCat.extendScalars.{u, u, max v u}
        (eC.symm.toRingHom.comp (f.comp eB.toRingHom))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor beta
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B') (ComplexShape.up ℤ))] :
    let EB := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eB)
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
    EB.functor ⋙ G ≅ F ⋙ EC.functor := by
  let EB := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eB)
  let EC := mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
  let f' := eC.symm.toRingHom.comp (f.comp eB.toRingHom)
  let adjF := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    f F alpha
  let adjG := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v}
    f' G beta
  let adjEB := EB.toAdjunction
  let adjEC := EC.toAdjunction
  let adj₁ := adjEB.comp adjG
  let adj₂ := adjF.comp adjEC
  exact adj₁.ofNatIsoRight (derivedRestrictionRingEquivIsoLarge.{u, v} eB eC f)
    |>.leftAdjointUniq adj₂

/-- Derived extension of scalars transported along a ring isomorphism of the target, all rings in
one universe. -/
noncomputable def derivedExtensionRingEquivIsoRightLarge
    {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']
    (eC : C' ≃+* C) (f : B →+* C)
    (F : DerivedCategory (ModuleCat.{max v u} B) ⥤ DerivedCategory (ModuleCat.{max v u} C))
    (alpha : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))]
    (G : DerivedCategory (ModuleCat.{max v u} B) ⥤ DerivedCategory (ModuleCat.{max v u} C'))
    (beta : DerivedCategory.Q ⋙ G ⟶
      (ModuleCat.extendScalars.{u, u, max v u}
        (eC.symm.toRingHom.comp (f.comp (RingEquiv.refl B).toRingHom))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor beta
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} B) (ComplexShape.up ℤ))] :
    let EC := mapDerivedCategoryEquivalenceOfEquivalence
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, max v u} eC)
    G ≅ F ⋙ EC.functor := by
  let h := derivedExtensionRingEquivIsoLarge.{u, v}
    (RingEquiv.refl B) eC f F alpha G beta
  exact (Functor.leftUnitor G).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryIdIsoLarge.{u, v} (B := B)).symm G ≪≫ h

end StacksDraft.DerivedRingEquivIso
