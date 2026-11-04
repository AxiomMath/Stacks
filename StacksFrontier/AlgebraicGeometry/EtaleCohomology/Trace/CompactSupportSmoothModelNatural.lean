module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModel

/-!
# Naturality of `H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))`

The identification of `Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso` of the
cohomology of Remark 03UI (2) with the cohomology of the smooth projective model `C` of the
geometric curve is natural in the sheaf `F` of `Λ`-modules on `X`. This file packages the complex
`RΓ_c(X_k̄, -)` as a functor of bounded below complexes and proves the naturality, one constituent
at a time.

## Main definitions

* `Stacks.EtaleCohomology.galoisCompactSupportCohomologyMap` — the morphism
  `RΓ_c(X_k̄, K) ⟶ RΓ_c(X_k̄, K')` induced by `K ⟶ K'`.

## Main results

* `Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso_hom_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Map

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The map `RΓ_c(X_k̄, K) ⟶ RΓ_c(X_k̄, K')` induced by a morphism of bounded below complexes of
sheaves of `Λ`-modules on `X`**: extension by zero, restriction to `X̄_k̄` and derived global
sections, applied to the morphism. -/
public abbrev galoisCompactSupportCohomologyMap
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (φ : K ⟶ K') :
    galoisCompactSupportCohomology.{u, r} Λ f j kbar K ⟶
      galoisCompactSupportCohomology.{u, r} Λ f j kbar K' :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).map
    (DerivedCategory.Plus.Q.map
      ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map φ)))

end Map

section SinglePlus

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] (F : A ⥤ B)
  [F.PreservesZeroMorphisms]

/-- `F(M[0]) ≅ F(M)[0]` is natural in `M`. -/
theorem mapCochainComplexPlusSinglePlusIso_hom_naturality {M M' : A} (g : M ⟶ M') :
    F.mapCochainComplexPlus.map ((Stacks.DerivedIndexing.singlePlusFunctor A 0).map g) ≫
        (mapCochainComplexPlusSinglePlusIso F M').hom =
      (mapCochainComplexPlusSinglePlusIso F M).hom ≫
        (Stacks.DerivedIndexing.singlePlusFunctor B 0).map (F.map g) := by
  ext : 1
  exact (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.naturality g

end SinglePlus

section ExtensionByZero

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

omit [Mono j] [Mono j'] in
/-- `j_!(f_* M) ⟶ f̄_*(j'_! M)` is natural in `M`. -/
theorem extensionByZeroIntegralDirectImageMap_naturality {M M' : EtaleModules.{u, 0} Λ V}
    (g : M ⟶ M') :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleDirectImage.{u, 0} Λ f).map g) ≫
        extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M' =
      extensionByZeroIntegralDirectImageMap Λ j j' f fb sq M ≫
        (etaleModuleDirectImage.{u, 0} Λ fb).map ((etaleModuleExtensionByZero.{u, 0} Λ j').map g)
            := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [extensionByZeroIntegralDirectImageMap, Equiv.apply_symm_apply]
  have hu : g ≫ (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M' =
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M ≫
        (etaleModuleRestriction.{u, 0} Λ j').map ((etaleModuleExtensionByZero.{u, 0} Λ j').map g) :=
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.naturality g
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc, Category.assoc]
  exact congrArg (_ ≫ ·) ((restrictionIntegralDirectImageIso Λ j j' f fb sq).hom.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ j').map g))

end ExtensionByZero

section Squares

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `H^i_c(X_k̄, F) ≅ H^i(X̄_k̄, (j_! F)|_{X̄_k̄})` is natural in `F`. -/
theorem galoisCompactSupportSingleIso_hom_naturality {F F' : EtaleModules.{u, r} Λ X}
    (g : F ⟶ F') (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
        (galoisCompactSupportCohomologyMap Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
        (galoisCompactSupportSingleIso f j kbar Λ F' i).hom =
      (galoisCompactSupportSingleIso f j kbar Λ F i).hom ≫
        ((etaleModuleGlobalSections.{u, r} Λ (pullback j.toBase (specAlgebraMap k
            kbar))).rightDerivedPlus
            i).map
          ((etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).map g)) := by
  let P := (etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase (specAlgebraMap k kbar)))
  let E := etaleModuleExtensionByZero.{u, r} Λ j.immersion
  have hc : P.mapCochainComplexPlus.map (E.mapCochainComplexPlus.map
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
      P.mapCochainComplexPlus.map (mapCochainComplexPlusSinglePlusIso E F').hom ≫
        (mapCochainComplexPlusSinglePlusIso P (E.obj F')).hom =
      (P.mapCochainComplexPlus.map (mapCochainComplexPlusSinglePlusIso E F).hom ≫
        (mapCochainComplexPlusSinglePlusIso P (E.obj F)).hom) ≫
        (Stacks.DerivedIndexing.singlePlusFunctor _ 0).map (P.map (E.map g)) := by
    rw [← Functor.map_comp_assoc, mapCochainComplexPlusSinglePlusIso_hom_naturality,
      Functor.map_comp_assoc, mapCochainComplexPlusSinglePlusIso_hom_naturality, Category.assoc]
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i
  let R := etaleModuleDerivedGlobalSections.{u, r} Λ (pullback j.toBase (specAlgebraMap k kbar))
  let Q := DerivedCategory.Plus.Q (C := EtaleModules.{u, r} Λ (pullback j.toBase (specAlgebraMap k
      kbar)))
  exact (H.map_commSq ⟨(R.map_commSq ⟨(Q.map_commSq ⟨hc⟩).w⟩).w⟩).w

omit [Field kbar] [Algebra k kbar] in
/-- `H^i(B, g_* H) ≅ H^i(A, H)` is natural in `H`. -/
theorem integralDirectImageCohomologyIso_hom_naturality {A B : Scheme.{u}} (g : A ⟶ B)
    [IsIntegralHom g] {H H' : EtaleModules.{u, r} Λ A} (h : H ⟶ H') (i : ℤ) :
    ((etaleModuleGlobalSections.{u, r} Λ B).rightDerivedPlus i).map
        ((etaleModuleDirectImage.{u, r} Λ g).map h) ≫
        (integralDirectImageCohomologyIso Λ g H' i).hom =
      (integralDirectImageCohomologyIso Λ g H i).hom ≫
        ((etaleModuleGlobalSections.{u, r} Λ A).rightDerivedPlus i).map h := by
  let Hm := DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i
  let RB := etaleModuleDerivedGlobalSections.{u, r} Λ B
  let e := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (etaleModuleDirectImage.{u, r} Λ g) 0
  let c := (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).symm
  have hc : RB.map ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((etaleModuleDirectImage.{u, r} Λ g).map h)) ≫ (RB.map (e.hom.app H') ≫ c.hom.app _) =
      (RB.map (e.hom.app H) ≫ c.hom.app _) ≫
        (etaleModuleDerivedGlobalSections.{u, r} Λ A).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map h) := by
    exact (CommSq.vert_comp (RB.map_commSq ⟨e.hom.naturality h⟩)
      ⟨c.hom.naturality ((DerivedCategory.Plus.singleFunctor _ 0).map h)⟩).w
  exact (Hm.map_commSq ⟨hc⟩).w

end Squares

section SmoothModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- `j'_! G ≅ f̄_* j_{C!} G` is natural in `G`. -/
theorem extensionByZeroGeometricSmoothModelIso_hom_naturality
    {G G' : EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar))} (h : G ⟶ G') :
    (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).map h
        ≫
        (extensionByZeroGeometricSmoothModelIso f j kbar Λ G').hom =
      (extensionByZeroGeometricSmoothModelIso f j kbar Λ G).hom ≫
        (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map h) := by
  let C := geometricSmoothModel f j kbar
  let J := etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)
  have s1 := J.map_commSq
    ⟨(etaleModuleDirectImageIdIso Λ (pullback f (specAlgebraMap k kbar))).inv.naturality h⟩
  have s2 := extensionByZeroIntegralDirectImageMap_naturality Λ
    (compactificationFieldBaseChangeImmersion f j kbar) C.j (𝟙 _) C.fb C.isPullback.flip h
  exact (CommSq.vert_comp s1 ⟨s2⟩).w

/-- The last two constituents of `galoisCompactSupportSmoothModelIso` are natural. -/
theorem smoothModelTail_naturality
    {G G' : EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar))} (h : G ⟶ G') (i : ℤ) :
    ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
        kbar))).rightDerivedPlus
        i).map ((etaleModuleExtensionByZero.{u, 0} Λ
          (compactificationFieldBaseChangeImmersion f j kbar)).map h) ≫
      ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
          kbar))).rightDerivedPlus
          i).map (extensionByZeroGeometricSmoothModelIso f j kbar Λ G').hom ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom =
    ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
        kbar))).rightDerivedPlus
          i).map (extensionByZeroGeometricSmoothModelIso f j kbar Λ G).hom ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom ≫
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).map
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map h) := by
  let R := (etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
      kbar))).rightDerivedPlus i
  have q3 := R.map_commSq
    ⟨extensionByZeroGeometricSmoothModelIso_hom_naturality f j kbar Λ h⟩
  have q4 := integralDirectImageCohomologyIso_hom_naturality.{u, 0} Λ
    (geometricSmoothModel f j kbar).fb
    ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map h) i
  exact (CommSq.vert_comp q3 ⟨q4⟩).w

/-- The four constituents of `galoisCompactSupportSmoothModelIso`. -/
lemma galoisCompactSupportSmoothModelIso_hom (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    (galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom =
      (galoisCompactSupportSingleIso f j kbar Λ F i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
            kbar))).rightDerivedPlus
            i).map ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.app F) ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
            kbar))).rightDerivedPlus
            i).map (extensionByZeroGeometricSmoothModelIso f j kbar Λ
              ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj
                  F)).hom ≫
        (integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i).hom :=
  rfl

/-- **`H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))` is natural in `F`.** -/
theorem galoisCompactSupportSmoothModelIso_hom_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (g : F ⟶ F') (i : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        (galoisCompactSupportCohomologyMap Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g)) ≫
        (galoisCompactSupportSmoothModelIso f j kbar Λ F' i).hom =
      (galoisCompactSupportSmoothModelIso f j kbar Λ F i).hom ≫
        ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
            i).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g)) :=
                by
  have q1 := galoisCompactSupportSingleIso_hom_naturality Λ f j kbar g i
  let R := (etaleModuleGlobalSections.{u, 0} Λ (pullback j.toBase (specAlgebraMap k
      kbar))).rightDerivedPlus i
  have q2 : R.map ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase
      (specAlgebraMap k kbar))).map ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)) ≫
      R.map ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.app F') =
      R.map ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.app F) ≫
        R.map ((etaleModuleExtensionByZero.{u, 0} Λ
          (compactificationFieldBaseChangeImmersion f j kbar)).map
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map g)) :=
    (R.map_commSq ⟨(compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.naturality
      g⟩).w
  have q34 := smoothModelTail_naturality f j kbar Λ ((etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst f (specAlgebraMap k kbar))).map g) i
  have q := (CommSq.vert_comp (CommSq.vert_comp ⟨q1⟩ ⟨q2⟩) ⟨q34⟩).w
  rw [galoisCompactSupportSmoothModelIso_hom, galoisCompactSupportSmoothModelIso_hom]
  simp only [Category.assoc] at q ⊢
  exact q

end SmoothModel

end Stacks.EtaleCohomology

end
