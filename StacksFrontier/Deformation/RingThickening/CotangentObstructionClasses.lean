module

public import StacksFrontier.Deformation.RingThickening.CotangentObstructionBaseChange
public import StacksFrontier.Deformation.RingThickening.CotangentObstructionCocycle
public import StacksFrontier.Deformation.RingThickening.CotangentObstructionTriangle
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange

/-!
# First extension classes out of `L_{B/A'}` and `L_{A/A'} ⊗_A B`

Let `A' → A → B` be ring maps and `N` a `B`-module. This file identifies
`Ext¹_B(L_{B/A'}, N)` and `Ext¹_B(L_{A/A'} ⊗_A B, N)` with the cokernels
`Hom(J/J², N) / Hom(Ω, N)` of the canonical presentations `A'[B] → B` and `A'[A] → A`, by
explicit cocycles: the class of a conormal functional is that of the cochain map it defines on
the naive cotangent complex, pulled back along `L → NL`.

## Main definitions

* `Stacks.Deformation.SquareZeroExtensionProblem.towerCocycleMap`,
  `Stacks.Deformation.SquareZeroExtensionProblem.baseCocycleMap`: the maps `L_{B/A'} → NL_{B/A'}`
  and `L_{A/A'} ⊗_A B → NL_{A/A'} ⊗_A B`, with the naive cotangent complexes written as mapping
  cones and everything lifted to the module universe of `cotangentExt`.

## Main results

* `Stacks.bijective_comp_of_isIso_truncGE`: precomposition with a `τ_{≥ n}`-isomorphism is
  bijective on maps into an object lying in degrees `≥ n`.
* `isIso_truncGE_map_Q_towerCocycleMap`, `isIso_truncGE_map_Q_baseCocycleMap`: the two maps are
  isomorphisms after `τ_{≥ -1}`.

## References

* [Stacks Project, Tag 08SP](https://stacks.math.columbia.edu/tag/08SP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₄

namespace Stacks

/-- **Precomposition with a `τ_{≥ n}`-isomorphism is bijective** on maps into an object lying in
degrees `≥ n`: both sides are maps out of the truncations. -/
theorem bijective_comp_of_isIso_truncGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {X Y Z : DerivedCategory C} (f : X ⟶ Y) (n : ℤ)
    [IsIso ((DerivedCategory.TStructure.t.truncGE n).map f)]
    [DerivedCategory.TStructure.t.IsGE Z n] :
    Function.Bijective (fun g : Y ⟶ Z => f ≫ g) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let e₁ := Deformation.truncGEHomAddEquiv t n Y Z
  let e₂ := Deformation.truncGEHomAddEquiv t n X Z
  have h : (fun g : Y ⟶ Z => f ≫ g) =
      e₂ ∘ (fun k => (t.truncGE n).map f ≫ k) ∘ e₁.symm := by
    funext g
    change _ = (t.truncGEπ n).app X ≫ (t.truncGE n).map f ≫ e₁.symm g
    rw [← Category.assoc, t.truncGEπ_naturality, Category.assoc]
    congr 1
    exact (e₁.apply_symm_apply g).symm
  rw [h]
  refine e₂.bijective.comp (Function.Bijective.comp ?_ e₁.symm.bijective)
  refine ⟨fun k k' hk => ?_, fun k => ⟨inv ((t.truncGE n).map f) ≫ k, by simp⟩⟩
  simpa using congrArg (fun m => inv ((t.truncGE n).map f) ≫ m) hk

/-- An exact functor of abelian categories carries `τ_{≥ n}`-isomorphisms of complexes to
`τ_{≥ n}`-isomorphisms. -/
theorem isIso_truncGE_map_Q_mapHomologicalComplex {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D] [Abelian D] [HasDerivedCategory D] (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ)
    [IsIso ((DerivedCategory.TStructure.t.truncGE n).map (DerivedCategory.Q.map φ))] :
    IsIso ((DerivedCategory.TStructure.t.truncGE n).map
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ))) := by
  have := isIso_truncGE_map_map_of_isIso_truncGE_map F.mapDerivedCategory
    (mapDerivedCategory_isLE F) (DerivedCategory.Q.map φ) n
  have e : DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) =
      (F.mapDerivedCategoryFactors.app K).inv ≫ F.mapDerivedCategory.map
        (DerivedCategory.Q.map φ) ≫ (F.mapDerivedCategoryFactors.app L).hom := by
    rw [Iso.app_hom, Functor.mapDerivedCategoryFactors_hom_naturality, Iso.app_inv,
      ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  rw [e, Functor.map_comp, Functor.map_comp]
  infer_instance

end Stacks

namespace Stacks.Deformation.SquareZeroExtensionProblem

attribute [local instance high] HasDerivedCategory.standard

variable (S : SquareZeroExtensionProblem.{u, u, u, u₄})

/-- The universe lift of `B`-modules into the module universe of `cotangentExt`. -/
noncomputable abbrev liftB : ModuleCat.{u} S.B ⥤ ModuleCat.{max u u₄} S.B :=
  ModuleCat.uliftFunctor.{u₄} S.B

/-- Extension of scalars along `A → B`, followed by the universe lift. -/
noncomputable abbrev liftBaseChange : ModuleCat.{u} S.A ⥤ ModuleCat.{max u u₄} S.B :=
  S.baseChangeFunctor ⋙ S.liftB

/-- The canonical presentation `A'[B] → B`. -/
noncomputable abbrev towerNaive : Algebra.Extension S.A' (CommAlgCat.of S.A' S.B) :=
  CommAlgCat.naiveExtension.{u, u} S.A' (CommAlgCat.of S.A' S.B)

/-- The canonical presentation `A'[A] → A`. -/
noncomputable abbrev baseNaive : Algebra.Extension S.A' (CommAlgCat.of S.A' S.A) :=
  CommAlgCat.naiveExtension.{u, u} S.A' (CommAlgCat.of S.A' S.A)

/-- The conormal differential of `A'[B] → B`, lifted: the two-term complex whose mapping cone is
`NL_{B/A'}`. -/
noncomputable abbrev towerDifferential :
    S.liftB.obj (ModuleCat.of S.B S.towerNaive.Cotangent) ⟶
      S.liftB.obj (ModuleCat.of S.B S.towerNaive.CotangentSpace) :=
  S.liftB.map (ModuleCat.ofHom S.towerNaive.cotangentComplex)

/-- The conormal differential of `A'[A] → A`, base changed to `B` and lifted: the two-term
complex whose mapping cone is `NL_{A/A'} ⊗_A B`. -/
noncomputable abbrev baseDifferential :
    S.liftBaseChange.obj (ModuleCat.of S.A S.baseNaive.Cotangent) ⟶
      S.liftBaseChange.obj (ModuleCat.of S.A S.baseNaive.CotangentSpace) :=
  S.liftBaseChange.map (ModuleCat.ofHom S.baseNaive.cotangentComplex)

/-- The map `L_{B/A'} → NL_{B/A'}` of Tag 08RB, lifted, with `NL_{B/A'}` written as a mapping
cone. -/
noncomputable def towerCocycleMap :
    (S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.B)) ⟶
      HomologicalComplex.homotopyCofiber
        (NaiveCotangent.ExtCokernelLinear.singleMap S.towerDifferential) :=
  (S.liftB.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)) ≫
    (naiveComplexCofiberIso S.liftB S.towerNaive).hom

/-- The map `L_{A/A'} ⊗_A B → NL_{A/A'} ⊗_A B`, the termwise base change of the map of Tag 08RB,
lifted, with `NL_{A/A'} ⊗_A B` written as a mapping cone. -/
noncomputable def baseCocycleMap :
    (S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CommAlgCat.cotangentComplex.{u, u} S.A' (CommAlgCat.of S.A' S.A)) ⟶
      HomologicalComplex.homotopyCofiber
        (NaiveCotangent.ExtCokernelLinear.singleMap S.baseDifferential) :=
  (S.liftBaseChange.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A)) ≫
    (naiveComplexCofiberIso S.liftBaseChange S.baseNaive).hom

/-- **The map `L_{B/A'} → NL_{B/A'}` is an isomorphism after `τ_{≥ -1}`** (Tag 08RB), in the
form `towerCocycleMap` writes it: lifted, with the naive cotangent complex as a mapping cone. -/
theorem isIso_truncGE_map_Q_towerCocycleMap :
    IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{max u u₄} S.B)).truncGE (-1)).map
      (DerivedCategory.Q.map S.towerCocycleMap)) := by
  have := Cotangent.isIso_truncGE_map_Q_cotangentComplexToNaive S.A'
    (CommAlgCat.of S.A' S.B)
  have := isIso_truncGE_map_Q_mapHomologicalComplex S.liftB
    (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.B)) (-1)
  rw [towerCocycleMap, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The map `L_{A/A'} ⊗_A B → NL_{A/A'} ⊗_A B` is an isomorphism after `τ_{≥ -1}`**, in the
form `baseCocycleMap` writes it: the termwise base change of the map of Tag 08RB, lifted, with
the naive cotangent complex as a mapping cone. -/
theorem isIso_truncGE_map_Q_baseCocycleMap :
    IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{max u u₄} S.B)).truncGE (-1)).map
      (DerivedCategory.Q.map S.baseCocycleMap)) := by
  have := S.isIso_truncGE_map_Q_extendScalars_cotangentComplexToNaive
  have h : IsIso (((DerivedCategory.TStructure.t (C := ModuleCat.{max u u₄} S.B)).truncGE
      (-1)).map (DerivedCategory.Q.map ((S.liftBaseChange.mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A))))) :=
    isIso_truncGE_map_Q_mapHomologicalComplex S.liftB
      ((S.baseChangeFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Cotangent.cotangentComplexToNaive.{u, u} S.A' (CommAlgCat.of S.A' S.A))) (-1)
  rw [baseCocycleMap, Functor.map_comp, Functor.map_comp]
  infer_instance

end Stacks.Deformation.SquareZeroExtensionProblem

end
