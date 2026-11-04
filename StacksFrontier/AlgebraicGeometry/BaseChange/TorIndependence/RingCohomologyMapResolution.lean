module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsResolution
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# Derived base change computed by a K-flat resolution of the new ring

Let `g : R → R'` be a ring map and `F → R'` a K-flat resolution of `R'` over `R`. Restricting
the derived base change `X ⊗ᴸ_R R'` back to `R` is computed by the ordinary total tensor product
`X ⊗_R F`, naturally in the complex `X`; on cohomology `Hⁿ(X ⊗ᴸ_R R') = Hⁿ(X ⊗_R F)`.

## Main definitions

* `RingTheory.TorIndependence.resolutionTensorIso`: the natural isomorphism
  `Q(X ⊗_R F) ≅ (Q(X) ⊗ᴸ_R R')|_R` of functors on complexes of `R`-modules.
* `RingTheory.TorIndependence.resolutionHomologyIso`: its value on cohomology.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section Resolution

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')

/-- Restricting the extension of scalars of `M` along `g` back to `R` is `M ⊗_R R'`. -/
def restrictExtendScalarsTensorIso :
    ModuleCat.extendScalars.{u, u, u} g ⋙ ModuleCat.restrictScalars.{u} g ≅
      StacksDraft.TorAmplitude.tensorModuleRight
        ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')) :=
  NatIso.ofComponents (fun M => LinearEquiv.toModuleIso
    (show (ModuleCat.restrictScalars.{u} g).obj ((ModuleCat.extendScalars.{u, u, u} g).obj M) ≃ₗ[R]
        (StacksDraft.TorAmplitude.tensorModuleRight
          ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).obj M from
    { toAddEquiv := (TensorProduct.comm R ((ModuleCat.restrictScalars.{u} g).obj
          (ModuleCat.of R' R')) M).toAddEquiv
      map_smul' := fun r x => by
        change TensorProduct.comm R _ M (r • x) = r • TensorProduct.comm R _ M x
        induction x using TensorProduct.induction_on with
        | zero =>
          exact (congrArg (TensorProduct.comm R _ M) (smul_zero (A := (ModuleCat.restrictScalars.{u} g).obj
            ((ModuleCat.extendScalars.{u, u, u} g).obj M)) r)).trans
              ((map_zero _).trans ((smul_zero r).symm.trans (congrArg (r • ·) (map_zero _).symm)))
        | add x y hx hy =>
          exact (congrArg (TensorProduct.comm R _ M) (smul_add (A := (ModuleCat.restrictScalars.{u} g).obj
            ((ModuleCat.extendScalars.{u, u, u} g).obj M)) r x y)).trans
              ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
                ((smul_add r _ _).symm.trans (congrArg (r • ·) (map_add _ _ _).symm))))
        | tmul s m =>
          change TensorProduct.comm R _ M ((r • s) ⊗ₜ[R] m) =
            r • TensorProduct.comm R _ M (s ⊗ₜ[R] m)
          rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.tmul_smul] })) fun {M N} φ => by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using TensorProduct.induction_on with
    | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
    | add x y hx hy =>
      exact (LinearMap.map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (LinearMap.map_add _ x y).symm)
    | tmul s m => rfl

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat)

/-- Tensoring on the right with a K-flat complex inverts quasi-isomorphisms. -/
theorem tensorRight_inverts_of_kFlat (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (tensorRight F ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have h : QuasiIso ((tensorRight F).map f) :=
    StacksDraft.TorAmplitude.quasiIso_tensorRight_map hF f
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorRight F).map f)))

/-- The descent of `- ⊗_R F` to `D(R)`, for `F` K-flat. -/
abbrev resolutionTensorLift :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (tensorRight F ⋙ DerivedCategory.Q) (tensorRight_inverts_of_kFlat F hF)
    DerivedCategory.Q

/-- The comparison `Q(X ⊗_R F) ⟶ Q(X ⊗_R R') = Q((X ⊗_R R')|_R)` induced by `F → R'`. -/
def resolutionTensorComparison
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) :
    DerivedCategory.Q ⋙ resolutionTensorLift F hF ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  (Localization.fac (tensorRight F ⋙ DerivedCategory.Q) (tensorRight_inverts_of_kFlat F hF)
      DerivedCategory.Q).hom ≫
    Functor.whiskerRight ((curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).flip.map q)
      DerivedCategory.Q ≫
    Functor.whiskerRight (StacksDraft.TorAmplitude.termwiseTensorSingleIso
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))).inv DerivedCategory.Q ≫
    Functor.whiskerRight (Functor.mapHomologicalComplexCompIso (restrictExtendScalarsTensorIso g)
      (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    Functor.whiskerLeft
      ((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors.inv

/-- The counit of restriction after derived base change, a left derived functor of restriction
after termwise base change. -/
abbrev restrictDerivedExtensionComparison :
    DerivedCategory.Q ⋙ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).comparison
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory

instance isLeftDerivedFunctor_restrictDerivedExtension :
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory).IsLeftDerivedFunctor
      (restrictDerivedExtensionComparison g)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let cmp : DerivedCategory.Q ⋙ D.functor ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} g ⋙ DerivedCategory.Q := D.comparison
  haveI : D.functor.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
  exact CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
    g D.functor cmp (ModuleCat.restrictScalars.{u} g).mapDerivedCategory

/-- The map from the descent of `- ⊗_R F` to restriction after derived base change. -/
def resolutionTensorToDerived
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) :
    resolutionTensorLift F hF ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  Functor.leftDerivedLift _ (restrictDerivedExtensionComparison g)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (resolutionTensorComparison g F hF q)

theorem resolutionTensorToDerived_fac
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R')))
    (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (resolutionTensorToDerived g F hF q).app (DerivedCategory.Q.obj X) ≫
        (restrictDerivedExtensionComparison g).app X =
      (resolutionTensorComparison g F hF q).app X :=
  Functor.leftDerived_fac_app _ _ _ _ _ X

instance isIso_resolutionTensorToDerived
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) [QuasiIso q] :
    IsIso (resolutionTensorToDerived g F hF q) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let γ := resolutionTensorToDerived g F hF q
  have hQ : ∀ X : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} X →
      IsIso (γ.app (DerivedCategory.Q.obj X)) := by
    intro X hX
    let cmp : DerivedCategory.Q ⋙ D.functor ⟶
        (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q := D.comparison
    haveI : D.functor.IsLeftDerivedFunctor cmp
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := D.isLeftDerived
    have h1 : IsIso ((restrictDerivedExtensionComparison g).app X) := by
      haveI : IsIso (cmp.app X) :=
        CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{u, u, u}
          g D.functor cmp X hX
      change IsIso (𝟙 _ ≫ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map (cmp.app X))
      infer_instance
    have h2 : IsIso ((resolutionTensorComparison g F hF q).app X) := by
      have : QuasiIso ((tensorLeft X).map q) :=
        StacksDraft.TorAmplitude.quasiIso_tensorLeft_map X hX q
      have : IsIso (DerivedCategory.Q.map ((tensorLeft X).map q)) := inferInstance
      dsimp only [resolutionTensorComparison, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app]
      exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' this inferInstance)
    have h3 := resolutionTensorToDerived_fac g F hF q X
    haveI : IsIso (γ.app (DerivedCategory.Q.obj X) ≫ (restrictDerivedExtensionComparison g).app X) := by
      rw [h3]
      exact h2
    exact IsIso.of_isIso_comp_right _ ((restrictDerivedExtensionComparison g).app X)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ γ fun Y => ?_
  obtain ⟨X, hX, ⟨e⟩⟩ := CochainComplex.DerivedExtensionScalars.exists_kFlat_model.{u, u, u} Y
  haveI := hQ X hX
  have h := γ.naturality e.inv
  have h' : γ.app Y = (resolutionTensorLift F hF).map e.hom ≫ γ.app (DerivedCategory.Q.obj X) ≫
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory).map e.inv := by
    rw [← h, ← Category.assoc, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h']
  infer_instance

/-- **Restriction after derived base change is computed by a K-flat resolution of `R'`.**
`Q(X ⊗_R F) ≅ (Q(X) ⊗ᴸ_R R')|_R`, naturally in the complex `X`. -/
def resolutionTensorIso
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) [QuasiIso q] :
    tensorRight F ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ (ModuleCat.restrictScalars.{u} g).mapDerivedCategory :=
  (Localization.fac (tensorRight F ⋙ DerivedCategory.Q) (tensorRight_inverts_of_kFlat F hF)
      DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (asIso (resolutionTensorToDerived g F hF q))

/-- **The cohomology of a derived base change computed by a K-flat resolution of `R'`.**
`Hⁿ(X ⊗_R F) ≅ Hⁿ(Q(X) ⊗ᴸ_R R')|_R`, naturally in the complex `X`. -/
def resolutionHomologyIso
    (q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of R' R'))) [QuasiIso q] (n : ℤ) :
    tensorRight F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n ≅
      DerivedCategory.Q ⋙ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n ⋙
          ModuleCat.restrictScalars.{u} g :=
  Functor.isoWhiskerLeft (tensorRight F)
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (resolutionTensorIso g F hF q)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (Functor.isoWhiskerLeft
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
      ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryHomologyIso n))

end Resolution

end RingTheory.TorIndependence

end
