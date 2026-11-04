module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedParasitic
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkCounit
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# `Lf^*` has zero kernel on complexes supported where `f` is flat and surjective (Stacks 0AFJ)

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `T ⊆ |X|` a subset such
that every geometric point `x̄` of `X` lying over `T` is the image `f(ȳ)` of a geometric point `ȳ`
of `Y` at which `f` is flat. Granted the stalk formula for derived pullbacks, in the form
`AlgebraicGeometry.Space.DerivedPullbackStalkComparisonStatement`, for `K ∈ D(𝒪_X)` supported on
`T`, `Lf^*K = 0` implies `K = 0`.

## Main results

* `AlgebraicGeometry.Space.isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber`: the
  derived geometric stalk of `K` vanishes exactly when the stalks of its cohomology sheaves do.
* `AlgebraicGeometry.Space.isZero_homology_extendScalars_of_isZero_geometricDerivedStalk`: if the
  stalk at `ȳ` of `f^*P` vanishes, so does the cohomology of `𝒪_{Y,ȳ} ⊗ P_{f(ȳ)}` (Stacks 05V5,
  through `AlgebraicGeometry.Space.ringedToposPullbackFiberIso`).
* `AlgebraicGeometry.Space.isZero_geometricDerivedStalk_of_isZero_smallEtaleDerivedModulePullback`:
  `Lf^*K = 0` forces `K_{f(ȳ)} = 0` at every geometric point `ȳ` where `f` is flat.
* `AlgebraicGeometry.Space.isZero_of_isZero_smallEtaleDerivedModulePullback`: **the zero kernel
  of `Lf^*` on complexes supported on `T`**.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_geometricPointMap_eq_of_mem`: in
  Situation 0AEV every geometric point of `X` over `|Z|` is the image of a geometric point of
  `f⁻¹Z`, where `f` is flat.

## References

* [Stacks Project, Tag 0AFJ](https://stacks.math.columbia.edu/tag/0AFJ)
* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] additive_smallEtalePullbackModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Kernel

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- The geometric module fibre at `ȳ` of the pullback of modules of the morphism of small étale
ringed topoi is the extension of scalars along `𝒪_{X,f(ȳ)} ⟶ 𝒪_{Y,ȳ}` of the fibre at `f(ȳ)`
(Stacks 05V5). -/
def ringedToposPullbackFiberIso (y : GeometricPoint B S hS Y.1) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O ≅
      Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y) :=
  Functor.isoWhiskerRight (ringedToposPullbackIsoModulePullback B S hS f) _ ≪≫
    modulePullbackFiberIso B S hS f y

/-- **The derived geometric stalk of `K` at `x̄` vanishes exactly when the module fibres at `x̄` of
all cohomology sheaves of `K` do.** -/
theorem isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber {W : AlgebraicSpaces B S hS}
    (x : GeometricPoint B S hS W.1) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS W.1 W.2)
    ∀ K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2),
      IsZero ((geometricDerivedStalk B S hS x).obj K) ↔
        ∀ n : ℤ, IsZero ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
          (smallEtaleRingedTopos B S hS W).O).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) n).obj K)) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS W.1 W.2)
  intro K
  exact @DerivedCategoryB.isZero_mapDerivedCategory_obj_iff _ _ _ _
    (HasDerivedCategory.standard _) _ _ (HasDerivedCategory.standard _)
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
      (smallEtaleRingedTopos B S hS W).O)
    (Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
      (smallEtaleRingedTopos B S hS W).O)
    (Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
      (smallEtaleRingedTopos B S hS W).O)
    (Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
      (etaleSitePoint B S hS W.1 x W.2) (smallEtaleRingedTopos B S hS W).O) K

/-- The module fibre at `x̄` of the `n`-th cohomology of a complex of modules vanishes exactly when
the `n`-th homology of the degreewise fibre complex does. -/
private theorem isZero_fiber_homologyFunctor_iff_isZero_homology {W : AlgebraicSpaces B S hS}
    [HasDerivedCategory (Modules.{u, u} B S hS W.1 W.2)] (x : GeometricPoint B S hS W.1)
    (P : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ) (n : ℤ) :
    IsZero ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
      (smallEtaleRingedTopos B S hS W).O).obj ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS W.1 W.2) n).obj (DerivedCategory.Q.obj P))) ↔
      IsZero ((((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
        (smallEtaleRingedTopos B S hS W).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P).homology n) :=
  haveI := Stacks.instAdditiveSheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
    (smallEtaleRingedTopos B S hS W).O
  haveI := Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS W.1 x W.2) (smallEtaleRingedTopos B S hS W).O
  haveI := Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS W.1 x W.2) (smallEtaleRingedTopos B S hS W).O
  Iso.isZero_iff (Functor.mapIso _ ((DerivedCategory.homologyFunctorFactors _ n).app P) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS W.1 x W.2)
        (smallEtaleRingedTopos B S hS W).O) (ComplexShape.up ℤ) n).symm.app P)

/-- **The stalk at `ȳ` of `f^*P`, through Stacks 05V5.** If the derived geometric stalk at `ȳ`
of the degreewise pullback `f^*P` of a complex `P` of `𝒪_X`-modules vanishes, then so does the
cohomology of `𝒪_{Y,ȳ} ⊗ P_{f(ȳ)}`, the degreewise extension of scalars of the stalk complex
along `𝒪_{X,f(ȳ)} ⟶ 𝒪_{Y,ȳ}`. -/
theorem isZero_homology_extendScalars_of_isZero_geometricDerivedStalk
    (y : GeometricPoint B S hS Y.1)
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (h : IsZero ((geometricDerivedStalk B S hS y).obj
      ((smallEtaleModulePullbackOnHomotopy B S hS f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))) (n : ℤ) :
    IsZero ((((ModuleCat.extendScalars
      (smallEtaleStalkPullbackRingMap B S hS f y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            P)).homology n) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS Y.1 Y.2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let C := ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have h₁ : IsZero ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
      (smallEtaleRingedTopos B S hS Y).O).obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) n).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)))) :=
    (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS y _).1 h n
  have h₃ : IsZero ((((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
      (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        C).homology n) :=
    (isZero_fiber_homologyFunctor_iff_isZero_homology B S hS y _ _).1
      (h₁.of_iso (Functor.mapIso _ ((DerivedCategory.homologyFunctor _ n).mapIso
        ((DerivedCategory.quotientCompQhIso _).app C))).symm)
  exact h₃.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (ringedToposPullbackFiberIso B S hS f y).app (P.X i))
      (fun i j _ ↦ ((ringedToposPullbackFiberIso B S hS f y).hom.naturality (P.d i j)).symm)).symm)

open CochainComplex.DerivedExtensionScalars in
/-- **`Lf^*K = 0` forces `K_{f(ȳ)} = 0` where `f` is flat**, granted the stalk formula for derived
pullbacks: for `K ∈ D(𝒪_X)` with `Lf^*K = 0` and a geometric point `ȳ` of `Y` at which `f` is
flat, the derived geometric stalk of `K` at `f(ȳ)` vanishes. -/
theorem isZero_geometricDerivedStalk_of_isZero_smallEtaleDerivedModulePullback
    (H : DerivedPullbackStalkComparisonStatement B S hS) (y : GeometricPoint B S hS Y.1)
    (hf : IsFlatAt B S hS f.hom y.image) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    ∀ K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      IsZero ((smallEtaleDerivedModulePullback B S hS f).obj K) →
        IsZero ((geometricDerivedStalk B S hS (geometricPointMap f.hom y)).obj K) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  intro K hK
  let ρ := smallEtaleStalkPullbackRingMap B S hS f y
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hc := H f y P (TotalDerivedExtensionScalars.isIso_comparison_app_of_flat _
    (flat_stalkStructureMap_of_isFlatAt f y hf) _)
  have h₀ : IsZero ((smallEtaleDerivedModulePullback B S hS f).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :=
    hK.of_iso ((smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P ≪≫ e))
  have h₁ : IsZero ((geometricDerivedStalk B S hS y).obj
      ((smallEtaleDerivedModulePullback B S hS f).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))) :=
    (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS y _).2 fun n ↦
      Functor.map_isZero _ ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) n).map_isZero h₀)
  have h₂ : IsZero ((geometricDerivedStalk B S hS y).obj
      ((smallEtaleModulePullbackOnHomotopy B S hS f).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) :=
    h₁.of_iso (asIso ((geometricDerivedStalk B S hS y).map
      ((smallEtaleDerivedModulePullbackComparison B S hS f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))).symm
  have hflat := flat_smallEtaleStalkPullbackRingMap_of_isFlatAt f y hf
  have hff := faithfullyFlat_smallEtaleStalkPullbackRingMap_of_isFlatAt f y hf
  refine (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS
    (geometricPointMap f.hom y) K).2 fun n ↦ ?_
  have h₅ : IsZero ((((Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
      (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        P).homology n) :=
    ModuleCat.isZero_of_isZero_extendScalars ρ hff _
      ((isZero_homology_extendScalars_of_isZero_geometricDerivedStalk B S hS f y P h₂ n).of_iso
        (ModuleCat.extendScalarsHomologyIso ρ hflat _ n).symm)
  exact ((isZero_fiber_homologyFunctor_iff_isZero_homology B S hS _ _ _).2 h₅).of_iso
    (Functor.mapIso _ ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) n).mapIso e.symm))

/-- **`Lf^*` has zero kernel on the complexes supported on `T`**, granted the stalk formula for
derived pullbacks, when every geometric point of `X` over `T` is the image of a geometric point of
`Y` at which `f` is flat. -/
theorem isZero_of_isZero_smallEtaleDerivedModulePullback
    (H : DerivedPullbackStalkComparisonStatement B S hS) (T : Set (points B S hS X.1))
    (hT : ∀ x : GeometricPoint B S hS X.1, x.image ∈ T →
      ∃ y : GeometricPoint B S hS Y.1, geometricPointMap f.hom y = x ∧
        IsFlatAt B S hS f.hom y.image) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    ∀ K, DerivedCategoryB.derivedCategoryB (supportedModules B S hS X T) K →
      IsZero ((smallEtaleDerivedModulePullback B S hS f).obj K) → IsZero K := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  intro K hK hLK
  have hx : ∀ x : GeometricPoint B S hS X.1, IsZero ((geometricDerivedStalk B S hS x).obj K) := by
    intro x
    by_cases hxT : x.image ∈ T
    · obtain ⟨y, rfl, hy⟩ := hT x hxT
      exact isZero_geometricDerivedStalk_of_isZero_smallEtaleDerivedModulePullback B S hS f H y hy
        K hLK
    · refine (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS x K).2
        fun n ↦ ?_
      exact isZero_sheafModuleFiberOfCommRing_obj_of_not_mem B S hS X x _ fun h ↦ hxT (hK n h)
  rw [CategoryTheory.Limits.isZero_iff_isIso_zero]
  refine (isIso_iff_forall_isIso_geometricDerivedStalk_map B S hS X _).2 fun x ↦
    (hx x).isIso ?_ _
  exact (isZero_geometricDerivedStalk_iff_forall_isZero_sheafModuleFiber B S hS x _).2
    fun n ↦ Functor.map_isZero _ ((DerivedCategory.homologyFunctor
    (Modules.{u, u} B S hS X.1 X.2) n).map_isZero (isZero_zero _))

end Kernel

/-! ### Situation 0AEV -/

/-- **In Situation 0AEV every geometric point of `X` over `|Z|` is the image of a geometric point
of `Y` at which `f` is flat**, namely of a geometric point of `f⁻¹Z`. -/
theorem FormalGlueingSituation.exists_geometricPointMap_eq_of_mem
    (D : FormalGlueingSituation B S hS) (x : GeometricPoint B S hS D.X)
    (hx : x.image ∈ subspacePointSet B S hS D.X D.Z) :
    ∃ y : GeometricPoint B S hS D.Y, geometricPointMap D.f y = x ∧
      IsFlatAt B S hS D.f y.image := by
  obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS
    (ObjectProperty.homMk D.Z.ι :
      (⟨D.Z.toFunctor, D.closed_Z.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨D.X, D.algebraicSpace_X⟩)
    D.closed_Z.2 x hx
  have := D.iso_over_Z
  let w := geometricPointMap (inv (D.Z.fromPreimage D.f)) z
  refine ⟨geometricPointMap (D.Z.preimage D.f).ι w, ?_, D.flat_at_preimage_Z w.image⟩
  have h : inv (D.Z.fromPreimage D.f) ≫ (D.Z.preimage D.f).ι ≫ D.f = D.Z.ι := by
    rw [← (Subfunctor.isPullback_preimage D.f D.Z).w, IsIso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ geometricPointMap k z) h

end AlgebraicGeometry.Space

end
