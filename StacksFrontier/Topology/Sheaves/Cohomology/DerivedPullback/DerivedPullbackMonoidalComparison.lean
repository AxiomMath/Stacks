module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal

/-!
# The two K-flat monoidal structures on derived pullback agree

For a morphism of ringed spaces `f : X ⟶ Y`, the derived pullback `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is
made strong monoidal for the derived tensor products of [Stacks, Tag 0FPT] twice, with the
tensorator of [Stacks, Tag 079U] in both cases:

* `Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal`, through
  `CategoryTheory.Functor.kFlatComputedMonoidal`;
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackKFlatMonoidal`, through
  `CochainComplex.KFlatMonoidal.derivedFunctorMonoidal`.

Both are `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` for the K-flat
localization, with the lifting given by an isomorphism `kFlatQ ⋙ Lf^* ≅ f^* ⋙ kFlatQ` whose
component at a K-flat complex is the comparison `Lf^*(K) ⟶ f^*K` in both cases. Two isomorphisms
with the same forward components are equal, so the two structures are equal, at any models of
the derived categories.

## Main results

* `CategoryTheory.Functor.kFlatComputedMonoidal_eq_derivedFunctorMonoidal` — the two
  constructions agree for liftings with the same components.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal`
  — the two monoidal structures on `Lf^*` are equal.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackMonoidal_δ_eq`,
  `…_μ_eq`, `…_ε_eq`, `…_η_eq` — hence so are their tensorators and units.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v₁ u₁ v₂ u₂ u

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [MonoidalCategory B]
  [(curriedTensor B).Additive] [∀ X : B, ((curriedTensor B).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ B), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X₁)]
  [∀ X₂ : B, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : A ⥤ B) [F.Additive] [F.Monoidal]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) F]
  (hF : ∀ K : CochainComplex A ℤ, KFlat (curriedTensor A) K →
    KFlat (curriedTensor B) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  [BraidedCategory (CochainComplex A ℤ)] [BraidedCategory (CochainComplex B ℤ)]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (hresA : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)
  (hresB : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat (curriedTensor B) P ∧ QuasiIso f)
  (LF : DerivedCategory A ⥤ DerivedCategory B)

/-- `CategoryTheory.Functor.kFlatComputedMonoidal` and
`CochainComplex.KFlatMonoidal.derivedFunctorMonoidal` are the same monoidal structure on `LF`
when their liftings `kFlatQ ⋙ LF ≅ F ⋙ kFlatQ` have the same forward components: both are
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` of the K-flat localization. -/
theorem Functor.kFlatComputedMonoidal_eq_derivedFunctorMonoidal
    (e : kFlatQ (curriedTensor A) ⋙ LF ≅ Functor.kFlatLift F hF ⋙ kFlatQ (curriedTensor B))
    (e' : kFlatQ (curriedTensor A) ⋙ LF ≅
      CochainComplex.KFlatMonoidal.kFlatLift F hF ⋙ kFlatQ (curriedTensor B))
    (h : ∀ P, e.hom.app P = e'.hom.app P) :
    Functor.kFlatComputedMonoidal F hF hresA hresB LF e =
      CochainComplex.KFlatMonoidal.derivedFunctorMonoidal F hF hresA hresB LF e' := by
  obtain rfl : e = e' := Iso.ext (NatTrans.ext (funext h))
  rfl

end CategoryTheory

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory
  abelianStructureSheafRing hasDerivedCategoryModulesX hasDerivedCategoryModulesY

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing Y))]

/-- **The two K-flat monoidal structures on `Lf^*` are equal**, at any models of the derived
categories: `Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal` and
`derivedPullbackKFlatMonoidal` are built from liftings with the same components, the comparison
`Lf^*(K) ⟶ f^*K` at K-flat `K`. -/
theorem derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal :
    Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f =
      derivedPullbackKFlatMonoidal f :=
  Functor.kFlatComputedMonoidal_eq_derivedFunctorMonoidal (StacksDraft.KFlat.modulePullback f)
    (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackMonoidal.kFlatComparison f) (derivedPullbackKFlatIso f)
    fun _ ↦ rfl

/-- The oplax tensorators `Lf^*(K ⊗ᴸ L) ⟶ Lf^*K ⊗ᴸ Lf^*L` of
`Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal` and
`derivedPullbackKFlatMonoidal` agree. -/
theorem derivedPullbackMonoidal_δ_eq
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    @Functor.OplaxMonoidal.δ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f).toOplaxMonoidal
        K L =
      @Functor.OplaxMonoidal.δ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatMonoidal f).toOplaxMonoidal K L := by
  rw [derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal]

/-- The lax tensorators `Lf^*K ⊗ᴸ Lf^*L ⟶ Lf^*(K ⊗ᴸ L)` of
`Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal` and
`derivedPullbackKFlatMonoidal` agree. -/
theorem derivedPullbackMonoidal_μ_eq
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    @Functor.LaxMonoidal.μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f).toLaxMonoidal K L =
      @Functor.LaxMonoidal.μ _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatMonoidal f).toLaxMonoidal K L := by
  rw [derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal]

/-- The lax units `𝒪_X ⟶ Lf^*𝒪_Y` of
`Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal` and
`derivedPullbackKFlatMonoidal` agree. -/
theorem derivedPullbackMonoidal_ε_eq :
    @Functor.LaxMonoidal.ε _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f).toLaxMonoidal =
      @Functor.LaxMonoidal.ε _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatMonoidal f).toLaxMonoidal := by
  rw [derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal]

/-- The oplax units `Lf^*𝒪_Y ⟶ 𝒪_X` of
`Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal` and
`derivedPullbackKFlatMonoidal` agree. -/
theorem derivedPullbackMonoidal_η_eq :
    @Functor.OplaxMonoidal.η _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (Stacks.Cohomology.DerivedPullbackMonoidal.derivedPullbackMonoidal f).toOplaxMonoidal =
      @Functor.OplaxMonoidal.η _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal Y.sheaf)
        _ _ (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatMonoidal f).toOplaxMonoidal := by
  rw [derivedPullbackMonoidal_eq_derivedPullbackKFlatMonoidal]

end Stacks.Cohomology.DerivedPullbackTensor

end
