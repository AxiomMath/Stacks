module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Monoidal.OplaxOfAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# Derived pullback as a monoidal functor on `D_QCoh`

For a morphism `f : X ⟶ Y` of algebraic spaces, derived pullback
`Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` with the isomorphisms `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of
Stacks 07A4 as structure maps is an oplax, hence strong, monoidal functor for the monoidal
structures `AlgebraicGeometry.Space.quasicoherentDerivedMonoidal`, as soon as Stacks 07A4 is
compatible with the associators of the derived tensor products of `D(𝒪_Y)` and `D(𝒪_X)`, read on
`D(𝒪)` (`quasicoherentDerivedMonoidal_associator_hom_hom`). No compatibility with the unitors is
needed: `Lf^*𝒪_Y ≅ 𝒪_X`, so the tensor structure determines a unit satisfying both unit laws.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedPullbackMonoidal`: the monoidal structure, whose
  tensor structure map is Stacks 07A4 (`quasicoherentDerivedPullbackMonoidal_δ`) and whose unit is
  the one that the tensor structure determines (`CategoryTheory.OplaxOfAssoc`).

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedPullbackTensorComparison_associativity`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace CategoryTheory

/-- Naturality in the first variable of a comparison of two tensor products with exchanged
factors along a functor. -/
theorem swapUncurry_naturality_left {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C)
    (T' : D ⥤ D ⥤ D) (F : C ⥤ D)
    (α : (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj T) ⋙ F ⟶
      F.prod F ⋙ (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj T'))
    {K K' : C} (g : K ⟶ K') (L : C) :
    α.app (L, K) ≫ (T'.map (F.map g)).app (F.obj L) = F.map ((T.map g).app L) ≫ α.app (L, K') := by
  simpa using (α.naturality ((𝟙 L, g) : ((L, K) : C × C) ⟶ (L, K'))).symm

/-- Naturality in the second variable of a comparison of two tensor products with exchanged
factors along a functor. -/
theorem swapUncurry_naturality_right {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C)
    (T' : D ⥤ D ⥤ D) (F : C ⥤ D)
    (α : (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj T) ⋙ F ⟶
      F.prod F ⋙ (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj T'))
    (K : C) {L L' : C} (g : L ⟶ L') :
    α.app (L, K) ≫ (T'.obj (F.obj K)).map (F.map g) = F.map ((T.obj K).map g) ≫ α.app (L', K) := by
  simpa using (α.naturality ((g, 𝟙 K) : ((L, K) : C × C) ⟶ (L', K))).symm

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- Stacks 07A4 on `D_QCoh` is invertible. -/
instance isIso_quasicoherentDerivedPullbackTensorComparison_app (f : X ⟶ Y)
    (P : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ×
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso ((quasicoherentDerivedPullbackTensorComparison f).app P) :=
  (ObjectProperty.isIso_hom_iff _).1
    (inferInstanceAs (IsIso ((smallEtaleDerivedPullbackTensorIso f).hom.app (P.2.obj, P.1.obj))))

/-- **Stacks 07A4 on `D_QCoh` is compatible with the associators**, given that it is on `D(𝒪)`. -/
theorem quasicoherentDerivedPullbackTensorComparison_associativity (f : X ⟶ Y)
    (hassoc : ∀ A A' A'', (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedTensorProduct B S hS Y).associatorGeneral A A' A'').hom ≫
        (smallEtaleDerivedPullbackTensorIso f).hom.app
          (A, ((smallEtaleDerivedTensor B S hS Y).obj A').obj A'') ≫
        ((smallEtaleDerivedTensor B S hS X).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj A)).map
            ((smallEtaleDerivedPullbackTensorIso f).hom.app (A', A'')) =
      (smallEtaleDerivedPullbackTensorIso f).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj A).obj A', A'') ≫
        ((smallEtaleDerivedTensor B S hS X).map
          ((smallEtaleDerivedPullbackTensorIso f).hom.app (A, A'))).app
            ((smallEtaleDerivedModulePullback B S hS f).obj A'') ≫
        ((smallEtaleDerivedTensorProduct B S hS X).associatorGeneral
          ((smallEtaleDerivedModulePullback B S hS f).obj A)
          ((smallEtaleDerivedModulePullback B S hS f).obj A')
          ((smallEtaleDerivedModulePullback B S hS f).obj A'')).hom)
    (K L M : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    letI := quasicoherentDerivedMonoidal X
    letI := quasicoherentDerivedMonoidal Y
    (quasicoherentDerivedPullbackTensorComparison f).app (M, K ⊗ L) ≫
        (quasicoherentDerivedPullbackTensorComparison f).app (L, K) ▷
          (quasicoherentDerivedModulePullback f).obj M ≫
        (α_ ((quasicoherentDerivedModulePullback f).obj K)
          ((quasicoherentDerivedModulePullback f).obj L)
          ((quasicoherentDerivedModulePullback f).obj M)).hom =
      (quasicoherentDerivedModulePullback f).map (α_ K L M).hom ≫
        (quasicoherentDerivedPullbackTensorComparison f).app (L ⊗ M, K) ≫
          (quasicoherentDerivedModulePullback f).obj K ◁
            (quasicoherentDerivedPullbackTensorComparison f).app (M, L) := by
  let := quasicoherentDerivedMonoidal X
  let := quasicoherentDerivedMonoidal Y
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    quasicoherentDerivedMonoidal_associator_hom_hom]
  have hmap : ((quasicoherentDerivedModulePullback f).map (α_ K L M).hom).hom =
      (smallEtaleDerivedModulePullback B S hS f).map
        ((smallEtaleDerivedTensorProduct B S hS Y).associatorGeneral K.obj L.obj M.obj).hom := by
    rw [← quasicoherentDerivedMonoidal_associator_hom_hom]
    rfl
  rw [hmap]
  exact (hassoc K.obj L.obj M.obj).symm


/-- The unit of derived pullback on `D_QCoh`: `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def quasicoherentDerivedPullbackUnitIso (f : X ⟶ Y) :
    letI := quasicoherentDerivedMonoidal X
    letI := quasicoherentDerivedMonoidal Y
    (quasicoherentDerivedModulePullback f).obj (𝟙_ _) ≅ 𝟙_ _ :=
  ObjectProperty.isoMk _ (smallEtaleDerivedModulePullbackUnitIso f)

/-- The associativity of Stacks 07A4 with respect to the associators of `⊗^L`, on `D(𝒪)`. -/
abbrev PullbackTensorAssociativity (f : X ⟶ Y) : Prop :=
  ∀ A A' A'', (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedTensorProduct B S hS Y).associatorGeneral A A' A'').hom ≫
        (smallEtaleDerivedPullbackTensorIso f).hom.app
          (A, ((smallEtaleDerivedTensor B S hS Y).obj A').obj A'') ≫
        ((smallEtaleDerivedTensor B S hS X).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj A)).map
            ((smallEtaleDerivedPullbackTensorIso f).hom.app (A', A'')) =
      (smallEtaleDerivedPullbackTensorIso f).hom.app
          (((smallEtaleDerivedTensor B S hS Y).obj A).obj A', A'') ≫
        ((smallEtaleDerivedTensor B S hS X).map
          ((smallEtaleDerivedPullbackTensorIso f).hom.app (A, A'))).app
            ((smallEtaleDerivedModulePullback B S hS f).obj A'') ≫
        ((smallEtaleDerivedTensorProduct B S hS X).associatorGeneral
          ((smallEtaleDerivedModulePullback B S hS f).obj A)
          ((smallEtaleDerivedModulePullback B S hS f).obj A')
          ((smallEtaleDerivedModulePullback B S hS f).obj A'')).hom

/-- The oplax monoidal structure of derived pullback on `D_QCoh`, with cotensorator Stacks 07A4 and
the counit that the cotensorator determines. -/
@[instance_reducible]
def quasicoherentDerivedPullbackOplaxMonoidal (f : X ⟶ Y)
    (hassoc : PullbackTensorAssociativity f) :
    @Functor.OplaxMonoidal _ _ (quasicoherentDerivedMonoidal Y) _ _ (quasicoherentDerivedMonoidal X)
      (quasicoherentDerivedModulePullback f) :=
  letI := quasicoherentDerivedMonoidal X
  letI := quasicoherentDerivedMonoidal Y
  OplaxOfAssoc.oplaxMonoidal (quasicoherentDerivedModulePullback f)
    (fun K L => (quasicoherentDerivedPullbackTensorComparison f).app (L, K))
    (fun g L => CategoryTheory.swapUncurry_naturality_left _ _ _
      (quasicoherentDerivedPullbackTensorComparison f) g L)
    (fun K g => CategoryTheory.swapUncurry_naturality_right _ _ _
      (quasicoherentDerivedPullbackTensorComparison f) K g)
    (quasicoherentDerivedPullbackTensorComparison_associativity f hassoc)
    (quasicoherentDerivedPullbackUnitIso f)

/-- The counit of `quasicoherentDerivedPullbackOplaxMonoidal` is invertible. -/
theorem isIso_quasicoherentDerivedPullbackOplaxMonoidal_η (f : X ⟶ Y)
    (hassoc : PullbackTensorAssociativity f) :
    @IsIso _ _ _ _ (@Functor.OplaxMonoidal.η _ _ (quasicoherentDerivedMonoidal Y) _ _
      (quasicoherentDerivedMonoidal X) _ (quasicoherentDerivedPullbackOplaxMonoidal f hassoc)) :=
  let := quasicoherentDerivedMonoidal X
  let := quasicoherentDerivedMonoidal Y
  OplaxOfAssoc.isIso_counit (quasicoherentDerivedModulePullback f)
    (fun K L => (quasicoherentDerivedPullbackTensorComparison f).app (L, K))
    (fun g L => CategoryTheory.swapUncurry_naturality_left _ _ _
      (quasicoherentDerivedPullbackTensorComparison f) g L)
    (fun K g => CategoryTheory.swapUncurry_naturality_right _ _ _
      (quasicoherentDerivedPullbackTensorComparison f) K g)
    (quasicoherentDerivedPullbackTensorComparison_associativity f hassoc)
    (quasicoherentDerivedPullbackUnitIso f)

/-- **Derived pullback is a monoidal functor on `D_QCoh`**, with the isomorphisms of Stacks 07A4
as its tensor structure, as soon as those are compatible with the associators of `⊗^L` on
`D(𝒪_Y)` and `D(𝒪_X)`. -/
@[instance_reducible]
def quasicoherentDerivedPullbackMonoidal (f : X ⟶ Y) (hassoc : PullbackTensorAssociativity f) :
    @Functor.Monoidal _ _ (quasicoherentDerivedMonoidal Y) _ _ (quasicoherentDerivedMonoidal X)
      (quasicoherentDerivedModulePullback f) :=
  letI := quasicoherentDerivedMonoidal X
  letI := quasicoherentDerivedMonoidal Y
  letI := quasicoherentDerivedPullbackOplaxMonoidal f hassoc
  haveI := isIso_quasicoherentDerivedPullbackOplaxMonoidal_η f hassoc
  haveI : ∀ K L, IsIso (Functor.OplaxMonoidal.δ (quasicoherentDerivedModulePullback f) K L) :=
    fun K L => inferInstanceAs (IsIso ((quasicoherentDerivedPullbackTensorComparison f).app (L, K)))
  Functor.Monoidal.ofOplaxMonoidal _

/-- The tensor structure map of `quasicoherentDerivedPullbackMonoidal` is Stacks 07A4. -/
theorem quasicoherentDerivedPullbackMonoidal_δ (f : X ⟶ Y) (hassoc : PullbackTensorAssociativity f)
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    @Functor.OplaxMonoidal.δ _ _ (quasicoherentDerivedMonoidal Y) _ _
        (quasicoherentDerivedMonoidal X) _
        (quasicoherentDerivedPullbackMonoidal f hassoc).toOplaxMonoidal K L =
      (quasicoherentDerivedPullbackTensorComparison f).app (L, K) := by
  rfl

end AlgebraicGeometry.Space

end
