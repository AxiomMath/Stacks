module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModulesStalkTotal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite

/-!
# Stacks 01CD on the stalks of total tensor complexes

For a morphism of schemes `g' : X' ⟶ X`, a point `x'` of `X'` and complexes `P`, `N` of
`𝒪_X`-modules, the stalk at `x'` of the comparison `g'^*Tot(P ⊗ N) ≅ Tot(g'^*P ⊗ g'^*N)` of
Stacks 01CD is, through the stalk identifications of a pullback and of a total tensor complex,
the monoidality of base change along `𝒪_{X,g'(x')} ⟶ 𝒪_{X',x'}`.

## Main results

* `Stacks.ModuleSkyscraper.pullbackStalk_tensorComplex`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u

namespace CategoryTheory

private theorem chase_six {C : Type*} [Category C]
    {E₀ E₁ E₂ E₃ E₄ E₅ F₁ F₂ F₃ F₄ F₅ G₁ G₂ G₃ G₄ : C}
    (i₁ : E₀ ⟶ E₁) (a₁ : E₁ ⟶ E₂) (a₂ : E₂ ⟶ E₃) (a₃ : E₃ ⟶ E₄) (a₄ : E₄ ⟶ E₅)
    (b₁ : E₁ ⟶ G₁) (b₂ : G₁ ⟶ E₅) (pb : E₀ ⟶ F₁) (j₁ : F₁ ⟶ E₂) (sc : F₁ ⟶ F₂) (j₂ : F₂ ⟶ E₃)
    (sg : F₂ ⟶ F₃) (j₃ : F₃ ⟶ E₄) (ph₁ : F₃ ⟶ F₄) (ph₂ : F₄ ⟶ F₅) (j₄ : F₅ ⟶ E₅)
    (es : E₀ ⟶ G₂) (k₁ : G₂ ⟶ G₁) (mu₁ : G₂ ⟶ G₃) (mu₂ : G₃ ⟶ G₄) (mu₃ : G₄ ⟶ F₅)
    (h1 : i₁ ≫ a₁ = pb ≫ j₁) (h2 : j₁ ≫ a₂ = sc ≫ j₂) (h3 : j₂ ≫ a₃ = sg ≫ j₃)
    (h4 : j₃ ≫ a₄ = ph₁ ≫ ph₂ ≫ j₄) (h5 : i₁ ≫ b₁ = es ≫ k₁)
    (h6 : k₁ ≫ b₂ = mu₁ ≫ mu₂ ≫ mu₃ ≫ j₄)
    (atom : pb ≫ sc ≫ sg ≫ ph₁ ≫ ph₂ = es ≫ mu₁ ≫ mu₂ ≫ mu₃) :
    i₁ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ = i₁ ≫ b₁ ≫ b₂ := by
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4, reassoc_of% h5, h6]
  simp only [← Category.assoc] at atom ⊢
  rw [atom]

/-- A functor preserves an equality of composites of two morphisms. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end CategoryTheory

namespace CategoryTheory.Functor

private theorem map_mapBifunctor_X_hom_ext {C₁ C₂ D E : Type*} [Category C₁] [Category C₂]
    [Category D] [Category E] [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
    (Φ : D ⥤ E) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)] (n : ℤ)
    [PreservesColimitsOfShape (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) Φ]
    {T : E} (f g : Φ.obj ((HomologicalComplex.mapBifunctor K L F (ComplexShape.up ℤ)).X n) ⟶ T)
    (h : ∀ (p q : ℤ) (hpq : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (p, q) = n),
      Φ.map (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫ f =
        Φ.map (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫ g) :
    f = g :=
  (isColimitOfPreserves Φ (GradedObject.isColimitCofanMapObj
    (((GradedObject.mapBifunctor F ℤ ℤ).obj K.X).obj L.X)
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)).hom_ext
      fun ⟨⟨⟨p, q⟩, hpq⟩⟩ => h p q hpq

end CategoryTheory.Functor

namespace Stacks.ModuleSkyscraper

open AlgebraicGeometry Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' : Scheme.{u}} (g' : X' ⟶ X) (x' : X')

/-- The stalk functor on complexes. -/
abbrev stk {Z : Scheme.{u}} (z : Z) :=
  (tensorModulesStalkFunctor z).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The stalk of a pullback, at the spelling of the tensor product of sheaves of modules. -/
def pullbackStalkIsoK :
    tensorModulesStalkFunctor (g' x') ⋙ ModuleCat.extendScalars (g'.stalkMap x').hom ≅
      StacksDraft.KFlat.modulePullback g'.toLRSHom.toShHom ⋙ tensorModulesStalkFunctor x' :=
  pullbackStalkIso g' x'

/-- The stalk of a pullback, on complexes. -/
abbrev pullbackStalkComplex (K : CochainComplex X.Modules ℤ) :=
  (NatIso.mapHomologicalComplex (pullbackStalkIso g' x') (ComplexShape.up ℤ)).app K

/-- On the `(p, q)` summand of degree `n`, the stalk at `z` of the total tensor complex of `K`
and `L` is identified by `modulesStalkTotalIso` with the summand `K_{p,z} ⊗ L_{q,z}` of the total
tensor complex of the stalks, through `modulesStalkTensorIso`. -/
@[reassoc]
theorem ι_modulesStalkTotalIso_hom {Z : Scheme.{u}} (z : Z)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      Z.toRingedSpace) ℤ) (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (tensorModulesStalkFunctor z).map (HomologicalComplex.ιMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf) (ComplexShape.up ℤ) p q n h) ≫
      (modulesStalkTotalIso z K L).hom.f n =
    (modulesStalkTensorIso z (K.X p) (L.X q)).hom ≫
      HomologicalComplex.ιMapBifunctor ((stk z).obj K) ((stk z).obj L)
        (curriedTensor (ModuleCat.{u} (Z.presheaf.stalk z))) (ComplexShape.up ℤ) p q n h :=
  CategoryTheory.Functor.ι_mapBifunctorTotalIso_hom _ _ _ _ _ _ _ _ _ _ K L p q n h

/-- The component at `(K, L)` of `pullbackTensorComplexNatIso f` is the isomorphism
`mapBifunctorTotalIso` induced by the degreewise comparisons `comparisonAppIso f`. -/
theorem pullbackTensorComplexNatIso_hom_app {Y₁ Y₂ : RingedSpace.{u, u}} (f : Y₁ ⟶ Y₂)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y₂) ℤ) :
    (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso f).hom.app (K, L) =
      (CategoryTheory.Functor.mapBifunctorTotalIso
        (Stacks.SheafOfModules.Tensor.sheafTensor Y₂.sheaf)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y₁.sheaf)
        (StacksDraft.KFlat.modulePullback f) (StacksDraft.KFlat.modulePullback f)
        (StacksDraft.KFlat.modulePullback f)
        (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso f)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (fun {_ _} w B =>
          Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_left f w B)
        (fun A {_ _} w =>
          Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso_naturality_right f A w)
        K L).hom := rfl

/-- On the `(p, q)` summand of degree `n`, the pullback along `f` of the total tensor complex of
`K` and `L` is identified by `pullbackTensorComplexNatIso f` with the summand `f^*K^p ⊗ f^*L^q`
of the total tensor complex of the pullbacks, through `comparisonAppIso f`. -/
theorem ι_pullbackTensorComplexNatIso_hom {Y₁ Y₂ : RingedSpace.{u, u}} (f : Y₁ ⟶ Y₂)
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y₂) ℤ)
    (p q n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    (StacksDraft.KFlat.modulePullback f).map
        (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y₂.sheaf) (ComplexShape.up ℤ) p q n h) ≫
      ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso f).hom.app (K, L)).f n =
    (Stacks.Cohomology.DerivedPullbackTensor.comparisonAppIso f (K.X p) (L.X q)).hom ≫
      HomologicalComplex.ιMapBifunctor
        ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).obj K)
        ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex f).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor Y₁.sheaf) (ComplexShape.up ℤ) p q n h := by
  rw [Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso_hom_app]
  exact Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_hom f K L p q n h

/-- **Stacks 01CD on the stalks of total tensor complexes.** -/
theorem pullbackStalk_tensorComplex
    (P N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      X.toRingedSpace) ℤ) :
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    (pullbackStalkComplex g' x' (HomologicalComplex.mapBifunctor P N
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ))).hom ≫
      (stk x').map ((Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
          g'.toLRSHom.toShHom).hom.app (P, N)) ≫
      (modulesStalkTotalIso x' _ _).hom ≫
      HomologicalComplex.mapBifunctorMap ((pullbackStalkComplex g' x' P).inv ≫
          (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
            (X'.presheaf.stalk x')) (ComplexShape.up ℤ)).inv.app ((stk (g' x')).obj P))
        (pullbackStalkComplex g' x' N).inv
        (curriedTensor (ModuleCat.{u} (X'.presheaf.stalk x'))) (ComplexShape.up ℤ) =
    ((ModuleCat.extendScalars (algebraMap (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x'))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (modulesStalkTotalIso (g' x') P N).hom ≫
      (extTensorIso ((stk (g' x')).obj P) ((stk (g' x')).obj N)).hom := by
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  ext n : 1
  apply CategoryTheory.Functor.map_mapBifunctor_X_hom_ext
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (tensorModulesStalkFunctor (g' x') ⋙ ModuleCat.extendScalars (algebraMap
      (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x'))) P N n
  intro p q hpq
  have s1 := (pullbackStalkIsoK g' x').hom.naturality
    (HomologicalComplex.ιMapBifunctor P N (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
      (ComplexShape.up ℤ) p q n hpq)
  have s2 := CategoryTheory.map_comp_eq_map_comp (tensorModulesStalkFunctor x')
    (ι_pullbackTensorComplexNatIso_hom g'.toLRSHom.toShHom P N p q n hpq)
  have s3 := ι_modulesStalkTotalIso_hom x'
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj P)
    ((Stacks.Cohomology.DerivedPullbackTensor.pullbackComplex g'.toLRSHom.toShHom).obj N) p q n hpq
  have s4 := HomologicalComplex.ι_mapBifunctorMap ((pullbackStalkComplex g' x' P).inv ≫
          (NatIso.mapHomologicalComplex (baseChangeIsoExtendScalars (X.presheaf.stalk (g' x'))
            (X'.presheaf.stalk x')) (ComplexShape.up ℤ)).inv.app ((stk (g' x')).obj P))
        (pullbackStalkComplex g' x' N).inv
        (curriedTensor (ModuleCat.{u} (X'.presheaf.stalk x'))) (ComplexShape.up ℤ) p q n hpq
  have s5 := CategoryTheory.map_comp_eq_map_comp (ModuleCat.extendScalars
    (algebraMap (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x')))
    (ι_modulesStalkTotalIso_hom (g' x') P N p q n hpq)
  have s6 := ι_extTensorIso_hom (A' := X'.presheaf.stalk x') ((stk (g' x')).obj P)
    ((stk (g' x')).obj N) p q n hpq
  have atom := stalk_pullbackTensorComparison g' x' (P.X p) (N.X q)
  rw [MonoidalCategory.tensorHom_def] at atom
  exact CategoryTheory.chase_six _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 s4 s5 s6
    atom

end Stacks.ModuleSkyscraper

