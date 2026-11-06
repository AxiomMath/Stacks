module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorSheafTensor
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Homology.KFlat.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product commutes with direct sums

Let `(C, 𝒪)` be a ringed site whose category of modules is Grothendieck abelian. For a fixed
object `L` of `D(𝒪)` the functor `K ↦ K ⊗^L_𝒪 L` commutes with direct sums. Choosing a K-flat
representative of `L`, the functor is computed on complexes by the total tensor complex
`Tot(- ⊗_𝒪 L)`, which commutes with direct sums because the tensor product of sheaves of modules
does (Stacks 05NB) and direct sums of complexes are computed degreewise; and the localization
`C(Mod(𝒪)) ⥤ D(𝒪)` commutes with direct sums.

## Main results

* `CategoryTheory.Functor.preservesColimit_mapBifunctorHomologicalComplex_flip_obj`: applying a
  bifunctor degreewise to a pair of complexes preserves colimits in the first variable.
* `CategoryTheory.Limits.preservesColimitsOfShape_of_comp_localization`: a functor out of the
  target of an essentially surjective functor `Q` preserving colimits of a shape preserves them
  as soon as its composite with `Q` agrees with `H ⋙ Q` for some `H` preserving them.
* `Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_flip_obj`: the
  derived tensor product commutes with direct sums in its first variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w x c u d

namespace CategoryTheory.Limits

/-- Let `Q : C ⥤ D` be essentially surjective and preserve colimits of shape `Discrete I`. A
functor `G : D ⥤ E` preserves them as soon as `Q ⋙ G ≅ H ⋙ Q'` for functors `H` and `Q'` which
preserve them: every discrete diagram in `D` is isomorphic to the image of one in `C`. -/
lemma preservesColimitsOfShape_of_comp_localization {C D E C' : Type*} [Category* C]
    [Category* D] [Category* E] [Category* C'] {I : Type w}
    [HasColimitsOfShape (Discrete I) C]
    (Q : C ⥤ D) [Q.EssSurj] [PreservesColimitsOfShape (Discrete I) Q]
    (G : D ⥤ E) (H : C ⥤ C') (Q' : C' ⥤ E) [PreservesColimitsOfShape (Discrete I) H]
    [PreservesColimitsOfShape (Discrete I) Q'] (e : Q ⋙ G ≅ H ⋙ Q') :
    PreservesColimitsOfShape (Discrete I) G := by
  refine ⟨fun {F} ↦ ?_⟩
  let K : Discrete I ⥤ C := Discrete.functor fun i ↦ Q.objPreimage (F.obj ⟨i⟩)
  have eF : K ⋙ Q ≅ F :=
    Discrete.natIso fun i ↦ Q.objObjPreimageIso (F.obj i)
  suffices PreservesColimit (K ⋙ Q) G from preservesColimit_of_iso_diagram G eF
  have : PreservesColimit K (Q ⋙ G) := preservesColimit_of_natIso K e.symm
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves Q (colimit.isColimit K))
    (isColimitOfPreserves (Q ⋙ G) (colimit.isColimit K))

end CategoryTheory.Limits

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry.RingedSite

variable {X : AlgebraicGeometry.RingedSite.{c, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d} (Modules.{c, u, u} X)]

/-- Supplied explicitly: since Mathlib v4.35.0 instance search for these coproducts times out. -/
local instance (J : Type u) : HasColimitsOfShape (Discrete J)
    (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- Supplied explicitly: since Mathlib v4.35.0 instance search for these coproducts times out. -/
local instance (J : Type u) :
    HasColimitsOfShape (Discrete J) (CochainComplex (Modules.{c, u, u} X) ℤ) :=
  have : HasColimitsOfShape (Discrete J) (Modules.{c, u, u} X) := inferInstance
  ⟨fun F ↦
    have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval _ _ n) :=
      HasColimitsOfShape.has_colimit _
    ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩⟩

/-- Tensoring sheaves of modules commutes with direct sums in the second variable
(Stacks 05NB). -/
@[ega "0 4.1.5" "partial", sga "4 IV 12.9" "special case"]
instance preservesColimitsOfShape_sheafTensor_obj (N : Modules.{c, u, u} X) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj N) :=
  letI := X.hasSheafCompose_forget₂_ringCat
  (Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight X.J X.O
    N).preservesColimitsOfShape

/-- The total tensor complex `Tot(K ⊗_𝒪 -)` commutes with direct sums of complexes. -/
instance preservesColimitsOfShape_tensorComplex_obj
    (K : CochainComplex (Modules.{c, u, u} X) ℤ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K) := by
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O
  have e : (F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K ⋙
      HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℤ) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, HomologicalComplex₂.totalFunctor_map,
        Iso.refl_hom, Stacks.SheafOfModules.Tensor.tensorComplex,
        Functor.map₂HomologicalComplexReg_obj_map, HomologicalComplex.mapBifunctorMapReg,
        HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.id_comp]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨fun {D} ↦ ?_⟩
  have := CochainComplex.KFlat.preservesColimit_mapBifunctorObj D K F
  have := CochainComplex.KFlat.preservesColimit_totalFunctor (C := Modules.{c, u, u} X)
    (c₁ := ComplexShape.up ℤ) (c₂ := ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (D ⋙ (F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K)
  exact preservesColimit_of_natIso D e

/-- Tensoring sheaves of modules commutes with direct sums in the first variable
(Stacks 05NB). -/
@[ega "0 4.1.5" "partial"]
instance preservesColimitsOfShape_sheafTensor_flip_obj (N : Modules.{c, u, u} X) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).flip.obj N) :=
  letI := X.hasSheafCompose_forget₂_ringCat
  (Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafLeft X.J X.O
    N).preservesColimitsOfShape

/-- The total tensor complex `Tot(- ⊗_𝒪 L)` commutes with direct sums of complexes. -/
instance preservesColimitsOfShape_tensorComplex_flip_obj
    (L : CochainComplex (Modules.{c, u, u} X) ℤ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj L) := by
  let F := Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O
  have e : (F.flip.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L ⋙
      HomologicalComplex₂.totalFunctor _ _ _ (ComplexShape.up ℤ) ≅
      (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj L :=
    NatIso.ofComponents (fun K ↦ HomologicalComplex.mapBifunctorFlipIso K L F (ComplexShape.up ℤ))
      (fun {K K'} f ↦ by
        have h := HomologicalComplex.mapBifunctorFlipIso_hom_naturality f (𝟙 L) F
          (ComplexShape.up ℤ)
        -- Simplify the left side of `h` only. Its right side `mapBifunctorMap f (𝟙 L)` is
        -- definitionally the goal's `((tensorComplex X.O).flip.obj L).map f`; simplifying it too
        -- leaves the kernel comparing Mathlib's spelling with the copy's at each step, which more
        -- than doubles this declaration's kernel time.
        conv_lhs at h => simp only [HomologicalComplex.mapBifunctorMap,
          CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
        exact h)
  refine ⟨fun {D} ↦ ?_⟩
  have := CochainComplex.KFlat.preservesColimit_mapBifunctorObj D L F.flip
  have := CochainComplex.KFlat.preservesColimit_totalFunctor (C := Modules.{c, u, u} X)
    (c₁ := ComplexShape.up ℤ) (c₂ := ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (D ⋙ (F.flip.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L)
  exact preservesColimit_of_natIso D e

variable [IsGrothendieckAbelian.{u} (Modules.{c, u, u} X)]

/-- **The derived tensor product commutes with direct sums in its second variable.** For a fixed
`E` in `D(𝒪)`, `E ⊗^L_𝒪 -` preserves coproducts indexed by a type of the module universe. On a
K-flat representative of `E` it is computed by the total tensor complex, which commutes with
direct sums of complexes, and the localization `C(Mod(𝒪)) ⥤ D(𝒪)` commutes with direct sums. -/
instance preservesColimitsOfShape_tensor_obj (T : DerivedTensorProduct.{c, u, u, d} X)
    (E : DerivedModules.{c, u, u, d} X) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (T.tensor.obj E) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (DerivedCategory.Q.objPreimage E)
  have eE : DerivedCategory.Q.obj P ≅ E := by
    have : IsIso (DerivedCategory.Q.map p) := by rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck
    (A := Modules.{c, u, u} X) I
  suffices PreservesColimitsOfShape (Discrete I) (T.tensor.obj (DerivedCategory.Q.obj P)) from
    preservesColimitsOfShape_of_natIso (T.tensor.mapIso eE)
  refine preservesColimitsOfShape_of_comp_localization DerivedCategory.Q _
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj P) DerivedCategory.Q
    (NatIso.ofComponents (fun K ↦ T.comparisonLeft P K hP) (fun {K K'} f ↦ ?_))
  have h := T.comparisonLeft_naturality (𝟙 P) f hP hP
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  exact h

/-- **The derived tensor product commutes with direct sums in its first variable.** For a fixed
`E` in `D(𝒪)`, `- ⊗^L_𝒪 E` preserves coproducts indexed by a type of the module universe. -/
instance preservesColimitsOfShape_tensor_flip_obj (T : DerivedTensorProduct.{c, u, u, d} X)
    (E : DerivedModules.{c, u, u, d} X) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (T.tensor.flip.obj E) := by
  obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (DerivedCategory.Q.objPreimage E)
  have eE : DerivedCategory.Q.obj P ≅ E := by
    have : IsIso (DerivedCategory.Q.map p) := by rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck
    (A := Modules.{c, u, u} X) I
  suffices PreservesColimitsOfShape (Discrete I)
      (T.tensor.flip.obj (DerivedCategory.Q.obj P)) from
    preservesColimitsOfShape_of_natIso (T.tensor.flip.mapIso eE)
  refine preservesColimitsOfShape_of_comp_localization DerivedCategory.Q _
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj P) DerivedCategory.Q
    (NatIso.ofComponents (fun K ↦ T.comparisonRight K P hP) (fun {K K'} f ↦ ?_))
  have h := T.comparisonRight_naturality f (𝟙 P) hP hP
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

end Stacks.SheafOfModules.DerivedTensorProduct
