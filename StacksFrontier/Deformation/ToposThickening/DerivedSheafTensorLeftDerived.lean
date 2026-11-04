module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.Resolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate

/-!
# The derived tensor product of a ringed site is a left derived functor

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`. For a sheaf of `O`-modules `M` this file exhibits
the partial functor `- ⊗^L_O M[0]` as the **total left derived functor** of the degreewise
tensor product `- ⊗_O M`, which is the universal property that
`CategoryTheory.Functor.leftDerivedUnique` and
`CategoryTheory.LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions` consume and which
the structure itself does not record.

The comparison is the structure's own canonical map `toTensor` to the total tensor complex,
followed by the identification of `Tot(K ⊗_O M[0])` with `K ⊗_O M` read degreewise. It is
invertible as soon as the left factor is K-flat, and the K-flat complexes resolve every complex
by Stacks 06YS, which is the criterion
`CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolvingComplexes`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.toTensorSingle`: the canonical map
  `- ⊗^L_O M[0] ⟶ Tot(- ⊗_O M[0])` as a natural transformation of functors on complexes.
* `Stacks.SheafOfModules.DerivedTensorProduct.singleTensorComparison`: that map followed by the
  degreewise identification, i.e. the comparison of `- ⊗^L_O M[0]` with `- ⊗_O M`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isIso_toTensor_of_kFlat_left`: the canonical map
  to the total tensor complex is invertible at a K-flat left factor.
* `Stacks.SheafOfModules.exists_kFlat_quasiIso_homotopy`: **Stacks 06YS on the homotopy
  category**, which is the resolving hypothesis the criterion takes.
* `Stacks.SheafOfModules.DerivedTensorProduct.isLeftDerivedFunctor_singleTensorComparison`:
  **`- ⊗^L_O M[0]` is the total left derived functor of `- ⊗_O M`.**

## Implementation notes

This is the ringed-*site* form, at a site all three of whose universes are free and at an
independent derived-category universe, of
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringOfResolvingComplexes`:
the same four steps — the canonical map, its invertibility on K-flat complexes, the degreewise
identification `HomologicalComplex.map₂SingleRightNatIso`, and the resolving-class criterion —
run against `Stacks.SheafOfModules.DerivedTensorProduct` instead of against the ringed-space
structure `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`. Nothing is reproved:
both the criterion and the degreewise identification are cited from the ringed-space file, where
they are already stated over an arbitrary abelian category and an arbitrary bifunctor.

Only the *left* variable is treated, and only a module in degree zero sits in the right one.
That is the shape the reduction triangle of
`StacksFrontier/Deformation/ToposThickening/DerivedReductionTriangle.lean` is built at, and it is
the shape in which a comparison with derived base change — also a left derived functor in the
one variable — can be read off uniqueness of left derived functors.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### Stacks 06YS on the homotopy category -/

/-- **Stacks 06YS on the homotopy category.** Every object of `K(Mod(O))` receives a
quasi-isomorphism from a K-flat complex: resolve a representing complex and pass to the
homotopy category, where a map is a quasi-isomorphism exactly when it is one on complexes. -/
theorem exists_kFlat_quasiIso_homotopy
    (Y : HomotopyCategory (Modules.{u, v, w} X) (ComplexShape.up ℤ)) :
    ∃ (Z : HomotopyCategory (Modules.{u, v, w} X) (ComplexShape.up ℤ))
      (_ : IsKFlat X.O Z.as) (s : Z ⟶ Y),
      HomotopyCategory.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ) s := by
  obtain ⟨P, p, hP, hp⟩ := KFlatResolution.exists_kFlat_quasiIso_ofSize X.O Y.as
  exact ⟨(HomotopyCategory.quotient _ _).obj P, hP, (HomotopyCategory.quotient _ _).map p,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩

variable [HasDerivedCategory.{d} (Modules.{u, v, w} X)]

/-- Tensoring on the right with a fixed sheaf of modules is additive, `⊗_O` being additive in
its first variable. -/
instance sheafTensor_flip_obj_additive (M : Modules.{u, v, w} X) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).flip.obj M).Additive where
  map_add := fun {_ _ f g} =>
    congrArg (fun α => NatTrans.app α M)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).map_add (f := f) (g := g))

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-! ### The canonical map to the total tensor complex, in the left variable -/

/-- **The canonical map to the total tensor complex is invertible at a K-flat left factor**: it
is then the left K-flat comparison isomorphism of the derived tensor product. -/
theorem isIso_toTensor_of_kFlat_left (K L : CochainComplex (Modules.{u, v, w} X) ℤ)
    (hK : IsKFlat X.O K) : IsIso (T.toTensor K L) := by
  rw [T.toTensor_eq_comparisonLeft K L hK]
  infer_instance

/-- Naturality of the canonical map to the total tensor complex in the left variable alone. -/
theorem toTensor_naturality_left {K K' : CochainComplex (Modules.{u, v, w} X) ℤ} (f : K ⟶ K')
    (L : CochainComplex (Modules.{u, v, w} X) ℤ) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        T.toTensor K' L =
      T.toTensor K L ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f (𝟙 L)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have h := T.toTensor_naturality f (𝟙 L)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- **The canonical map `- ⊗^L_O M[0] ⟶ Tot(- ⊗_O M[0])`** of Stacks 06YU, read as a natural
transformation of functors on complexes. -/
def toTensorSingle (M : Modules.{u, v, w} X) :
    DerivedCategory.Q ⋙
        T.tensor.flip.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M)) ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.obj
          ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M) ⋙
        DerivedCategory.Q where
  app K := T.toTensor K ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M)
  naturality _ _ f :=
    T.toTensor_naturality_left f
      ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M)

/-- **`Tot(- ⊗_O M[0])` is `- ⊗_O M` read degreewise**, after the localization: the second
factor carries no differential, so only one summand of the total complex survives. -/
def totalTensorSingleIso (M : Modules.{u, v, w} X) :
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O).map₂CochainComplex.flip.obj
          ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M) ⋙
        DerivedCategory.Q ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
    (HomologicalComplex.map₂SingleRightNatIso
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) M).symm DerivedCategory.Q

/-- **The comparison of `- ⊗^L_O M[0]` with the degreewise tensor product `- ⊗_O M`.** On a
complex `K` it is the canonical map of Stacks 06YU to the total tensor complex
`Tot(K ⊗_O M[0])`, followed by the identification of that complex with `K ⊗_O M` read
degreewise. -/
def singleTensorComparison (M : Modules.{u, v, w} X) :
    DerivedCategory.Q ⋙
        T.tensor.flip.obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M)) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  T.toTensorSingle M ≫ (totalTensorSingleIso M).hom

/-- **At a K-flat complex the comparison is invertible.** The canonical map to the total tensor
complex is an isomorphism as soon as the left factor is K-flat, and the degreewise
identification is an isomorphism always. -/
theorem isIso_singleTensorComparison_app (M : Modules.{u, v, w} X)
    (K : CochainComplex (Modules.{u, v, w} X) ℤ) (hK : IsKFlat X.O K) :
    IsIso ((T.singleTensorComparison M).app K) := by
  have h₁ : IsIso ((T.toTensorSingle M).app K) :=
    T.isIso_toTensor_of_kFlat_left K
      ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M) hK
  have h₂ : IsIso ((totalTensorSingleIso M).hom.app K) :=
    ((totalTensorSingleIso (X := X) M).app K).isIso_hom
  exact IsIso.comp_isIso' h₁ h₂

/-- The degreewise tensor product read on the homotopy category, precomposed with the homotopy
quotient, is the degreewise tensor product on complexes followed by the localization. This is
the factorization the resolving-class criterion asks for. -/
def quotientCompTensorSingleIso (M : Modules.{u, v, w} X) :
    HomotopyCategory.quotient (Modules.{u, v, w} X) (ComplexShape.up ℤ) ⋙
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules.{u, v, w} X))

/-- **`- ⊗^L_O M[0]` is the total left derived functor of `- ⊗_O M`.** The comparison
`Stacks.SheafOfModules.DerivedTensorProduct.singleTensorComparison` is invertible at every
K-flat complex, and the K-flat complexes resolve every object of the homotopy category by
Stacks 06YS, so the comparison already has the universal property of the total left derived
functor along the localization of cochain complexes at the quasi-isomorphisms.

This is the universal property that the structure
`Stacks.SheafOfModules.DerivedTensorProduct` does not itself record, and the one from which a
comparison with any other left derived functor of `- ⊗_O M` — derived base change along a
surjection `O ⟶ O/I`, say — is a formal consequence. -/
theorem isLeftDerivedFunctor_singleTensorComparison (M : Modules.{u, v, w} X) :
    (T.tensor.flip.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules.{u, v, w} X) 0).obj M))).IsLeftDerivedFunctor
      (T.singleTensorComparison M)
      (HomologicalComplex.quasiIso (Modules.{u, v, w} X) (ComplexShape.up ℤ)) :=
  CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolvingComplexes
    (IsKFlat X.O) exists_kFlat_quasiIso_homotopy _
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj M).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (quotientCompTensorSingleIso M) _ (T.singleTensorComparison M)
    (fun K hK => T.isIso_singleTensorComparison_app M K hK)

end DerivedTensorProduct

end Stacks.SheafOfModules

end
