module

public import Mathlib.Algebra.Homology.Bifunctor
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomLeftAdjoint

/-!
# The projection map on total complexes

Let `E ⊣ F` be an adjunction of additive functors and let `μ : F(A ⊗ B) ≅ F A ⊗ F B` compare
two tensor bifunctors. If every projection map `E(Z ⊗ F M) ⟶ E Z ⊗ M`
(`CategoryTheory.PullbackInternalHom.leftAdjointProjectionMap`) is invertible, then on cochain
complexes the projection maps in each bidegree assemble into an isomorphism of total complexes
`E Tot(W ⊗ F N) ≅ Tot(E W ⊗ N)`.

## Main definitions

* `CategoryTheory.PullbackInternalHom.projectionBicomplexIso`: the bidegreewise isomorphism.
* `CategoryTheory.PullbackInternalHom.projectionTotalIso`: the isomorphism of total complexes.

## Main results

* `CategoryTheory.PullbackInternalHom.ι_projectionTotalIso_hom`: on each summand it is the
  projection map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackInternalHom

open HomologicalComplex₂.TotalMap

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {E : D ⥤ C} (adjE : E ⊣ F)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)

variable [E.Additive] [F.Additive] [∀ X, (TC.obj X).Additive] [∀ X, (TD.obj X).Additive]
  [TC.Additive] [TD.Additive]
  (hπ : ∀ Z M, IsIso (leftAdjointProjectionMap adjE TC TD μ Z M))

/-- The projection maps in each bidegree, as an isomorphism of bicomplexes
`E(W^p ⊗ F N^q) ≅ E W^p ⊗ N^q`. -/
def projectionBicomplexIso (W : CochainComplex D ℤ) (N : CochainComplex C ℤ) :
    mapBicomplex E (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj W).obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) ≅
    ((TC.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)).obj N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => @asIso _ _ _ _ (leftAdjointProjectionMap adjE TC TD μ (W.X p) (N.X q)) (hπ _ _))
      (fun q q' _ => (leftAdjointProjectionMap_naturality_right adjE TC TD μ (W.X p)
        (N.d q q')).symm))
    (fun p p' _ => by
      ext q : 1
      exact (leftAdjointProjectionMap_naturality_left adjE TC TD μ (W.d p p') (N.X q)).symm)

variable [∀ (W N : CochainComplex D ℤ), HomologicalComplex.HasMapBifunctor W N TD
    (ComplexShape.up ℤ)]
  [∀ (W N : CochainComplex C ℤ), HomologicalComplex.HasMapBifunctor W N TC (ComplexShape.up ℤ)]

/-- **The projection map on total complexes**: `E Tot(W ⊗ F N) ≅ Tot(E W ⊗ N)`, the projection
maps in each bidegree, through the commutation of `E` with total complexes. -/
def projectionTotalIso (W : CochainComplex D ℤ) (N : CochainComplex C ℤ) :
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HomologicalComplex.mapBifunctor W
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) TD (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) N
        TC (ComplexShape.up ℤ) :=
  haveI := adjE.leftAdjoint_preservesColimits.{0, 0}
  haveI := HomologicalComplex₂.hasTotal_of_iso
    (projectionBicomplexIso adjE TC TD μ hπ W N).symm (ComplexShape.up ℤ)
  (totalIso E _).symm ≪≫
    HomologicalComplex₂.total.mapIso (projectionBicomplexIso adjE TC TD μ hπ W N)
      (ComplexShape.up ℤ)

/-- **The projection map on total complexes is the projection map on each summand**: on the
summand of bidegree `(p, q)` it is `E(W^p ⊗ F N^q) ⟶ E W^p ⊗ N^q`. -/
lemma ι_projectionTotalIso_hom (W : CochainComplex D ℤ) (N : CochainComplex C ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    E.map (HomologicalComplex.ιMapBifunctor W ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)
        TD (ComplexShape.up ℤ) p q n hpq) ≫
        (projectionTotalIso adjE TC TD μ hπ W N).hom.f n =
      leftAdjointProjectionMap adjE TC TD μ (W.X p) (N.X q) ≫
        HomologicalComplex.ιMapBifunctor ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) N
          TC (ComplexShape.up ℤ) p q n hpq := by
  have := adjE.leftAdjoint_preservesColimits.{0, 0}
  have := HomologicalComplex₂.hasTotal_of_iso
    (projectionBicomplexIso adjE TC TD μ hπ W N).symm (ComplexShape.up ℤ)
  have hι := ι_totalMapf (c₁₂ := ComplexShape.up ℤ) E
    (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj W).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) n p q hpq
  have h1 : E.map ((((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj W).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)).ιTotal
          (ComplexShape.up ℤ) p q n hpq) ≫
      (totalIso E (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj W).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))).inv.f n =
        (mapBicomplex E (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj W).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))).ιTotal
              (ComplexShape.up ℤ) p q n hpq := by
    rw [← hι, Category.assoc,
      show totalMapf (c₁₂ := ComplexShape.up ℤ) E
            (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj W).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)) n ≫
          (totalIso E (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
            (ComplexShape.up ℤ)).obj W).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))).inv.f n = 𝟙 _ from
        congrArg (fun φ => HomologicalComplex.Hom.f φ n)
          (totalIso (c₁₂ := ComplexShape.up ℤ) E
            (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj W).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))).hom_inv_id,
      Category.comp_id]
  have h2 := HomologicalComplex₂.ιTotal_map (mapBicomplex E
      (((TD.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj W).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj N)))
    _ (projectionBicomplexIso adjE TC TD μ hπ W N).hom (ComplexShape.up ℤ) p q n hpq
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (HomologicalComplex₂.total.mapIso
      (projectionBicomplexIso adjE TC TD μ hπ W N) (ComplexShape.up ℤ)).hom.f n) h1)).trans h2

end CategoryTheory.PullbackInternalHom

end
