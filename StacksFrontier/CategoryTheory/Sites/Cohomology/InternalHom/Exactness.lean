module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated

/-!
# The derived internal Hom is exact in the covariant variable

Let `(C, O)` be a ringed site.  The derived internal Hom out of a fixed object,
`RSheafHom(E, -) : D(O) ⥤ D(O)`, carries a distinguished triangle of `D(O)` to a distinguished
triangle.  This is the covariant half of the assertion that `RSheafHom(-, -)` transforms
distinguished triangles into distinguished triangles in both variables.

## Main results

* `AlgebraicGeometry.RingedSite.exists_kInjective_degreewiseSplit_presentation`: every
  distinguished triangle of `D(O)` is isomorphic to the triangle of a termwise split short exact
  sequence of complexes all three of whose terms are K-injective.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality_id_second`: the K-injective
  model comparison is natural in the target at a fixed source, in the
  `Stacks.Cohomology.InternalHom.sheafHomComplexMap` spelling.
* `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_second`: the derived
  internal Hom out of a fixed object carries a distinguished triangle to a distinguished
  triangle.

## Implementation notes

The statements name the ambient category in `CategoryTheory.Pretriangulated.distTriang`
explicitly rather than writing `distTriang _`: with the placeholder, the existential binder for
the connecting morphism enters the instance problem and the search for
`CategoryTheory.Abelian (SheafOfModules X.ringSheaf)` exhausts its heartbeats.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Every distinguished triangle of `D(O)` is presented by a termwise split short exact
sequence of K-injective complexes.** -/
theorem exists_kInjective_degreewiseSplit_presentation
    (T : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ (S : ShortComplex
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
      (σ : ∀ n, (S.map (HomologicalComplex.eval
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
          n)).Splitting),
      S.X₁.IsKInjective ∧ S.X₂.IsKInjective ∧ S.X₃.IsKInjective ∧
        Nonempty (T ≅ DerivedCategory.Q.mapTriangle.obj
          (CochainComplex.triangleOfDegreewiseSplit S σ)) := by
  obtain ⟨A, B, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T.invRotate).mp
    (inv_rot_of_distTriang _ hT)
  set g : (kInjectiveResolution X).obj A ⟶ (kInjectiveResolution X).obj B :=
    (kInjectiveResolution X).map f with hg
  have harrow : Arrow.mk (DerivedCategory.Q.map f) ≅ Arrow.mk (DerivedCategory.Q.map g) :=
    Arrow.isoMk (asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app A)))
      (asIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app B))) (by
        symm
        change DerivedCategory.Q.map f ≫
            DerivedCategory.Q.map ((kInjectiveAugmentation X).app B) =
          DerivedCategory.Q.map ((kInjectiveAugmentation X).app A) ≫ DerivedCategory.Q.map g
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg DerivedCategory.Q.map ((kInjectiveAugmentation X).naturality f))
  obtain ⟨e₂, -, -⟩ := exists_iso_of_arrow_iso _ _
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) harrow
  have hcone : (CochainComplex.mappingCone g).IsKInjective := by
    rw [CochainComplex.isKInjective_iff_rightOrthogonal]
    exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
      (HomotopyCategory.mappingCone_triangleh_distinguished g)
      (CochainComplex.IsKInjective.rightOrthogonal ((kInjectiveResolution X).obj A))
      (CochainComplex.IsKInjective.rightOrthogonal ((kInjectiveResolution X).obj B))
  refine ⟨CochainComplex.mappingCone.triangleRotateShortComplex g,
    CochainComplex.mappingCone.triangleRotateShortComplexSplitting g,
    inferInstanceAs (((kInjectiveResolution X).obj B).IsKInjective), hcone,
    inferInstanceAs ((((kInjectiveResolution X).obj A)⟦(1 : ℤ)⟧).IsKInjective), ⟨?_⟩⟩
  exact (invRotCompRot.app T).symm ≪≫ (rotate _).mapIso (e ≪≫ e₂) ≪≫
    DerivedCategory.Q.mapTriangleRotateIso.app (CochainComplex.mappingCone.triangle g) ≪≫
    DerivedCategory.Q.mapTriangle.mapIso
      (CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit g)

/-- The K-injective model comparison, natural in the target at a fixed source, in the
`Stacks.Cohomology.InternalHom.sheafHomComplexMap` spelling. -/
theorem derivedSheafHomComparison_naturality_id_second
    {K M M' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [M.IsKInjective] [M'.IsKInjective] (g : M ⟶ M') :
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).map
          (DerivedCategory.Q.map g) ≫ (derivedSheafHomComparison X K M').hom =
      (derivedSheafHomComparison X K M).hom ≫
        DerivedCategory.Q.map (Stacks.Cohomology.InternalHom.sheafHomComplexMap X (𝟙 K) g) := by
  have h := derivedSheafHomComparison_naturality X (𝟙 K) g
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  rw [h, Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap]

/-- For a triangle presented by a termwise split short exact sequence of K-injective complexes
and the class of a complex `K` in the fixed slot, the two morphisms induced on the derived
internal Hom out of `K` extend to a distinguished triangle of `D(O)`. -/
theorem exists_distinguished_derivedSheafHom_second_of_ses
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
        n)).Splitting)
    (h₁ : S.X₁.IsKInjective) (h₂ : S.X₂.IsKInjective) (h₃ : S.X₃.IsKInjective) :
    ∃ δ : ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
          (DerivedCategory.Q.obj S.X₃) ⟶
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
          (DerivedCategory.Q.obj S.X₁))⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).map
          (DerivedCategory.Q.map S.f))
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).map
          (DerivedCategory.Q.map S.g))
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  let _ := h₁
  let _ := h₂
  let _ := h₃
  obtain ⟨w, hSE⟩ := Stacks.Cohomology.InternalHom.internalHom_shortExact_second X S
    (fun n => ⟨σ n⟩) K
  exact exists_distinguished_of_iso _ _ _ (DerivedCategory.triangleOfSES_distinguished hSE)
    (derivedSheafHomComparison X K S.X₁) (derivedSheafHomComparison X K S.X₂)
    (derivedSheafHomComparison X K S.X₃)
    (derivedSheafHomComparison_naturality_id_second X S.f)
    (derivedSheafHomComparison_naturality_id_second X S.g)

/-- For a triangle presented by a termwise split short exact sequence of K-injective complexes
and any object `E` of `D(O)`, the two morphisms induced on the derived internal Hom out of `E`
extend to a distinguished triangle of `D(O)`. -/
theorem exists_distinguished_derivedSheafHom_second_of_ses_obj
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
        n)).Splitting)
    (h₁ : S.X₁.IsKInjective) (h₂ : S.X₂.IsKInjective) (h₃ : S.X₃.IsKInjective) :
    ∃ δ : ((derivedSheafHomBifunctor X).obj (op E)).obj (DerivedCategory.Q.obj S.X₃) ⟶
        (((derivedSheafHomBifunctor X).obj (op E)).obj (DerivedCategory.Q.obj S.X₁))⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).obj (op E)).map (DerivedCategory.Q.map S.f))
        (((derivedSheafHomBifunctor X).obj (op E)).map (DerivedCategory.Q.map S.g))
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom_second_of_ses X
    (DerivedCategory.Q.objPreimage E) S σ h₁ h₂ h₃
  let c := (derivedSheafHomBifunctor X).mapIso (DerivedCategory.Q.objObjPreimageIso E).op
  exact exists_distinguished_of_iso _ _ _ hδ
    (c.app (DerivedCategory.Q.obj S.X₁)) (c.app (DerivedCategory.Q.obj S.X₂))
    (c.app (DerivedCategory.Q.obj S.X₃))
    (c.hom.naturality (DerivedCategory.Q.map S.f))
    (c.hom.naturality (DerivedCategory.Q.map S.g))

/-- The derived internal Hom out of a fixed object carries a distinguished triangle of `D(O)` to
a distinguished triangle: for any distinguished `T` and any `E`, the two morphisms
`RSheafHom(E, T.obj₁) ⟶ RSheafHom(E, T.obj₂) ⟶ RSheafHom(E, T.obj₃)` induced by `T.mor₁` and
`T.mor₂` extend by a connecting morphism to a distinguished triangle. -/
@[stacks 08JC "covariant variable"]
theorem exists_distinguished_derivedSheafHom_second
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (T : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ δ : ((derivedSheafHomBifunctor X).obj (op E)).obj T.obj₃ ⟶
        (((derivedSheafHomBifunctor X).obj (op E)).obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).obj (op E)).map T.mor₁)
        (((derivedSheafHomBifunctor X).obj (op E)).map T.mor₂)
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain ⟨S, σ, h₁, h₂, h₃, ⟨e⟩⟩ := exists_kInjective_degreewiseSplit_presentation X T hT
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom_second_of_ses_obj X E S σ h₁ h₂ h₃
  let H := (derivedSheafHomBifunctor X).obj (op E)
  refine exists_distinguished_of_iso _ _ _ hδ (H.mapIso (Triangle.π₁.mapIso e))
    (H.mapIso (Triangle.π₂.mapIso e)) (H.mapIso (Triangle.π₃.mapIso e)) ?_ ?_
  · exact (H.map_comp _ _).symm.trans ((congrArg H.map e.hom.comm₁).trans (H.map_comp _ _))
  · exact (H.map_comp _ _).symm.trans ((congrArg H.map e.hom.comm₂).trans (H.map_comp _ _))

end AlgebraicGeometry.RingedSite

end
