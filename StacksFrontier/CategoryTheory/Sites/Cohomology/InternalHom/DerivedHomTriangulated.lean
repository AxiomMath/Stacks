module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TermwiseSplitShortExact
public import StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso

/-!
# Derived internal Hom of a distinguished triangle

Let `(C, O)` be a ringed site.  Stacks 08JC says that `RSheafHom(-, -)` carries distinguished
triangles of `D(O)` to distinguished triangles in either variable.  This file proves the
contravariant half in full: for an arbitrary distinguished triangle and an arbitrary object in
the fixed slot.

The route is the one the source's proof indicates and the one the ring-level analogue of this
development takes.  A termwise split short exact sequence of complexes stays short exact after
applying the internal Hom complex — `Stacks.Cohomology.InternalHom.internalHom_shortExact_first`
— and a short exact sequence of complexes gives a distinguished triangle in the derived category
by `CategoryTheory.DerivedCategory.triangleOfSES_distinguished`.  Comparing that triangle with
the one built from the derived internal Hom is exactly the naturality of the K-injective model
comparison, `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality_id`: the K-injective model
  comparison intertwines the map induced on derived internal Hom by a morphism of the source with
  the induced map of internal Hom complexes, in the `sheafHomComplexMap` spelling.
* `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_of_ses`: **Stacks 08JC in the
  contravariant variable**, for a triangle presented by a termwise split short exact sequence and
  a K-injective object in the fixed slot.
* `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_of_ses_obj`: the same with an
  **arbitrary** object in the fixed slot, by passing to its K-injective model.
* `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`: **Stacks 08JC in the
  contravariant variable**, for an arbitrary distinguished triangle, since every distinguished
  triangle is presented by a termwise split short exact sequence of complexes.

## Implementation notes

The statement is the "there is a connecting morphism making the image a distinguished triangle"
form rather than a `CategoryTheory.Functor.IsTriangulated` instance, and that is deliberate.
`Functor.IsTriangulated` is defined relative to a chosen `CategoryTheory.Functor.CommShift`, and
no `CommShift` exists for the derived internal Hom in the **contravariant** variable in this
development — the covariant one is
`AlgebraicGeometry.RingedSite.commShift_derivedSheafHom`, transported along
`AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction`; the
ring-level analogue of this result,
`StacksDraft.DerivedHom.exists_distinguished_derivedHom` in
`StacksFrontier/Homology/HomComplex/Evaluation/Iterated.lean`, takes the same form for the same
reason.

`derivedSheafHomComparison_naturality_id` is where the two parallel spellings of the induced map
of internal Hom complexes have to be identified: the comparison's naturality is stated for
`AlgebraicGeometry.RingedSite.homMap`, while short exactness above is stated for
`Stacks.Cohomology.InternalHom.sheafHomComplexMap`.  That identification is
`Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap`.

The reduction to an arbitrary object in the fixed slot is carried out by the K-injective model
`AlgebraicGeometry.RingedSite.kInjectiveModel` and its isomorphism, transported again by
`CategoryTheory.Pretriangulated.exists_distinguished_of_iso`.  That statement names the ambient
category in `distTriang` explicitly rather than writing `distTriang _`: with the placeholder, the
existential binder for the connecting morphism enters the instance problem and the search for
`CategoryTheory.Abelian (SheafOfModules X.ringSheaf)` exhausts its heartbeats.

Tag 08JC asserts the statement in *both* variables, so its covering set is two declarations:
the contravariant one below and the covariant
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_second` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/Exactness.lean`.

The two variables are not symmetric.  The comparison requires the **target** to be K-injective
and allows an arbitrary source, so contravariantly the fixed slot carries that condition and the
triangle varies in the source, where none is needed; covariantly the triangle varies in the
target, which is why the covariant half presents it by a termwise split short exact sequence of
K-injective complexes.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The K-injective model comparison, natural in the source at a fixed K-injective target, in the
`Stacks.Cohomology.InternalHom.sheafHomComplexMap` spelling.  This is
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality` at an identity target, with
the two spellings of the induced map identified. -/
theorem derivedSheafHomComparison_naturality_id
    {K K' M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [M.IsKInjective]
    (f : K' ⟶ K) :
    ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
        (DerivedCategory.Q.obj M) ≫ (derivedSheafHomComparison X K' M).hom =
      (derivedSheafHomComparison X K M).hom ≫
        DerivedCategory.Q.map (Stacks.Cohomology.InternalHom.sheafHomComplexMap X f (𝟙 M)) := by
  have h := derivedSheafHomComparison_naturality X f (𝟙 M)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [h, Stacks.Cohomology.InternalHom.homMap_eq_sheafHomComplexMap]

/-- **Stacks 08JC, contravariant variable**, for a triangle presented by a termwise split short
exact sequence of complexes and a K-injective object in the fixed slot: the two morphisms induced
on derived internal Hom extend to a distinguished triangle of `D(O)`.

Note the reversal of order, which is the contravariance: the morphism induced by `S.g` comes
first. -/
theorem exists_distinguished_derivedSheafHom_of_ses
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [M.IsKInjective] :
    ∃ δ, Triangle.mk
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map S.g).op).app
        (DerivedCategory.Q.obj M))
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map S.f).op).app
        (DerivedCategory.Q.obj M))
      δ ∈ distTriang _ := by
  obtain ⟨w, hSE⟩ := Stacks.Cohomology.InternalHom.internalHom_shortExact_first X S hS M
  exact exists_distinguished_of_iso _ _ _ (DerivedCategory.triangleOfSES_distinguished hSE)
    (derivedSheafHomComparison X S.X₃ M) (derivedSheafHomComparison X S.X₂ M)
    (derivedSheafHomComparison X S.X₁ M)
    (derivedSheafHomComparison_naturality_id X S.g)
    (derivedSheafHomComparison_naturality_id X S.f)

/-- **Stacks 08JC, contravariant variable, arbitrary object in the fixed slot.**  The same as
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_of_ses`, with the K-injective
hypothesis discharged by passing to the K-injective model of the given object. -/
theorem exists_distinguished_derivedSheafHom_of_ses_obj
    (S : ShortComplex
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
    (hS : ∀ n, Nonempty
      ((S.map (HomologicalComplex.eval
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ) n)).Splitting))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ∃ δ : ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj S.X₁))).obj E ⟶
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj S.X₃))).obj E)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map S.g).op).app E)
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map S.f).op).app E)
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom_of_ses X S hS (kInjectiveModel X E)
  let c := (derivedSheafHomBifunctor X).flip.mapIso (kInjectiveModelIso X E).symm
  exact exists_distinguished_of_iso _ _ _ hδ
    (c.app (op (DerivedCategory.Q.obj S.X₃)))
    (c.app (op (DerivedCategory.Q.obj S.X₂)))
    (c.app (op (DerivedCategory.Q.obj S.X₁)))
    (c.hom.naturality (DerivedCategory.Q.map S.g).op)
    (c.hom.naturality (DerivedCategory.Q.map S.f).op)

/-- **Stacks 08JC, contravariant variable.**  The derived internal Hom into a fixed object carries
a distinguished triangle of `D(O)` to a distinguished triangle: for any distinguished `T` and any
`E`, the two morphisms `RSheafHom(T.obj₃, E) ⟶ RSheafHom(T.obj₂, E) ⟶ RSheafHom(T.obj₁, E)`
induced by `T.mor₂` and `T.mor₁` extend by a connecting morphism to a distinguished triangle.

Every distinguished triangle is presented by a termwise split short exact sequence of complexes,
so this follows from
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom_of_ses_obj`. -/
@[stacks 08JC "contravariant variable"]
theorem exists_distinguished_derivedSheafHom
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (T : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    ∃ δ : ((derivedSheafHomBifunctor X).flip.obj E).obj (op T.obj₁) ⟶
        (((derivedSheafHomBifunctor X).flip.obj E).obj (op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHomBifunctor X).flip.obj E).map T.mor₂.op)
        (((derivedSheafHomBifunctor X).flip.obj E).map T.mor₁.op)
        δ ∈ distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  obtain ⟨A, B, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T.invRotate).mp
    (inv_rot_of_distTriang _ hT)
  let S := CochainComplex.mappingCone.triangleRotateShortComplex f
  let σ := CochainComplex.mappingCone.triangleRotateShortComplexSplitting f
  let e' : T ≅ DerivedCategory.Q.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S σ) :=
    (invRotCompRot.app T).symm ≪≫ (rotate _).mapIso e ≪≫
      DerivedCategory.Q.mapTriangleRotateIso.app (CochainComplex.mappingCone.triangle f) ≪≫
      DerivedCategory.Q.mapTriangle.mapIso
        (CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit f)
  let H := (derivedSheafHomBifunctor X).flip.obj E
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom_of_ses_obj X S (fun n => ⟨σ n⟩) E
  let i₁ : T.obj₁ ≅ DerivedCategory.Q.obj S.X₁ :=
    ⟨e'.hom.hom₁, e'.inv.hom₁, e'.hom_inv_id_triangle_hom₁, e'.inv_hom_id_triangle_hom₁⟩
  let i₂ : T.obj₂ ≅ DerivedCategory.Q.obj S.X₂ :=
    ⟨e'.hom.hom₂, e'.inv.hom₂, e'.hom_inv_id_triangle_hom₂, e'.inv_hom_id_triangle_hom₂⟩
  let i₃ : T.obj₃ ≅ DerivedCategory.Q.obj S.X₃ :=
    ⟨e'.hom.hom₃, e'.inv.hom₃, e'.hom_inv_id_triangle_hom₃, e'.inv_hom_id_triangle_hom₃⟩
  have key : ∀ {A B C D : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
      {a : A ⟶ B} {b : C ⟶ D} {u : A ⟶ C} {v : B ⟶ D} (_ : a ≫ v = u ≫ b),
      H.map v.op ≫ H.map a.op = H.map b.op ≫ H.map u.op := fun h => by
    rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp, h]
  refine exists_distinguished_of_iso _ _ _ hδ
    (H.mapIso i₃.symm.op) (H.mapIso i₂.symm.op) (H.mapIso i₁.symm.op) ?_ ?_
  · exact (key e'.inv.comm₂).symm
  · exact (key e'.inv.comm₁).symm

end AlgebraicGeometry.RingedSite

end
