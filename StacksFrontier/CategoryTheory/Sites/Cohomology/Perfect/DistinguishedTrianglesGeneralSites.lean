module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMapGeneral

/-!
# Perfect objects and distinguished triangles, at independent site universes

Let `(C, O)` be a ringed site and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(O)`.
If two of `K`, `L`, `M` are perfect then so is the third (Stacks 08G9).
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DistinguishedTriangles.lean` proves this at
`RingedSite.{u, u, 0}`, because the form of Stacks 08FR it used tied the universes of the site.
That form is now available with the object, morphism and section universes independent
(`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_general`), and with it the same
argument runs at `RingedSite.{u, v, w}`.  This is what the small étale site of an algebraic space,
a `RingedSite.{u + 1, u, u}`, needs.

## Main results

* `AlgebraicGeometry.RingedSite.nonempty_mappingCone_iso_mapDerivedCategory_obj₃`: after an exact
  functor, the third object of a distinguished triangle is the cone of a map of representatives.
* `AlgebraicGeometry.RingedSite.modelSieveGeneral` and
  `AlgebraicGeometry.RingedSite.isPerfectComplex_iff_modelSieveGeneral`: perfectness of a complex
  as a covering condition on the sieve of objects carrying a strictly perfect model.

## Implementation notes

The argument is the one of the tied file: above a small enough object both `K` and `L` have
strictly perfect models, the map `K ⟶ L` is there the image of a map of complexes (Stacks 08FR),
and `M` is the cone of that map, which is strictly perfect (Stacks 08FM).  The derived categories
of the slices are taken at the standard model, which is the one Stacks 08FR is stated at; the
conclusion, perfectness, is a statement about complexes and does not see that choice.

The three implications of Stacks 08G9 and the stability under shifts at these universes are
`AlgebraicGeometry.RingedSite.isPerfect_obj₃_of_distinguished_general`,
`AlgebraicGeometry.RingedSite.isPerfect_obj₂_of_distinguished_general`,
`AlgebraicGeometry.RingedSite.isPerfect_obj₁_of_distinguished_general` and
`AlgebraicGeometry.RingedSite.isPerfect_shift_general`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DistinguishedTrianglesGeneral.lean`.

## References

* [Stacks Project, Tag 08G9](https://stacks.math.columbia.edu/tag/08G9)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u₁ u₂ v₁ v₂ u v w d

namespace AlgebraicGeometry.RingedSite

section Cone

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- **The third object of a distinguished triangle is, after an exact functor, a cone.**  Let `H`
be an exact functor of abelian categories and `T` a distinguished triangle in `D(A)` whose first
two objects are represented by complexes `P` and `Q`, and let `α : P ⟶ Q` in `D(A)` correspond to
`T.mor₁` under these identifications.  If `H(α)` is represented by a map of complexes `β`, then
the cone of `β` represents `H(T.obj₃)`. -/
theorem nonempty_mappingCone_iso_mapDerivedCategory_obj₃
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    {P Q : CochainComplex A ℤ}
    (eP : DerivedCategory.Q.obj P ≅ T.obj₁) (eQ : DerivedCategory.Q.obj Q ≅ T.obj₂)
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q)
    (hα : eP.hom ≫ T.mor₁ = α ≫ eQ.hom)
    (β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (hβ : H.mapDerivedCategory.map α ≫ H.mapDerivedCategoryFactors.hom.app Q =
      H.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone β) ≅
      H.mapDerivedCategory.obj T.obj₃) := by
  let i : Arrow.mk α ≅ Arrow.mk T.mor₁ := Arrow.isoMk eP eQ hα
  let j : Arrow.mk (DerivedCategory.Q.map β) ≅ Arrow.mk (H.mapDerivedCategory.map α) :=
    Arrow.isoMk (H.mapDerivedCategoryFactors.app P).symm
      (H.mapDerivedCategoryFactors.app Q).symm (by
        show H.mapDerivedCategoryFactors.inv.app P ≫ H.mapDerivedCategory.map α =
          DerivedCategory.Q.map β ≫ H.mapDerivedCategoryFactors.inv.app Q
        apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app Q)).mp
        simpa only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
          Iso.inv_hom_id_app_assoc] using
          congrArg (fun f => H.mapDerivedCategoryFactors.inv.app P ≫ f) hβ)
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β))
    (H.mapDerivedCategory.mapTriangle.obj T)
    (DerivedCategory.mappingCone_triangle_distinguished β)
    (H.mapDerivedCategory.map_distinguished T hT)
    (j ≪≫ H.mapDerivedCategory.mapArrow.mapIso i)
  exact ⟨Triangle.π₃.mapIso e⟩

end Cone

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The sieve on `U` of the arrows whose source carries a strictly perfect model of the
restriction of `E`.  It is a sieve because such a model restricts along every arrow of the site
(`AlgebraicGeometry.RingedSite.exists_localModel_restrictComplex_of_hom`). -/
def modelSieveGeneral
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) : Sieve U where
  arrows V _ := ∃ P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      ∃ q : P ⟶ X.restrictComplex E V, QuasiIso q
  downward_closed h g := exists_localModel_restrictComplex_of_hom X _ g h

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A complex is perfect exactly when the sieve of objects carrying a strictly perfect model of
its restriction is covering above every object of the site. -/
theorem isPerfectComplex_iff_modelSieveGeneral
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    X.IsPerfectComplex E ↔ ∀ U : X.C, modelSieveGeneral X E U ∈ X.J U := by
  refine ⟨fun h U => ?_, fun h U => ⟨(modelSieveGeneral X E U).arrows, ?_, fun _ _ hf => hf⟩⟩
  · obtain ⟨S, hS, hm⟩ := h U
    exact X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr hm) hS
  · rw [Sieve.generate_sieve]; exact h U

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A strictly perfect complex isomorphic in `D(O|_U)` to the restriction of `E` to `U` makes the
model sieve of `E` covering above `U`: by Stacks 08FR the isomorphism is, on a covering sieve of
`U`, an honest quasi-isomorphism. -/
theorem modelSieveGeneral_mem_of_iso
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    [HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    {P : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (X.restrictComplex E U)) :
    modelSieveGeneral X E U ∈ X.J U := by
  obtain ⟨S, hS, hquasi⟩ := exists_coveringSieve_quasiIso_of_derivedIso_general X U hP e
  refine X.J.superset_covering (fun W g hg => ?_) hS
  obtain ⟨β, hβ⟩ := hquasi g hg
  let := hβ
  let c := (Stacks.SheafOfModules.overFunctorMapComplexIso
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app E
  refine ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP, β ≫ c.hom, ?_⟩
  let : IsIso c.hom := c.isIso_hom
  infer_instance

end AlgebraicGeometry.RingedSite

end
