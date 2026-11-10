module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTriangles

/-!
# Perfect objects in distinguished triangles, at independent site universes

The three clauses of Stacks 08G9 — in a distinguished triangle of `D(O)` an object is perfect if
the other two are — for a ringed site whose objects, morphisms and sections of the structure
sheaf lie in three independent universes.  The statements of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/DistinguishedTriangles.lean`, which carry
the registrations of Stacks 08G9, are at `RingedSite.{u, u, 0}`, where the small étale site of an
algebraic space, a `RingedSite.{u + 1, u, u}`, is not reached; the proofs are the same, with
Stacks 08FR (1) read at independent universes
(`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_general`).

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_obj₃_of_distinguished_general`,
  `…isPerfect_obj₂_of_distinguished_general`, `…isPerfect_obj₁_of_distinguished_general`.

## References

* [Stacks Project, Tag 08G9](https://stacks.math.columbia.edu/tag/08G9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u₁ u₂ v₁ v₂ u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits

/-- The category of sheaves of modules over the restriction of the structure sheaf to `V` has a
derived category. -/
local instance trianglesHasDerivedOver_general (V : X.C) :
    HasDerivedCategory (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
  HasDerivedCategory.standard _

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- Carrying a strictly perfect model is stable under restriction along an arrow of the site. -/
theorem exists_strictlyPerfect_model_restrict_general
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {V W : X.C} (f : W ⟶ V)
    (h : ∃ P : CochainComplex (SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ q : P ⟶ X.restrictComplex E V, QuasiIso q) :
    ∃ P : CochainComplex (SheafOfModules.{w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ q : P ⟶ X.restrictComplex E W, QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  let HC := (SheafOfModules.overMap.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨HC.obj P, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general _ f hP,
    HC.map q ≫ ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).app E).hom, inferInstance⟩

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The sieve on `U` of arrows whose source carries a strictly perfect model of the restriction
of `E`. -/
def modelSieve_general
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) : Sieve U where
  arrows _ _ := ∃ P : CochainComplex (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over _)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over _) P ∧
      ∃ q : P ⟶ X.restrictComplex E _, QuasiIso q
  downward_closed h g := exists_strictlyPerfect_model_restrict_general X g h

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A complex is perfect exactly when the sieve of objects carrying a strictly perfect model of
its restriction is covering above every object of the site. -/
theorem isPerfectComplex_iff_modelSieve_general
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    X.IsPerfectComplex E ↔ ∀ U : X.C, modelSieve_general X E U ∈ X.J U := by
  refine ⟨fun h U => ?_, fun h U => ⟨(modelSieve_general X E U).arrows, ?_, fun _ _ hf => hf⟩⟩
  · obtain ⟨S, hS, hm⟩ := h U
    exact X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr hm) hS
  · simpa [Sieve.generate_sieve] using h U

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A strictly perfect complex isomorphic in `D(O|_U)` to the restriction of `E` to `U` makes the
model sieve of `E` covering above `U`: by Stacks 08FR the isomorphism is, on a covering sieve of
`U`, the image of an honest quasi-isomorphism. -/
theorem modelSieve_covering_of_iso_general
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C)
    {P : CochainComplex (SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (X.restrictComplex E U)) :
    modelSieve_general X E U ∈ X.J U := by
  obtain ⟨S, hS, hm⟩ := exists_coveringSieve_complexMap_general X U hP e.hom
  refine X.J.superset_covering (fun V f hf => ?_) hS
  obtain ⟨_, _, _, _, _, β, hβ⟩ := hm f hf
  let H := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have hi : IsIso (H.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β) := by
    rw [← hβ]
    infer_instance
  have : IsIso (DerivedCategory.Q.map β) :=
    IsIso.of_isIso_comp_left (H.mapDerivedCategoryFactors.hom.app P) _
  have : QuasiIso β := (DerivedCategory.isIso_Q_map_iff_quasiIso _ β).mp inferInstance
  exact ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general _ f hP,
    β ≫ ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).app E).hom, inferInstance⟩

/-- Perfectness of an object of `D(O)` is stable under shifting. -/
theorem isPerfect_shift_general
    {K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : X.IsPerfect K) (n : ℤ) : X.IsPerfect (K⟦n⟧) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  refine ⟨E⟦n⟧, fun U => ?_,
    ⟨(DerivedCategory.Q.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso e⟩⟩
  obtain ⟨S, hS, hm⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hm f hf
  let F := (SheafOfModules.overFunctor.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨P⟦n⟧, SheafOfModules.isStrictlyPerfect_shift _ hP n,
    q⟦n⟧' ≫ ((F.commShiftIso n).app E).inv, inferInstance⟩

/-- **Stacks 08G9, third object.** In a distinguished triangle of `D(O)`, the third object is
perfect if the first two are. -/
theorem isPerfect_obj₃_of_distinguished_general
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : X.IsPerfect T.obj₁) (h₂ : X.IsPerfect T.obj₂) :
    X.IsPerfect T.obj₃ := by
  classical
  obtain ⟨A, hA, ⟨a⟩⟩ := h₁
  obtain ⟨B, hB, ⟨b⟩⟩ := h₂
  let E := DerivedCategory.Q.objPreimage T.obj₃
  let e : DerivedCategory.Q.obj E ≅ T.obj₃ := DerivedCategory.Q.objObjPreimageIso _
  refine ⟨E, (isPerfectComplex_iff_modelSieve_general X E).mpr fun U => ?_, ⟨e⟩⟩
  refine X.J.transitive (X.J.intersection_covering
    ((isPerfectComplex_iff_modelSieve_general X A).mp hA U)
    ((isPerfectComplex_iff_modelSieve_general X B).mp hB U))
    (modelSieve_general X E U) fun {V} f hf => ?_
  change modelSieve_general X E V ∈ X.J V
  obtain ⟨P, hP, p, hp⟩ := hf.1
  obtain ⟨Q, hQ, q, hq⟩ := hf.2
  let R := SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  let T' := R.mapDerivedCategory.mapTriangle.obj T
  let eP : DerivedCategory.Q.obj P ≅ T'.obj₁ :=
    asIso (DerivedCategory.Q.map p) ≪≫ (R.mapDerivedCategoryFactors.app A).symm ≪≫
      R.mapDerivedCategory.mapIso a
  let eQ : DerivedCategory.Q.obj Q ≅ T'.obj₂ :=
    asIso (DerivedCategory.Q.map q) ≪≫ (R.mapDerivedCategoryFactors.app B).symm ≪≫
      R.mapDerivedCategory.mapIso b
  obtain ⟨S, hS, hm⟩ :=
    exists_coveringSieve_complexMap_general X V hP (eP.hom ≫ T'.mor₁ ≫ eQ.inv)
  refine X.J.transitive hS (modelSieve_general X E V) fun {W} g hg => ?_
  change modelSieve_general X E W ∈ X.J W
  obtain ⟨_, _, _, _, _, β, hβ⟩ := hm g hg
  let H := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  obtain ⟨c⟩ := exists_cone_iso H T' (R.mapDerivedCategory.map_distinguished T hT) eP eQ β hβ
  refine modelSieve_covering_of_iso_general X E W (mappingCone_isStrictlyPerfect
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) β
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP)
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hQ)) ?_
  exact c ≪≫ H.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso e.symm) ≪≫
    H.mapDerivedCategory.mapIso (R.mapDerivedCategoryFactors.app E) ≪≫
    H.mapDerivedCategoryFactors.app (X.restrictComplex E V) ≪≫
    DerivedCategory.Q.mapIso ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app E)

/-- **Stacks 08G9, second object.** In a distinguished triangle of `D(O)`, the second object is
perfect if the other two are. -/
theorem isPerfect_obj₂_of_distinguished_general
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : X.IsPerfect T.obj₁) (h₃ : X.IsPerfect T.obj₃) :
    X.IsPerfect T.obj₂ :=
  isPerfect_obj₃_of_distinguished_general X T.invRotate (inv_rot_of_distTriang T hT)
    (isPerfect_shift_general X h₃ (-1)) h₁

/-- **Stacks 08G9, first object.** In a distinguished triangle of `D(O)`, the first object is
perfect if the other two are. -/
theorem isPerfect_obj₁_of_distinguished_general
    (T : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₂ : X.IsPerfect T.obj₂) (h₃ : X.IsPerfect T.obj₃) :
    X.IsPerfect T.obj₁ := by
  obtain ⟨P, hP, ⟨i⟩⟩ :=
    isPerfect_shift_general X
      (isPerfect_obj₃_of_distinguished_general X T.rotate (rot_of_distTriang T hT) h₂ h₃) (-1)
  exact ⟨P, hP, ⟨i ≪≫ shiftShiftNeg T.obj₁ (1 : ℤ)⟩⟩

end AlgebraicGeometry.RingedSite

end
