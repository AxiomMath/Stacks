module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
import StacksCore.Tactic.StacksAttribute

/-!
# Perfect objects and distinguished triangles on a ringed site

Let `(C, O)` be a ringed site and let `(K, L, M, f, g, h)` be a distinguished triangle in
`D(O)`. If two of `K`, `L`, `M` are perfect then so is the third. This is Stacks 08G9.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_obj₃_of_distinguished`,
  `AlgebraicGeometry.RingedSite.isPerfect_obj₂_of_distinguished` and
  `AlgebraicGeometry.RingedSite.isPerfect_obj₁_of_distinguished`: the three implications of
  Stacks 08G9.
* `AlgebraicGeometry.RingedSite.modelSieve` and
  `AlgebraicGeometry.RingedSite.isPerfectComplex_iff_modelSieve`: perfectness of a complex
  expressed as a covering condition on the sieve of objects carrying a strictly perfect model.
* `AlgebraicGeometry.RingedSite.isPerfect_shift`: perfectness is stable under shifts.

## Implementation notes

The source offers two proofs. The one followed here is the second, which does not pass through
Stacks 08G8: above a small enough object both `K` and `L` are represented by strictly perfect
complexes, the map `K → L` is represented by a map of complexes (Stacks 08FR), and `M` is then
the cone of that map, which is strictly perfect by Stacks 08FM.

Carrying a strictly perfect model is stable under restriction along an arrow of the site, by
`Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong`, so the objects of `C` above
which a complex has one form a sieve; perfectness of the complex says exactly that this sieve is
covering above every object. Phrasing it that way turns the two layers of coverings produced by
the argument into a single application of the transitivity axiom, with no explicit binding of
presieves.

Stacks 08FR is available only for a site whose objects and morphisms live in the same universe,
so this file is stated at `RingedSite.{u, u, 0}`.

## References

* [Stacks Project, Tag 08G9](https://stacks.math.columbia.edu/tag/08G9)
* [Stacks Project, Tag 08FM](https://stacks.math.columbia.edu/tag/08FM)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u₁ u₂ v₁ v₂ u d

namespace AlgebraicGeometry.RingedSite

section Cone

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]

/-- Let `H` be an exact functor of abelian categories and let `T` be a distinguished triangle in
`D(A)` whose first two objects are represented by complexes `P` and `Q`. If the image under `H`
of the connecting map `P ⟶ Q` is represented by a map of complexes `β`, then the cone of `β`
represents `H(T.obj₃)`.

This is the general form of the step in Stacks 08G9 which exhibits the third object of a
distinguished triangle as a cone. -/
private theorem exists_cone_iso
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distinguishedTriangles)
    {P Q : CochainComplex A ℤ}
    (eP : DerivedCategory.Q.obj P ≅ T.obj₁) (eQ : DerivedCategory.Q.obj Q ≅ T.obj₂)
    (β : (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
    (hβ : H.mapDerivedCategory.map (eP.hom ≫ T.mor₁ ≫ eQ.inv) ≫
        H.mapDerivedCategoryFactors.hom.app Q =
      H.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β) :
    Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone β) ≅
      H.mapDerivedCategory.obj T.obj₃) := by
  let α := eP.hom ≫ T.mor₁ ≫ eQ.inv
  let i : Arrow.mk α ≅ Arrow.mk T.mor₁ := Arrow.isoMk eP eQ (by simp [α])
  let j : Arrow.mk (DerivedCategory.Q.map β) ≅ Arrow.mk (H.mapDerivedCategory.map α) :=
    Arrow.isoMk (H.mapDerivedCategoryFactors.app P).symm
      (H.mapDerivedCategoryFactors.app Q).symm (by
        show H.mapDerivedCategoryFactors.inv.app P ≫ H.mapDerivedCategory.map α =
          DerivedCategory.Q.map β ≫ H.mapDerivedCategoryFactors.inv.app Q
        apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app Q)).mp
        simpa only [α, Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
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

/-- A strictly perfect complex mapping by a quasi-isomorphism to the restriction of `E` to `V`
restricts to a strictly perfect model of `E` above any `W ⟶ V`. -/
private theorem exists_strictlyPerfect_model_of_quasiIso_map (X : RingedSite.{u, u, 0})
    [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{0}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {V W : X.C} (f : W ⟶ V)
    {P : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P)
    (β : (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
        |>.mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex E V))
    [QuasiIso β] :
    ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ q : P ⟶ X.restrictComplex E W, QuasiIso q :=
  ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f hP,
    β ≫ ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).app E).hom, inferInstance⟩

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{0}]
variable [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor
  preservesFiniteLimitsOverMap' preservesFiniteColimitsOverMap'

/-- The category of sheaves of modules over the restriction of the structure sheaf to an object
`V` of the site has a derived category. -/
local instance trianglesHasDerivedOver (V : X.C) :
    HasDerivedCategory (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
  HasDerivedCategory.standard _

variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- Carrying a strictly perfect model is stable under restriction along an arrow of the site. -/
theorem exists_strictlyPerfect_model_restrict
    {E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {V W : X.C} (f : W ⟶ V)
    (h : ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ q : P ⟶ X.restrictComplex E V, QuasiIso q) :
    ∃ P : CochainComplex
        (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ q : P ⟶ X.restrictComplex E W, QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  exact exists_strictlyPerfect_model_of_quasiIso_map X f hP
    ((SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).map q)

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The sieve on `U` of arrows whose source carries a strictly perfect model of the restriction
of `E`. -/
def modelSieve
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) : Sieve U where
  arrows _ _ := ∃ P : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over _)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over _) P ∧
      ∃ q : P ⟶ X.restrictComplex E _, QuasiIso q
  downward_closed h g := exists_strictlyPerfect_model_restrict X g h

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A complex is perfect exactly when the sieve of objects carrying a strictly perfect model of
its restriction is covering above every object of the site. -/
theorem isPerfectComplex_iff_modelSieve
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    X.IsPerfectComplex E ↔ ∀ U : X.C, modelSieve X E U ∈ X.J U := by
  refine ⟨fun h U => ?_, fun h U => ⟨(modelSieve X E U).arrows, ?_, fun _ _ hf => hf⟩⟩
  · obtain ⟨S, hS, hm⟩ := h U
    exact X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr hm) hS
  · simpa only [Sieve.generate_sieve] using h U

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- A strictly perfect complex isomorphic in `D(O|_U)` to the restriction of `E` to `U` makes the
model sieve of `E` covering above `U`: by Stacks 08FR the isomorphism is, on a covering sieve of
`U`, the image of an honest quasi-isomorphism. -/
theorem modelSieve_covering_of_iso
    (E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) {P : CochainComplex
      (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj (X.restrictComplex E U)) :
    modelSieve X E U ∈ X.J U := by
  obtain ⟨S, hS, hm⟩ := exists_coveringSieve_complexMap X U hP e.hom
  refine X.J.superset_covering (fun V f hf => ?_) hS
  obtain ⟨_, _, _, _, _, β, hβ⟩ := hm f hf
  let H := SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have hi : IsIso (H.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β) := by
    rw [← hβ]
    infer_instance
  have : QuasiIso β := (DerivedCategory.isIso_Q_map_iff_quasiIso _ β).mp
    (IsIso.of_isIso_comp_left (H.mapDerivedCategoryFactors.hom.app P) _)
  exact exists_strictlyPerfect_model_of_quasiIso_map X f hP β

/-- Perfectness of an object of `D(O)` is stable under shifting. -/
theorem isPerfect_shift
    {K : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (h : X.IsPerfect K) (n : ℤ) : X.IsPerfect (K⟦n⟧) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  refine ⟨E⟦n⟧, fun U => ?_,
    ⟨(DerivedCategory.Q.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso e⟩⟩
  obtain ⟨S, hS, hm⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hm f hf
  let F := (SheafOfModules.overFunctor.{0}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨P⟦n⟧, SheafOfModules.isStrictlyPerfect_shift _ hP n,
    q⟦n⟧' ≫ ((F.commShiftIso n).app E).inv, inferInstance⟩

/-- **Stacks 08G9, third object.** In a distinguished triangle of `D(O)`, the third object is
perfect if the first two are. -/
@[stacks 08G9 "third object"]
theorem isPerfect_obj₃_of_distinguished
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : X.IsPerfect T.obj₁) (h₂ : X.IsPerfect T.obj₂) :
    X.IsPerfect T.obj₃ := by
  obtain ⟨A, hA, ⟨a⟩⟩ := h₁
  obtain ⟨B, hB, ⟨b⟩⟩ := h₂
  let E := DerivedCategory.Q.objPreimage T.obj₃
  let e : DerivedCategory.Q.obj E ≅ T.obj₃ := DerivedCategory.Q.objObjPreimageIso _
  refine ⟨E, (isPerfectComplex_iff_modelSieve X E).mpr fun U => ?_, ⟨e⟩⟩
  refine X.J.transitive (X.J.intersection_covering
    ((isPerfectComplex_iff_modelSieve X A).mp hA U)
    ((isPerfectComplex_iff_modelSieve X B).mp hB U)) (modelSieve X E U) fun {V} f hf => ?_
  show modelSieve X E V ∈ X.J V
  obtain ⟨P, hP, p, hp⟩ := hf.1
  obtain ⟨Q, hQ, q, hq⟩ := hf.2
  let R := SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  let T' := R.mapDerivedCategory.mapTriangle.obj T
  let eP : DerivedCategory.Q.obj P ≅ T'.obj₁ :=
    asIso (DerivedCategory.Q.map p) ≪≫ (R.mapDerivedCategoryFactors.app A).symm ≪≫
      R.mapDerivedCategory.mapIso a
  let eQ : DerivedCategory.Q.obj Q ≅ T'.obj₂ :=
    asIso (DerivedCategory.Q.map q) ≪≫ (R.mapDerivedCategoryFactors.app B).symm ≪≫
      R.mapDerivedCategory.mapIso b
  obtain ⟨S, hS, hm⟩ :=
    exists_coveringSieve_complexMap X V hP (eP.hom ≫ T'.mor₁ ≫ eQ.inv)
  refine X.J.transitive hS (modelSieve X E V) fun {W} g hg => ?_
  show modelSieve X E W ∈ X.J W
  obtain ⟨_, _, _, _, _, β, hβ⟩ := hm g hg
  let H := SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
  obtain ⟨c⟩ := exists_cone_iso H T' (R.mapDerivedCategory.map_distinguished T hT) eP eQ β hβ
  refine modelSieve_covering_of_iso X E W (mappingCone_isStrictlyPerfect
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) β
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hP)
    (Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hQ)) ?_
  exact c ≪≫ H.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso e.symm) ≪≫
    H.mapDerivedCategory.mapIso (R.mapDerivedCategoryFactors.app E) ≪≫
    H.mapDerivedCategoryFactors.app (X.restrictComplex E V) ≪≫
    DerivedCategory.Q.mapIso ((Stacks.SheafOfModules.overFunctorMapComplexIso
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app E)

/-- **Stacks 08G9, second object.** In a distinguished triangle of `D(O)`, the second object is
perfect if the other two are. -/
@[stacks 08G9 "second object"]
theorem isPerfect_obj₂_of_distinguished
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : X.IsPerfect T.obj₁) (h₃ : X.IsPerfect T.obj₃) :
    X.IsPerfect T.obj₂ :=
  isPerfect_obj₃_of_distinguished X T.invRotate (inv_rot_of_distTriang T hT)
    (isPerfect_shift X h₃ (-1)) h₁

/-- **Stacks 08G9, first object.** In a distinguished triangle of `D(O)`, the first object is
perfect if the other two are. -/
@[stacks 08G9 "first object"]
theorem isPerfect_obj₁_of_distinguished
    (T : Triangle
      (DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distinguishedTriangles)
    (h₂ : X.IsPerfect T.obj₂) (h₃ : X.IsPerfect T.obj₃) :
    X.IsPerfect T.obj₁ := by
  obtain ⟨P, hP, ⟨i⟩⟩ :=
    isPerfect_shift X (isPerfect_obj₃_of_distinguished X T.rotate (rot_of_distTriang T hT) h₂ h₃)
      (-1)
  exact ⟨P, hP, ⟨i ≪≫ shiftShiftNeg T.obj₁ (1 : ℤ)⟩⟩

end AlgebraicGeometry.RingedSite

end
