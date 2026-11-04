module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.ShiftedBundleSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.CategoryTheory.Triangulated.ConeOfZero
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Extending `F ⊕ F[1]` from a quasi-compact open

Let `X` be a scheme and `U ⊆ X` an open. Suppose `α : E₁ ⟶ E` is a morphism of perfect objects
of `D(𝒪_X)` whose restriction to `U` is, in suitable direct-sum coordinates `A ⊞ B` of both
`E₁|_U` and `E|_U`, the *partial identity* `diag(𝟙_A, 0)`. Then the cone of `α` is a perfect
object of `D(𝒪_X)` whose restriction to `U` is `B ⊞ B[1]`.

## Main results

* `CategoryTheory.Pretriangulated.nonempty_iso_biprod_shift_of_map_eq_biprod_map_id_zero`:
  the triangulated-functor transport. If a triangulated functor `R` carries `α : E₁ ⟶ E` to a
  partial identity `A ⊞ B ⟶ A ⊞ B` in direct-sum coordinates, then `R` carries the cone of `α`
  to `B ⊞ B⟦1⟧`. The category is abstract and every object is a variable.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_restrict_iso_biprod_shift_of_partialId`:
  the same for `R = (·)|_U` on a scheme, with the conclusion a *perfect complex* `P` of
  `𝒪_X`-modules whose degreewise restriction to `U` represents `B ⊞ B⟦1⟧`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_restrict_iso_biprod_shift_of_lift`: for
  `X` affine and `U` quasi-compact, if every perfect `E` admits morphisms `γ : E₁ ⟶ E` restricting
  to partial identities, then `F ⊞ F⟦1⟧` is the restriction of a perfect complex for every
  perfect `F` on `U`.

## Implementation notes

Every isomorphism in these statements has `A ⊞ B` as its source, so all of them are written in
the `U.toScheme.Modules` spelling of the restricted category; composing with an isomorphism
written against `derivedRestrictModules` on both sides makes the unifier compare the two
categories' instances, which exceeds the heartbeat budget.

Restriction appears in two forms: degreewise on complexes, as
`DerivedCategory.Q.obj ((restrictModules X U).mapHomologicalComplex _ |>.obj P)`, and as the
triangulated functor `AlgebraicGeometry.RingedSpace.derivedRestrictModules` on derived
categories. They are identified by `AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso`.

## References

* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08EG](https://stacks.math.columbia.edu/tag/08EG)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasBinaryBiproducts D]

/-- Let `R : C ⥤ D` be a triangulated functor, let `E₁ --α--> E --g--> Z --h--> E₁⟦1⟧` be a
distinguished triangle of `C`, and suppose `A ⊞ B` is identified with both `R.obj E₁` and
`R.obj E` in such a way that `R.map α` becomes the partial identity `diag(𝟙_A, 0)`. Then
`R.obj Z ≅ B ⊞ B⟦1⟧`. -/
theorem nonempty_iso_biprod_shift_of_map_eq_biprod_map_id_zero (R : C ⥤ D) [R.CommShift ℤ]
    [R.IsTriangulated] {A B : D} {E₁ E Z : C} (α : E₁ ⟶ E) (g : E ⟶ Z)
    (h : Z ⟶ E₁⟦(1 : ℤ)⟧) (hT : Triangle.mk α g h ∈ distTriang C)
    (a : A ⊞ B ≅ R.obj E₁) (b : A ⊞ B ≅ R.obj E)
    (hα : a.hom ≫ R.map α = biprod.map (𝟙 A) (0 : B ⟶ B) ≫ b.hom) :
    Nonempty (B ⊞ B⟦(1 : ℤ)⟧ ≅ R.obj Z) := by
  have hT' : Triangle.mk (R.map α) (R.map g)
      (R.map h ≫ (R.commShiftIso (1 : ℤ)).hom.app E₁) ∈ distTriang D :=
    R.map_distinguished _ hT
  refine nonempty_iso_biprod_shift_of_cone_biprod_map_id_zero (b.hom ≫ R.map g)
    ((R.map h ≫ (R.commShiftIso (1 : ℤ)).hom.app E₁) ≫ a.inv⟦(1 : ℤ)⟧')
    (isomorphic_distinguished _ hT' _
      (Triangle.isoMk _ _ a b (Iso.refl _) hα.symm (Category.comp_id _) ?_))
  dsimp only [Triangle.mk_mor₃, Triangle.mk_obj₃, Iso.refl_hom]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp]
  exact congrArg (R.map h ≫ ·) (Category.comp_id _)

end CategoryTheory.Pretriangulated

namespace Stacks.DerivedQCoh.OpenLift

attribute [local instance 10000] HasDerivedCategory.standard

/-- Let `X` be a scheme, `U ⊆ X` an open, and `α : E₁ ⟶ E` a morphism of perfect objects of
`D(𝒪_X)`. Suppose `A ⊞ B` is identified with both `E₁|_U` and `E|_U` so that `α|_U` becomes
`diag(𝟙_A, 0)`. Then there is a perfect complex `P` of `𝒪_X`-modules whose degreewise restriction
to `U` represents `B ⊞ B[1]`. -/
theorem exists_isPerfectComplex_restrict_iso_biprod_shift_of_partialId
    (X : Scheme.{u}) (U : X.Opens)
    {A B : DerivedCategory U.toScheme.Modules}
    {E₁ E : DerivedCategory (OXMod.{u, u, u} X.toRingedSpace)}
    (hE₁ : IsPerfect (X := X.toRingedSpace) E₁) (hE : IsPerfect (X := X.toRingedSpace) E)
    (α : E₁ ⟶ E)
    (a : A ⊞ B ≅
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E₁)
    (b : A ⊞ B ≅
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E)
    (hα : a.hom ≫
        (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).map α =
      biprod.map (𝟙 A) (0 : B ⟶ B) ≫ b.hom) :
    ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsPerfectComplex P ∧
      Nonempty ((B ⊞ B⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj
        (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
          U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  obtain ⟨P, hP, ⟨i⟩⟩ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished _ hT hE₁ hE
  obtain ⟨e⟩ : Nonempty ((B ⊞ B⟦(1 : ℤ)⟧) ≅
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj Z) :=
    nonempty_iso_biprod_shift_of_map_eq_biprod_map_id_zero
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U) α g h hT a b hα
  exact ⟨P, hP, ⟨e ≪≫
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).mapIso i).symm ≪≫
    AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso X.toRingedSpace U P⟩⟩

/-- Let `X` be an affine scheme and `U ⊆ X` a quasi-compact open. Suppose that for every perfect
object `E` of `D(𝒪_X)` and every direct-sum decomposition `A ⊞ B ≅ E|_U` there are a perfect
object `E₁` of `D(𝒪_X)` and a morphism `γ : E₁ ⟶ E` whose restriction to `U` is, in coordinates
`A ⊞ B` on `E₁|_U` as well, the partial identity `diag(𝟙_A, 0)`. Then for every perfect object
`F` of `D(𝒪_U)` the object `F ⊕ F[1]` is the restriction of a perfect complex of
`𝒪_X`-modules. -/
theorem exists_isPerfectComplex_restrict_iso_biprod_shift_of_lift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (hlift : ∀ E : DerivedCategory (OXMod.{u, u, u} X.toRingedSpace),
      IsPerfect (X := X.toRingedSpace) E →
      ∀ (A B : DerivedCategory U.toScheme.Modules)
        (b : A ⊞ B ≅
          (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E),
        ∃ (E₁ : DerivedCategory (OXMod.{u, u, u} X.toRingedSpace)) (γ : E₁ ⟶ E)
          (a : A ⊞ B ≅
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj E₁),
          IsPerfect (X := X.toRingedSpace) E₁ ∧
          a.hom ≫ (AlgebraicGeometry.RingedSpace.derivedRestrictModules
              X.toRingedSpace U).map γ =
            biprod.map (𝟙 A) (0 : B ⟶ B) ≫ b.hom)
    (F : DerivedCategory U.toScheme.Modules)
    (hF : IsPerfect (X := U.toScheme.toRingedSpace) F) :
    ∃ P : CochainComplex (OXMod.{u, u, u} X.toRingedSpace) ℤ,
      IsPerfectComplex P ∧
      Nonempty ((F ⊞ F⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj
        (((AlgebraicGeometry.RingedSpace.restrictModules.{u, u} X.toRingedSpace
          U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨r, G, P₀, -, hP₀, ⟨e⟩⟩ :=
    exists_finiteLocallyFree_biprod_iso_restrict_of_isPerfect X U hU F hF
  have hE : IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj P₀) :=
    ⟨P₀, hP₀, ⟨Iso.refl _⟩⟩
  have ee : ((DerivedCategory.singleFunctor U.toScheme.Modules r).obj G ⊞ F) ≅
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules X.toRingedSpace U).obj
        (DerivedCategory.Q.obj P₀) :=
    e ≪≫ (AlgebraicGeometry.RingedSpace.derivedRestrictModulesObjQIso
      X.toRingedSpace U P₀).symm
  obtain ⟨E₁, γ, a, hE₁, hγ⟩ := hlift (DerivedCategory.Q.obj P₀) hE
    ((DerivedCategory.singleFunctor U.toScheme.Modules r).obj G) F ee
  exact exists_isPerfectComplex_restrict_iso_biprod_shift_of_partialId X U hE₁ hE γ a ee hγ

end Stacks.DerivedQCoh.OpenLift

end
