module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomHomotopyCommShift

/-!
# `Hom(K, -)` is exact as a functor of triangulated categories

Let `K` be a cochain complex in a preadditive category `B` with a zero object and binary
biproducts, and let `E = End(K)`. The functor `Hom(K, -) : K(B) ⥤ K(E, d)` of Tag 09LE is exact:
it commutes with the translation, which is `CochainComplex.homHomotopyFunctorCommShift`, and it
carries distinguished triangles to distinguished triangles. The second half is
`CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`, and what is done here is to
put it into the `CategoryTheory.Functor.mapTriangle` form that
`CategoryTheory.Functor.IsTriangulated` asks for. Consequently the functor being right derived in
Tag 09LK, `Hom(K, -) : K(B) ⥤ D(E, d)`, is exact as well.

## Main results

* `CochainComplex.homHomotopyFunctorLift_isTriangulated`: the descent of `Hom(K, -)` along the
  quotient by homotopy is exact.
* `CochainComplex.homHomotopyFunctor_isTriangulated`: **`Hom(K, -) : K(B) ⥤ K(E, d)` is exact.**
* `CochainComplex.homToDerivedCategory_isTriangulated`: **the functor being right derived in Tag
  09LK, `Hom(K, -) : K(B) ⥤ D(E, d)`, is exact.**

## Implementation notes

The triangle statement is proved for the *descent*
`CochainComplex.homHomotopyFunctorLift` and transported to
`CochainComplex.homHomotopyFunctor` by `CategoryTheory.Functor.isTriangulated_of_iso` along
`CochainComplex.homHomotopyFunctorLiftIso`, which is legitimate because
`CochainComplex.homHomotopyFunctorCommShift` is by construction
`CategoryTheory.Functor.CommShift.ofIso` of that isomorphism, so
`CategoryTheory.Functor.CommShift.ofIso_compatibility` supplies the compatibility the transport
needs. Working with the descent is what makes the third arrow of
`CategoryTheory.Functor.mapTriangle` computable: the descent's `CategoryTheory.Functor.CommShift`
is `CategoryTheory.Quotient.liftCommShift`, whose components are pinned by
`CategoryTheory.Quotient.LiftCommShift.iso_hom_app` without any appeal to the shift on the
quotient.

Two things make the identification of that third arrow delicate.

The first is that `CategoryTheory.HasShift.quotient` and
`CategoryTheory.Quotient.functor_commShift` are `irreducible` in Mathlib — deliberately, to
prevent abuse of defeq — so the shift comparison of the homotopy quotient of complexes is opaque
and no statement here may compute it. None has to. The third arrow of the triangle of a degreewise
split short exact sequence already carries that comparison, because
`CochainComplex.trianglehOfDegreewiseSplit` is itself a `CategoryTheory.Functor.mapTriangle`, and
`CategoryTheory.Quotient.LiftCommShift.iso_hom_app` writes the shift comparison of the descent at
a complex with the *inverse* of that same comparison in front; so the two cancel by
`CategoryTheory.Iso.hom_inv_id_app` and `CategoryTheory.Functor.map_id`. That cancellation is
`CochainComplex.map_homotopyQuotient_commShiftIso_hom_app_comp`, in the style of
`DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_comp`. The shift comparison of
the homotopy quotient of differential graded modules is opaque for the same reason, and is the
`eqToHom` of the statement; it is reached through
`DifferentialGradedModule.toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom`, the form of that
comparison which elaborates without the shift on the quotient.

The second is that the endomorphism algebra has two spellings. `CochainComplex.endAlgebra` is the
algebra of `DGCategory.homRepresentation`, which is definitionally but not reducibly
`DGCategory.endAlgebra`, and `CochainComplex.homComplexesFunctor` is stated with the latter while
`CochainComplex.homHomotopyFunctorLift` is stated with the former. A term mentioning both is
therefore not type-correct at the transparency `rw` and `simp` check against, so every step
relating the two is taken in term position — by `Eq.trans` and `congrArg` — where the elaborator
unfolds definitions fully.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose exactness clause
  this is; [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for `Hom(K, -)` and its shift
  comparison; [Tag 09K8](https://stacks.math.columbia.edu/tag/09K8) for the distinguished
  triangles of `K(E, d)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CochainComplex

open CochainComplex.HomComplex HomologicalComplex DifferentialGradedModule

variable (B : Type u) [Category.{0} B] [Preadditive B] (K : CochainComplex B ℤ)

section

/-- A functor sends `f ≫ g = 𝟙` to a pair of maps that cancel in front of any further map. -/
private theorem map_comp_map_comp_of_comp_eq_id {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) {Z : D}
    (k : F.obj X ⟶ Z) : F.map f ≫ F.map g ≫ k = k := by
  rw [← Category.assoc, ← F.map_comp, hfg, F.map_id, Category.id_comp]

/-- **The shift comparison of the homotopy quotient of complexes is cancelled by that of the
descent.** `CategoryTheory.Quotient.LiftCommShift.iso_hom_app` writes the shift comparison of the
descent, at a complex, as the descent applied to the *inverse* of the shift comparison of the
homotopy quotient followed by the shift comparison of Tag 09LE; so precomposing it with the
descent applied to that same comparison leaves the comparison of Tag 09LE alone. Nothing here
computes the comparison of the homotopy quotient, which Mathlib makes `irreducible`. -/
theorem map_homotopyQuotient_commShiftIso_hom_app_comp (X : CochainComplex B ℤ) (n : ℤ) :
    (homHomotopyFunctorLift B K).map
          (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso n).hom.app X) ≫
        ((homHomotopyFunctorLift B K).commShiftIso n).hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj X) =
      ((homComplexesFunctor B K ⋙ DifferentialGradedModule.toHomotopyCategory
        (endAlgebra B K)).commShiftIso n).hom.app X := by
  exact (congrArg _ (CategoryTheory.Quotient.LiftCommShift.iso_hom_app _ _ _ n X)).trans
    (map_comp_map_comp_of_comp_eq_id _ _ _ (Iso.hom_inv_id_app _ X) _)

variable (S : ShortComplex (CochainComplex B ℤ))
  (σ : ∀ n, (S.map (eval B (ComplexShape.up ℤ) n)).Splitting)

/-- **The third arrow of `CategoryTheory.Functor.mapTriangle` for the descent of `Hom(K, -)` is
the arrow of `CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`.** The arrow of
`mapTriangle` is the descent applied to the third arrow of the triangle of a degreewise split
short exact sequence, followed by the degree-one shift comparison of the descent. That third
arrow is itself the connecting map of the sequence followed by the shift comparison of the
homotopy quotient, and `CochainComplex.map_homotopyQuotient_commShiftIso_hom_app_comp` cancels
the latter against the comparison of the descent, leaving the shift comparison
`Hom(K, S.X₁[1]) ≅ Hom(K, S.X₁)[1]` of Tag 09LE followed by the shift comparison of the homotopy
quotient of differential graded modules, which is the `eqToHom` written here. -/
theorem homHomotopyFunctorLift_mapTriangle_mor₃ :
    ((homHomotopyFunctorLift B K).mapTriangle.obj (trianglehOfDegreewiseSplit S σ)).mor₃ =
      (toHomotopyCategory (endAlgebra B K)).map (homComplexesConnecting B K S σ) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel (DGCategory.endAlgebra (dgCategory B) K)) ℤ
          (DGCategory.representableModule (dgCategory B) K S.X₁) 1).symm := by
  have hsplit : ((homComplexesFunctor B K ⋙ DifferentialGradedModule.toHomotopyCategory
        (DGCategory.endAlgebra (dgCategory B) K)).commShiftIso (1 : ℤ)).hom.app S.X₁ =
      (toHomotopyCategory (DGCategory.endAlgebra (dgCategory B) K)).map
          (((homComplexesFunctor B K).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫
        eqToHom (CategoryTheory.Quotient.functor_obj_shift
          (homotopyRel (DGCategory.endAlgebra (dgCategory B) K)) ℤ
          (DGCategory.representableModule (dgCategory B) K S.X₁) 1).symm :=
    (Functor.commShiftIso_comp_hom_app ..).trans (congrArg (fun w =>
        (toHomotopyCategory (DGCategory.endAlgebra (dgCategory B) K)).map
          (((homComplexesFunctor B K).commShiftIso (1 : ℤ)).hom.app S.X₁) ≫ w)
      (toHomotopyCategory_commShiftIso_hom_app_eq_eqToHom
        (DGCategory.endAlgebra (dgCategory B) K)
        (DGCategory.representableModule (dgCategory B) K S.X₁) 1))
  refine Eq.trans (congrArg (fun w => w ≫
    ((homHomotopyFunctorLift B K).commShiftIso (1 : ℤ)).hom.app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj S.X₁))
      ((homHomotopyFunctorLift B K).map_comp
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (homOfDegreewiseSplit S σ))
        (((HomotopyCategory.quotient B (ComplexShape.up ℤ)).commShiftIso
          (1 : ℤ)).hom.app S.X₁))) ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans (congrArg (fun w => (homHomotopyFunctorLift B K).map
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (homOfDegreewiseSplit S σ)) ≫ w)
      ((map_homotopyQuotient_commShiftIso_hom_app_comp B K S.X₁ 1).trans hsplit)) ?_
  exact (Category.assoc _ _ _).symm

/-- **The image under the descent of `Hom(K, -)` of the triangle of a degreewise split short exact
sequence is the triangle whose distinguishedness is
`CochainComplex.isDistinguishedTriangle_homComplexesFunctor_triangleOfDegreewiseSplit`.** All
three vertices agree on the nose, because the descent commutes strictly with the homotopy
quotient; only the third arrow needs an argument, and that is
`CochainComplex.homHomotopyFunctorLift_mapTriangle_mor₃`. -/
noncomputable def homHomotopyFunctorLiftMapTriangleIso :
    (homHomotopyFunctorLift B K).mapTriangle.obj (trianglehOfDegreewiseSplit S σ) ≅
      Pretriangulated.Triangle.mk
        ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.f))
        ((toHomotopyCategory _).map ((homComplexesFunctor B K).map S.g))
        ((toHomotopyCategory _).map (homComplexesConnecting B K S σ) ≫
          eqToHom (CategoryTheory.Quotient.functor_obj_shift
            (homotopyRel (DGCategory.endAlgebra (dgCategory B) K)) ℤ
            (DGCategory.representableModule (dgCategory B) K S.X₁) 1).symm) := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
  have hid : (CategoryTheory.shiftFunctor
        (DifferentialGradedModule.HomotopyCategory (endAlgebra B K)) (1 : ℤ)).map
      (𝟙 ((homHomotopyFunctorLift B K).mapTriangle.obj
        (trianglehOfDegreewiseSplit S σ)).obj₁) = 𝟙 _ :=
    (CategoryTheory.shiftFunctor
      (DifferentialGradedModule.HomotopyCategory (endAlgebra B K)) (1 : ℤ)).map_id _
  simp only [Iso.refl_hom]
  refine Eq.trans (congrArg (fun u =>
    ((homHomotopyFunctorLift B K).mapTriangle.obj
      (trianglehOfDegreewiseSplit S σ)).mor₃ ≫ u) hid) ?_
  exact (Category.comp_id _).trans
    ((homHomotopyFunctorLift_mapTriangle_mor₃ B K S σ).trans (Category.id_comp _).symm)

end

variable [HasZeroObject B] [HasBinaryBiproducts B]

/-- **The descent of `Hom(K, -)` along the quotient by homotopy is exact.** Every distinguished
triangle of `K(B)` is isomorphic to the triangle of a degreewise split short exact sequence of
complexes, and such a triangle is carried to a distinguished triangle of `K(E, d)` by
`CochainComplex.exists_isDistinguishedTriangle_homComplexesFunctor`. -/
noncomputable instance homHomotopyFunctorLift_isTriangulated :
    (homHomotopyFunctorLift B K).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨S, σ, ⟨e⟩, hdist⟩ := exists_isDistinguishedTriangle_homComplexesFunctor B K T hT
    rw [DifferentialGradedModule.distinguishedTriangles_eq]
    exact DifferentialGradedModule.isDistinguishedTriangle_of_iso _
      (((homHomotopyFunctorLift B K).mapTriangle.mapIso e ≪≫
        homHomotopyFunctorLiftMapTriangleIso B K S σ).symm) hdist

/-- **Stacks 09LK, the exactness of `Hom(K, -)` on the homotopy categories.** The differential
graded Hom functor `Hom(K, -) : K(B) ⥤ K(E, d)` of Tag 09LE is exact as a functor of triangulated
categories: it commutes with the translation, which is
`CochainComplex.homHomotopyFunctorCommShift`, and it carries distinguished triangles to
distinguished triangles.

This is the exactness asserted by Tag 09LK of the functor being derived, read on the homotopy
categories. It is obtained from the exactness of the descent of `Hom(K, -)` along the quotient by
homotopy, transported along `CochainComplex.homHomotopyFunctorLiftIso`. -/
@[stacks 09LK "the differential graded Hom functor Hom(K, -) : K(B) ⥤ K(E, d) is exact as a \
functor of triangulated categories -- it commutes with the translation and carries distinguished \
triangles to distinguished triangles, which is the exactness of the functor being derived read \
on the homotopy categories"]
noncomputable instance homHomotopyFunctor_isTriangulated :
    (homHomotopyFunctor B K).IsTriangulated :=
  letI : NatTrans.CommShift (homHomotopyFunctorLiftIso B K).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (homHomotopyFunctorLiftIso B K) ℤ
  Functor.isTriangulated_of_iso (homHomotopyFunctorLiftIso B K)

/-- **Stacks 09LK, the exactness of the functor being right derived.** The functor
`Hom(K, -) : K(B) ⥤ D(E, d)` of Tag 09LK — the differential graded Hom functor followed by the
localization of the differential graded `E`-modules at the quasi-isomorphisms — is exact as a
functor of triangulated categories, the localization functor being exact. -/
@[stacks 09LK "the functor Hom(K, -) : K(B) ⥤ D(E, d) being right derived is exact as a functor \
of triangulated categories"]
noncomputable instance homToDerivedCategory_isTriangulated :
    (homToDerivedCategory B K).IsTriangulated :=
  inferInstanceAs ((homHomotopyFunctor B K ⋙
    (DifferentialGradedModule.quasiIsomorphisms' (endAlgebra B K)).Q).IsTriangulated)

end CochainComplex

end
