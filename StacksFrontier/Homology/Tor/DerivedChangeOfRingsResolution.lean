module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# The resolution step for the derived extension-of-scalars adjunction

The unit and counit of `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`
(Stacks 0GMT) are known on objects of the form `DerivedCategory.Q.obj X`, and the unit only where
the model comparison is invertible at `X`, that is — by
`CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat` — at K-flat `X`. This
module computes both at an arbitrary object, by transport along an isomorphism to such a model.

## Main results

* `CategoryTheory.Adjunction.unit_app_eq_of_iso` and
  `CategoryTheory.Adjunction.counit_app_eq_of_iso` — the unit and the counit of an adjunction at an
  object are conjugate to those at any isomorphic object;
* `CategoryTheory.Adjunction.homEquiv_symm_apply_of_iso_left` and
  `CategoryTheory.Adjunction.homEquiv_apply_of_iso_left` — the same transport for the adjunction's
  `homEquiv` in its source variable;
* `CochainComplex.DerivedExtensionScalars.exists_kFlat_model` — every object of `D(R)` is
  isomorphic to `DerivedCategory.Q` of a K-flat complex, at the universes of the adjunction;
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_model`
  and `..._counit_app_eq_of_model` — the unit and the counit at an arbitrary object, presented
  through a chosen model.

## References

* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [The Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **The resolution step for the unit of an adjunction.** The unit at an object `Z` is the unit
at any isomorphic object `Z'`, conjugated by the isomorphism. -/
theorem unit_app_eq_of_iso {Z Z' : C} (φ : Z ≅ Z') :
    adj.unit.app Z = φ.hom ≫ adj.unit.app Z' ≫ R.map (L.map φ.inv) := by
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← R.map_comp, ← L.map_comp]
  simp

/-- **The resolution step for the counit of an adjunction.** The counit at an object `W` is the
counit at any isomorphic object `W'`, conjugated by the isomorphism. -/
theorem counit_app_eq_of_iso {W W' : D} (φ : W ≅ W') :
    adj.counit.app W = L.map (R.map φ.hom) ≫ adj.counit.app W' ≫ φ.inv :=
  Stacks.Adjunction.counit_app_of_iso adj φ

/-- The inverse transpose of an adjunction at a source `Z` is its inverse transpose at any
isomorphic source `Z'`, conjugated by the isomorphism. -/
theorem homEquiv_symm_apply_of_iso_left {Z Z' : C} (φ : Z ≅ Z') (W : D) (g : Z ⟶ R.obj W) :
    (adj.homEquiv Z W).symm g = L.map φ.hom ≫ (adj.homEquiv Z' W).symm (φ.inv ≫ g) := by
  rw [← adj.homEquiv_naturality_left_symm, ← Category.assoc, φ.hom_inv_id, Category.id_comp]

/-- The transpose of an adjunction at a source `Z` is its transpose at any isomorphic source
`Z'`, conjugated by the isomorphism. -/
theorem homEquiv_apply_of_iso_left {Z Z' : C} (φ : Z ≅ Z') (W : D) (g : L.obj Z ⟶ W) :
    adj.homEquiv Z W g = φ.hom ≫ adj.homEquiv Z' W (L.map φ.inv ≫ g) := by
  rw [← adj.homEquiv_naturality_left, ← Category.assoc, ← L.map_comp, φ.hom_inv_id, L.map_id,
    Category.id_comp]

end CategoryTheory.Adjunction

namespace CochainComplex.DerivedExtensionScalars

universe uR uA uM wR wA

/-- **Stacks 06Y4 at the universes of the extension-of-scalars adjunction.** Every object of
`D(R)` is isomorphic to `DerivedCategory.Q` of a K-flat complex, with the K-flatness spelled as
`CochainComplex.KFlat.{uR, max uM uA}`. -/
theorem exists_kFlat_model {R : Type uR} [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    ∃ X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ,
      CochainComplex.KFlat.{uR, max uM uA} X ∧ Nonempty (Z ≅ DerivedCategory.Q.obj X) := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := DerivedCategory.Q (C := ModuleCat.{max uR uA uM} R)) Z
  obtain ⟨X, q, hX, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, max uM uA} M
  have := hq
  exact ⟨X, hX, ⟨e.symm ≪≫ (asIso (DerivedCategory.Q.map q)).symm⟩⟩

/-- **The unit of Stacks 0GMT at an arbitrary object.** Given an isomorphism `φ` from an object
`Z` of `D(R)` to `DerivedCategory.Q` of a K-flat complex `X`, the unit at `Z` is the degreewise
unit of the extension–restriction adjunction on cochain complexes at `X`, read through
`CategoryTheory.Functor.mapDerivedCategoryFactors` and back along the comparison, and conjugated
by `φ`. -/
theorem derivedExtensionScalarsAdjunction_unit_app_eq_of_model
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hX : CochainComplex.KFlat.{uR, max uM uA} X)
    (φ : Z ≅ DerivedCategory.Q.obj X),
    letI : IsIso (comparison.app X) :=
      isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison X hX
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Z =
      φ.hom ≫
        (DerivedCategory.Q.map
            (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).unit.app X) ≫
          (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
              (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫
            (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
              (inv (comparison.app X))) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
          (F.map φ.inv) := by
  let _ : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF Z X hX φ
  have : IsIso (comparison.app X) :=
    isIso_comparison_app_of_kFlat.{uR, uA, uM} f F comparison X hX
  rw [(derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit_app_eq_of_iso φ,
    derivedExtensionScalarsAdjunction_unit_app_eq.{uR, uA, uM} f F comparison X]

/-- **The counit of Stacks 0GMT at an arbitrary object.** Given an isomorphism `φ` from an object
`W` of `D(A)` to `DerivedCategory.Q.obj Y`, the counit at `W` is the degreewise counit of the
extension–restriction adjunction on cochain complexes at `Y`, read through
`CategoryTheory.Functor.mapDerivedCategoryFactors` and the comparison, and conjugated by `φ`. -/
theorem derivedExtensionScalarsAdjunction_counit_app_eq_of_model
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA uM} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA uM} A)] :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (W : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (φ : W ≅ DerivedCategory.Q.obj Y),
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app W =
      F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map φ.hom) ≫
        (F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
              f).mapDerivedCategoryFactors.hom.app Y) ≫
          comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR, uA}
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
            DerivedCategory.Q.map
              (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).counit.app Y)) ≫
        φ.inv := by
  intro F comparison hF W Y φ
  exact derivedExtensionScalarsAdjunction_counit_app_eq_of_iso.{uR, uA, uM} f F comparison W Y φ

end CochainComplex.DerivedExtensionScalars

end
