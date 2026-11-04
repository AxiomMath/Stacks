module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Postcomposing a total right derived functor with an exact functor, at the complex localization

Let `A` be a Grothendieck abelian category, let `F : A ⥤ B₁` be additive and let `G : B₁ ⥤ B₂` be
exact.  Deriving `F` and then applying the functor `G` induces on unbounded derived categories is
the same as deriving `G ∘ F`:

`R(F) ⋙ G.mapDerivedCategory ≅ R(G ∘ F)`.

This is `Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso` with
the total right derived functors taken along `CategoryTheory.DerivedCategory.Q` and the
quasi-isomorphisms of cochain complexes, rather than along
`CategoryTheory.DerivedCategory.Qh` and the quasi-isomorphisms of the homotopy category.  The two
localizations are different and `CategoryTheory.Functor.IsRightDerivedFunctor` is indexed by one
of them, so neither statement follows from the other; the shape proved here is the one in which
the coherator of an algebraic space is derived
(`AlgebraicGeometry.Space.derivedCoherator`).

## Main definitions

* `Stacks.Injectives.KInjectiveResolution.totalRightDerivedCompUnitQ`: the candidate comparison
  for `R(F) ⋙ G`.
* `Stacks.Injectives.KInjectiveResolution.mapDerivedCategorySourceIsoQ`: the underived comparison
  of the two functors on cochain complexes.
* `Stacks.Injectives.KInjectiveResolution.totalRightDerivedMapDerivedCategoryIsoQ`: the
  comparison of the two total right derived functors.

## Main results

* `Stacks.Injectives.KInjectiveResolution.invertsQuasiIsoOfIsKInjective_comp`: a functor
  inverting the quasi-isomorphisms between K-injective complexes still does so after any
  postcomposition.
* `Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_totalRightDerived_compQ`:
  postcomposing a total right derived functor with any functor again gives a right derived
  functor.

## Implementation notes

The recognition criterion is
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`: a
candidate is the right derived functor exactly when its unit is invertible at every K-injective
cochain complex.  The unit of `R(F) ⋙ G` at a complex is `G` applied to the unit of `R(F)`, which
is invertible there, so the criterion applies with no exactness of `G` at all; exactness of `G`
enters only in `mapDerivedCategorySourceIsoQ`, where `G.mapDerivedCategory` has to exist and to
be induced by `G.mapHomologicalComplex`.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Injectives.KInjectiveResolution

universe v₁ v₂ v₃ vH u₁ u₂ u₃ uH wG wD wD₁ wD₂

section Postcomposition

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
    [HasDerivedCategory.{wD} A]
  {B : Type u₂} [Category.{v₂} B] {H : Type uH} [Category.{vH} H]

omit [IsGrothendieckAbelian.{wG, v₁, u₁} A] [HasDerivedCategory A] in
/-- A functor inverting the quasi-isomorphisms between K-injective cochain complexes still does
so after postcomposition with any functor, which carries isomorphisms to isomorphisms. -/
theorem invertsQuasiIsoOfIsKInjective_comp {F : CochainComplex A ℤ ⥤ B}
    (hF : InvertsQuasiIsoOfIsKInjective F) (G : B ⥤ H) :
    InvertsQuasiIsoOfIsKInjective (F ⋙ G) := fun f hK hL hf =>
  have := hF f hK hL hf
  inferInstanceAs (IsIso (G.map (F.map f)))

/-- The candidate comparison exhibiting `R(F) ⋙ G` as a right derived functor of `F ⋙ G`: the
unit of `R(F)` whiskered with `G`. -/
def totalRightDerivedCompUnitQ (F : CochainComplex A ℤ ⥤ B)
    [F.HasRightDerivedFunctor (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) :
    F ⋙ G ⟶ DerivedCategory.Q ⋙ (F.totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ⋙ G) :=
  Functor.whiskerRight (F.totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))) G ≫
    (Functor.associator DerivedCategory.Q _ G).hom

omit [IsGrothendieckAbelian.{wG, v₁, u₁} A] in
/-- The candidate comparison of `Stacks.Injectives.KInjectiveResolution.totalRightDerivedCompUnitQ`
is `G` applied to the unit of `R(F)`. -/
@[simp]
theorem totalRightDerivedCompUnitQ_app (F : CochainComplex A ℤ ⥤ B)
    [F.HasRightDerivedFunctor (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) (K : CochainComplex A ℤ) :
    (totalRightDerivedCompUnitQ F G).app K =
      G.map ((F.totalRightDerivedUnit DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))).app K) := by
  simp [totalRightDerivedCompUnitQ]

/-- **Postcomposing a total right derived functor with any functor again gives a right derived
functor.**  The unit of `R(F)` is invertible at every K-injective cochain complex, hence so is
its image under `G`, and a comparison invertible on K-injectives is a right derived functor. -/
theorem isRightDerivedFunctor_totalRightDerived_compQ (F : CochainComplex A ℤ ⥤ B)
    (hF : InvertsQuasiIsoOfIsKInjective F)
    [F.HasRightDerivedFunctor (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (G : B ⥤ H) :
    (F.totalRightDerived DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ⋙ G).IsRightDerivedFunctor
      (totalRightDerivedCompUnitQ F G)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
  rw [isRightDerivedFunctor_iff_isIso_app_of_isKInjective (C := A) DerivedCategory.Q _ _
    (invertsQuasiIsoOfIsKInjective_comp hF G)]
  intro K hK
  have := isIso_app_of_isKInjective (C := A) DerivedCategory.Q
    (F.totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (F.totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))) hF K hK
  rw [totalRightDerivedCompUnitQ_app]
  infer_instance

end Postcomposition

section Exact

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
    [HasDerivedCategory.{wD} A]
  {B₁ : Type u₂} [Category.{v₂} B₁] [Abelian B₁] [HasDerivedCategory.{wD₁} B₁]
  {B₂ : Type u₃} [Category.{v₃} B₂] [Abelian B₂] [HasDerivedCategory.{wD₂} B₂]
  (F : A ⥤ B₁) [F.Additive]
  (G : B₁ ⥤ B₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The comparison, on the cochain complexes of `A`, between localizing the complexes of
`F`-images and then applying `G.mapDerivedCategory`, and localizing the complexes of
`(F ⋙ G)`-images.  It is `CategoryTheory.Functor.mapDerivedCategoryFactors`, the identification
of `G.mapDerivedCategory` as the functor induced by `G.mapHomologicalComplex`. -/
def mapDerivedCategorySourceIsoQ :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory ≅
      (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactors

/-- **A total right derived functor postcomposed with an exact functor derives the composite.**
For `F : A ⥤ B₁` additive out of a Grothendieck abelian category and `G : B₁ ⥤ B₂` exact, the
total right derived functor of `F` followed by the functor `G` induces on derived categories is
canonically the total right derived functor of `F ⋙ G`.

This is the statement at the localization `CategoryTheory.DerivedCategory.Q` of the cochain
complexes; see the module documentation. -/
def totalRightDerivedMapDerivedCategoryIsoQ :
    letI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (A := B₁) (C := A) F
    letI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (A := B₂) (C := A) (F ⋙ G)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
        DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ⋙
        G.mapDerivedCategory ≅
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).totalRightDerived DerivedCategory.Q
          (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  letI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (A := B₁) (C := A) F
  letI := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q (A := B₂) (C := A) (F ⋙ G)
  haveI := isRightDerivedFunctor_totalRightDerived_compQ
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q F) G.mapDerivedCategory
  Functor.rightDerivedNatIso
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
      DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ⋙
      G.mapDerivedCategory)
    (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (totalRightDerivedCompUnitQ
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) G.mapDerivedCategory)
    (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (mapDerivedCategorySourceIsoQ F G)

end Exact

end Stacks.Injectives.KInjectiveResolution

end
