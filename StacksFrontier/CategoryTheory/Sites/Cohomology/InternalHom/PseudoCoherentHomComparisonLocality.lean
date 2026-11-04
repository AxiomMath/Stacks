module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.PseudoCoherentHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RestrictionHomComparison
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects

/-!
# A monoidal t-exact functor commutes with `RSheafHom` out of a pseudo-coherent object

Let `X` and `Y` be ringed sites and `Φ : D(O_X) ⥤ D(O_Y)` a monoidal, triangulated, t-exact
functor. Suppose that a continuous functor `u : X.C ⥤ Y.C`, whose image covers the final object,
relates the two at the level of slices: every object of `X` and its image under `u` are
subterminal, both sites have binary products, and `Φ` followed by restriction to `u W` kills
every object which restriction to `W` kills. Then for `E` pseudo-coherent and `M` bounded below,
the comparison

`Φ RSheafHom(E, M) ⟶ RSheafHom(Φ E, Φ M)`

of `AlgebraicGeometry.RingedSite.homComparisonMonoidal` is an isomorphism.

The question is local on the members `u W` of a covering of the final object of `Y`. On such a
member it is the corresponding question for the localized functor at the restrictions, and there
`E` is approximated in degrees `≥ m` by a strictly perfect complex, for which the comparison is
invertible; the truncation estimate gives invertibility on cohomology below `a - m`, for every
`m`.

## Main definitions

* `AlgebraicGeometry.RingedSite.sliceDerivedRestriction`: derived restriction to the slice over
  `W`.
* `AlgebraicGeometry.RingedSite.sliceDerivedExtensionByZero`: derived extension by zero from the
  slice over `W`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_map_homComparisonMonoidal_iff_of_iso`: invertibility of the
  image of the comparison under any functor only depends on the isomorphism class of the first
  argument.
* `AlgebraicGeometry.RingedSite.isIso_homComparisonMonoidal_of_isPseudoCoherent`: the comparison
  `Φ RSheafHom(E, M) ⟶ RSheafHom(Φ E, Φ M)` is an isomorphism for `E` pseudo-coherent and `M`
  bounded below.

## References

* [Stacks Project, Tag 08JP](https://stacks.math.columbia.edu/tag/08JP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedInternalHomPullback

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section Iso

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (Ψ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [Ψ.Monoidal]

/-- **Invertibility of the comparison, after any functor, depends only on the isomorphism class
of its first argument**: the comparison is natural in it. -/
theorem isIso_map_homComparisonMonoidal_iff_of_iso {E : Type*} [Category E]
    (Θ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤ E)
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (e : A ≅ A')
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Θ.map (homComparisonMonoidal Ψ A M)) ↔ IsIso (Θ.map (homComparisonMonoidal Ψ A' M)) := by
  have hc : homComparisonMonoidal Ψ A M =
      inv (Ψ.map (((derivedSheafHomBifunctor X).map e.hom.op).app M)) ≫
        homComparisonMonoidal Ψ A' M ≫
          ((derivedSheafHomBifunctor Y).map (Ψ.map e.hom).op).app (Ψ.obj M) := by
    rw [IsIso.eq_inv_comp, homComparisonMonoidal_naturality_source Ψ e.hom M]
  exact Transpose.isIso_map_iff_of_eq_conj Θ _ _ _ _ hc

end Iso

section Typed

variable (X : RingedSite.{u, u, u}) (W : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [(X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Derived restriction to the slice over `W`, as a functor between the derived categories of the
ringed sites `X` and `X.over W`. -/
def sliceDerivedRestriction :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) :=
  (Stacks.DerivedTensor.ExtensionByZero.restriction X W).mapDerivedCategory

/-- Derived restriction to the slice over `W` is monoidal. -/
instance : (sliceDerivedRestriction X W).Monoidal :=
  Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X W

/-- Derived restriction to the slice over `W` commutes with shifts. -/
instance : (sliceDerivedRestriction X W).CommShift ℤ :=
  inferInstanceAs
    ((Stacks.DerivedTensor.ExtensionByZero.restriction X W).mapDerivedCategory.CommShift ℤ)

/-- Derived restriction to the slice over `W` is triangulated. -/
instance : (sliceDerivedRestriction X W).IsTriangulated :=
  inferInstanceAs
    ((Stacks.DerivedTensor.ExtensionByZero.restriction X W).mapDerivedCategory.IsTriangulated)

/-- Derived extension by zero from the slice over `W`, as a functor between the derived
categories of the ringed sites `X.over W` and `X`. -/
def sliceDerivedExtensionByZero :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (SheafOfModules.pullback.{u} (F := Over.forget W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).mapDerivedCategory

/-- Derived extension by zero from the slice over `W` is left adjoint to derived restriction. -/
def sliceDerivedAdjunction : sliceDerivedExtensionByZero X W ⊣ sliceDerivedRestriction X W :=
  Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction X W

/-- When `X` has binary products and `Over.forget W` has invertible unit for its adjunction with
`Over.star W`, the unit of the adjunction between derived extension by zero and derived
restriction is an isomorphism. -/
instance [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar W).unit] :
    IsIso (sliceDerivedAdjunction X W).unit :=
  isIso_derivedExtensionByZeroRestrictionAdjunction_unit X W

/-- Derived extension by zero from the slice over `W` commutes with shifts. -/
instance : (sliceDerivedExtensionByZero X W).CommShift ℤ :=
  inferInstanceAs ((SheafOfModules.pullback.{u} (F := Over.forget W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).mapDerivedCategory.CommShift ℤ)

/-- Derived extension by zero from the slice over `W` is triangulated. -/
instance : (sliceDerivedExtensionByZero X W).IsTriangulated :=
  inferInstanceAs ((SheafOfModules.pullback.{u} (F := Over.forget W)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))).mapDerivedCategory.IsTriangulated)

/-- Restriction of the class of a complex is the class of its restriction. -/
def sliceDerivedRestrictionQIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (sliceDerivedRestriction X W).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (X.restrictComplex K W) :=
  (Stacks.DerivedTensor.ExtensionByZero.restriction X W).mapDerivedCategoryFactors.app K

/-- Derived restriction to the slice preserves objects concentrated in degrees `≤ n`. -/
theorem isLE_sliceDerivedRestriction_obj (K) (n : ℤ) (h : K.IsLE n) :
    ((sliceDerivedRestriction X W).obj K).IsLE n :=
  Functor.isLE_mapDerivedCategory_obj (Stacks.DerivedTensor.ExtensionByZero.restriction X W) K n h

/-- Derived restriction to the slice preserves objects concentrated in degrees `≥ n`. -/
theorem isGE_sliceDerivedRestriction_obj (K) (n : ℤ) (h : K.IsGE n) :
    ((sliceDerivedRestriction X W).obj K).IsGE n :=
  Functor.isGE_mapDerivedCategory_obj (Stacks.DerivedTensor.ExtensionByZero.restriction X W) K n h

/-- If a morphism induces an isomorphism on cohomology in degree `j`, so does its derived
restriction to the slice. -/
theorem isIso_homologyMap_sliceDerivedRestriction_map {K L} (g : K ⟶ L) (j : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ j).map g)) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map ((sliceDerivedRestriction X W).map g)) :=
  Functor.isIso_homologyMap_mapDerivedCategory_map
    (Stacks.DerivedTensor.ExtensionByZero.restriction X W) g j h

/-- Cohomology commutes with restriction to the slice. -/
def sliceDerivedRestrictionHomologyIso (n : ℤ) :
    sliceDerivedRestriction X W ⋙ DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙
        SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W :=
  StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (Stacks.DerivedTensor.ExtensionByZero.restriction X W) n

section Extension

omit [HasSheafify (X.J.over W) AddCommGrpCat]
  [(X.J.over W).WEqualsLocallyBijective AddCommGrpCat] in
private instance preservesFiniteLimits_sliceExtension :
    PreservesFiniteLimits (SheafOfModules.pullback.{u} (F := Over.forget W)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))) :=
  ((exactFunctor_iff _).mp (Stacks.Sites.ExtensionByZero.extensionByZero_exact X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)).1

/-- Derived extension by zero from the slice preserves objects concentrated in degrees `≤ n`. -/
theorem isLE_sliceDerivedExtensionByZero_obj (K) (n : ℤ) (h : K.IsLE n) :
    ((sliceDerivedExtensionByZero X W).obj K).IsLE n :=
  @Functor.isLE_mapDerivedCategory_obj _ _ _ _ _ _ _ _ _
    (Stacks.Cohomology.Localization.additive_extensionByZero X W) _ _ K n h

/-- Derived extension by zero from the slice preserves objects concentrated in degrees `≥ n`. -/
theorem isGE_sliceDerivedExtensionByZero_obj (K) (n : ℤ) (h : K.IsGE n) :
    ((sliceDerivedExtensionByZero X W).obj K).IsGE n :=
  @Functor.isGE_mapDerivedCategory_obj _ _ _ _ _ _ _ _ _
    (Stacks.Cohomology.Localization.additive_extensionByZero X W) _ _ K n h

/-- If a morphism induces an isomorphism on cohomology in degree `j`, so does its derived
extension by zero from the slice. -/
theorem isIso_homologyMap_sliceDerivedExtensionByZero_map {K L} (g : K ⟶ L) (j : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ j).map g)) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map ((sliceDerivedExtensionByZero X W).map g)) :=
  @Functor.isIso_homologyMap_mapDerivedCategory_map _ _ _ _ _ _ _ _ _
    (Stacks.Cohomology.Localization.additive_extensionByZero X W) _ _ K L g j h

end Extension

end Typed

section Main

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasWeakSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (W : X.C) (V : Over W), HasSheafify ((X.J.over W).over V) AddCommGrpCat.{u}]
  [∀ (W : X.C) (V : Over W), ((X.J.over W).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (W : X.C) (V : Over W), HasWeakSheafify ((X.J.over W).over V) AddCommGrpCat.{u}]
  [HasBinaryProducts X.C] [∀ W : X.C, HasBinaryProducts (X.over W).C] [HasBinaryProducts Y.C]
  [∀ W : X.C, IsIso (Over.forgetAdjStar W).unit]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [∀ W : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).Additive]
  [∀ W : X.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).obj A).Additive]
  [∀ W : X.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.over W).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor (X.over W).O)
      (ComplexShape.up ℤ)]
  [∀ W : Y.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over W).O).Additive]
  [∀ W : Y.C, ∀ A,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y.over W).O).obj A).Additive]
  [∀ W : Y.C, ∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Y.over W).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor (Y.over W).O)
      (ComplexShape.up ℤ)]

omit [∀ (W : X.C) (V : Over W), HasSheafify ((X.J.over W).over V) AddCommGrpCat]
  [∀ (W : X.C) (V : Over W), ((X.J.over W).over V).WEqualsLocallyBijective AddCommGrpCat]
  [∀ (W : X.C) (V : Over W), HasWeakSheafify ((X.J.over W).over V) AddCommGrpCat] in
/-- **A monoidal t-exact functor commutes with `RSheafHom` out of a pseudo-coherent object into a
bounded below one**, when it is local on the slices: for `E` pseudo-coherent and `M` bounded
below, the comparison `Φ RSheafHom(E, M) ⟶ RSheafHom(Φ E, Φ M)` is an isomorphism. -/
theorem isIso_homComparisonMonoidal_of_isPseudoCoherent
    (u : X.C ⥤ Y.C) [u.IsContinuous X.J Y.J] (hTop : Y.J.CoversTop u.obj)
    [∀ W : X.C, IsIso (Over.forgetAdjStar (u.obj W)).unit]
    (Φ : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [Φ.Monoidal] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hLE : ∀ K n, K.IsLE n → (Φ.obj K).IsLE n)
    (hGE : ∀ K n, K.IsGE n → (Φ.obj K).IsGE n)
    (hH : ∀ {K L} (g : K ⟶ L) (j : ℤ), IsIso ((DerivedCategory.homologyFunctor _ j).map g) →
      IsIso ((DerivedCategory.homologyFunctor _ j).map (Φ.map g)))
    (hK : ∀ (W : X.C) K, IsZero ((sliceDerivedRestriction X W).obj K) →
      IsZero ((sliceDerivedRestriction Y (u.obj W)).obj (Φ.obj K)))
    (E M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPseudoCoherent E) (a : ℤ) (hM : M.IsGE a) :
    IsIso (homComparisonMonoidal Φ E M) := by
  obtain ⟨K, hKpc, ⟨e⟩⟩ := hE
  have key : ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor _ n).map
      (homComparisonMonoidal Φ (DerivedCategory.Q.obj K) M)) := by
    intro n
    let p : X.C → Prop := fun W => ∃ P : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ α : P ⟶ X.restrictComplex K W,
          (∀ j : ℤ, a - n - 1 < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α (a - n - 1))
    have hcover := GrothendieckTopology.coversTop_obj_subtype u X.J Y.J hTop p (fun U => by
      obtain ⟨S, hS, h⟩ := hKpc (a - n - 1) U
      exact ⟨S, hS, fun V g hg => h g hg⟩)
    refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hcover _ ?_
    rintro ⟨W, P, hP, α, hiso, hepi⟩
    let := localizedFunctorMonoidal Φ (sliceDerivedRestriction X W)
      (sliceDerivedRestriction Y (u.obj W)) (sliceDerivedAdjunction X W) (hK W)
    have h₁ : IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((sliceDerivedRestriction Y (u.obj W)).map
          (homComparisonMonoidal Φ (DerivedCategory.Q.obj K) M))) := by
      rw [isIso_map_map_homComparisonMonoidal_iff Φ (sliceDerivedRestriction X W)
        (sliceDerivedRestriction Y (u.obj W)) (sliceDerivedAdjunction X W) (hK W)
        (fun A B => by exact isIso_homComparisonMonoidal_restriction X W A B)
        (fun A B => by exact isIso_homComparisonMonoidal_restriction Y (u.obj W) A B)]
      rw [isIso_map_homComparisonMonoidal_iff_of_iso _ _ (sliceDerivedRestrictionQIso X W K)]
      refine isIso_homologyMap_homComparisonMonoidal_of_approximation (X := X.over W)
        (Y := Y.over (u.obj W)) _ ?_ ?_ ?_ hP α (a - n - 1) hiso hepi _ a
        (isGE_sliceDerivedRestriction_obj X W M a hM) n (by omega)
      · exact fun K' m h => isLE_sliceDerivedRestriction_obj Y (u.obj W) _ m
          (hLE _ m (isLE_sliceDerivedExtensionByZero_obj X W K' m h))
      · exact fun K' m h => isGE_sliceDerivedRestriction_obj Y (u.obj W) _ m
          (hGE _ m (isGE_sliceDerivedExtensionByZero_obj X W K' m h))
      · exact fun g j h => isIso_homologyMap_sliceDerivedRestriction_map Y (u.obj W) _ j
          (hH _ j (isIso_homologyMap_sliceDerivedExtensionByZero_map X W g j h))
    exact (NatIso.isIso_map_iff (sliceDerivedRestrictionHomologyIso Y (u.obj W) n) _).1 h₁
  have hQ : IsIso (homComparisonMonoidal Φ (DerivedCategory.Q.obj K) M) := by
    rw [DerivedCategory.isIso_iff]
    exact key
  have sq := homComparisonMonoidal_naturality_source Φ e.hom M
  have h₂ : IsIso (homComparisonMonoidal Φ E M ≫
      ((derivedSheafHomBifunctor Y).map (Φ.map e.hom).op).app (Φ.obj M)) := by
    rw [← sq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (((derivedSheafHomBifunctor Y).map (Φ.map e.hom).op).app (Φ.obj M))

end Main

end AlgebraicGeometry.RingedSite

end
