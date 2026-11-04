module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.DerivedCategoryAsLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor bifunctor on the derived category of a ringed site

Let `(C, O)` be a ringed site. This file constructs the bifunctor

`- ⊗^L_O - : D(Mod(O)) ⥤ D(Mod(O)) ⥤ D(Mod(O))`

together with the isomorphism identifying its value at `(A, L)` with the ordinary total tensor
complex `Tot(A ⊗_O L)` whenever the *first* factor is K-flat — for an arbitrary second
factor — naturally in both.

The asymmetry is deliberate and is what the construction turns on. The total tensor product of
complexes, followed by the localization functor `DerivedCategory.Q`, inverts a
quasi-isomorphism in the first variable as soon as that quasi-isomorphism is between K-flat
complexes (Stacks 06YT), and inverts *every* quasi-isomorphism in the second variable as soon
as the first factor is K-flat (Stacks 06YP). So it descends along the pair of localization
functors: the K-flat complexes, which localize onto `D(Mod(O))` because every complex has a
K-flat resolution (Stacks 06YS) and the K-flat complexes form a pre-triangulated subcategory
of the homotopy category (Stacks 07A3), by Stacks 0GSL; and `DerivedCategory.Q` on all
complexes. The comparison isomorphism is then the lifting datum of that descent, whence its
naturality in the K-flat first factor and the arbitrary second factor simultaneously.

Because the first localization is taken at the level of *complexes*, the comparison holds on
the nose at `DerivedCategory.Q.obj A` and `DerivedCategory.Q.obj L` with no transport.

## Main definitions

* `Stacks.SheafOfModules.kFlatComplexes`: K-flatness as a property of complexes.
* `Stacks.SheafOfModules.kFlatComplexQ`: the functor from K-flat complexes to the derived
  category.
* `Stacks.SheafOfModules.derivedTensorBifunctor`: the bifunctor `- ⊗^L_O -`.
* `Stacks.SheafOfModules.kFlatComparison`: for `A` K-flat and `L` arbitrary, the isomorphism
  `A ⊗^L_O L ≅ Tot(A ⊗_O L)`.

## Main results

* `Stacks.SheafOfModules.kFlatComplexQ_isLocalization`: the K-flat complexes localize onto the
  derived category.
* `Stacks.SheafOfModules.kFlatTensorToDerived_inverts`: the inverting property that makes the
  descent possible.
* `Stacks.SheafOfModules.kFlatComparison_naturality`: the comparison is natural in the K-flat
  first factor and in the arbitrary second factor.

## Implementation notes on spelling

Morphisms of total tensor complexes are written throughout as values of
`Stacks.SheafOfModules.Tensor.tensorComplex`, never as `HomologicalComplex.mapBifunctorMap`. The
  two are
definitionally equal but comparing them is expensive at the default elaboration limits, since
it unfolds the total complex and its direct sums; the generic
`HomologicalComplex.mapBifunctorMap_eq_map₂_comp` is the one place that comparison is made,
and it is proved before `Stacks.SheafOfModules.Tensor.sheafTensor` is substituted in.

## Implementation notes

That the K-flat complexes localize onto the derived category is obtained from the
corresponding statement for the K-flat objects of the homotopy category
(`Stacks.SheafOfModules.kFlatQ_isLocalization`) by the general two-step factorisation
`CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization`.

The universes are all equal, inherited from the existence of K-flat resolutions.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
* [Stacks Project, Tag 06YT](https://stacks.math.columbia.edu/tag/06YT)
* [Stacks Project, Tag 0GSL](https://stacks.math.columbia.edu/tag/0GSL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- K-flatness as a property of cochain complexes of sheaves of modules. -/
abbrev kFlatComplexes :
    ObjectProperty (CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ) :=
  ObjectProperty.complexSubcategory (kFlatObjects.{c, u, u} X.O)

/-- `kFlatComplexes` is K-flatness of the complex. -/
theorem kFlatComplexes_iff
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatComplexes X K ↔ IsKFlat X.O K :=
  Iff.rfl

/-- A K-flat complex, as an object of the full subcategory of K-flat complexes. -/
abbrev kFlatObj
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A) : (kFlatComplexes X).FullSubcategory :=
  ⟨A, hA⟩

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] kFlatQ_isLocalization
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex

/-- The functor from K-flat complexes to the derived category. -/
abbrev kFlatComplexQ :
    (kFlatComplexes X).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (kFlatComplexes X).ι ⋙ DerivedCategory.Q

/-- The quasi-isomorphisms between K-flat complexes. -/
abbrev kFlatComplexQuasiIso :
    MorphismProperty (kFlatComplexes X).FullSubcategory :=
  (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up
        ℤ)).inverseImage
    (kFlatComplexes X).ι

/-- The derived category of sheaves of modules on a ringed site is the localization of the
K-flat complexes at the quasi-isomorphisms between them. -/
instance kFlatComplexQ_isLocalization :
    (kFlatComplexQ X).IsLocalization (kFlatComplexQuasiIso X) :=
  ObjectProperty.ι_comp_Q_isLocalization (kFlatObjects.{c, u, u} X.O)

/-- The total tensor product of a K-flat complex with an arbitrary complex, pushed into the
derived category. This is the bifunctor whose descent is the derived tensor product. -/
abbrev kFlatTensorToDerived :
    (kFlatComplexes X).FullSubcategory ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (kFlatComplexes X).ι ⋙ Stacks.SheafOfModules.Tensor.tensorComplex X.O ⋙
    (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q

/-- `kFlatTensorToDerived` inverts quasi-isomorphisms between K-flat complexes in the first
variable and all quasi-isomorphisms in the second, simultaneously. The first is Stacks 06YT
and the second is Stacks 06YP. -/
theorem kFlatTensorToDerived_inverts :
    MorphismProperty.IsInvertedBy₂ (kFlatComplexQuasiIso X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerived X) := by
  rintro ⟨A, L⟩ ⟨B, L'⟩ ⟨c, g⟩ ⟨hc, hg⟩
  have hA := (kFlatComplexes_iff X _).1 A.2
  have hB := (kFlatComplexes_iff X _).1 B.2
  have e1 : IsIso (((kFlatTensorToDerived X).map c).app L) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 <|
      quasiIso_tensorComplex_map_app_of_kFlat X c.hom
        ((HomologicalComplex.mem_quasiIso_iff c.hom).1 hc) hA hB L
  have e2 : IsIso (((kFlatTensorToDerived X).obj B).map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 <|
      IsKFlat.quasiIso_tensorComplex_obj_map X.O B.obj hB g
        ((HomologicalComplex.mem_quasiIso_iff g).1 hg)
  rw [Functor.uncurry_obj_map]
  infer_instance

/-- The derived tensor product bifunctor on the derived category of sheaves of modules on a
ringed site. -/
def derivedTensorBifunctor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Localization.lift₂ (kFlatTensorToDerived X) (kFlatTensorToDerived_inverts X)
    (kFlatComplexQ X) DerivedCategory.Q

/-- `derivedTensorBifunctor` descends `kFlatTensorToDerived` along the two localizations. -/
@[instance_reducible]
def derivedTensorBifunctorLifting :
    Localization.Lifting₂ (kFlatComplexQ X) DerivedCategory.Q
      (kFlatComplexQuasiIso X)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
      (kFlatTensorToDerived X) (derivedTensorBifunctor X) := by
  unfold derivedTensorBifunctor
  infer_instance

attribute [local instance] derivedTensorBifunctorLifting

/-- The comparison isomorphism of bifunctors: on a K-flat first factor and an arbitrary
second factor, the derived tensor product is the ordinary total tensor product. -/
abbrev kFlatComparisonNatIso :
    (((Functor.whiskeringLeft₂ _).obj (kFlatComplexQ X)).obj
        DerivedCategory.Q).obj (derivedTensorBifunctor X) ≅
      kFlatTensorToDerived X :=
  Localization.Lifting₂.iso (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X)

/-- For a K-flat complex `A` and an arbitrary complex `L`, the derived tensor product of their
classes is the class of their total tensor complex. -/
def kFlatComparison
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : IsKFlat X.O A)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj A)).obj
        (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj L) :=
  ((kFlatComparisonNatIso X).app (kFlatObj X A hA)).app L

/-- The comparison isomorphism is natural in the K-flat first factor and in the arbitrary
second factor at once. The morphism of total tensor complexes is written as the composite of
the two one-variable images; `HomologicalComplex.mapBifunctorMap_eq_map₂_comp` identifies it
with `HomologicalComplex.mapBifunctorMap c g`. -/
theorem kFlatComparison_naturality
    {A B L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : IsKFlat X.O A) (hB : IsKFlat X.O B) (c : A ⟶ B) (g : L ⟶ L') :
    ((derivedTensorBifunctor X).map (DerivedCategory.Q.map c)).app
          (DerivedCategory.Q.obj L) ≫
        ((derivedTensorBifunctor X).obj (DerivedCategory.Q.obj B)).map
          (DerivedCategory.Q.map g) ≫
        (kFlatComparison X B hB L').hom =
      (kFlatComparison X A hA L).hom ≫
        DerivedCategory.Q.map (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map c).app L ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj B).map g) := by
  have h := (Functor.uncurry.map (kFlatComparisonNatIso X).hom).naturality
    ((⟨(⟨c⟩ : kFlatObj X A hA ⟶ kFlatObj X B hB), g⟩ :
      ((kFlatObj X A hA, L) : _ × _) ⟶ (kFlatObj X B hB, L')))
  simp only [Functor.uncurry_obj_map, Functor.uncurry_map_app, Category.assoc] at h
  rw [Functor.map_comp]
  exact h

end Stacks.SheafOfModules

end
