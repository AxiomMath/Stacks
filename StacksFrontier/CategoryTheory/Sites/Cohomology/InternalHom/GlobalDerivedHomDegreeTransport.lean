module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeSource

/-!
# The degree-`n` reading of the canonical map, for arbitrary complexes

Let `(C, O)` be a ringed site. The degree-`n` reading of the canonical map
`Hom^•(A, B) ⟶ RHom_O(A, B)` of `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is
proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeSource` at a
*representative pair*: a K-flat source and a K-injective target. This file transports it to
**arbitrary** complexes: for every `A`, `B` and every `n` the degree-`n` cohomology of the
canonical map is the localization functor `K(O) ⥤ D(O)` on morphism groups, read on the source by
Tag 0A5X in degree `n`.

This is the form the central clause of Tag 0CS6 needs: the complexes that clause is about are the
tensor products `M ⊗_E K` and `N ⊗_E K`, and neither is K-flat nor K-injective.

## Main results

* `AlgebraicGeometry.RingedSite.localizationHomAddHom_conj`: the localization map on morphism
  groups is compatible with pre- and postcomposition by morphisms of complexes.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree`: **the degree-`n`
  reading, for arbitrary complexes.**

## Implementation notes

*The two representatives.* `AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement` at the
identity of `Q A` yields a K-flat `R` together with a morphism of complexes `u : R ⟶ A` whose class
is invertible, and `AlgebraicGeometry.RingedSite.exists_Q_map_eq_kInjectiveModelIso_inv` yields a
morphism of complexes `h : B ⟶ kInjectiveModel (Q B)` into a K-injective complex whose class is
invertible. No morphism of complexes out of the chosen K-flat *model* into `A` is available — the
chosen K-flat model maps into the chosen K-injective one, which is why
`AlgebraicGeometry.RingedSite.kFlatModelIso_hom_comp` is phrased as it is — so the contravariant
variable goes through the refinement and not through the chosen model.

*The cancellation.* The degree-`n` homology of the naturality square
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_naturality` at `(u, h)` is read on the
target side by `AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv_naturality` at
`(Q u, Q h)` and on the source side by
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_conj`; what is left is `Q u` on the left and
the class of the `n`-shift of `h` on the right, both invertible — the second because `h` is a
quasi-isomorphism and the quasi-isomorphisms are stable under the translation.

*Why the reading is restated in degree `n` first.* Transporting the reading in the degree-zero
shape at the pair `(F, G[n])` in which
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat` states it would
additionally need the naturality of `CochainComplex.HomComplex.homComplexTargetShiftIso` under
`CochainComplex.HomComplex.homComplexConj`. Restating it in degree `n` first, which is what
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree_of_isKFlat` does,
removes the target shift from the statement and with it that input.

*The associativity obstruction.* The degree-`n` homology of the naturality square is taken by `congrArg`
and not by rewriting: the target of the canonical map is spelled with
`AlgebraicGeometry.RingedSite.globalDerivedHom` while the morphism it is composed with is spelled
with `AlgebraicGeometry.RingedSite.derivedModuleGlobalSections` applied to the derived internal
Hom, so `CategoryTheory.Functor.map_comp` cannot be used backwards to *form* the composite — only
forwards, on the composite the naturality statement already contains.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The localization map on morphism groups is compatible with pre- and postcomposition.** For
morphisms of complexes `u : A' ⟶ A` and `m : D ⟶ D'`, conjugating a homotopy class by them and
localizing is localizing and conjugating by their classes. -/
theorem localizationHomAddHom_conj
    {A A' D D' :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : A' ⟶ A) (m : D ⟶ D')
    (f : (HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj D) :
    localizationHomAddHom X A' D'
        ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).map u ≫
          f ≫
            (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).map m) =
      DerivedCategory.Q.map u ≫ localizationHomAddHom X A D f ≫ DerivedCategory.Q.map m := by
  have hQh : ∀ {P P' : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (g : P ⟶ P'),
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ)).map g) =
        (DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app P ≫
          DerivedCategory.Q.map g ≫
            (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv.app P' := by
    intro P P' g
    rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc]
    simp
  rw [localizationHomAddHom_apply, localizationHomAddHom_apply,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hQh u, hQh m]
  simp

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The canonical map `Hom^•(A, B) ⟶ RHom_O(A, B)` is the localization functor on degree-`n`
cohomology, for arbitrary complexes.** The degree-`n` cohomology of `Hom^•(A, B)` is
`Hom_{K(O)}(A, B[n])` by Tag 0A5X, the degree-`n` cohomology of `RHom_O(A, B)` is
`Hom_{D(O)}(Q A, (Q B)[n])` by Tag 0B6E
(`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`), and the map between them induced by
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom` is the localization functor
`K(O) ⥤ D(O)`.

Neither complex is assumed K-flat or K-injective. -/
theorem homComplexToGlobalDerivedHom_homology_degree
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj (A.HomComplex B)) : Type u)) :
    globalDerivedHomDegreeEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) n
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (homComplexToGlobalDerivedHom X A B) η) ≫
        (DerivedCategory.Q.commShiftIso n).inv.app B =
      localizationHomAddHom X A (B⟦n⟧)
        (homComplexHomologyAddEquiv A B n
          (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
            (A.HomComplex B)).hom η)) := by
  obtain ⟨R, hR, u, -, hu, -⟩ := exists_kFlat_common_refinement X
    (𝟙 (DerivedCategory.Q.obj A))
  obtain ⟨h, hh, -⟩ := exists_Q_map_eq_kInjectiveModelIso_inv X B
  -- the class of the `n`-shift of `h` is invertible, because `h` is a quasi-isomorphism
  have hqh : QuasiIso h := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hh
  have hhn : IsIso (DerivedCategory.Q.map (h⟦n⟧')) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  -- the degree-`n` homology of the naturality square
  have h0 := congrArg (fun z => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map z)
    (homComplexToGlobalDerivedHom_naturality X u h)
  have hsq' : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (homComplexToGlobalDerivedHom X R (kInjectiveModel X (DerivedCategory.Q.obj B)))
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (DerivedCategory.Q.map (homComplexConj u h)) η) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
              (DerivedCategory.Q.obj B) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
              (DerivedCategory.Q.map h)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (homComplexToGlobalDerivedHom X A B) η) :=
    ConcreteCategory.congr_hom
      ((Functor.map_comp _ _ _).symm.trans (h0.trans (Functor.map_comp _ _ _))) η
  -- the source-side transport
  have hsrc : ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          (R.HomComplex (kInjectiveModel X (DerivedCategory.Q.obj B)))).hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (DerivedCategory.Q.map (homComplexConj u h)) η) =
      HomologicalComplex.homologyMap (homComplexConj u h) n
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          (A.HomComplex B)).hom η) :=
    ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).hom.naturality
        (homComplexConj u h)) η
  -- the reading at the representative pair, rewritten on both sides
  have hkey := homComplexToGlobalDerivedHom_homology_degree_of_isKFlat X R
    (kInjectiveModel X (DerivedCategory.Q.obj B)) hR n
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      (DerivedCategory.Q.map (homComplexConj u h)) η)
  rw [hsq', globalDerivedHomDegreeEquiv_naturality X (DerivedCategory.Q.map u)
      (DerivedCategory.Q.map h) n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (homComplexToGlobalDerivedHom X A B) η),
    hsrc,
    homComplexHomologyAddEquiv_conj u h n
      (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
        (A.HomComplex B)).hom η),
    localizationHomAddHom_conj X u (h⟦n⟧')
      (homComplexHomologyAddEquiv A B n
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          (A.HomComplex B)).hom η))] at hkey
  -- cancel `Q u` on the left and the class of the `n`-shift of `h` on the right
  rw [Category.assoc, Category.assoc] at hkey
  have hcancel := (cancel_epi (DerivedCategory.Q.map u)).1 hkey
  rw [CategoryTheory.Functor.commShiftIso_inv_naturality DerivedCategory.Q h n,
    ← Category.assoc] at hcancel
  exact (cancel_mono (DerivedCategory.Q.map (h⟦n⟧'))).1 hcancel

end AlgebraicGeometry.RingedSite

end
