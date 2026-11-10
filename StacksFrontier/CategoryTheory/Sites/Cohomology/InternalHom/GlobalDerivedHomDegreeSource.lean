module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomCanonicalNaturality
public import StacksFrontier.Homology.HomComplex.TargetShiftDegree

/-!
# The degree-`n` reading of the canonical map, against the degree-`n` source identification

Let `(C, O)` be a ringed site. The degree-`n` reading
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat` of the canonical
map `Hom^•(F, G) ⟶ RHom_O(F, G)` states its answer in the **degree-zero** shape at the pair
`(F, G[n])`, because that is the shape the degree-zero reading it is deduced from already has.
This file restates it against the degree-`n` identification of Tag 0A5X,
`CochainComplex.HomComplex.homComplexHomologyAddEquiv` at `n`, which is the form the central clause
of Tag 0CS6 consumes; the comparison of the two shapes is
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift_Q` of
`StacksFrontier.Homology.HomComplex.TargetShiftDegree`.

It also records the two statements the transport of that reading off the representative pair needs
on the *source* side: the naturality of the degree-`n` identification of Tag 0A5X under pre- and
postcomposition, and the localization functor on morphism groups out of a complex with no
hypothesis on the target.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationHomAddHom`: the map
  `Hom_{K(O)}(A, B) →+ Hom_{D(O)}(A, B)` induced by the localization functor, for **arbitrary**
  complexes — the map that `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv` is an
  isomorphism onto when the target is K-injective.

## Main results

* `CochainComplex.HomComplex.homComplexHomologyAddEquiv_conj`: **the source-side naturality.** The
  degree-`n` identification of Tag 0A5X carries the map induced on the cohomology of the Hom
  complex by pre- and postcomposition to pre- and postcomposition in the homotopy category.
* `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_eq`: at a K-injective target the
  isomorphism of `AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv` is
  `AlgebraicGeometry.RingedSite.localizationHomAddHom`.
* `AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_degree_of_isKFlat`: **the
  degree-`n` reading, against the degree-`n` source identification.** For a K-flat `F` and a
  K-injective `G` the degree-`n` cohomology of the canonical map is the localization functor on
  morphism groups, with the source class read by Tag 0A5X in degree `n`.

## Implementation notes

*What this removes from the remaining work.* The transport of the degree-`n` reading off the
representative pair was planned — see the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHom` — to need the naturality
of `CochainComplex.HomComplex.homComplexTargetShiftIso` under
`CochainComplex.HomComplex.homComplexConj` as well as
`AlgebraicGeometry.RingedSite.homologyAddEquiv_conj`. With the reading restated in degree `n` the
target shift no longer appears in it, so only the second is needed, and
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_conj` below is exactly it.

*Why the localization map has to be named.* The reading at a representative pair is stated against
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`, which is an *isomorphism* and
therefore exists only at a K-injective target. The complexes the central clause of Tag 0CS6 is
about are not K-injective, so the transported statement cannot be phrased with it; what survives
the transport is the underlying map, which is the localization functor conjugated by the comparison
of the two localizations, with no hypothesis. That map is
`AlgebraicGeometry.RingedSite.localizationHomAddHom`.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The degree-`n` identification of Tag 0A5X is natural in both complexes.** The map induced on
the degree-`n` cohomology of the Hom complex by pre- and postcomposition
(`CochainComplex.HomComplex.homComplexConj`) is pre- and postcomposition in the homotopy category,
the postcomposition being with the `n`-shift of the morphism.

This is `AlgebraicGeometry.RingedSite.homologyAddEquiv_conj` read through
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`, for which the two naturality statements
are `CochainComplex.HomComplex.toHom_cohomologyClassPrecomp` and
`CochainComplex.HomComplex.toHom_cohomologyClassPostcomp`. -/
theorem homComplexHomologyAddEquiv_conj {K K' L L' : CochainComplex C ℤ} (f : K' ⟶ K) (g : L ⟶ L')
    (n : ℤ) (η : (K.HomComplex L).homology n) :
    homComplexHomologyAddEquiv K' L' n
        (HomologicalComplex.homologyMap (homComplexConj f g) n η) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f ≫
        homComplexHomologyAddEquiv K L n η ≫
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (g⟦n⟧') := by
  rw [homComplexHomologyAddEquiv, homComplexHomologyAddEquiv, AddEquiv.trans_apply,
    AddEquiv.trans_apply, homologyAddEquiv_conj f g n η]
  simp only [CohomologyClass.homAddEquiv_apply, toHom_cohomologyClassPrecomp,
    toHom_cohomologyClassPostcomp]

end CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **The localization functor on morphism groups out of a complex**, for arbitrary complexes:
`Hom_{K(O)}(A, B) →+ Hom_{D(O)}(A, B)`. It is `CategoryTheory.DerivedCategory.Qh` on morphisms,
conjugated by the comparison `CategoryTheory.DerivedCategory.quotientCompQhIso` of the two
localizations of the category of complexes.

No complex is assumed K-injective: at a K-injective target this map is the isomorphism
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv`
(`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv_eq`), but the transport of the
degree-`n` reading of the canonical map off a representative pair needs the map itself; see the
implementation notes. -/
def localizationHomAddHom
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj A ⟶
        (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj B) →+
      (DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :=
  ((CategoryTheory.Linear.homCongr ℤ
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app A)
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          B)).toAddEquiv.toAddMonoidHom).comp
    DerivedCategory.Qh.mapAddHom

/-- The localization functor on morphism groups out of a complex, written out: the class of a
homotopy class is the comparison of the two localizations, the image under
`CategoryTheory.DerivedCategory.Qh`, and the comparison again. -/
theorem localizationHomAddHom_apply
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj B) :
    localizationHomAddHom X A B f =
      ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app A).inv ≫
        DerivedCategory.Qh.map f ≫
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app B).hom := by
  simp [localizationHomAddHom, CategoryTheory.Linear.homCongr, CategoryTheory.Linear.leftComp,
    CategoryTheory.Linear.rightComp]

/-- **At a K-injective target the comparison of the homotopy category with the derived category is
the localization map.** This is what lets a statement proved against
`AlgebraicGeometry.RingedSite.homotopyHomDerivedCategoryEquiv` be transported to complexes for
which no K-injectivity is available. -/
theorem homotopyHomDerivedCategoryEquiv_eq
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective]
    (f : (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj I) :
    homotopyHomDerivedCategoryEquiv A I f = localizationHomAddHom X A I f :=
  rfl

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The canonical map `Hom^•(F, G) ⟶ RHom_O(F, G)` is the localization functor on degree-`n`
cohomology, at a K-flat source and a K-injective target, read against the degree-`n`
identification of Tag 0A5X.** This is
`AlgebraicGeometry.RingedSite.homComplexToGlobalDerivedHom_homology_of_isKFlat` with its
degree-zero source shape at the pair `(F, G[n])` replaced by
`CochainComplex.HomComplex.homComplexHomologyAddEquiv` in degree `n`, which is the identification
the other inputs of the central clause of Tag 0CS6 speak; the comparison of the two shapes is
`CochainComplex.HomComplex.homComplexHomologyAddEquiv_degreeShift_Q`. -/
theorem homComplexToGlobalDerivedHom_homology_degree_of_isKFlat
    (F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) [G.IsKInjective] (n : ℤ)
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj (F.HomComplex G)) : Type u)) :
    globalDerivedHomDegreeEquiv X (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj G) n
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (homComplexToGlobalDerivedHom X F G) η) ≫
        (DerivedCategory.Q.commShiftIso n).inv.app G =
      localizationHomAddHom X F (G⟦n⟧)
        (homComplexHomologyAddEquiv F G n
          (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
            (F.HomComplex G)).hom η)) := by
  refine (homComplexToGlobalDerivedHom_homology_of_isKFlat X F G hF n η).trans ?_
  refine congrArg (fun z => homotopyHomDerivedCategoryEquiv F (G⟦n⟧) z) ?_
  rw [Category.id_comp]
  exact homComplexHomologyAddEquiv_degreeShift_Q F G n η

end AlgebraicGeometry.RingedSite

end
