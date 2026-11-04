module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualRepresentatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalUnitality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 08JD is the diagonal of Stacks 0BYS

Let `(C, O)` be a ringed site, let `L` be an object of `D(O)` with dual `L^∨ = RSheafHom(L, O)`
and let `M` be an arbitrary object of `D(O)`. **Stacks 08JD** supplies a canonical map

`Φ_{L,M} : M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`,

`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, as derived composition of
Stacks 0A98 at intermediate object the structure sheaf. **Stacks 08JJ** asserts that it is an
isomorphism when `L` is perfect.

That isomorphism was already in the library, as
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`, but by a route that bypasses `Φ`
entirely: the diagonal morphism of **Stacks 0BYS** at target object the structure sheaf,
invertible by Stacks 0ATN. The two morphisms have the same type and nothing compared them, so
the invertibility of the *canonical* map was not available. This file compares them, and
concludes that `Φ_{L,M}` is an isomorphism for a perfect `L`.

## The comparison, and why no Koszul sign intervenes

Read on representatives, `Φ` is the chain-level composition morphism of **Stacks 0A91**
(`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_kFlatModel`), while the diagonal of
Stacks 0BYS is the chain-level interchange morphism of **Stacks 0BYR**
(`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels`). Comparing the two was
recorded in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom` as "a chain-level
identity between the composition morphism of Stacks 0A91 and the interchange morphism of
Stacks 0BYR, with their Koszul signs".

There is no sign to compare. The interchange morphism is *defined* as the diagonal morphism of
Stacks 0A93 tensored with the identity followed by the composition morphism of Stacks 0A91
(`AlgebraicGeometry.RingedSite.tensorHomInterchange`), so the chain-level identity
`tensorHomInterchange_comp_homMap` below is the covariant naturality of the composition
morphism in its target, `compositionMap_natural_target`, and nothing else.

What the comparison costs instead is the matching of models. The K-flat computation of
Stacks 0A98 wants the *second* tensor factor K-flat — a K-flat resolution `f : H ⟶ SheafHom(E, J)`
of the dual, with `J` a K-injective resolution of the structure sheaf — while the computation of
the diagonal of Stacks 0BYS wants the *first* one K-flat, a K-flat complex `A` representing the
tensor factor. The two are compared through the roof `Tot(A ⊗_O H)`, over which both source
comparisons factor through the canonical map `A ⊗^L_O H ⟶ Tot(A ⊗_O H)` of Stacks 06YU: that
map is natural in both complexes with no flatness hypothesis, which is the field
`toTensor_naturality` of `Stacks.SheafOfModules.DerivedTensorProduct`, and it is both
one-sided comparisons by `toTensor_eq_comparisonLeft` and `toTensor_eq_comparisonRight`.

The left legs of the two models then have to be identified, and that is the one place where
actual content enters: the left tensor factor of the interchange morphism is the diagonal of
Stacks 0A93 followed by the chosen model `q : Tot(A ⊗_O J) ⟶ I` of the unit constraint, and the
left tensor factor of `Φ` is the identification of `M` with `RSheafHom(O, M)`. That the two
agree is `derivedSheafHomComparison_eq_diagonalLeg` below, which is the chain-level unitality
identity `diagonalMap_comp_homMap_comp_homMap_comp_structureSheafHomEvaluation` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalUnitality` read in `D(O)`.
Both sides are sign-free there as well.

## Main definitions

* `AlgebraicGeometry.RingedSite.toTensorTotal`: the canonical map of Stacks 06YU to the total
  tensor-product complex, in the `tensorTotal` spelling.
* `AlgebraicGeometry.RingedSite.roofPrefix`: the roof through which the two source comparisons
  are compared.

## Main results

* `AlgebraicGeometry.RingedSite.tensorHomInterchange_comp_homMap`: **the chain-level comparison
  of Stacks 0BYR with Stacks 0A91**, with no Koszul sign.
* `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_eq_diagonalLeg`: the two left tensor
  factors agree.
* `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_comp_derivedSheafHomComparison`:
  **the canonical map of Stacks 08JD is the diagonal of Stacks 0BYS**, at models.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_isPerfect_canonical`:
  **Stacks 08JJ for the canonical map of Stacks 08JD** — it is an isomorphism for a perfect `L`.

## Implementation notes

The derived tensor product is instantiated at `Stacks.SheafOfModules.canonicalDerivedTensorProduct`
from the point where the diagonal of Stacks 0BYS enters, since that is the datum the diagonal is
stated for; the statements before it carry a derived tensor product as a parameter.

The model-level comparison is stated at `Q E` and `Q I` with `I` K-injective, which is the
generality `derivedTensorDualToSheafHom_kFlatModel` is stated in; the passage to arbitrary
objects of `D(O)` is the two transport lemmas
`isIso_derivedTensorDualToSheafHom_of_iso` and `isIso_derivedTensorDualToSheafHom_of_iso_target`
of `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDualDevissage`, which
is why no naturality of the diagonal of Stacks 0BYS is needed.

The morphism `q : Tot(A ⊗_O J) ⟶ I` is not canonical: it is *chosen*, through
`AlgebraicGeometry.RingedSite.exists_Q_map_eq_of_isKInjective`, to have the class prescribed by
the model of the unit constraint. Only its class matters, and the hypothesis `hq` of the
comparison fixes it.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A93](https://stacks.math.columbia.edu/tag/0A93)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})

/-- **The chain-level comparison of Stacks 0BYR with Stacks 0A91.** The interchange morphism
`Tot(A ⊗_O SheafHom(N, C)) ⟶ SheafHom(N, Tot(A ⊗_O C))` of Stacks 0BYT, followed by the map
induced by a morphism `ξ : Tot(A ⊗_O C) ⟶ Z`, is the composition morphism of Stacks 0A91 at
intermediate complex `C`, preceded in its left tensor factor by the diagonal morphism of
Stacks 0A93 followed by `ξ`.

No Koszul sign intervenes: the interchange morphism is *defined* as the diagonal tensored with
the identity followed by composition, so the identity is the covariant naturality of the
composition morphism in its target, `compositionMap_natural_target`. -/
theorem tensorHomInterchange_comp_homMap
    (A C N Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (ξ : tensorTotal X A C ⟶ Z) :
    tensorHomInterchange X A C N ≫ homMap X (𝟙 N) ξ =
      tensorTotalMap X (diagonalMap X A C ≫ homMap X (𝟙 C) ξ)
          (𝟙 (sheafHomComplex X N C).obj) ≫
        compositionMap X N C Z := by
  rw [tensorHomInterchange, Category.assoc, ← compositionMap_natural_target X N C ξ,
    ← Category.assoc, tensorTotalMap_comp, Category.comp_id]

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- The canonical map from the derived tensor product of two classes of complexes to the class
of their total tensor-product complex, written in the `tensorTotal` spelling of Section 34. -/
def toTensorTotal
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (T.tensor.obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj (tensorTotal X A B) :=
  T.toTensor A B ≫ DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B).inv

/-- The canonical map to the total tensor complex is natural in both complexes, with no
K-flatness hypothesis. -/
theorem derivedTensorMap_comp_toTensorTotal
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (c : A ⟶ A') (d : B ⟶ B') :
    derivedTensorMap X T (DerivedCategory.Q.map c) (DerivedCategory.Q.map d) ≫
        toTensorTotal X T A' B' =
      toTensorTotal X T A B ≫ DerivedCategory.Q.map (tensorTotalMap X c d) := by
  dsimp only [toTensorTotal, derivedTensorMap]
  simp only [Category.assoc]
  rw [reassoc_of% (T.toTensor_naturality c d)]
  simp only [← DerivedCategory.Q.map_comp]
  rw [tensorTotalIsoTensorComplex_naturality]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ T.toTensor A B ≫ z) (DerivedCategory.Q.map_comp _ _).symm)

omit [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two chain-level models of the comparison meet on `Tot(A ⊗_O H)`.** The composition
morphism of Stacks 0A91, preceded by `f` in its right tensor factor and by the left leg
`diagonalMap ≫ SheafHom(𝟙, q)` in its left one, is the interchange morphism of Stacks 0BYR
followed by `SheafHom(𝟙, q)`, preceded by `f` in its right tensor factor. Both sides are
`Tot(a ⊗ f)` followed by composition. -/
theorem tensorTotalMap_comp_compositionMap_eq_canonical
    (A H E J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : H ⟶ (sheafHomComplex X E J).obj) (q : tensorTotal X A J ⟶ I) :
    tensorTotalMap X (diagonalMap X A J ≫ homMap X (𝟙 J) q) (𝟙 H) ≫
        tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f ≫ compositionMap X E J I =
      tensorTotalMap X (𝟙 A) f ≫ tensorHomInterchange X A J E ≫ homMap X (𝟙 E) q := by
  rw [tensorHomInterchange_comp_homMap]
  simp only [← Category.assoc, tensorTotalMap_comp, Category.comp_id, Category.id_comp]

omit [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive] in
/-- **The left tensor factor of the two models agrees.** For a K-injective resolution
`g : O[0] ⟶ J` of the structure sheaf, a K-injective `I`, and a morphism
`q : Tot(A ⊗_O J) ⟶ I` whose class is the comparison `Q A ≅ Q I`, the K-injective model
comparison `RSheafHom(QJ, QI) ≅ Q SheafHom(J, I)` is restriction along `g` followed by the
identification `RSheafHom(O, QI) ≅ QI`, by `eA⁻¹`, and by the class of the left leg
`diagonalMap ≫ SheafHom(𝟙, q)`.

This is the chain-level unitality identity
`diagonalMap_comp_homMap_comp_homMap_comp_structureSheafHomEvaluation`, read in `D(O)`. -/
theorem derivedSheafHomComparison_eq_diagonalLeg
    {A J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g))
    (q : tensorTotal X A J ⟶ I)
    (eA : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj I)
    (hq : DerivedCategory.Q.map
      (diagonalTensorUnit X (A := A) ≫ tensorTotalMap X (𝟙 A) g ≫ q) = eA.hom) :
    (derivedSheafHomComparison X J I).hom =
      ((((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
            (DerivedCategory.Q.obj I) ≫
          (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom) ≫ eA.inv) ≫
        DerivedCategory.Q.map (diagonalMap X A J ≫ homMap X (𝟙 J) q) := by
  have := hg
  have : IsIso (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
    (DerivedCategory.Q.obj I)) := inferInstance
  have hnat := derivedSheafHomMap_homComparison X (derivedInternalHomOfBifunctor X) g (𝟙 I)
  simp only [CategoryTheory.Functor.map_id, derivedSheafHomMap,
    CategoryTheory.Functor.map_id, Category.comp_id] at hnat
  have h1 : (derivedSheafHomComparison X J I).hom ≫
        DerivedCategory.Q.map (homMap X g (𝟙 I) ≫ structureSheafHomEvaluation X I) =
      ((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
          (DerivedCategory.Q.obj I) ≫
        (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom := by
    rw [derivedStructureSheafHomIso_model, DerivedCategory.Q.map_comp, ← Category.assoc,
      ← hnat, Category.assoc]
  have h2 : DerivedCategory.Q.map (diagonalMap X A J ≫ homMap X (𝟙 J) q) ≫
      DerivedCategory.Q.map (homMap X g (𝟙 I) ≫ structureSheafHomEvaluation X I) = eA.hom := by
    rw [← DerivedCategory.Q.map_comp, ← hq]
    exact congrArg DerivedCategory.Q.map (by
      simp only [Category.assoc]
      exact diagonalMap_comp_homMap_comp_homMap_comp_structureSheafHomEvaluation X g q)
  have : IsIso (DerivedCategory.Q.map
      (homMap X g (𝟙 I) ≫ structureSheafHomEvaluation X I)) := by
    have hcomp : IsIso ((derivedSheafHomComparison X J I).hom ≫
        DerivedCategory.Q.map (homMap X g (𝟙 I) ≫ structureSheafHomEvaluation X I)) := by
      rw [h1]; infer_instance
    exact IsIso.of_isIso_comp_left (derivedSheafHomComparison X J I).hom _
  refine (cancel_mono (DerivedCategory.Q.map
    (homMap X g (𝟙 I) ≫ structureSheafHomEvaluation X I))).1 (h1.trans ?_)
  simp only [Category.assoc, h2, Iso.inv_hom_id, Category.comp_id]

section Comparison

variable {A H E J I :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The roof through which the two source comparisons are compared: a morphism into the class
of a complex `A`, tensored with the class of `H`, followed by the canonical map to the class of
`Tot(A ⊗_O H)`. -/
def roofPrefix
    {Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (U : Y ⟶ DerivedCategory.Q.obj A)
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (T.tensor.obj Y).obj (DerivedCategory.Q.obj H) ⟶
      DerivedCategory.Q.obj (tensorTotal X A H) :=
  derivedTensorMap X T U (𝟙 (DerivedCategory.Q.obj H)) ≫ toTensorTotal X T A H

/-- Absorbing a pair of morphisms of the tensor factors into the roof. -/
private theorem roofPrefix_comp_map_map
    {Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A' H' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (U : Y ⟶ DerivedCategory.Q.obj A) (c : A ⟶ A') (d : H ⟶ H') :
    roofPrefix X T U H ≫ DerivedCategory.Q.map (tensorTotalMap X c d) =
      derivedTensorMap X T (U ≫ DerivedCategory.Q.map c) (DerivedCategory.Q.map d) ≫
        toTensorTotal X T A' H' := by
  rw [roofPrefix, Category.assoc, ← derivedTensorMap_comp_toTensorTotal, ← Category.assoc,
    derivedTensorMap_comp, Category.id_comp]

/-- Absorbing a morphism of the left tensor factor into the roof. -/
theorem roofPrefix_comp_map
    {Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (U : Y ⟶ DerivedCategory.Q.obj A) (c : A ⟶ A')
    (H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    roofPrefix X T U H ≫ DerivedCategory.Q.map (tensorTotalMap X c (𝟙 H)) =
      roofPrefix X T (U ≫ DerivedCategory.Q.map c) H := by
  rw [roofPrefix_comp_map_map, CategoryTheory.Functor.map_id]
  rfl

/-- Absorbing a morphism of the right tensor factor into the roof. -/
theorem roofPrefix_comp_map_right
    {Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {H' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (U : Y ⟶ DerivedCategory.Q.obj A) (d : H ⟶ H') :
    roofPrefix X T U H ≫ DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) d) =
      derivedTensorMap X T U (DerivedCategory.Q.map d) ≫ toTensorTotal X T A H' := by
  rw [roofPrefix_comp_map_map, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The source comparison of the K-flat computation of Stacks 0A98, read through the roof.**
Composing the roof with the class of `Tot(a ⊗ 𝟙)`, where `a` is the left leg
`diagonalMap ≫ SheafHom(𝟙, q)`, recovers it. -/
theorem derivedEvaluationSourceComparison_eq_roofPrefix
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g))
    (q : tensorTotal X A J ⟶ I)
    (eA : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj I)
    (hq : DerivedCategory.Q.map
      (diagonalTensorUnit X (A := A) ≫ tensorTotalMap X (𝟙 A) g ≫ q) = eA.hom)
    (hH : Stacks.SheafOfModules.IsKFlat X.O H) :
    (derivedEvaluationSourceComparison X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (derivedInternalHomOfBifunctor X) H J I hH).hom =
      roofPrefix X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          ((((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
              (DerivedCategory.Q.obj I) ≫
            (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom) ≫ eA.inv) H ≫
        DerivedCategory.Q.map
          (tensorTotalMap X (diagonalMap X A J ≫ homMap X (𝟙 J) q) (𝟙 H)) := by
  rw [roofPrefix_comp_map, ← derivedSheafHomComparison_eq_diagonalLeg X g hg q eA hq,
    derivedEvaluationSourceComparison_hom]
  rfl

/-- **The source comparison of the diagonal of Stacks 0BYS, read through the roof.** -/
theorem derivedTensorDualSourceComparison_comp_sourceIsoOfModels
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g))
    (f : H ⟶ (sheafHomComplex X E J).obj)
    (eA : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj I)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) :
    derivedTensorDualSourceComparison X
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E J I H g f ≫
        (derivedTensorHomSourceIsoOfModels X hA eA (asIso (DerivedCategory.Q.map g)).symm
          (Iso.refl (DerivedCategory.Q.obj E))).hom =
      roofPrefix X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          ((((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
              (DerivedCategory.Q.obj I) ≫
            (derivedStructureSheafHomIso X (DerivedCategory.Q.obj I)).hom) ≫ eA.inv) H ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) f) := by
  have := hg
  have hw : (DerivedCategory.Q.map f ≫
        ((derivedInternalHomOfBifunctor X).homComparison E J).inv ≫
        ((derivedInternalHomOfBifunctor X).hom.obj (op (DerivedCategory.Q.obj E))).map
          (inv (DerivedCategory.Q.map g))) ≫
      (derivedSheafHomObjectsModelIso X (Iso.refl (DerivedCategory.Q.obj E))
          (asIso (DerivedCategory.Q.map g)).symm ≪≫
        derivedSheafHomComparison X E J).hom = DerivedCategory.Q.map f := by
    simp only [derivedSheafHomObjectsModelIso, derivedInternalHomOfBifunctor,
      Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
      Iso.refl_hom, Iso.op_hom, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Iso.symm_inv, asIso_hom, Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  have hsrc : (derivedTensorHomSourceIsoOfModels X hA eA (asIso (DerivedCategory.Q.map g)).symm
        (Iso.refl (DerivedCategory.Q.obj E))).hom =
      derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (𝟙 (DerivedCategory.Q.obj I))
          ((derivedSheafHomObjectsModelIso X (Iso.refl (DerivedCategory.Q.obj E))
              (asIso (DerivedCategory.Q.map g)).symm ≪≫
            derivedSheafHomComparison X E J).hom) ≫
        derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) eA.inv
            (𝟙 (DerivedCategory.Q.obj (sheafHomComplex X E J).obj)) ≫
          toTensorTotal X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) A
            (sheafHomComplex X E J).obj := by
    rw [derivedTensorMap_id_left, derivedTensorMap_id_right]
    dsimp only [derivedTensorHomSourceIsoOfModels, toTensorTotal, Iso.trans_hom, Iso.app_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.symm_hom]
    rw [(Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_eq_comparisonLeft A
      (sheafHomComplex X E J).obj hA]
    rfl
  rw [roofPrefix_comp_map_right, hsrc, derivedTensorDualSourceComparison, ← Category.assoc,
    derivedTensorMap_comp, Category.comp_id, hw, ← Category.assoc, derivedTensorMap_comp,
    Category.comp_id]

/-- The induced map on derived tensor products of two isomorphisms is an isomorphism. -/
theorem isIso_derivedTensorMap_of_isIso
    {Y Y' Z Z' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : Y ⟶ Y') (b : Z ⟶ Z') [IsIso a] [IsIso b] : IsIso (derivedTensorMap X T a b) := by
  have : IsIso (T.tensor.map a) := CategoryTheory.Functor.map_isIso _ _
  dsimp only [derivedTensorMap]
  infer_instance

/-- The source comparison of Stacks 08JD on representatives is an isomorphism as soon as the
chosen K-flat model of the dual and the chosen resolution of the structure sheaf are. -/
theorem isIso_derivedTensorDualSourceComparison
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g))
    (f : H ⟶ (sheafHomComplex X E J).obj) (hf : IsIso (DerivedCategory.Q.map f)) :
    IsIso (derivedTensorDualSourceComparison X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E J I H g f) := by
  have := hg
  have := hf
  have : IsIso (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map g).op).app
    (DerivedCategory.Q.obj I)) := inferInstance
  have : IsIso (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj E))).map
    (inv (DerivedCategory.Q.map g))) := CategoryTheory.Functor.map_isIso _ _
  exact isIso_derivedTensorMap_of_isIso X _ _ _

/-- **The canonical map of Stacks 08JD is the diagonal of Stacks 0BYS, at models.** For a
K-injective resolution `g : O[0] ⟶ J` of the structure sheaf, a K-injective `I`, a K-flat
resolution `f : H ⟶ SheafHom(E, J)` of the dual, a K-flat `A` representing `Q I` and a
morphism `q : Tot(A ⊗_O J) ⟶ I` representing the unit constraint, the canonical map

`Q I ⊗^L_O (Q E)^∨ ⟶ RSheafHom(Q E, Q I)`

of Stacks 08JD, read through the K-injective model comparison, is the diagonal morphism of
Stacks 0BYS read through the model comparison of its target. -/
theorem derivedTensorDualToSheafHom_comp_derivedSheafHomComparison
    [J.IsKInjective] [I.IsKInjective]
    (g : structureSheafComplex X ⟶ J) (hg : IsIso (DerivedCategory.Q.map g))
    (f : H ⟶ (sheafHomComplex X E J).obj) (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (hf : IsIso (DerivedCategory.Q.map f))
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj I)
    (q : tensorTotal X A J ⟶ I) (hqiso : IsIso (DerivedCategory.Q.map q))
    (hq : DerivedCategory.Q.map
      (diagonalTensorUnit X (A := A) ≫ tensorTotalMap X (𝟙 A) g ≫ q) = eA.hom) :
    derivedTensorDualToSheafHom X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
          (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj I) ≫
        (derivedSheafHomComparison X E I).hom =
      derivedTensorHomDiagonal X (DerivedCategory.Q.obj I) (derivedStructureSheaf X)
          (DerivedCategory.Q.obj E) ≫
        (derivedTensorHomTargetIsoOfModels X hA eA (asIso (DerivedCategory.Q.map g)).symm
          (Iso.refl (DerivedCategory.Q.obj E)) q hqiso).hom := by
  have := hg
  have := isIso_derivedTensorDualSourceComparison X (I := I) g hg f hf
  have hPhi := derivedTensorDualToSheafHom_kFlatModel X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E J I H g f hH
  have hDiag := derivedTensorHomDiagonal_eq_ofModels X (DerivedCategory.Q.obj I)
    (derivedStructureSheaf X) (DerivedCategory.Q.obj E) hA eA
    (asIso (DerivedCategory.Q.map g)).symm (Iso.refl (DerivedCategory.Q.obj E)) q hqiso
  have hev := derivedEvaluationSourceComparison_eq_roofPrefix X g hg q eA hq hH
  have hsrc := derivedTensorDualSourceComparison_comp_sourceIsoOfModels X g hg f eA hA
  simp only [Category.assoc] at hsrc
  refine (cancel_epi (derivedTensorDualSourceComparison X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E J I H g f)).1 ?_
  rw [hPhi, hev]
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  rw [tensorTotalMap_comp_compositionMap_eq_canonical,
    show tensorTotalMap X (𝟙 A) f ≫ tensorHomInterchange X A J E ≫ homMap X (𝟙 E) q =
      tensorTotalMap X (𝟙 A) f ≫ derivedTensorHomMapOfModels X (N := E) q from rfl,
    DerivedCategory.Q.map_comp, ← Category.assoc, ← hsrc, Category.assoc, ← hDiag,
    Iso.hom_inv_id_assoc]

end Comparison


section Perfect

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 08JJ, third assertion, for the canonical map of Stacks 08JD.** Let `(C, O)` be a
ringed site, let `L` be a **perfect** object of `D(O)` with dual `L^∨ = RSheafHom(L, O)` and let
`M` be an arbitrary object of `D(O)`. Then the canonical map

`M ⊗^L_O L^∨ ⟶ RSheafHom(L, M)`

of Stacks 08JD, `AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom`, is an isomorphism.

The isomorphism itself was already in the library as
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso`, the diagonal of Stacks 0BYS at
target object the structure sheaf; what is proved here is that the *canonical* map of
Stacks 08JD is that diagonal, so that the invertibility supplied by Stacks 0ATN applies to it.
The comparison is
`AlgebraicGeometry.RingedSite.derivedTensorDualToSheafHom_comp_derivedSheafHomComparison`, whose
chain-level content is `AlgebraicGeometry.RingedSite.tensorHomInterchange_comp_homMap`: the
interchange morphism of Stacks 0BYR is the diagonal of Stacks 0A93 tensored with the identity
followed by the composition morphism of Stacks 0A91, so no Koszul sign separates the two
morphisms. -/
@[stacks 08JJ "the canonical map M ⊗^L_O L^∨ ⟶ RSheafHom_O(L, M) of Stacks 08JD is an \
isomorphism for a perfect L"]
theorem isIso_derivedTensorDualToSheafHom_of_isPerfect_canonical
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : X.IsPerfect L) :
    IsIso (derivedTensorDualToSheafHom X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) L M) := by
  refine isIso_derivedTensorDualToSheafHom_of_iso X _ (kInjectiveModelIso X L).symm M ?_
  refine isIso_derivedTensorDualToSheafHom_of_iso_target X _ _
    (kInjectiveModelIso X M).symm ?_
  have hQE : X.IsPerfect (DerivedCategory.Q.obj (kInjectiveModel X L)) := by
    obtain ⟨N, hN, ⟨eN⟩⟩ := hL
    exact ⟨N, hN, ⟨eN ≪≫ (kInjectiveModelIso X L).symm⟩⟩
  obtain ⟨g, hgdef⟩ := exists_Q_map_eq_of_isKInjective X
    (A := structureSheafComplex X) (I := kInjectiveModel X (derivedStructureSheaf X))
    (kInjectiveModelIso X (derivedStructureSheaf X)).inv
  have hg : IsIso (DerivedCategory.Q.map g) := by rw [hgdef]; infer_instance
  obtain ⟨H, f, hH, hf0⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (sheafHomComplex X (kInjectiveModel X L)
      (kInjectiveModel X (derivedStructureSheaf X))).obj
  have hf : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hf0
  have hA := isKFlat_kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M))
  have hdtu : IsIso (DerivedCategory.Q.map (diagonalTensorUnit X
      (A := kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M))))) :=
    CategoryTheory.Functor.map_isIso _ _
  have htt : IsIso (DerivedCategory.Q.map (tensorTotalMap X
      (𝟙 (kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M)))) g)) :=
    isIso_Q_map_tensorTotalMap_right X _ g hA hg
  obtain ⟨q, hqdef⟩ := exists_Q_map_eq_of_isKInjective X
    (A := tensorTotal X (kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M)))
      (kInjectiveModel X (derivedStructureSheaf X)))
    (I := kInjectiveModel X M)
    (inv (DerivedCategory.Q.map (tensorTotalMap X
        (𝟙 (kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M)))) g)) ≫
      inv (DerivedCategory.Q.map (diagonalTensorUnit X
        (A := kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M))))) ≫
      (kFlatModelIso X (DerivedCategory.Q.obj (kInjectiveModel X M))).hom)
  have hqiso : IsIso (DerivedCategory.Q.map q) := by rw [hqdef]; infer_instance
  have hq : DerivedCategory.Q.map (diagonalTensorUnit X
        (A := kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M))) ≫
      tensorTotalMap X (𝟙 (kFlatModel X (DerivedCategory.Q.obj (kInjectiveModel X M)))) g ≫ q) =
      (kFlatModelIso X (DerivedCategory.Q.obj (kInjectiveModel X M))).hom := by
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, hqdef]
    simp only [IsIso.hom_inv_id_assoc]
  have hkey := derivedTensorDualToSheafHom_comp_derivedSheafHomComparison X g hg f hH hf hA
    (kFlatModelIso X (DerivedCategory.Q.obj (kInjectiveModel X M))) q hqiso hq
  have : IsIso (derivedTensorHomDiagonal X (DerivedCategory.Q.obj (kInjectiveModel X M))
      (derivedStructureSheaf X) (DerivedCategory.Q.obj (kInjectiveModel X L))) :=
    isIso_derivedTensorHomDiagonal_of_isPerfect X _ _ _ hQE
  have : IsIso (derivedTensorDualToSheafHom X
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (DerivedCategory.Q.obj (kInjectiveModel X L))
        (DerivedCategory.Q.obj (kInjectiveModel X M)) ≫
      (derivedSheafHomComparison X (kInjectiveModel X L) (kInjectiveModel X M)).hom) := by
    rw [hkey]; infer_instance
  exact IsIso.of_isIso_comp_right _
    (derivedSheafHomComparison X (kInjectiveModel X L) (kInjectiveModel X M)).hom

end Perfect

end AlgebraicGeometry.RingedSite

end
