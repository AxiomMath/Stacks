module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.DerivedTensorDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.FilteredColimitOfKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionExists

/-!
# The derived tensor product on a ringed site commutes with direct sums

Let `(C, O)` be a ringed site, let `T` be a derived tensor product datum on it
([Stacks, Tag 06YU], `Stacks.SheafOfModules.DerivedTensorProduct`) and let `L` be an object of
`D(O)`. Then `K ↦ K ⊗ᴸ_O L` commutes with direct sums indexed by any type of the universe of the
sections.

This is `Stacks.Duality.preservesColimitsOfShape_discrete_derivedTensorRight` of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/DerivedTensorDirectSums.lean`, with
two pins removed. That statement is about a scheme, and about the one derived tensor product
`Stacks.Cohomology.TorAmplitude.derTensor` of its ringed space, at the one model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` that its file has in scope. Neither
restriction is used: the argument consumes only the `comparisonRight` field of a derived tensor
product datum and the existence of a K-flat representative, and both are available on an
arbitrary ringed site, for an arbitrary datum and at an arbitrary chosen derived category.

Removing the pins is what a consumer of [Stacks, Tag 08JJ] needs. That tag is stated for
`Stacks.SheafOfModules.derivedTensorProductFunctor`, the bifunctor of
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, and under
`CategoryTheory.HasDerivedCategory.standard`; that bifunctor is a *different* term from
`Stacks.Cohomology.TorAmplitude.derTensor`, both being opaque `irreducible_def` constructions, so
the scheme-level result says nothing about it.

## The argument

It is the one of the cited file, with the scheme replaced by the ringed site.

* At the level of complexes, `K ↦ Tot(K ⊗_O L)` commutes with direct sums. Tensoring with a fixed
  sheaf of modules does ([Stacks, Tag 05NB], `preservesColimits_sheafTensorFlipObj`), colimits of
  double complexes are computed in each bidegree
  (`Stacks.Duality.preservesColimitsOfShape_mapBifunctorHomologicalComplexFlipObj`), and
  totalisation commutes with them because `Tot(Z)ⁿ` is a coproduct of the `Z^{p,q}`
  (`CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor`).
* `Q : C(O) ⥤ D(O)` commutes with direct sums indexed by the Grothendieck universe at *any*
  chosen model (`Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts`) and is
  essentially surjective, so direct-sum preservation descends through it
  (`Stacks.Duality.preservesColimitsOfShape_discrete_of_essSurj`).
* The isomorphism it descends along is the `comparisonRight` field of the datum, read in the left
  variable at a K-flat representative of `L` ([Stacks, Tag 06YS],
  `Stacks.SheafOfModules.exists_kFlat_quasiIso`).

## Main results

* `Stacks.SheafOfModules.preservesColimitsOfShape_discrete_tensorComplexFlipObj` — the
  complex-level statement.
* `Stacks.SheafOfModules.preservesColimitsOfShape_discrete_derivedTensorRight` — **the derived
  tensor product with a fixed right factor commutes with direct sums.**

## References

* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **`K ↦ Tot(K ⊗_O L)` commutes with direct sums**, for a fixed complex `L` of `O`-modules.
The total tensor complex of [Stacks, Tag 06YM] is the tensor double complex followed by
totalisation, and both commute with direct sums — the first by [Stacks, Tag 05NB] in each
bidegree, the second because `Tot(Z)ⁿ` is a coproduct of the `Z^{p,q}`. -/
theorem preservesColimitsOfShape_discrete_tensorComplexFlipObj (J : Type u)
    (L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) :
    PreservesColimitsOfShape (Discrete J)
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj L) := by
  have hbi : PreservesColimitsOfShape (Discrete J)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj L) :=
    Stacks.Duality.preservesColimitsOfShape_mapBifunctorHomologicalComplexFlipObj _ L fun Y => by
      have := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj X.O Y
      infer_instance
  have htf := CochainComplex.KFlatBifunctor.preservesColimitsOfShape_totalFunctor
    (D := RingedSite.Modules.{u, u, u} X) (J := Discrete J)
  exact preservesColimitsOfShape_of_natIso
    (Stacks.Duality.map₂HomologicalComplexFlipObjIsoTotal
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L).symm

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]

/-- **The derived tensor product with a fixed right factor commutes with direct sums.** For every
ringed site, every derived tensor product datum `T` on it ([Stacks, Tag 06YU]), every object `L`
of `D(O)` and every index type of the universe of the sections, the endofunctor
`K ↦ K ⊗ᴸ_O L` of `D(O)` preserves coproducts of that shape.

Choose a K-flat complex `Lc` representing `L` ([Stacks, Tag 06YS]). Read in `K`, the field
`comparisonRight` of `T` is an isomorphism of functors
`Q ⋙ (- ⊗ᴸ Q(Lc)) ≅ Tot(- ⊗ Lc) ⋙ Q`; the right-hand side commutes with direct sums because
`Tot(- ⊗ Lc)` does and `Q` does, and that descends to the left-hand factor because `Q` is
essentially surjective. -/
theorem preservesColimitsOfShape_discrete_derivedTensorRight
    (T : DerivedTensorProduct.{u, u, u, d} X) (J : Type u)
    (L : DerivedCategory (RingedSite.Modules.{u, u, u} X)) :
    PreservesColimitsOfShape (Discrete J) (T.tensor.flip.obj L) := by
  obtain ⟨Lc, hLc, ⟨eL⟩⟩ := exists_kFlat_iso X L
  have hQ : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := RingedSite.Modules.{u, u, u} X)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts
      (RingedSite.Modules.{u, u, u} X) J
  have key : PreservesColimitsOfShape (Discrete J)
      (T.tensor.flip.obj (DerivedCategory.Q.obj Lc)) := by
    refine Stacks.Duality.preservesColimitsOfShape_discrete_of_essSurj
      (C₀ := CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)
      (D₀ := DerivedCategory (RingedSite.Modules.{u, u, u} X))
      (DerivedCategory.Q (C := RingedSite.Modules.{u, u, u} X))
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj Lc)
      (T.tensor.flip.obj (DerivedCategory.Q.obj Lc))
      (preservesColimitsOfShape_discrete_tensorComplexFlipObj X J Lc) ?_
    exact NatIso.ofComponents (fun K => T.comparisonRight K Lc hLc) (fun {K K'} f => by
      have h := T.comparisonRight_naturality f (𝟙 Lc) hLc hLc
      simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
      exact h)
  exact preservesColimitsOfShape_of_natIso (T.tensor.flip.mapIso eL)

end Stacks.SheafOfModules

end
