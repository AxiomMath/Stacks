module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap

/-!
# The relative cup product on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `K, M ∈ D(𝒪_X)`.  There is a
canonical morphism

`Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M)`,

the *relative cup product*, which is the adjoint transpose of

`Lf^*(Rf_*K ⊗^L_{𝒪_Y} Rf_*M) ≅ Lf^*Rf_*K ⊗^L_{𝒪_X} Lf^*Rf_*M ⟶ K ⊗^L_{𝒪_X} M`,

where the first map is the derived pullback-tensor comparison of Stacks 079U and the second is
the counit of `Lf^* ⊣ Rf_*` in both tensor factors.

## Main definitions

* `Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap`: the abstract form of the
  construction, for an adjunction `L ⊣ R` with binary functors `A` on the source and `B` on the
  target and a morphism of bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct`: the relative cup product
  `Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M)` for a morphism of ringed spaces.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_eq`: the relative cup product
  is the abstract construction at `Lf^* ⊣ Rf_*` and the comparison of Stacks 079U.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_eq_projectionFormulaMap`: the
  relative cup product factors as the derived projection-formula map of Stacks 0B53 for the
  pair `(K, Rf_*M)` followed by the counit of `Lf^* ⊣ Rf_*` in the second tensor factor.
* `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural`, and its one-variable
  forms `relativeCupProduct_natural_left` and `relativeCupProduct_natural_right`: the relative
  cup product is natural in `K` and in `M`, for arbitrary derived modules and with no
  finiteness, flatness or quasi-coherence hypothesis.
* `Stacks.Cohomology.DerivedRelativeCupProduct.isIso_adjunctionBitensorMap_of_isIso`: the abstract
  construction is invertible as soon as the unit of `L ⊣ R` is invertible at the tensor product
  of the two sections, the comparison `α` is invertible there, and the counit is invertible at
  the two arguments.

## Implementation notes

*What the source asserts.*  Stacks 0B68 is a remark: it constructs the map and says nothing
else.  It claims no associativity, commutativity, unit compatibility, naturality, or
compatibility with composition of morphisms of ringed spaces, so the only clause of 0B68 below
is the construction itself; the naturality statements are supplied in addition.

*The shape of the construction.*  The relative cup product differs from the derived
projection-formula map of Stacks 0B53 only in applying the counit of `Lf^* ⊣ Rf_*` to **both**
tensor factors rather than to the first one alone.  Accordingly the formal content is isolated
in `adjunctionBitensorMap`, the doubled-counit analogue of
`CategoryTheory.adjunctionTensorMap`, and
`relativeCupProduct_eq_projectionFormulaMap` records that the two constructions agree after one
further counit.

*The inputs are the repository's own.*  The adjunction is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`, Stacks 079W for an
arbitrary morphism of ringed spaces; the two derived tensor products are
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of Stacks 06YU at the ringed sites
of opens of `X` and of `Y`; and the bifunctorial comparison `α` is
`Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison`, the isomorphism of
Stacks 079U.  Bifunctoriality of the latter is what the construction needs, since it is
evaluated at the pair `(Rf_*K, Rf_*M)` of arbitrary objects of `D(𝒪_Y)`.

*The four sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for
`AddCommGrpCat.{u}` on the two sites of opens are the binders the derived tensor product of
Stacks 06YU is stated under.  Both are `Prop`s and both are inhabited for every ringed space, by
`Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, so they are not a weakening.

## References

* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The abstract relative cup product `A(R G, R G') ⟶ R (B (G, G'))`: the adjoint transpose of
`α` followed by the counit of `L ⊣ R` in both factors of `B`. -/
def adjunctionBitensorMap (G G' : D) :
    A.obj (R.obj G, R.obj G') ⟶ R.obj (B.obj (G, G')) :=
  adj.homEquiv _ _ (α.app (R.obj G, R.obj G') ≫
    B.map (adj.counit.app G ×ₘ adj.counit.app G'))

/-- The abstract relative cup product is the abstract projection-formula map of
`CategoryTheory.adjunctionTensorMap` evaluated at `R G'`, followed
by the counit of `L ⊣ R` in the second factor. -/
lemma adjunctionBitensorMap_eq_adjunctionTensorMap (G G' : D) :
    adjunctionBitensorMap adj A B α G G' =
      CategoryTheory.adjunctionTensorMap adj A B α G (R.obj G') ≫
        R.map (B.map (𝟙 G ×ₘ adj.counit.app G')) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap CategoryTheory.adjunctionTensorMap
  rw [Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  rw [Category.assoc, ← Functor.map_comp]
  simp

/-- The abstract relative cup product is natural in both arguments. -/
lemma adjunctionBitensorMap_natural {G G' H H' : D} (g : G ⟶ H) (g' : G' ⟶ H') :
    A.map (R.map g ×ₘ R.map g') ≫ adjunctionBitensorMap adj A B α H H' =
      adjunctionBitensorMap adj A B α G G' ≫ R.map (B.map (g ×ₘ g')) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha : L.map (A.map (R.map g ×ₘ R.map g')) ≫ α.app (R.obj H, R.obj H') =
      α.app (R.obj G, R.obj G') ≫ B.map (L.map (R.map g) ×ₘ L.map (R.map g')) :=
    α.naturality (R.map g ×ₘ R.map g')
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  congr 2
  exact Prod.hom_ext (adj.counit.naturality g) (adj.counit.naturality g')

/-- **The abstract relative cup product is invertible when its three inputs are.**  Being the
adjoint transpose `η ≫ R(α ≫ B(ε, ε))`, it is an isomorphism as soon as the unit of `L ⊣ R` is
invertible at `A(R G, R G')`, the comparison `α` is invertible at `(R G, R G')`, and the counit
is invertible at `G` and at `G'`.  The same statement is
`Stacks.Cohomology.DerivedRelativeCupProduct.isIso_adjunctionBitensorMap` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointCupProductNondegeneracy`,
which
imports `GlobalCupProduct` and so cannot be imported by it; this copy sits below both. -/
lemma isIso_adjunctionBitensorMap_of_isIso (G G' : D)
    (hunit : IsIso (adj.unit.app (A.obj (R.obj G, R.obj G'))))
    (hα : IsIso (α.app (R.obj G, R.obj G')))
    (hG : IsIso (adj.counit.app G)) (hG' : IsIso (adj.counit.app G')) :
    IsIso (adjunctionBitensorMap adj A B α G G') := by
  have hprod : IsIso (adj.counit.app G ×ₘ adj.counit.app G' :
      (L.obj (R.obj G), L.obj (R.obj G')) ⟶ (G, G')) :=
    ((asIso (adj.counit.app G)).prod (asIso (adj.counit.app G'))).isIso_hom
  rw [adjunctionBitensorMap, adj.homEquiv_unit]
  infer_instance

end Abstract

universe u

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The relative cup product** `Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M)`: the adjoint
transpose of the derived pullback-tensor comparison of Stacks 079U followed by the counit of
`Lf^* ⊣ Rf_*` in both tensor factors.  It is defined for arbitrary `K, M ∈ D(𝒪_X)`. -/
@[stacks 0B68]
def relativeCupProduct
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj M) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).obj M) :=
  adjunctionBitensorMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) K M

/-- The relative cup product is the abstract doubled-counit adjunction morphism for the derived
adjunction `Lf^* ⊣ Rf_*` and the two derived tensor products. -/
theorem relativeCupProduct_eq
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    relativeCupProduct f K M =
      adjunctionBitensorMap
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) K M :=
  rfl

/-- The relative cup product is the derived projection-formula morphism of Stacks 0B53 for the
pair `(K, Rf_*M)`, followed by the counit `Lf^*Rf_*M ⟶ M` in the second tensor factor. -/
theorem relativeCupProduct_eq_projectionFormulaMap
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    relativeCupProduct f K M =
      Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f K
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj M) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit.app
              M)) := by
  rw [relativeCupProduct_eq, Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq,
    ← uncurry_map_id_left
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf) K
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit.app M)]
  exact adjunctionBitensorMap_eq_adjunctionTensorMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) K M

/-- The relative cup product is natural in both derived modules on the source. -/
@[stacks 0B68 "naturality in both complexes"]
theorem relativeCupProduct_natural
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map k ×ₘ
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map m) ≫
        relativeCupProduct f K' M' =
      relativeCupProduct f K M ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
              (k ×ₘ m)) :=
  adjunctionBitensorMap_natural
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f) k m

/-- The relative cup product is natural in the first derived module. -/
@[stacks 0B68 "naturality in the first complex"]
theorem relativeCupProduct_natural_left
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (k : K ⟶ K')
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map k)).app
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj M) ≫
        relativeCupProduct f K' M =
      relativeCupProduct f K M ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map k).app M) :=
  Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_natural_left_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit k M

/-- The relative cup product is natural in the second derived module. -/
@[stacks 0B68 "naturality in the second complex"]
theorem relativeCupProduct_natural_right
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (m : M ⟶ M') :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj K)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map m) ≫
        relativeCupProduct f K M' =
      relativeCupProduct f K M ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj K).map m) :=
  Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_natural_right_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).counit K m

end Stacks.Cohomology.DerivedRelativeCupProduct

end
