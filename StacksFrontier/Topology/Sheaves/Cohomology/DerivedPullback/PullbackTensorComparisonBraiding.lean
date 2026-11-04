module

public import StacksFrontier.CategoryTheory.BifunctorComparisonConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatPairDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoAlongAComposite

/-!
# The derived pullback–tensor comparison is braided

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  The comparison of
[Stacks, Tag 079U],

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`,

carries the commutativity constraint of the symmetric monoidal derived category of
[Stacks, Tag 0FPT] on `D(𝒪_Y)` to the one on `D(𝒪_X)`: `Lf^*` is a *braided* functor for the
derived tensor product of [Stacks, Tag 06YU], and not merely a functor with a comparison.

This is the fusion of the two halves that were available separately.  On a pair of K-flat
complexes `K, L` the comparison is computed by the ordinary total tensor complex
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_derivedToTensor`),
the commutativity constraint of Tag 0FPT is computed there by the Koszul symmetry of complexes
(`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison_braiding`), and the comparison of
total tensor complexes of [Stacks, Tag 01CD] is braided for that symmetry
(`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding`).  The diagram
chase joining them is `CategoryTheory.bifunctor_comparison_braiding_of_models`, and the passage
from K-flat representatives to all of `D(𝒪_Y) × D(𝒪_Y)` is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding_app_of_kFlat`: the
  compatibility at a pair of K-flat complexes.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`: **the
  compatibility for arbitrary `M, N ∈ D(𝒪_Y)`**, with no finiteness, flatness or
  quasi-coherence hypothesis.

## Implementation notes

*Where the content is.*  Not here.  Each of the three inputs above is proved, the chase that
joins them is carried out for an arbitrary functor and arbitrary bifunctors in
`StacksFrontier.CategoryTheory.BifunctorComparisonConstraints`, and this file supplies the
instantiation: the two comparisons of Tag 06YU read at the pinned spelling of Tag 0FPT
(`canonicalComparisonHom`), the naturality of the commutativity constraint, and the
complex-level identity carried into the derived category along
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans`.

*The inverse direction of the comparison of total complexes.*
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding` is stated for the
tensorator `pullbackTensorComplexMu`, which points `f^*K ⊗ f^*L ⟶ f^*(K ⊗ L)`; the model
identification of Tag 079U has the *other* direction, since
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso` is the comparison
`f^*Tot(K ⊗ L) ⟶ Tot(f^*K ⊗ f^*L)`.  `pullbackTensorComplexMuHom` names that direction at the
monoidal spelling of the total tensor complex, with a `rfl` lemma identifying it with the
component of the bifunctor isomorphism, and `pullbackTensorComplexIso_braiding_hom` is the
identity read on it.  No total complex is taken apart.

*Seating.*  The instances are those of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexAssociator`,
re-attributed rather than re-declared: a second copy of any of them would be a second instance
term, and the statements of the files this one builds on mention the first.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open scoped CategoryTheory.Prod
open Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory

-- `TopCat.Sheaf` and `TopCat.Presheaf.IsSheaf` join the list because the canonical tensor
-- product's ring sheaf is `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf`, whose argument has
-- type `TopCat.Sheaf CommRingCat Z.carrier` while `ringSheaf` asks for a
-- `CategoryTheory.Sheaf (Opens.grothendieckTopology Z.carrier) CommRingCat`.  The two are the
-- same type, but only once `TopCat.Sheaf` is unfolded, so without the attribute every statement
-- here is ill-typed at `implicit` transparency and `rw` reports that it did not find a pattern
-- the goal visibly contains.
--
-- `structureSheafRing` is deliberately *not* in the list.  It is globally
-- `@[instance_reducible]`, a status that already unfolds at `implicit` transparency, so naming
-- it here adds nothing; and `[implicit_reducible]` is the strictly higher status, so naming it
-- here would move it off `instances` transparency and hide it from typeclass *search* -- the
-- one thing its own declaration site asks for, the instances on `SheafOfModules R` being found
-- only while `R` reduces to a closed term.
attribute [local implicit_reducible]
  StacksDraft.KFlat.modulePullback CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-! ### The comparison of Tag 06YU at the pinned spelling of Tag 0FPT -/

section Comparison

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The canonical map to the ordinary total tensor complex is, on K-flat complexes, the
comparison of Tag 06YU at the spelling Tag 0FPT's coherence clauses are written at.**  Both are
the `comparison` field of Tag 06YU; the left-hand side reaches it through the `toTensor` field
and the right-hand side through
`Stacks.SheafOfModules.DerivedMonoidal.canonicalComparison`. -/
theorem derivedToTensorNatTrans_app_eq_canonicalComparisonHom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    (derivedToTensorNatTrans Z).app (K, L) = canonicalComparisonHom Z.sheaf K L hK hL :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Z.sheaf).toTensor_eq_comparison K L hK hL

/-- The comparison of Tag 06YU is an isomorphism on K-flat complexes, at the pinned spelling. -/
theorem isIso_canonicalComparisonHom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    IsIso (canonicalComparisonHom Z.sheaf K L hK hL) :=
  Iso.isIso_hom (canonicalComparison Z.sheaf K L hK hL)

/-- **The commutativity constraint of Tag 0FPT is natural in both derived modules**, at the
pinned spelling `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` and with the
bifunctor written uncurried, which is the shape the comparison of Tag 079U is a
transformation of. -/
theorem canonicalBraidingHom_naturality
    {G G' H H' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)}
    (u : G ⟶ H) (v : G' ⟶ H') :
    (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map (u ×ₘ v) ≫
        canonicalBraidingHom Z.sheaf H H' =
      canonicalBraidingHom Z.sheaf G G' ≫
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf)).map (v ×ₘ u) :=
  letI := canonicalDerivedMonoidal Z.sheaf
  letI := canonicalDerivedSymmetric Z.sheaf
  BraidedCategory.braiding_naturality u v

end Comparison

/-! ### The comparison of total tensor complexes, in the direction Tag 079U presents -/

section Complexes

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of total tensor complexes `f^*Tot(K ⊗ L) ⟶ Tot(f^*K ⊗ f^*L)`**, read at
the monoidal spelling of the total tensor product.  This is the inverse of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu`, ascribed once at the
spelling the Koszul symmetry is written at. -/
def pullbackTensorComplexMuHom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackComplex f).obj (K ⊗ L) ⟶
      (pullbackComplex f).obj K ⊗ (pullbackComplex f).obj L :=
  (pullbackTensorComplexIsoOfIsIso f K L).hom

/-- `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMuHom` is the component of the
bifunctorial comparison of total tensor complexes of Tag 079U. -/
theorem pullbackTensorComplexMuHom_eq
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMuHom f K L = (pullbackTensorComplexNatIso f).hom.app (K, L) :=
  rfl

/-- `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMuHom` is inverse to the
tensorator. -/
theorem pullbackTensorComplexMuHom_comp_mu
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMuHom f K L ≫ pullbackTensorComplexMu f K L = 𝟙 _ :=
  (pullbackTensorComplexIsoOfIsIso f K L).hom_inv_id

/-- `Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexMu` is inverse to it. -/
theorem mu_comp_pullbackTensorComplexMuHom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMu f K L ≫ pullbackTensorComplexMuHom f K L = 𝟙 _ :=
  (pullbackTensorComplexIsoOfIsIso f K L).inv_hom_id

/-- **The Koszul symmetry of total tensor complexes**, with its source and target written
through `Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` rather than through `⊗`.

The two spellings of the total tensor complex are the same object, but the identification is a
conversion the `HomologicalComplex` instance arguments make expensive, and `getColimitCocone` is
not exposed, so it cannot be finished by unfolding.  Everything below is written at the
`totalComplexPair` spelling, which is the one the model identification of Tag 079U uses, and
this definition pays for the identification **once**. -/
def complexBraidingPair (Z : RingedSpace.{u, u})
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (K, L) ⟶
      (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).obj (L, K) :=
  (β_ K L).hom

/-- `Stacks.Cohomology.DerivedPullbackTensor.complexBraidingPair` is the Koszul symmetry. -/
theorem complexBraidingPair_eq (Z : RingedSpace.{u, u})
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    complexBraidingPair Z K L = (β_ K L).hom :=
  rfl

/-- **The comparison `f^*Tot(K ⊗ L) ⟶ Tot(f^*K ⊗ f^*L)` of Tag 01CD is braided for the Koszul
symmetry.**  This is
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexIso_braiding`, which is stated for
the tensorator, read on the inverse comparison: both the symmetry and the tensorator are
isomorphisms, so the identity transposes. -/
theorem pullbackTensorComplexIso_braiding_hom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorComplexMuHom f K L ≫
        (β_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom =
      (pullbackComplex f).map (β_ K L).hom ≫ pullbackTensorComplexMuHom f L K := by
  have hβ : (β_ ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom =
      pullbackTensorComplexMu f K L ≫
        (pullbackComplex f).map (β_ K L).hom ≫ pullbackTensorComplexMuHom f L K := by
    rw [← Category.assoc, pullbackTensorComplexIso_braiding f K L, Category.assoc,
      mu_comp_pullbackTensorComplexMuHom, Category.comp_id]
  rw [hβ, ← Category.assoc, pullbackTensorComplexMuHom_comp_mu, Category.id_comp]

/-- **The comparison of Tag 01CD is braided**, with every term written at the
`totalComplexPair` spelling of the total tensor complex.  This is
`pullbackTensorComplexIso_braiding_hom`; the identification of the two spellings is paid for
here, once, and nothing below mentions `⊗`. -/
theorem pullbackTensorComplexIso_braiding_pair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso f).hom.app (K, L) ≫
        complexBraidingPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L) =
      (pullbackComplex f).map (complexBraidingPair Y K L) ≫
        (pullbackTensorComplexNatIso f).hom.app (L, K) :=
  pullbackTensorComplexIso_braiding_hom f K L

end Complexes

/-! ### The compatibility on K-flat representatives -/

section KFlat

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The model of `Lf^*(QK ⊗^L QL)` on the target: the derived pullback of a complex, then the
comparison of total tensor complexes. -/
def pullbackTensorModel
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L))) ⟶
      DerivedCategory.Q.obj
        ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
          ((pullbackComplex f).obj K, (pullbackComplex f).obj L)) :=
  (derivedPullbackNatTrans f).app
      ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).obj (K, L)) ≫
    DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L))

/-- **The model identification of Tag 079U, with both comparisons of Tag 06YU at the pinned
spelling of Tag 0FPT.**  This is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_derivedToTensor`
with the two canonical maps to the ordinary total tensor complex rewritten as the comparison of
Tag 06YU, which is the form the diagram chase consumes. -/
theorem derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          canonicalComparisonHom X.sheaf ((pullbackComplex f).obj K)
              ((pullbackComplex f).obj L) (kFlat_modulePullback_unconditional f K hK)
              (kFlat_modulePullback_unconditional f L hL) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (canonicalComparisonHom Y.sheaf K L hK hL) ≫ pullbackTensorModel f K L := by
  rw [← derivedToTensorNatTrans_app_eq_canonicalComparisonHom X _ _
      (kFlat_modulePullback_unconditional f K hK) (kFlat_modulePullback_unconditional f L hL),
    ← derivedToTensorNatTrans_app_eq_canonicalComparisonHom Y K L hK hL]
  exact derivedPullbackTensorIso_hom_app_comp_derivedToTensor f K L hK hL

/-- **The model of `Lf^*(QK ⊗^L QL)` carries the Koszul symmetry of complexes to the Koszul
symmetry of complexes.**  The derived pullback of a complex is natural, and the comparison of
total tensor complexes is braided (`pullbackTensorComplexIso_braiding_pair`). -/
theorem pullbackTensorModel_braiding_pair
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorModel f K L ≫
          DerivedCategory.Q.map
            (complexBraidingPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (DerivedCategory.Q.map (complexBraidingPair Y K L)) ≫
        pullbackTensorModel f L K := by
  have hQ : DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L)) ≫
        DerivedCategory.Q.map
          (complexBraidingPair X ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)) =
      DerivedCategory.Q.map ((pullbackComplex f).map (complexBraidingPair Y K L)) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (L, K)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (pullbackTensorComplexIso_braiding_pair f K L)).trans
        (DerivedCategory.Q.map_comp _ _))
  have hnat := (derivedPullbackNatTrans f).naturality (complexBraidingPair Y K L)
  dsimp only [pullbackTensorModel]
  rw [Category.assoc, hQ, reassoc_of% hnat]

/-- `pullbackTensorModel_braiding_pair` with the two symmetries read as the commutativity
constraint of complexes at the pinned spelling of Tag 0FPT, which is the shape the diagram chase
consumes. -/
theorem pullbackTensorModel_braiding
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    pullbackTensorModel f K L ≫ complexBraidingHom X.sheaf ((pullbackComplex f).obj K)
          ((pullbackComplex f).obj L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (complexBraidingHom Y.sheaf K L) ≫ pullbackTensorModel f L K :=
  pullbackTensorModel_braiding_pair f K L

/-- **The comparison of Tag 079U carries the commutativity constraint of Tag 0FPT on `D(𝒪_Y)`
to the one on `D(𝒪_X)`, at a pair of K-flat complexes.**  The chase is
`CategoryTheory.bifunctor_comparison_braiding_of_models`; the models are the comparison of
Tag 06YU on both sides, their compatibility with the constraints is the braiding clause of
Tag 0FPT, and the identity linking the two models of the tensor product is
`pullbackTensorModel_braiding`. -/
theorem derivedPullbackTensorIso_braiding_app_of_kFlat
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (canonicalBraidingHom Y.sheaf (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj L, DerivedCategory.Q.obj K) =
      (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        canonicalBraidingHom X.sheaf
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
            (DerivedCategory.Q.obj K))
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
            (DerivedCategory.Q.obj L)) := by
  have hKx := kFlat_modulePullback_unconditional f K hK
  have hLx := kFlat_modulePullback_unconditional f L hL
  have hpair : IsIso ((derivedPullbackNatTrans f).app L ×ₘ (derivedPullbackNatTrans f).app K) := by
    rw [isIso_prod_iff]
    exact ⟨isIso_derivedPullbackNatTrans_app f L hL, isIso_derivedPullbackNatTrans_app f K hK⟩
  have hiso : IsIso ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
      ((derivedPullbackNatTrans f).app L ×ₘ (derivedPullbackNatTrans f).app K) ≫
    canonicalComparisonHom X.sheaf ((pullbackComplex f).obj L)
      ((pullbackComplex f).obj K) hLx hKx) :=
    IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hpair)
      (isIso_canonicalComparisonHom X _ _ hLx hKx)
  exact bifunctor_comparison_braiding_of_models
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (derivedPullbackTensorIso f).hom
    (canonicalBraidingHom Y.sheaf (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (canonicalBraidingHom X.sheaf (DerivedCategory.Q.obj ((pullbackComplex f).obj K))
      (DerivedCategory.Q.obj ((pullbackComplex f).obj L)))
    (canonicalBraidingHom X.sheaf
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj K))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj L)))
    (@IsIso.mono_of_iso _ _ _ _ _ hiso)
    (canonicalComparison_braiding Y.sheaf K L hK hL)
    (canonicalComparison_braiding X.sheaf ((pullbackComplex f).obj K)
      ((pullbackComplex f).obj L) hKx hLx)
    (canonicalBraidingHom_naturality X ((derivedPullbackNatTrans f).app K)
      ((derivedPullbackNatTrans f).app L))
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f K L hK hL)
    (derivedPullbackTensorIso_hom_app_comp_canonicalComparisonHom f L K hL hK)
    (pullbackTensorModel_braiding f K L)

end KFlat

/-! ### The compatibility for arbitrary derived modules -/

section Descent

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The commutativity constraint of Tag 0FPT as a natural transformation** of the uncurried
derived tensor bifunctor into its composite with the swap of the two factors.  Its components
are `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` and its naturality is
`canonicalBraidingHom_naturality`; packaging it this way is what lets the two sides of the
commutativity compatibility be assembled by whiskering, so that their naturality costs
nothing. -/
def canonicalBraidingNatTrans (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf) where
  app MN := canonicalBraidingHom Z.sheaf MN.1 MN.2
  naturality _ _ g := canonicalBraidingHom_naturality Z g.1 g.2

/-- The left-hand side of the commutativity compatibility, as a transformation
`(M, N) ↦ Lf^*(M ⊗^L N) ⟶ Lf^*N ⊗^L Lf^*M` on `D(𝒪_Y) × D(𝒪_Y)`: the derived pullback of the
commutativity constraint, then the comparison of Tag 079U at the swapped pair. -/
def braidingThenComparison :
    pullbackOfTensor f ⟶ CategoryTheory.Prod.swap _ _ ⋙ tensorOfPullbacks f :=
  Functor.whiskerRight (canonicalBraidingNatTrans Y)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ≫
    Functor.whiskerLeft (CategoryTheory.Prod.swap _ _) (derivedPullbackTensorIso f).hom

/-- The right-hand side: the comparison of Tag 079U, then the commutativity constraint of the
derived pullbacks. -/
def comparisonThenBraiding :
    pullbackOfTensor f ⟶ CategoryTheory.Prod.swap _ _ ⋙ tensorOfPullbacks f :=
  (derivedPullbackTensorIso f).hom ≫
    Functor.whiskerLeft
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f))
      (canonicalBraidingNatTrans X)

/-- The components of `braidingThenComparison`. -/
theorem braidingThenComparison_app
    (M N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (braidingThenComparison f).app (M, N) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (canonicalBraidingHom Y.sheaf M N) ≫
        (derivedPullbackTensorIso f).hom.app (N, M) :=
  rfl

/-- The components of `comparisonThenBraiding`. -/
theorem comparisonThenBraiding_app
    (M N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (comparisonThenBraiding f).app (M, N) =
      (derivedPullbackTensorIso f).hom.app (M, N) ≫
        canonicalBraidingHom X.sheaf
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj M)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj N) :=
  rfl

/-- **The derived pullback–tensor comparison of Tag 079U is braided**, as an identity of
natural transformations on `D(𝒪_Y) × D(𝒪_Y)`.

Both sides are transformations `Lf^*(M ⊗^L_{𝒪_Y} N) ⟶ Lf^*N ⊗^L_{𝒪_X} Lf^*M`, and `D(𝒪_Y)` is
the localization of the K-flat objects of the homotopy category at the quasi-isomorphisms
(Stacks 06YS), so they agree as soon as they agree at a pair of K-flat representatives. -/
theorem braidingThenComparison_eq :
    braidingThenComparison f = comparisonThenBraiding f :=
  natTrans_ext_of_kFlat Y _ _ fun K L hK hL =>
    (braidingThenComparison_app f _ _).trans
      ((derivedPullbackTensorIso_braiding_app_of_kFlat f K L hK hL).trans
        (comparisonThenBraiding_app f _ _).symm)

/-- **The derived pullback–tensor comparison of Tag 079U carries the commutativity constraint of
the symmetric monoidal derived category of Tag 0FPT on `D(𝒪_Y)` to the one on `D(𝒪_X)`**, for
arbitrary `M, N ∈ D(𝒪_Y)` and with no finiteness, flatness or quasi-coherence hypothesis.

Equivalently: `Lf^*` is a braided functor for the derived tensor product of Tag 06YU. -/
theorem derivedPullbackTensorIso_braiding
    (M N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          (canonicalBraidingHom Y.sheaf M N) ≫
        (derivedPullbackTensorIso f).hom.app (N, M) =
      (derivedPullbackTensorIso f).hom.app (M, N) ≫
        canonicalBraidingHom X.sheaf
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj M)
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj N) :=
  (braidingThenComparison_app f M N).symm.trans
    ((congrArg (fun τ => τ.app (M, N)) (braidingThenComparison_eq f)).trans
      (comparisonThenBraiding_app f M N))

end Descent

end Stacks.Cohomology.DerivedPullbackTensor

end
